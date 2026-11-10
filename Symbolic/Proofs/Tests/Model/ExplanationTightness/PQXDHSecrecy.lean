/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Init.Data.String.Defs
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
public import Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas
import Symbolic.Proofs.Tests.Shared.ExplanationTightness.PQXDHSecrecyTraces
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

@[expose] public section

set_option autoImplicit false

/-!
# Tightness of Composed PQXDH Handshake-Secrecy Excuses

Mutant analysis of `AliceHandshakeWasCompromised` (`AliceInitiatorSecrecy`) and
`BobHandshakeWasCompromised` (`BobResponderSecrecy`) over reachable traces of the composed
protocol. Omitting any of the four initiator-secrecy excuse branches, any of the seven
responder-secrecy excuse branches, or any inner KEM/OPK disjunction alternative falsifies the
corresponding secrecy property via an exclusive reachable witness trace. Tightening post-exchange
`EventLogged` clauses in `BobHandshakeWasCompromised` to `i <= j` or adding positive index gaps to
any `LoggedBefore` bound likewise falsifies secrecy.
-/

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.PQXDHSecrecy

open Symbolic.Proofs.Tests.Shared.Composed.Adversary (advEkSk advForgedBobCt advForgedBobKeys
  advIkA advIkB advPqSk advPqskB advSpkB advSpkSk isBrokenDH isBrokenKEM isCompIK isCompIkOf
  isCompPQ isCompSPK not_loggedBefore_of_none not_loggedBefore_of_singleton trBrokenDHA
  trBrokenDHA_aliceDone trBrokenDHA_brokenDH trBrokenDHA_compromise_indices trBrokenDHA_knows_block
  trBrokenDHA_no_sessionStateExposed trBrokenDHA_out trBrokenDHA_reach trBrokenDHB
  trBrokenDHB_bobDone trBrokenDHB_brokenDH trBrokenDHB_compromise_indices trBrokenDHB_knows_block
  trBrokenDHB_no_sessionStateExposed trBrokenDHB_reach trIKA trIKA_bobDone trIKA_compIK
  trIKA_compromise_indices trIKA_knows_block trIKA_no_sessionStateExposed trIKA_reach trIKB
  trIKB_aliceDone trIKB_compIK trIKB_compromise_indices trIKB_knows_block
  trIKB_no_sessionStateExposed trIKB_out trIKB_reach trSPKB trSPKB_bobDone trSPKB_compSPK
  trSPKB_compromise_indices trSPKB_knows_block trSPKB_no_sessionStateExposed trSPKB_reach
  trThm7Case1_kem trThm7Case1_kem_aliceDone trThm7Case1_kem_brokenKEM trThm7Case1_kem_compIK
  trThm7Case1_kem_compSPK trThm7Case1_kem_compromise_indices trThm7Case1_kem_knows_block
  trThm7Case1_kem_no_sessionStateExposed trThm7Case1_kem_reach trThm7Case1_pq
  trThm7Case1_pq_aliceDone trThm7Case1_pq_compIK trThm7Case1_pq_compPQ trThm7Case1_pq_compSPK
  trThm7Case1_pq_compromise_indices trThm7Case1_pq_knows_block
  trThm7Case1_pq_no_sessionStateExposed trThm7Case1_pq_reach trThm7Case3_kem
  trThm7Case3_kem_aliceDone trThm7Case3_kem_brokenDH trThm7Case3_kem_brokenKEM
  trThm7Case3_kem_compromise_indices trThm7Case3_kem_knows_block
  trThm7Case3_kem_no_sessionStateExposed trThm7Case3_kem_reach trThm7Case3_pq
  trThm7Case3_pq_aliceDone trThm7Case3_pq_brokenDH trThm7Case3_pq_compPQ
  trThm7Case3_pq_compromise_indices trThm7Case3_pq_knows_block
  trThm7Case3_pq_no_sessionStateExposed trThm7Case3_pq_reach trThm9Case2 trThm9Case2_bobDone
  trThm9Case2_compIK trThm9Case2_compPQ trThm9Case2_compSPK trThm9Case2_compromise_indices
  trThm9Case2_knows_block trThm9Case2_no_sessionStateExposed trThm9Case2_opk
  trThm9Case2_opk_bobDone trThm9Case2_opk_compIK trThm9Case2_opk_compOPK trThm9Case2_opk_compPQ
  trThm9Case2_opk_compSPK trThm9Case2_opk_compromise_indices trThm9Case2_opk_knows_block
  trThm9Case2_opk_no_sessionStateExposed trThm9Case2_opk_reach trThm9Case2_reach trThm9Case3
  trThm9Case3_bobDone trThm9Case3_brokenKEM trThm9Case3_compIK trThm9Case3_compSPK
  trThm9Case3_compromise_indices trThm9Case3_knows_block trThm9Case3_no_sessionStateExposed
  trThm9Case3_opk trThm9Case3_opk_bobDone trThm9Case3_opk_brokenKEM trThm9Case3_opk_compIK
  trThm9Case3_opk_compOPK trThm9Case3_opk_compSPK trThm9Case3_opk_compromise_indices
  trThm9Case3_opk_knows_block trThm9Case3_opk_no_sessionStateExposed trThm9Case3_opk_reach
  trThm9Case3_reach trThm9Case5 trThm9Case5_bobDone trThm9Case5_brokenDH trThm9Case5_compPQ
  trThm9Case5_compromise_indices trThm9Case5_knows_block trThm9Case5_no_sessionStateExposed
  trThm9Case5_reach trThm9Case6 trThm9Case6_bobDone trThm9Case6_brokenDH trThm9Case6_brokenKEM
  trThm9Case6_compromise_indices trThm9Case6_knows_block trThm9Case6_no_sessionStateExposed
  trThm9Case6_reach)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (evIdx ikA ikB isCompromise keys1 keysOpk
  not_logged o1 oOpk opkB pqskB spkB)
open Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas (Thm7Case)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.PQXDHSecrecyTraces (
  not_atOrAfter_of_singleton not_gap_lt_of_singleton trR2 trR2_bobDone trR2_compIK
  trR2_compromise_indices trR2_compPQ trR2_compSPK trR2_keys trR2_knows_block
  trR2_no_sessionStateExposed trR2_out trR2_reach)
open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.DiffieHellman DY.PQKem
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open DY.Libsignal.PQXDH

/-! ## Parameterized queries and case decompositions -/

def ResponderSecrecyQueryWith
    (E : Participant → Bytes → Bytes → Bytes → Nat → ExecTrace → Prop)
    (tr : ExecTrace) (Knows : Bytes → Prop) : Prop :=
  ∀ a b ikA ikB spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i →
    ∀ k, IsHandshakeBlock keys k → Knows k →
    E b ikB spk pqpk i tr ∨ SessionStateExposed tr keys k

theorem responderSecrecyQueryWith_real (tr : ExecTrace) (Knows : Bytes → Prop) :
    ResponderSecrecyQueryWith AliceHandshakeWasCompromised tr Knows ↔ AliceInitiatorSecrecyQuery tr Knows := Iff.rfl

/-- `AliceInitiatorSecrecy` parameterized by the handshake-compromise predicate `E`. -/
def ResponderSecrecyWith
    (E : Participant → Bytes → Bytes → Bytes → Nat → ExecTrace → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    ResponderSecrecyQueryWith E tr (fun t => t.AttackerKnows tr)

theorem responderSecrecyWith_real :
    ResponderSecrecyWith AliceHandshakeWasCompromised ↔ AliceInitiatorSecrecy := Iff.rfl

theorem responderSecrecyWith_thm7Excuse_iff :
    ResponderSecrecyWith AliceHandshakeWasCompromised ↔ AliceInitiatorSecrecy := Iff.rfl

def InitiatorSecrecyQueryWith
    (E : Participant → Participant → Bytes → Bytes → Bytes → Bytes → Option Bytes → Nat →
      ExecTrace → Prop)
    (tr : ExecTrace) (Knows : Bytes → Prop) : Prop :=
  ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    ∀ k, IsHandshakeBlock keys k → Knows k →
    E b a ikB ikA spk pqpk opk i tr ∨ SessionStateExposed tr keys k

theorem initiatorSecrecyQueryWith_real (tr : ExecTrace) (Knows : Bytes → Prop) :
    InitiatorSecrecyQueryWith BobHandshakeWasCompromised tr Knows ↔ BobResponderSecrecyQuery tr Knows := Iff.rfl

/-- `BobResponderSecrecy` parameterized by the handshake-compromise predicate `E`. -/
def InitiatorSecrecyWith
    (E : Participant → Participant → Bytes → Bytes → Bytes → Bytes → Option Bytes → Nat →
      ExecTrace → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    InitiatorSecrecyQueryWith E tr (fun t => t.AttackerKnows tr)

theorem initiatorSecrecyWith_real :
    InitiatorSecrecyWith BobHandshakeWasCompromised ↔ BobResponderSecrecy := Iff.rfl

theorem initiatorSecrecyWith_thm9Excuse_iff :
    InitiatorSecrecyWith BobHandshakeWasCompromised ↔ BobResponderSecrecy := Iff.rfl

theorem thm7Excuse_iff_exists_case (b : Participant) (ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) :
    AliceHandshakeWasCompromised b ikB spk pqpk i tr ↔ ∃ k : Fin 4, Thm7Case b ikB spk pqpk i tr k := by
  constructor
  · rintro (⟨j, hj, hlt | ⟨hS, hPQ⟩⟩ | ⟨j, hj, hlt | hP | hK⟩)
    · exact ⟨0, j, hj, hlt⟩
    · exact ⟨1, ⟨j, hj⟩, hS, hPQ⟩
    · exact ⟨2, j, hj, hlt⟩
    · exact ⟨3, ⟨j, hj⟩, Or.inl hP⟩
    · exact ⟨3, ⟨j, hj⟩, Or.inr hK⟩
  · rintro ⟨k, hk⟩
    match k with
    | 0 => obtain ⟨j, hj, hlt⟩ := hk; exact Or.inl ⟨j, hj, Or.inl hlt⟩
    | 1 => obtain ⟨⟨j, hj⟩, hS, hPQ⟩ := hk; exact Or.inl ⟨j, hj, Or.inr ⟨hS, hPQ⟩⟩
    | 2 => obtain ⟨j, hj, hlt⟩ := hk; exact Or.inr ⟨j, hj, Or.inl hlt⟩
    | 3 => obtain ⟨⟨j, hj⟩, hPQ⟩ := hk; exact Or.inr ⟨j, hj, Or.inr hPQ⟩

/-- Seven-branch case decomposition of `BobHandshakeWasCompromised`. -/
def Thm9Case (b a : Participant) (ikB ikA spk pqpk : Bytes) (opk : Option Bytes)
    (i : Nat) (tr : ExecTrace) : Fin 7 → Prop
  | 0 => LoggedBefore (PQXDHEvent.CompromisedIK a ikA) i tr
  | 1 => LoggedBefore (PQXDHEvent.CompromisedSPK b spk) i tr
  | 2 => tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
      tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
      tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∧ OPKAbsentOrCompromised b opk i tr
  | 3 => tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
      tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
      tr.EventLogged PQXDHEvent.BrokenKEM ∧ OPKAbsentOrCompromised b opk i tr
  | 4 => LoggedBefore PQXDHEvent.BrokenDH i tr
  | 5 => tr.EventLogged PQXDHEvent.BrokenDH ∧ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk)
  | 6 => tr.EventLogged PQXDHEvent.BrokenDH ∧ tr.EventLogged PQXDHEvent.BrokenKEM

theorem thm9Excuse_iff_exists_case (b a : Participant) (ikB ikA spk pqpk : Bytes)
    (opk : Option Bytes) (i : Nat) (tr : ExecTrace) :
    BobHandshakeWasCompromised b a ikB ikA spk pqpk opk i tr ↔
      ∃ k : Fin 7, Thm9Case b a ikB ikA spk pqpk opk i tr k := by
  constructor
  · rintro ((h0 | h1 | h4) | ⟨hI, hS, hO, hP | hK⟩ | ⟨hD, hP | hK⟩)
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨4, h4⟩
    · exact ⟨2, hI, hS, hP, hO⟩
    · exact ⟨3, hI, hS, hK, hO⟩
    · exact ⟨5, hD, hP⟩
    · exact ⟨6, hD, hK⟩
  · rintro ⟨k, hk⟩
    match k with
    | 0 => exact .inl (.inl hk)
    | 1 => exact .inl (.inr (.inl hk))
    | 2 => obtain ⟨hI, hS, hP, hO⟩ := hk; exact .inr (.inl ⟨hI, hS, hO, .inl hP⟩)
    | 3 => obtain ⟨hI, hS, hK, hO⟩ := hk; exact .inr (.inl ⟨hI, hS, hO, .inr hK⟩)
    | 4 => exact .inl (.inr (.inr hk))
    | 5 => obtain ⟨hD, hP⟩ := hk; exact .inr (.inr ⟨hD, .inl hP⟩)
    | 6 => obtain ⟨hD, hK⟩ := hk; exact .inr (.inr ⟨hD, .inr hK⟩)

theorem initiatorSecrecyWith_exists_thm9Case_iff :
    InitiatorSecrecyWith
      (fun b a ikB ikA spk pqpk opk i tr => ∃ k : Fin 7, Thm9Case b a ikB ikA spk pqpk opk i tr k) ↔
      BobResponderSecrecy := by
  constructor
  · intro h tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv k hk hKnows
    exact (h tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv k hk hKnows).imp
      (thm9Excuse_iff_exists_case b a ikB ikA spk pqpk opk i tr).mpr id
  · intro h tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv k hk hKnows
    exact (h tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv k hk hKnows).imp
      (thm9Excuse_iff_exists_case b a ikB ikA spk pqpk opk i tr).mp id

theorem responderSecrecyWith_exists_thm7Case_iff :
    ResponderSecrecyWith (fun b ikB spk pqpk i tr => ∃ k : Fin 4, Thm7Case b ikB spk pqpk i tr k) ↔
      AliceInitiatorSecrecy := by
  constructor
  · intro h tr hR a b ikA ikB spk pqpk opk ek ct keys i hEv k hk hKnows
    exact (h tr hR a b ikA ikB spk pqpk opk ek ct keys i hEv k hk hKnows).imp
      (thm7Excuse_iff_exists_case b ikB spk pqpk i tr).mpr id
  · intro h tr hR a b ikA ikB spk pqpk opk ek ct keys i hEv k hk hKnows
    exact (h tr hR a b ikA ikB spk pqpk opk ek ct keys i hEv k hk hKnows).imp
      (thm7Excuse_iff_exists_case b ikB spk pqpk i tr).mp id

theorem not_ResponderSecrecyWith_of_witness
    {E : Participant → Bytes → Bytes → Bytes → Nat → ExecTrace → Prop} {tr : ExecTrace}
    {a b : Participant} {ikA ikB spk pqpk : Bytes} {opk : Option Bytes} {ek ct : Bytes}
    {keys : HandshakeKeys} {i : Nat} {k : Bytes}
    (hR : tr.Reachable reachability)
    (hEv : tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i)
    (hBlk : IsHandshakeBlock keys k)
    (hK : k.AttackerKnows tr)
    (hNoSSE : ¬ SessionStateExposed tr keys k)
    (hEx : ¬ E b ikB spk pqpk i tr) :
    ¬ ResponderSecrecyWith E :=
  fun hMut =>
    match hMut tr hR a b ikA ikB spk pqpk opk ek ct keys i hEv k hBlk hK with
    | Or.inl hE => hEx hE
    | Or.inr hSSE => hNoSSE hSSE

theorem not_InitiatorSecrecyWith_of_witness
    {E : Participant → Participant → Bytes → Bytes → Bytes → Bytes → Option Bytes → Nat →
      ExecTrace → Prop} {tr : ExecTrace}
    {b a : Participant} {ikB ikA spk pqpk : Bytes} {opk : Option Bytes} {ek ct : Bytes}
    {keys : HandshakeKeys} {i : Nat} {k : Bytes}
    (hR : tr.Reachable reachability)
    (hEv : tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i)
    (hBlk : IsHandshakeBlock keys k)
    (hK : k.AttackerKnows tr)
    (hNoSSE : ¬ SessionStateExposed tr keys k)
    (hEx : ¬ E b a ikB ikA spk pqpk opk i tr) :
    ¬ InitiatorSecrecyWith E :=
  fun hMut =>
    match hMut tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv k hBlk hK with
    | Or.inl hE => hEx hE
    | Or.inr hSSE => hNoSSE hSSE

/-! ## Whole-branch omissions -/

section WholeCases

def Thm7ExcuseWithout (omitted : Fin 4) (b : Participant) (ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  ∃ k : Fin 4, k ≠ omitted ∧ Thm7Case b ikB spk pqpk i tr k

/-- `AliceInitiatorSecrecy` omitting branch `omitted` of `Thm7Case`. -/
def Thm7_withoutCase (omitted : Fin 4) : Prop :=
  ResponderSecrecyWith (Thm7ExcuseWithout omitted)

abbrev Thm7_withoutCase_ikBefore : Prop := Thm7_withoutCase 0
abbrev Thm7_withoutCase_ikAndPrekeys : Prop := Thm7_withoutCase 1
abbrev Thm7_withoutCase_brokenDHBefore : Prop := Thm7_withoutCase 2
abbrev Thm7_withoutCase_brokenDHAndPQ : Prop := Thm7_withoutCase 3

def Thm9ExcuseWithout (omitted : Fin 7) (b a : Participant) (ikB ikA spk pqpk : Bytes)
    (opk : Option Bytes) (i : Nat) (tr : ExecTrace) : Prop :=
  ∃ k : Fin 7, k ≠ omitted ∧ Thm9Case b a ikB ikA spk pqpk opk i tr k

/-- `BobResponderSecrecy` omitting branch `omitted` of `Thm9Case`. -/
def Thm9_withoutCase (omitted : Fin 7) : Prop :=
  InitiatorSecrecyWith (Thm9ExcuseWithout omitted)

abbrev Thm9_withoutCase_ikABefore : Prop := Thm9_withoutCase 0
abbrev Thm9_withoutCase_spkBefore : Prop := Thm9_withoutCase 1
abbrev Thm9_withoutCase_bobKeysAndPQ : Prop := Thm9_withoutCase 2
abbrev Thm9_withoutCase_bobKeysAndBrokenKEM : Prop := Thm9_withoutCase 3
abbrev Thm9_withoutCase_brokenDHBefore : Prop := Thm9_withoutCase 4
abbrev Thm9_withoutCase_brokenDHAndPQ : Prop := Thm9_withoutCase 5
abbrev Thm9_withoutCase_brokenDHAndBrokenKEM : Prop := Thm9_withoutCase 6

/-- Reachable witness trace where `AliceDone` exposes a handshake block without
`SessionStateExposed`, satisfying `Thm7Case` branch `c` and no other branch. -/
def ExclusiveThm7Witness (c : Fin 4) : Prop :=
  ∃ tr a b ikA ikB spk pqpk opk ek ct keys i k,
    tr.Reachable reachability ∧
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i ∧
    IsHandshakeBlock keys k ∧ k.AttackerKnows tr ∧ ¬ SessionStateExposed tr keys k ∧
    Thm7Case b ikB spk pqpk i tr c ∧
    ∀ c' : Fin 4, c' ≠ c → ¬ Thm7Case b ikB spk pqpk i tr c'

/-- Reachable witness trace where `BobDone` exposes a handshake block without
`SessionStateExposed`, satisfying `Thm9Case` branch `c` and no other branch. -/
def ExclusiveThm9Witness (c : Fin 7) : Prop :=
  ∃ tr b a ikB ikA spk pqpk opk ek ct keys i k,
    tr.Reachable reachability ∧
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i ∧
    IsHandshakeBlock keys k ∧ k.AttackerKnows tr ∧ ¬ SessionStateExposed tr keys k ∧
    Thm9Case b a ikB ikA spk pqpk opk i tr c ∧
    ∀ c' : Fin 7, c' ≠ c → ¬ Thm9Case b a ikB ikA spk pqpk opk i tr c'

private theorem refute_thm7_without {c : Fin 4} (h : ExclusiveThm7Witness c) :
    ¬ Thm7_withoutCase c := by
  obtain ⟨tr, a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, i, k,
    hR, hEv, hBlk, hK, hNoSSE, _, hEx⟩ := h
  exact not_ResponderSecrecyWith_of_witness hR hEv hBlk hK hNoSSE
    fun ⟨c', hcNe, hc⟩ => hEx c' hcNe hc

private theorem refute_thm9_without {c : Fin 7} (h : ExclusiveThm9Witness c) :
    ¬ Thm9_withoutCase c := by
  obtain ⟨tr, b, a, ikB, ikA, spk, pqpk, opk, ek, ct, keys, i, k,
    hR, hEv, hBlk, hK, hNoSSE, _, hEx⟩ := h
  exact not_InitiatorSecrecyWith_of_witness hR hEv hBlk hK hNoSSE
    fun ⟨c', hcNe, hc⟩ => hEx c' hcNe hc

theorem thm7Case0_exclusive_witness : ExclusiveThm7Witness 0 := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trIKB p = (evIdx trIKB isCompromise).filter fun i =>
        match trIKB.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trIKB.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine ⟨trIKB, "alice", "bob", dhPk advIkA, dhPk advIkB, dhPk advSpkSk, kemPk advPqSk,
    none, trIKB_out.ek, trIKB_out.ct, trIKB_out.keys, 33, trIKB_out.keys.rk,
    trIKB_reach, trIKB_aliceDone, Or.inl rfl, trIKB_knows_block (Or.inl rfl),
    trIKB_no_sessionStateExposed _, ⟨22, trIKB_compIK, by decide⟩, ?_⟩
  intro c hc; match c with
  | 0 => exact absurd rfl hc
  | 1 =>
    exact fun ⟨_, hS, _⟩ => not_logged (p := isCompSPK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trIKB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trIKB_compIK]; all_goals decide) rfl hS
  | 2 =>
    exact not_loggedBefore_of_none (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trIKB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trIKB_compIK]; all_goals decide) rfl
  | 3 =>
    exact fun ⟨hD, _⟩ => not_logged (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trIKB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trIKB_compIK]; all_goals decide) rfl hD

/-- Omitting `Thm7Case 0` (`LoggedBefore (CompromisedIK b ikB) i tr`) falsifies
`AliceInitiatorSecrecy`. -/
theorem not_thm7_withoutCase_ikBefore : ¬ Thm7_withoutCase_ikBefore :=
  refute_thm7_without thm7Case0_exclusive_witness

theorem thm7Case1_exclusive_witness : ExclusiveThm7Witness 1 := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trThm7Case1_pq p = (evIdx trThm7Case1_pq isCompromise).filter fun i =>
        match trThm7Case1_pq.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trThm7Case1_pq.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine ⟨trThm7Case1_pq, "alice", "bob", dhPk ikA, dhPk ikB, dhPk spkB, kemPk pqskB,
    none, o1.ek, o1.ct, keys1, 27, keys1.rk,
    trThm7Case1_pq_reach, trThm7Case1_pq_aliceDone, Or.inl rfl,
    trThm7Case1_pq_knows_block (Or.inl rfl), trThm7Case1_pq_no_sessionStateExposed _,
    ⟨⟨31, trThm7Case1_pq_compIK⟩, ⟨33, trThm7Case1_pq_compSPK⟩,
      Or.inl ⟨35, trThm7Case1_pq_compPQ⟩⟩, ?_⟩
  intro c hc; match c with
  | 0 =>
    exact not_loggedBefore_of_singleton (p := isCompIK) (k := 31)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case1_pq_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compPQ]; all_goals decide)
      rfl (by decide)
  | 1 => exact absurd rfl hc
  | 2 =>
    exact not_loggedBefore_of_none (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case1_pq_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compPQ]; all_goals decide) rfl
  | 3 =>
    exact fun ⟨hD, _⟩ => not_logged (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case1_pq_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compPQ]; all_goals decide) rfl hD

/-- Omitting `Thm7Case 1` (post-exchange `CompromisedIK`, `CompromisedSPK`, and PQ compromise)
falsifies `AliceInitiatorSecrecy`. -/
theorem not_thm7_withoutCase_ikAndPrekeys : ¬ Thm7_withoutCase_ikAndPrekeys :=
  refute_thm7_without thm7Case1_exclusive_witness

theorem thm7Case2_exclusive_witness : ExclusiveThm7Witness 2 := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trBrokenDHA p = (evIdx trBrokenDHA isCompromise).filter fun i =>
        match trBrokenDHA.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trBrokenDHA.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine ⟨trBrokenDHA, "alice", "bob", dhPk advIkA, dhPk advIkB, dhPk advSpkSk, kemPk advPqSk,
    none, trBrokenDHA_out.ek, trBrokenDHA_out.ct, trBrokenDHA_out.keys, 33,
    trBrokenDHA_out.keys.rk, trBrokenDHA_reach, trBrokenDHA_aliceDone, Or.inl rfl,
    trBrokenDHA_knows_block (Or.inl rfl), trBrokenDHA_no_sessionStateExposed _,
    ⟨22, trBrokenDHA_brokenDH, by decide⟩, ?_⟩
  intro c hc; match c with
  | 0 =>
    exact not_loggedBefore_of_none (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHA_brokenDH]; all_goals decide) rfl
  | 1 =>
    exact fun ⟨hI, _⟩ => not_logged (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHA_brokenDH]; all_goals decide) rfl hI
  | 2 => exact absurd rfl hc
  | 3 =>
    exact fun ⟨_, h⟩ =>
      h.elim (not_logged (p := isCompPQ)
          (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHA_brokenDH]; all_goals decide) rfl)
        (not_logged (p := isBrokenKEM)
          (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHA_brokenDH]; all_goals decide) rfl)

/-- Omitting `Thm7Case 2` (`LoggedBefore BrokenDH i tr`) falsifies `AliceInitiatorSecrecy`. -/
theorem not_thm7_withoutCase_brokenDHBefore : ¬ Thm7_withoutCase_brokenDHBefore :=
  refute_thm7_without thm7Case2_exclusive_witness

theorem thm7Case3_exclusive_witness : ExclusiveThm7Witness 3 := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trThm7Case3_kem p = (evIdx trThm7Case3_kem isCompromise).filter fun i =>
        match trThm7Case3_kem.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trThm7Case3_kem.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine ⟨trThm7Case3_kem, "alice", "bob", dhPk ikA, dhPk ikB, dhPk spkB, kemPk pqskB,
    none, o1.ek, o1.ct, keys1, 27, keys1.rk,
    trThm7Case3_kem_reach, trThm7Case3_kem_aliceDone, Or.inl rfl,
    trThm7Case3_kem_knows_block (Or.inl rfl), trThm7Case3_kem_no_sessionStateExposed _,
    ⟨⟨31, trThm7Case3_kem_brokenDH⟩, Or.inr ⟨34, trThm7Case3_kem_brokenKEM⟩⟩, ?_⟩
  intro c hc; match c with
  | 0 =>
    exact not_loggedBefore_of_none (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case3_kem_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_kem_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_kem_brokenKEM]; all_goals decide) rfl
  | 1 =>
    exact fun ⟨hI, _⟩ => not_logged (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case3_kem_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_kem_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_kem_brokenKEM]; all_goals decide) rfl hI
  | 2 =>
    exact not_loggedBefore_of_singleton (p := isBrokenDH) (k := 31)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case3_kem_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_kem_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_kem_brokenKEM]; all_goals decide)
      rfl (by decide)
  | 3 => exact absurd rfl hc

/-- Omitting `Thm7Case 3` (post-exchange `BrokenDH` and PQ compromise) falsifies
`AliceInitiatorSecrecy`. -/
theorem not_thm7_withoutCase_brokenDHAndPQ : ¬ Thm7_withoutCase_brokenDHAndPQ :=
  refute_thm7_without thm7Case3_exclusive_witness

theorem thm9Case0_exclusive_witness : ExclusiveThm9Witness 0 := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trIKA p = (evIdx trIKA isCompromise).filter fun i =>
        match trIKA.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trIKA.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine ⟨trIKA, "bob", "alice", dhPk advIkB, dhPk advIkA, dhPk advSpkB, kemPk advPqskB,
    none, dhPk advEkSk, advForgedBobCt, advForgedBobKeys, 29, advForgedBobKeys.rk,
    trIKA_reach, trIKA_bobDone, Or.inl rfl, trIKA_knows_block (Or.inl rfl),
    trIKA_no_sessionStateExposed _, ⟨22, trIKA_compIK, by decide⟩, ?_⟩
  intro c hc; match c with
  | 0 => exact absurd rfl hc
  | 1 =>
    exact not_loggedBefore_of_none (p := isCompSPK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trIKA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trIKA_compIK]; all_goals decide) rfl
  | 2 | 3 =>
    exact fun ⟨_, hS, _⟩ => not_logged (p := isCompSPK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trIKA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trIKA_compIK]; all_goals decide) rfl hS
  | 4 =>
    exact not_loggedBefore_of_none (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trIKA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trIKA_compIK]; all_goals decide) rfl
  | 5 | 6 =>
    exact fun ⟨hD, _⟩ => not_logged (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trIKA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trIKA_compIK]; all_goals decide) rfl hD

/-- Omitting `Thm9Case 0` (`LoggedBefore (CompromisedIK a ikA) i tr`) falsifies
`BobResponderSecrecy`. -/
theorem not_thm9_withoutCase_ikABefore : ¬ Thm9_withoutCase_ikABefore :=
  refute_thm9_without thm9Case0_exclusive_witness

theorem thm9Case1_exclusive_witness : ExclusiveThm9Witness 1 := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trSPKB p = (evIdx trSPKB isCompromise).filter fun i =>
        match trSPKB.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trSPKB.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine ⟨trSPKB, "bob", "alice", dhPk advIkB, dhPk advIkA, dhPk advSpkB, kemPk advPqskB,
    none, dhPk advEkSk, advForgedBobCt, advForgedBobKeys, 29, advForgedBobKeys.rk,
    trSPKB_reach, trSPKB_bobDone, Or.inl rfl, trSPKB_knows_block (Or.inl rfl),
    trSPKB_no_sessionStateExposed _, ⟨22, trSPKB_compSPK, by decide⟩, ?_⟩
  intro c hc; match c with
  | 0 =>
    exact not_loggedBefore_of_none (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trSPKB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trSPKB_compSPK]; all_goals decide) rfl
  | 1 => exact absurd rfl hc
  | 2 | 3 =>
    exact fun ⟨hI, _⟩ => not_logged (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trSPKB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trSPKB_compSPK]; all_goals decide) rfl hI
  | 4 =>
    exact not_loggedBefore_of_none (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trSPKB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trSPKB_compSPK]; all_goals decide) rfl
  | 5 | 6 =>
    exact fun ⟨hD, _⟩ => not_logged (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trSPKB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trSPKB_compSPK]; all_goals decide) rfl hD

/-- Omitting `Thm9Case 1` (`LoggedBefore (CompromisedSPK b spk) i tr`) falsifies
`BobResponderSecrecy`. -/
theorem not_thm9_withoutCase_spkBefore : ¬ Thm9_withoutCase_spkBefore :=
  refute_thm9_without thm9Case1_exclusive_witness

theorem thm9Case2_exclusive_witness : ExclusiveThm9Witness 2 := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trThm9Case2_opk p = (evIdx trThm9Case2_opk isCompromise).filter fun i =>
        match trThm9Case2_opk.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trThm9Case2_opk.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine ⟨trThm9Case2_opk, "bob", "alice", dhPk ikB, dhPk ikA, dhPk spkB, kemPk pqskB,
    some (dhPk opkB), oOpk.ek, oOpk.ct, keysOpk, 47, keysOpk.rk,
    trThm9Case2_opk_reach, trThm9Case2_opk_bobDone, Or.inl rfl,
    trThm9Case2_opk_knows_block (Or.inl rfl), trThm9Case2_opk_no_sessionStateExposed _,
    ⟨⟨54, trThm9Case2_opk_compIK⟩, ⟨56, trThm9Case2_opk_compSPK⟩,
      ⟨58, trThm9Case2_opk_compPQ⟩, Or.inr ⟨dhPk opkB, rfl, ⟨42, trThm9Case2_opk_compOPK, by decide⟩⟩⟩, ?_⟩
  intro c hc; match c with
  | 0 =>
    exact not_loggedBefore_of_none (p := isCompIkOf "alice")
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case2_opk_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compPQ, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compOPK]; all_goals decide) rfl
  | 1 =>
    exact not_loggedBefore_of_singleton (p := isCompSPK) (k := 56)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case2_opk_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compPQ, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compOPK]; all_goals decide)
      rfl (by decide)
  | 2 => exact absurd rfl hc
  | 3 =>
    exact fun ⟨_, _, hK, _⟩ => not_logged (p := isBrokenKEM)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case2_opk_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compPQ, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compOPK]; all_goals decide) rfl hK
  | 4 =>
    exact not_loggedBefore_of_none (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case2_opk_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compPQ, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compOPK]; all_goals decide) rfl
  | 5 | 6 =>
    exact fun ⟨hD, _⟩ => not_logged (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case2_opk_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compPQ, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compOPK]; all_goals decide) rfl hD

/-- Omitting `Thm9Case 2` (post-exchange Bob key compromises with `CompromisedPQSPK`) falsifies
`BobResponderSecrecy`. -/
theorem not_thm9_withoutCase_bobKeysAndPQ : ¬ Thm9_withoutCase_bobKeysAndPQ :=
  refute_thm9_without thm9Case2_exclusive_witness

theorem thm9Case3_exclusive_witness : ExclusiveThm9Witness 3 := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trThm9Case3 p = (evIdx trThm9Case3 isCompromise).filter fun i =>
        match trThm9Case3.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trThm9Case3.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine ⟨trThm9Case3, "bob", "alice", dhPk ikB, dhPk ikA, dhPk spkB, kemPk pqskB,
    none, o1.ek, o1.ct, keys1, 47, keys1.rk,
    trThm9Case3_reach, trThm9Case3_bobDone, Or.inl rfl,
    trThm9Case3_knows_block (Or.inl rfl), trThm9Case3_no_sessionStateExposed _,
    ⟨⟨54, trThm9Case3_compIK⟩, ⟨56, trThm9Case3_compSPK⟩,
      ⟨58, trThm9Case3_brokenKEM⟩, Or.inl rfl⟩, ?_⟩
  intro c hc; match c with
  | 0 =>
    exact not_loggedBefore_of_none (p := isCompIkOf "alice")
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case3_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_brokenKEM]; all_goals decide) rfl
  | 1 =>
    exact not_loggedBefore_of_singleton (p := isCompSPK) (k := 56)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case3_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_brokenKEM]; all_goals decide)
      rfl (by decide)
  | 2 =>
    exact fun ⟨_, _, hP, _⟩ => not_logged (p := isCompPQ)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case3_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_brokenKEM]; all_goals decide) rfl hP
  | 3 => exact absurd rfl hc
  | 4 =>
    exact not_loggedBefore_of_none (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case3_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_brokenKEM]; all_goals decide) rfl
  | 5 | 6 =>
    exact fun ⟨hD, _⟩ => not_logged (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case3_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_brokenKEM]; all_goals decide) rfl hD

/-- Omitting `Thm9Case 3` (post-exchange Bob key compromises with `BrokenKEM`) falsifies
`BobResponderSecrecy`. -/
theorem not_thm9_withoutCase_bobKeysAndBrokenKEM : ¬ Thm9_withoutCase_bobKeysAndBrokenKEM :=
  refute_thm9_without thm9Case3_exclusive_witness

theorem thm9Case4_exclusive_witness : ExclusiveThm9Witness 4 := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trBrokenDHB p = (evIdx trBrokenDHB isCompromise).filter fun i =>
        match trBrokenDHB.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trBrokenDHB.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine ⟨trBrokenDHB, "bob", "alice", dhPk advIkB, dhPk advIkA, dhPk advSpkB, kemPk advPqskB,
    none, dhPk advEkSk, advForgedBobCt, advForgedBobKeys, 29, advForgedBobKeys.rk,
    trBrokenDHB_reach, trBrokenDHB_bobDone, Or.inl rfl,
    trBrokenDHB_knows_block (Or.inl rfl), trBrokenDHB_no_sessionStateExposed _,
    ⟨22, trBrokenDHB_brokenDH, by decide⟩, ?_⟩
  intro c hc; match c with
  | 0 =>
    exact not_loggedBefore_of_none (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHB_brokenDH]; all_goals decide) rfl
  | 1 =>
    exact not_loggedBefore_of_none (p := isCompSPK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHB_brokenDH]; all_goals decide) rfl
  | 2 | 3 =>
    exact fun ⟨hI, _⟩ => not_logged (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHB_brokenDH]; all_goals decide) rfl hI
  | 4 => exact absurd rfl hc
  | 5 =>
    exact fun ⟨_, hP⟩ => not_logged (p := isCompPQ)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHB_brokenDH]; all_goals decide) rfl hP
  | 6 =>
    exact fun ⟨_, hK⟩ => not_logged (p := isBrokenKEM)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHB_brokenDH]; all_goals decide) rfl hK

/-- Omitting `Thm9Case 4` (`LoggedBefore BrokenDH i tr`) falsifies `BobResponderSecrecy`. -/
theorem not_thm9_withoutCase_brokenDHBefore : ¬ Thm9_withoutCase_brokenDHBefore :=
  refute_thm9_without thm9Case4_exclusive_witness

theorem thm9Case5_exclusive_witness : ExclusiveThm9Witness 5 := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trThm9Case5 p = (evIdx trThm9Case5 isCompromise).filter fun i =>
        match trThm9Case5.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trThm9Case5.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine ⟨trThm9Case5, "bob", "alice", dhPk ikB, dhPk ikA, dhPk spkB, kemPk pqskB,
    none, o1.ek, o1.ct, keys1, 47, keys1.rk,
    trThm9Case5_reach, trThm9Case5_bobDone, Or.inl rfl,
    trThm9Case5_knows_block (Or.inl rfl), trThm9Case5_no_sessionStateExposed _,
    ⟨⟨54, trThm9Case5_brokenDH⟩, ⟨57, trThm9Case5_compPQ⟩⟩, ?_⟩
  intro c hc; match c with
  | 0 =>
    exact not_loggedBefore_of_none (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case5_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case5_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case5_compPQ]; all_goals decide) rfl
  | 1 =>
    exact not_loggedBefore_of_none (p := isCompSPK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case5_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case5_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case5_compPQ]; all_goals decide) rfl
  | 2 | 3 =>
    exact fun ⟨hI, _⟩ => not_logged (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case5_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case5_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case5_compPQ]; all_goals decide) rfl hI
  | 4 =>
    exact not_loggedBefore_of_singleton (p := isBrokenDH) (k := 54)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case5_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case5_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case5_compPQ]; all_goals decide)
      rfl (by decide)
  | 5 => exact absurd rfl hc
  | 6 =>
    exact fun ⟨_, hK⟩ => not_logged (p := isBrokenKEM)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case5_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case5_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case5_compPQ]; all_goals decide) rfl hK

/-- Omitting `Thm9Case 5` (post-exchange `BrokenDH` and `CompromisedPQSPK`) falsifies
`BobResponderSecrecy`. -/
theorem not_thm9_withoutCase_brokenDHAndPQ : ¬ Thm9_withoutCase_brokenDHAndPQ :=
  refute_thm9_without thm9Case5_exclusive_witness

theorem thm9Case6_exclusive_witness : ExclusiveThm9Witness 6 := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trThm9Case6 p = (evIdx trThm9Case6 isCompromise).filter fun i =>
        match trThm9Case6.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trThm9Case6.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine ⟨trThm9Case6, "bob", "alice", dhPk ikB, dhPk ikA, dhPk spkB, kemPk pqskB,
    none, o1.ek, o1.ct, keys1, 47, keys1.rk,
    trThm9Case6_reach, trThm9Case6_bobDone, Or.inl rfl,
    trThm9Case6_knows_block (Or.inl rfl), trThm9Case6_no_sessionStateExposed _,
    ⟨⟨54, trThm9Case6_brokenDH⟩, ⟨57, trThm9Case6_brokenKEM⟩⟩, ?_⟩
  intro c hc; match c with
  | 0 =>
    exact not_loggedBefore_of_none (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case6_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case6_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case6_brokenKEM]; all_goals decide) rfl
  | 1 =>
    exact not_loggedBefore_of_none (p := isCompSPK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case6_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case6_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case6_brokenKEM]; all_goals decide) rfl
  | 2 | 3 =>
    exact fun ⟨hI, _⟩ => not_logged (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case6_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case6_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case6_brokenKEM]; all_goals decide) rfl hI
  | 4 =>
    exact not_loggedBefore_of_singleton (p := isBrokenDH) (k := 54)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case6_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case6_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case6_brokenKEM]; all_goals decide)
      rfl (by decide)
  | 5 =>
    exact fun ⟨_, hP⟩ => not_logged (p := isCompPQ)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case6_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case6_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case6_brokenKEM]; all_goals decide) rfl hP
  | 6 => exact absurd rfl hc

/-- Omitting `Thm9Case 6` (post-exchange `BrokenDH` and `BrokenKEM`) falsifies
`BobResponderSecrecy`. -/
theorem not_thm9_withoutCase_brokenDHAndBrokenKEM : ¬ Thm9_withoutCase_brokenDHAndBrokenKEM :=
  refute_thm9_without thm9Case6_exclusive_witness

end WholeCases

/-! ## Inner KEM disjunctions in `AliceHandshakeWasCompromised` -/

section Thm7Inner

def Thm7Excuse_case1WithoutBrokenKEM (b : Participant) (ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  (∃ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) j ∧
    (j < i ∨ (tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
      tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk)))) ∨
  (∃ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j ∧
    (j < i ∨ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∨
      tr.EventLogged PQXDHEvent.BrokenKEM))

def Thm7Excuse_case1WithoutCompromisedPQSPK (b : Participant) (ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  (∃ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) j ∧
    (j < i ∨ (tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
      tr.EventLogged PQXDHEvent.BrokenKEM))) ∨
  (∃ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j ∧
    (j < i ∨ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∨
      tr.EventLogged PQXDHEvent.BrokenKEM))

def Thm7Excuse_case3WithoutBrokenKEM (b : Participant) (ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  (∃ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) j ∧
    (j < i ∨ (tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
      (tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∨
        tr.EventLogged PQXDHEvent.BrokenKEM)))) ∨
  (∃ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j ∧
    (j < i ∨ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk)))

def Thm7Excuse_case3WithoutCompromisedPQSPK (b : Participant) (ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  (∃ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) j ∧
    (j < i ∨ (tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
      (tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∨
        tr.EventLogged PQXDHEvent.BrokenKEM)))) ∨
  (∃ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j ∧
    (j < i ∨ tr.EventLogged PQXDHEvent.BrokenKEM))

abbrev ResponderSecrecy_case1WithoutBrokenKEM : Prop :=
  ResponderSecrecyWith Thm7Excuse_case1WithoutBrokenKEM

abbrev ResponderSecrecy_case1WithoutCompromisedPQSPK : Prop :=
  ResponderSecrecyWith Thm7Excuse_case1WithoutCompromisedPQSPK

abbrev ResponderSecrecy_case3WithoutBrokenKEM : Prop :=
  ResponderSecrecyWith Thm7Excuse_case3WithoutBrokenKEM

abbrev ResponderSecrecy_case3WithoutCompromisedPQSPK : Prop :=
  ResponderSecrecyWith Thm7Excuse_case3WithoutCompromisedPQSPK

theorem thm7Excuse_of_mutantExcuse (b : Participant) (ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) :
    (Thm7Excuse_case1WithoutBrokenKEM b ikB spk pqpk i tr →
      AliceHandshakeWasCompromised b ikB spk pqpk i tr) ∧
    (Thm7Excuse_case1WithoutCompromisedPQSPK b ikB spk pqpk i tr →
      AliceHandshakeWasCompromised b ikB spk pqpk i tr) ∧
    (Thm7Excuse_case3WithoutBrokenKEM b ikB spk pqpk i tr →
      AliceHandshakeWasCompromised b ikB spk pqpk i tr) ∧
    (Thm7Excuse_case3WithoutCompromisedPQSPK b ikB spk pqpk i tr →
      AliceHandshakeWasCompromised b ikB spk pqpk i tr) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (⟨j, hj, hlt | ⟨hS, hP⟩⟩ | h)
    · exact Or.inl ⟨j, hj, Or.inl hlt⟩
    · exact Or.inl ⟨j, hj, Or.inr ⟨hS, Or.inl hP⟩⟩
    · exact Or.inr h
  · rintro (⟨j, hj, hlt | ⟨hS, hK⟩⟩ | h)
    · exact Or.inl ⟨j, hj, Or.inl hlt⟩
    · exact Or.inl ⟨j, hj, Or.inr ⟨hS, Or.inr hK⟩⟩
    · exact Or.inr h
  · rintro (h | ⟨j, hj, hlt | hP⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, Or.inl hlt⟩
    · exact Or.inr ⟨j, hj, Or.inr (Or.inl hP)⟩
  · rintro (h | ⟨j, hj, hlt | hK⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, Or.inl hlt⟩
    · exact Or.inr ⟨j, hj, Or.inr (Or.inr hK)⟩

/-- Omitting the `BrokenKEM` alternative in the first disjunct of `AliceHandshakeWasCompromised`
falsifies `AliceInitiatorSecrecy`. -/
theorem not_ResponderSecrecy_case1WithoutBrokenKEM :
    ¬ ResponderSecrecy_case1WithoutBrokenKEM := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trThm7Case1_kem p = (evIdx trThm7Case1_kem isCompromise).filter fun i =>
        match trThm7Case1_kem.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trThm7Case1_kem.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine not_ResponderSecrecyWith_of_witness trThm7Case1_kem_reach trThm7Case1_kem_aliceDone
    (Or.inl rfl) (trThm7Case1_kem_knows_block (Or.inl rfl))
    (trThm7Case1_kem_no_sessionStateExposed _) ?_
  rintro (⟨j, hj, hlt | ⟨_, hP⟩⟩ | ⟨j, hj, _⟩)
  · exact not_loggedBefore_of_singleton (p := isCompIK) (k := 31)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case1_kem_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_kem_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_kem_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_kem_brokenKEM]; all_goals decide)
      rfl (by decide) ⟨j, hj, hlt⟩
  · exact not_logged (p := isCompPQ)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case1_kem_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_kem_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_kem_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_kem_brokenKEM]; all_goals decide) rfl hP
  · exact not_logged (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case1_kem_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_kem_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_kem_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_kem_brokenKEM]; all_goals decide) rfl ⟨j, hj⟩

/-- Omitting the `CompromisedPQSPK` alternative in the first disjunct of
`AliceHandshakeWasCompromised` falsifies `AliceInitiatorSecrecy`. -/
theorem not_ResponderSecrecy_case1WithoutCompromisedPQSPK :
    ¬ ResponderSecrecy_case1WithoutCompromisedPQSPK := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trThm7Case1_pq p = (evIdx trThm7Case1_pq isCompromise).filter fun i =>
        match trThm7Case1_pq.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trThm7Case1_pq.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine not_ResponderSecrecyWith_of_witness trThm7Case1_pq_reach trThm7Case1_pq_aliceDone
    (Or.inl rfl) (trThm7Case1_pq_knows_block (Or.inl rfl))
    (trThm7Case1_pq_no_sessionStateExposed _) ?_
  rintro (⟨j, hj, hlt | ⟨_, hK⟩⟩ | ⟨j, hj, _⟩)
  · exact not_loggedBefore_of_singleton (p := isCompIK) (k := 31)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case1_pq_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compPQ]; all_goals decide)
      rfl (by decide) ⟨j, hj, hlt⟩
  · exact not_logged (p := isBrokenKEM)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case1_pq_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compPQ]; all_goals decide) rfl hK
  · exact not_logged (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case1_pq_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case1_pq_compPQ]; all_goals decide) rfl ⟨j, hj⟩

/-- Omitting the `BrokenKEM` alternative in the second disjunct of `AliceHandshakeWasCompromised`
falsifies `AliceInitiatorSecrecy`. -/
theorem not_ResponderSecrecy_case3WithoutBrokenKEM :
    ¬ ResponderSecrecy_case3WithoutBrokenKEM := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trThm7Case3_kem p = (evIdx trThm7Case3_kem isCompromise).filter fun i =>
        match trThm7Case3_kem.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trThm7Case3_kem.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine not_ResponderSecrecyWith_of_witness trThm7Case3_kem_reach trThm7Case3_kem_aliceDone
    (Or.inl rfl) (trThm7Case3_kem_knows_block (Or.inl rfl))
    (trThm7Case3_kem_no_sessionStateExposed _) ?_
  rintro (⟨j, hj, _⟩ | ⟨j, hj, hlt | hP⟩)
  · exact not_logged (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case3_kem_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_kem_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_kem_brokenKEM]; all_goals decide) rfl ⟨j, hj⟩
  · exact not_loggedBefore_of_singleton (p := isBrokenDH) (k := 31)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case3_kem_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_kem_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_kem_brokenKEM]; all_goals decide)
      rfl (by decide) ⟨j, hj, hlt⟩
  · exact not_logged (p := isCompPQ)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case3_kem_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_kem_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_kem_brokenKEM]; all_goals decide) rfl hP

/-- Omitting the `CompromisedPQSPK` alternative in the second disjunct of
`AliceHandshakeWasCompromised` falsifies `AliceInitiatorSecrecy`. -/
theorem not_ResponderSecrecy_case3WithoutCompromisedPQSPK :
    ¬ ResponderSecrecy_case3WithoutCompromisedPQSPK := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trThm7Case3_pq p = (evIdx trThm7Case3_pq isCompromise).filter fun i =>
        match trThm7Case3_pq.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trThm7Case3_pq.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine not_ResponderSecrecyWith_of_witness trThm7Case3_pq_reach trThm7Case3_pq_aliceDone
    (Or.inl rfl) (trThm7Case3_pq_knows_block (Or.inl rfl))
    (trThm7Case3_pq_no_sessionStateExposed _) ?_
  rintro (⟨j, hj, _⟩ | ⟨j, hj, hlt | hK⟩)
  · exact not_logged (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case3_pq_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_pq_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_pq_compPQ]; all_goals decide) rfl ⟨j, hj⟩
  · exact not_loggedBefore_of_singleton (p := isBrokenDH) (k := 31)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case3_pq_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_pq_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_pq_compPQ]; all_goals decide)
      rfl (by decide) ⟨j, hj, hlt⟩
  · exact not_logged (p := isBrokenKEM)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm7Case3_pq_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_pq_brokenDH, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm7Case3_pq_compPQ]; all_goals decide) rfl hK

end Thm7Inner

/-! ## Inner OPK disjunctions in `BobHandshakeWasCompromised` -/

section Thm9Inner

def Thm9Excuse_case2WithoutCompromisedOPK (b a : Participant) (ikB ikA spk pqpk : Bytes)
    (opk : Option Bytes) (i : Nat) (tr : ExecTrace) : Prop :=
  (∃ k : Fin 7, k ≠ 2 ∧ Thm9Case b a ikB ikA spk pqpk opk i tr k) ∨
  (tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
    tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
    tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∧ opk = none)

def Thm9Excuse_case2WithoutAbsentOPK (b a : Participant) (ikB ikA spk pqpk : Bytes)
    (opk : Option Bytes) (i : Nat) (tr : ExecTrace) : Prop :=
  (∃ k : Fin 7, k ≠ 2 ∧ Thm9Case b a ikB ikA spk pqpk opk i tr k) ∨
  (tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
    tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
    tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∧
    ∃ o, opk = some o ∧ LoggedBefore (PQXDHEvent.CompromisedOPK b o) i tr)

def Thm9Excuse_case3WithoutCompromisedOPK (b a : Participant) (ikB ikA spk pqpk : Bytes)
    (opk : Option Bytes) (i : Nat) (tr : ExecTrace) : Prop :=
  (∃ k : Fin 7, k ≠ 3 ∧ Thm9Case b a ikB ikA spk pqpk opk i tr k) ∨
  (tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
    tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
    tr.EventLogged PQXDHEvent.BrokenKEM ∧ opk = none)

def Thm9Excuse_case3WithoutAbsentOPK (b a : Participant) (ikB ikA spk pqpk : Bytes)
    (opk : Option Bytes) (i : Nat) (tr : ExecTrace) : Prop :=
  (∃ k : Fin 7, k ≠ 3 ∧ Thm9Case b a ikB ikA spk pqpk opk i tr k) ∨
  (tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
    tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
    tr.EventLogged PQXDHEvent.BrokenKEM ∧
    ∃ o, opk = some o ∧ LoggedBefore (PQXDHEvent.CompromisedOPK b o) i tr)

abbrev InitiatorSecrecy_case2WithoutCompromisedOPK : Prop :=
  InitiatorSecrecyWith Thm9Excuse_case2WithoutCompromisedOPK

abbrev InitiatorSecrecy_case2WithoutAbsentOPK : Prop :=
  InitiatorSecrecyWith Thm9Excuse_case2WithoutAbsentOPK

abbrev InitiatorSecrecy_case3WithoutCompromisedOPK : Prop :=
  InitiatorSecrecyWith Thm9Excuse_case3WithoutCompromisedOPK

abbrev InitiatorSecrecy_case3WithoutAbsentOPK : Prop :=
  InitiatorSecrecyWith Thm9Excuse_case3WithoutAbsentOPK

theorem thm9Excuse_of_mutantExcuse (b a : Participant) (ikB ikA spk pqpk : Bytes)
    (opk : Option Bytes) (i : Nat) (tr : ExecTrace) :
    (Thm9Excuse_case2WithoutCompromisedOPK b a ikB ikA spk pqpk opk i tr →
      BobHandshakeWasCompromised b a ikB ikA spk pqpk opk i tr) ∧
    (Thm9Excuse_case2WithoutAbsentOPK b a ikB ikA spk pqpk opk i tr →
      BobHandshakeWasCompromised b a ikB ikA spk pqpk opk i tr) ∧
    (Thm9Excuse_case3WithoutCompromisedOPK b a ikB ikA spk pqpk opk i tr →
      BobHandshakeWasCompromised b a ikB ikA spk pqpk opk i tr) ∧
    (Thm9Excuse_case3WithoutAbsentOPK b a ikB ikA spk pqpk opk i tr →
      BobHandshakeWasCompromised b a ikB ikA spk pqpk opk i tr) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (⟨k, _, h⟩ | ⟨hI, hS, hP, hO⟩)
    · exact (thm9Excuse_iff_exists_case b a ikB ikA spk pqpk opk i tr).mpr ⟨k, h⟩
    · exact (thm9Excuse_iff_exists_case b a ikB ikA spk pqpk opk i tr).mpr ⟨2, hI, hS, hP, Or.inl hO⟩
  · rintro (⟨k, _, h⟩ | ⟨hI, hS, hP, hO⟩)
    · exact (thm9Excuse_iff_exists_case b a ikB ikA spk pqpk opk i tr).mpr ⟨k, h⟩
    · exact (thm9Excuse_iff_exists_case b a ikB ikA spk pqpk opk i tr).mpr ⟨2, hI, hS, hP, Or.inr hO⟩
  · rintro (⟨k, _, h⟩ | ⟨hI, hS, hK, hO⟩)
    · exact (thm9Excuse_iff_exists_case b a ikB ikA spk pqpk opk i tr).mpr ⟨k, h⟩
    · exact (thm9Excuse_iff_exists_case b a ikB ikA spk pqpk opk i tr).mpr ⟨3, hI, hS, hK, Or.inl hO⟩
  · rintro (⟨k, _, h⟩ | ⟨hI, hS, hK, hO⟩)
    · exact (thm9Excuse_iff_exists_case b a ikB ikA spk pqpk opk i tr).mpr ⟨k, h⟩
    · exact (thm9Excuse_iff_exists_case b a ikB ikA spk pqpk opk i tr).mpr ⟨3, hI, hS, hK, Or.inr hO⟩

/-- Omitting the `CompromisedOPK` alternative of `OPKAbsentOrCompromised` in `Thm9Case 2`
falsifies `BobResponderSecrecy`. -/
theorem not_InitiatorSecrecy_case2WithoutCompromisedOPK :
    ¬ InitiatorSecrecy_case2WithoutCompromisedOPK := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trThm9Case2_opk p = (evIdx trThm9Case2_opk isCompromise).filter fun i =>
        match trThm9Case2_opk.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trThm9Case2_opk.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine not_InitiatorSecrecyWith_of_witness trThm9Case2_opk_reach trThm9Case2_opk_bobDone
    (Or.inl rfl) (trThm9Case2_opk_knows_block (Or.inl rfl))
    (trThm9Case2_opk_no_sessionStateExposed _) ?_
  rintro (⟨k, hk, hCase⟩ | ⟨_, _, _, ⟨⟩⟩)
  revert hk hCase; match k with
  | 0 =>
    exact fun _ => not_loggedBefore_of_none (p := isCompIkOf "alice")
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case2_opk_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compPQ, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compOPK]; all_goals decide) rfl
  | 1 =>
    exact fun _ => not_loggedBefore_of_singleton (p := isCompSPK) (k := 56)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case2_opk_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compPQ, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compOPK]; all_goals decide)
      rfl (by decide)
  | 2 => exact fun hk => absurd rfl hk
  | 3 =>
    exact fun _ ⟨_, _, hK, _⟩ => not_logged (p := isBrokenKEM)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case2_opk_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compPQ, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compOPK]; all_goals decide) rfl hK
  | 4 =>
    exact fun _ => not_loggedBefore_of_none (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case2_opk_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compPQ, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compOPK]; all_goals decide) rfl
  | 5 | 6 =>
    exact fun _ ⟨hD, _⟩ => not_logged (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case2_opk_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compPQ, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_opk_compOPK]; all_goals decide) rfl hD

/-- Omitting the `opk = none` alternative of `OPKAbsentOrCompromised` in `Thm9Case 2`
falsifies `BobResponderSecrecy`. -/
theorem not_InitiatorSecrecy_case2WithoutAbsentOPK :
    ¬ InitiatorSecrecy_case2WithoutAbsentOPK := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trThm9Case2 p = (evIdx trThm9Case2 isCompromise).filter fun i =>
        match trThm9Case2.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trThm9Case2.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine not_InitiatorSecrecyWith_of_witness trThm9Case2_reach trThm9Case2_bobDone
    (Or.inl rfl) (trThm9Case2_knows_block (Or.inl rfl))
    (trThm9Case2_no_sessionStateExposed _) ?_
  rintro (⟨k, hk, hCase⟩ | ⟨_, _, _, _, ⟨⟩, _⟩)
  revert hk hCase; match k with
  | 0 =>
    exact fun _ => not_loggedBefore_of_none (p := isCompIkOf "alice")
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case2_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_compPQ]; all_goals decide) rfl
  | 1 =>
    exact fun _ => not_loggedBefore_of_singleton (p := isCompSPK) (k := 56)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case2_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_compPQ]; all_goals decide)
      rfl (by decide)
  | 2 => exact fun hk => absurd rfl hk
  | 3 =>
    exact fun _ ⟨_, _, hK, _⟩ => not_logged (p := isBrokenKEM)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case2_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_compPQ]; all_goals decide) rfl hK
  | 4 =>
    exact fun _ => not_loggedBefore_of_none (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case2_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_compPQ]; all_goals decide) rfl
  | 5 | 6 =>
    exact fun _ ⟨hD, _⟩ => not_logged (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case2_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case2_compPQ]; all_goals decide) rfl hD

/-- Omitting the `CompromisedOPK` alternative of `OPKAbsentOrCompromised` in `Thm9Case 3`
falsifies `BobResponderSecrecy`. -/
theorem not_InitiatorSecrecy_case3WithoutCompromisedOPK :
    ¬ InitiatorSecrecy_case3WithoutCompromisedOPK := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trThm9Case3_opk p = (evIdx trThm9Case3_opk isCompromise).filter fun i =>
        match trThm9Case3_opk.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trThm9Case3_opk.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine not_InitiatorSecrecyWith_of_witness trThm9Case3_opk_reach trThm9Case3_opk_bobDone
    (Or.inl rfl) (trThm9Case3_opk_knows_block (Or.inl rfl))
    (trThm9Case3_opk_no_sessionStateExposed _) ?_
  rintro (⟨k, hk, hCase⟩ | ⟨_, _, _, ⟨⟩⟩)
  revert hk hCase; match k with
  | 0 =>
    exact fun _ => not_loggedBefore_of_none (p := isCompIkOf "alice")
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case3_opk_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_brokenKEM, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_compOPK]; all_goals decide) rfl
  | 1 =>
    exact fun _ => not_loggedBefore_of_singleton (p := isCompSPK) (k := 56)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case3_opk_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_brokenKEM, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_compOPK]; all_goals decide)
      rfl (by decide)
  | 2 =>
    exact fun _ ⟨_, _, hP, _⟩ => not_logged (p := isCompPQ)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case3_opk_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_brokenKEM, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_compOPK]; all_goals decide) rfl hP
  | 3 => exact fun hk => absurd rfl hk
  | 4 =>
    exact fun _ => not_loggedBefore_of_none (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case3_opk_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_brokenKEM, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_compOPK]; all_goals decide) rfl
  | 5 | 6 =>
    exact fun _ ⟨hD, _⟩ => not_logged (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case3_opk_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_brokenKEM, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_opk_compOPK]; all_goals decide) rfl hD

/-- Omitting the `opk = none` alternative of `OPKAbsentOrCompromised` in `Thm9Case 3`
falsifies `BobResponderSecrecy`. -/
theorem not_InitiatorSecrecy_case3WithoutAbsentOPK :
    ¬ InitiatorSecrecy_case3WithoutAbsentOPK := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trThm9Case3 p = (evIdx trThm9Case3 isCompromise).filter fun i =>
        match trThm9Case3.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trThm9Case3.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine not_InitiatorSecrecyWith_of_witness trThm9Case3_reach trThm9Case3_bobDone
    (Or.inl rfl) (trThm9Case3_knows_block (Or.inl rfl))
    (trThm9Case3_no_sessionStateExposed _) ?_
  rintro (⟨k, hk, hCase⟩ | ⟨_, _, _, _, ⟨⟩, _⟩)
  revert hk hCase; match k with
  | 0 =>
    exact fun _ => not_loggedBefore_of_none (p := isCompIkOf "alice")
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case3_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_brokenKEM]; all_goals decide) rfl
  | 1 =>
    exact fun _ => not_loggedBefore_of_singleton (p := isCompSPK) (k := 56)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case3_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_brokenKEM]; all_goals decide)
      rfl (by decide)
  | 2 =>
    exact fun _ ⟨_, _, hP, _⟩ => not_logged (p := isCompPQ)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case3_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_brokenKEM]; all_goals decide) rfl hP
  | 3 => exact fun hk => absurd rfl hk
  | 4 =>
    exact fun _ => not_loggedBefore_of_none (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case3_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_brokenKEM]; all_goals decide) rfl
  | 5 | 6 =>
    exact fun _ ⟨hD, _⟩ => not_logged (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trThm9Case3_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trThm9Case3_brokenKEM]; all_goals decide) rfl hD

end Thm9Inner

/-! ## Post-exchange temporal ordering in `BobHandshakeWasCompromised` -/

section R2

/-- Event logged at or after step `i`. -/
def LoggedAtOrAfter (ev : PQXDHEvent) (i : Nat) (tr : ExecTrace) : Prop :=
  ∃ j, tr.EventLoggedAt ev j ∧ i ≤ j

def Thm9CaseAfter (After : PQXDHEvent → Nat → ExecTrace → Prop)
    (b a : Participant) (ikB ikA spk pqpk : Bytes) (opk : Option Bytes)
    (i : Nat) (tr : ExecTrace) : Fin 7 → Prop
  | 0 => LoggedBefore (PQXDHEvent.CompromisedIK a ikA) i tr
  | 1 => LoggedBefore (PQXDHEvent.CompromisedSPK b spk) i tr
  | 2 => After (PQXDHEvent.CompromisedIK b ikB) i tr ∧
      After (PQXDHEvent.CompromisedSPK b spk) i tr ∧
      After (PQXDHEvent.CompromisedPQSPK b pqpk) i tr ∧ OPKAbsentOrCompromised b opk i tr
  | 3 => After (PQXDHEvent.CompromisedIK b ikB) i tr ∧
      After (PQXDHEvent.CompromisedSPK b spk) i tr ∧
      After PQXDHEvent.BrokenKEM i tr ∧ OPKAbsentOrCompromised b opk i tr
  | 4 => LoggedBefore PQXDHEvent.BrokenDH i tr
  | 5 => After PQXDHEvent.BrokenDH i tr ∧
      After (PQXDHEvent.CompromisedPQSPK b pqpk) i tr
  | 6 => After PQXDHEvent.BrokenDH i tr ∧ After PQXDHEvent.BrokenKEM i tr

def Thm9ExcuseAfter (After : PQXDHEvent → Nat → ExecTrace → Prop)
    (b a : Participant) (ikB ikA spk pqpk : Bytes) (opk : Option Bytes)
    (i : Nat) (tr : ExecTrace) : Prop :=
  ∃ k, Thm9CaseAfter After b a ikB ikA spk pqpk opk i tr k

theorem thm9CaseAfter_real (b a : Participant) (ikB ikA spk pqpk : Bytes)
    (opk : Option Bytes) (i : Nat) (tr : ExecTrace) (k : Fin 7) :
    Thm9CaseAfter (fun ev _ tr => tr.EventLogged ev) b a ikB ikA spk pqpk opk i tr k ↔
      Thm9Case b a ikB ikA spk pqpk opk i tr k := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact Iff.rfl

theorem thm9ExcuseAfter_real (b a : Participant) (ikB ikA spk pqpk : Bytes)
    (opk : Option Bytes) (i : Nat) (tr : ExecTrace) :
    Thm9ExcuseAfter (fun ev _ tr => tr.EventLogged ev) b a ikB ikA spk pqpk opk i tr ↔
      BobHandshakeWasCompromised b a ikB ikA spk pqpk opk i tr :=
  (exists_congr (thm9CaseAfter_real b a ikB ikA spk pqpk opk i tr)).trans
    (thm9Excuse_iff_exists_case b a ikB ikA spk pqpk opk i tr).symm

theorem initiatorSecrecyAfter_real :
    InitiatorSecrecyWith (Thm9ExcuseAfter (fun ev _ tr => tr.EventLogged ev)) ↔
      BobResponderSecrecy := by
  constructor
  · intro h tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv k hk hKnows
    exact (h tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv k hk hKnows).imp
      (thm9ExcuseAfter_real b a ikB ikA spk pqpk opk i tr).1 id
  · intro h tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv k hk hKnows
    exact (h tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv k hk hKnows).imp
      (thm9ExcuseAfter_real b a ikB ikA spk pqpk opk i tr).2 id

abbrev Thm9Case_strictAfter :
    Participant → Participant → Bytes → Bytes → Bytes → Bytes → Option Bytes → Nat →
      ExecTrace → Fin 7 → Prop :=
  Thm9CaseAfter LoggedAtOrAfter

abbrev Thm9Excuse_strictAfter :
    Participant → Participant → Bytes → Bytes → Bytes → Bytes → Option Bytes → Nat →
      ExecTrace → Prop :=
  Thm9ExcuseAfter LoggedAtOrAfter

abbrev InitiatorSecrecyQuery_strictAfter (tr : ExecTrace) (Knows : Bytes → Prop) : Prop :=
  InitiatorSecrecyQueryWith Thm9Excuse_strictAfter tr Knows

/-- `BobResponderSecrecy` where post-exchange cases (`2, 3, 5, 6`) require compromise or break
events to occur at or after step `i`. -/
abbrev Thm9_strictAfter : Prop :=
  InitiatorSecrecyWith Thm9Excuse_strictAfter

/-- Splitting compromises across `BobDone` (`compromiseIK "bob"` before, `compromiseSPK "bob"` and
`compromisePQSPK "bob"` after) satisfies `BobHandshakeWasCompromised` while refuting `Thm9_strictAfter`. -/
theorem splitCompromise_refutesStrictAfterThm9 :
    (∃ tr b a ikB ikA spk pqpk opk ek ct keys i k,
      tr.Reachable reachability ∧
      tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i ∧
      IsHandshakeBlock keys k ∧ k.AttackerKnows tr ∧ ¬ SessionStateExposed tr keys k ∧
      BobHandshakeWasCompromised b a ikB ikA spk pqpk opk i tr ∧
      ¬ InitiatorSecrecyQuery_strictAfter tr (fun t => t.AttackerKnows tr)) ∧
    ¬ Thm9_strictAfter := by
  have hfR2 (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trR2 p = (evIdx trR2 isCompromise).filter fun i =>
        match trR2.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trR2.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  have hNoStrict :
      ¬ Thm9Excuse_strictAfter "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB)
          none 42 trR2 := by
    rintro ⟨c, hc⟩
    revert hc; match c with
    | 0 =>
      exact not_loggedBefore_of_none (p := isCompIkOf "alice")
        (by rw [hfR2 _ (by intro e he; cases e <;> first | rfl | nomatch he), trR2_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trR2_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trR2_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trR2_compPQ]; all_goals decide) rfl
    | 1 =>
      exact not_loggedBefore_of_singleton (p := isCompSPK) (k := 49)
        (by rw [hfR2 _ (by intro e he; cases e <;> first | rfl | nomatch he), trR2_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trR2_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trR2_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trR2_compPQ]; all_goals decide)
        rfl (by decide)
    | 2 | 3 =>
      exact fun ⟨⟨j, hj, hle⟩, _⟩ =>
        not_atOrAfter_of_singleton (p := isCompIkOf "bob") (k := 22) hj
          (by rw [hfR2 _ (by intro e he; cases e <;> first | rfl | nomatch he), trR2_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trR2_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trR2_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trR2_compPQ]; all_goals decide)
          rfl (by decide) hle
    | 4 =>
      exact not_loggedBefore_of_none (p := isBrokenDH)
        (by rw [hfR2 _ (by intro e he; cases e <;> first | rfl | nomatch he), trR2_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trR2_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trR2_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trR2_compPQ]; all_goals decide) rfl
    | 5 | 6 =>
      exact fun ⟨⟨j, hj, _⟩, _⟩ => not_logged (p := isBrokenDH)
        (by rw [hfR2 _ (by intro e he; cases e <;> first | rfl | nomatch he), trR2_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trR2_compIK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trR2_compSPK, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trR2_compPQ]; all_goals decide) rfl ⟨j, hj⟩
  have hNoQuery : ¬ InitiatorSecrecyQuery_strictAfter trR2 (fun t => t.AttackerKnows trR2) := by
    intro hq
    rcases hq "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB) none
        trR2_out.ek trR2_out.ct trR2_keys 42 trR2_bobDone trR2_keys.rk (Or.inl rfl)
        (trR2_knows_block (Or.inl rfl)) with hEx | hSSE
    · exact hNoStrict hEx
    · exact trR2_no_sessionStateExposed _ hSSE
  exact ⟨⟨trR2, "bob", "alice", dhPk ikB, dhPk ikA, dhPk spkB, kemPk pqskB, none,
      trR2_out.ek, trR2_out.ct, trR2_keys, 42, trR2_keys.rk,
      trR2_reach, trR2_bobDone, Or.inl rfl, trR2_knows_block (Or.inl rfl),
      trR2_no_sessionStateExposed _,
      .inr (.inl ⟨⟨22, trR2_compIK⟩, ⟨49, trR2_compSPK⟩, Or.inl rfl, .inl ⟨51, trR2_compPQ⟩⟩),
      hNoQuery⟩,
    fun hAll => hNoQuery (hAll trR2 trR2_reach)⟩

theorem not_Thm9_strictAfter : ¬ Thm9_strictAfter :=
  splitCompromise_refutesStrictAfterThm9.2

end R2

/-! ## Pre-exchange index-gap bounds -/

section BoundsGap

def LoggedBeforeGap (g : Nat) (ev : PQXDHEvent) (i : Nat) (tr : ExecTrace) : Prop :=
  ∃ j, tr.EventLoggedAt ev j ∧ j + g < i

theorem loggedBeforeGap_zero (ev : PQXDHEvent) (i : Nat) (tr : ExecTrace) :
    LoggedBeforeGap 0 ev i tr ↔ LoggedBefore ev i tr := Iff.rfl

def Thm7ExcuseGap (gIK gDH : Nat) (b : Participant) (ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  (∃ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) j ∧
    (j + gIK < i ∨ (tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
      (tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∨
        tr.EventLogged PQXDHEvent.BrokenKEM)))) ∨
  (∃ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j ∧
    (j + gDH < i ∨ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∨
      tr.EventLogged PQXDHEvent.BrokenKEM))

/-- `AliceInitiatorSecrecy` with pre-exchange index-gap bounds `j + gIK < i` and `j + gDH < i`. -/
def ResponderSecrecyGap (gIK gDH : Nat) : Prop :=
  ResponderSecrecyWith (Thm7ExcuseGap gIK gDH)

theorem responderSecrecyGap_zero : ResponderSecrecyGap 0 0 ↔ AliceInitiatorSecrecy := Iff.rfl

def Thm9CaseGap (gIKA gSPK gDH : Nat) (b a : Participant) (ikB ikA spk pqpk : Bytes)
    (opk : Option Bytes) (i : Nat) (tr : ExecTrace) : Fin 7 → Prop
  | 0 => LoggedBeforeGap gIKA (PQXDHEvent.CompromisedIK a ikA) i tr
  | 1 => LoggedBeforeGap gSPK (PQXDHEvent.CompromisedSPK b spk) i tr
  | 2 => tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
      tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
      tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∧ OPKAbsentOrCompromised b opk i tr
  | 3 => tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
      tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
      tr.EventLogged PQXDHEvent.BrokenKEM ∧ OPKAbsentOrCompromised b opk i tr
  | 4 => LoggedBeforeGap gDH PQXDHEvent.BrokenDH i tr
  | 5 => tr.EventLogged PQXDHEvent.BrokenDH ∧ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk)
  | 6 => tr.EventLogged PQXDHEvent.BrokenDH ∧ tr.EventLogged PQXDHEvent.BrokenKEM

def Thm9ExcuseGap (gIKA gSPK gDH : Nat) (b a : Participant) (ikB ikA spk pqpk : Bytes)
    (opk : Option Bytes) (i : Nat) (tr : ExecTrace) : Prop :=
  ∃ k, Thm9CaseGap gIKA gSPK gDH b a ikB ikA spk pqpk opk i tr k

/-- `BobResponderSecrecy` with pre-exchange index-gap bounds `gIKA`, `gSPK`, and `gDH`. -/
def InitiatorSecrecyGap (gIKA gSPK gDH : Nat) : Prop :=
  InitiatorSecrecyWith (Thm9ExcuseGap gIKA gSPK gDH)

theorem thm9CaseGap_zero (b a : Participant) (ikB ikA spk pqpk : Bytes)
    (opk : Option Bytes) (i : Nat) (tr : ExecTrace) (k : Fin 7) :
    Thm9CaseGap 0 0 0 b a ikB ikA spk pqpk opk i tr k ↔
      Thm9Case b a ikB ikA spk pqpk opk i tr k := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact Iff.rfl

theorem initiatorSecrecyGap_zero : InitiatorSecrecyGap 0 0 0 ↔ BobResponderSecrecy := by
  have hEx (b a : Participant) (ikB ikA spk pqpk : Bytes) (opk : Option Bytes)
      (i : Nat) (tr : ExecTrace) :
      Thm9ExcuseGap 0 0 0 b a ikB ikA spk pqpk opk i tr ↔
        BobHandshakeWasCompromised b a ikB ikA spk pqpk opk i tr :=
    (exists_congr (thm9CaseGap_zero b a ikB ikA spk pqpk opk i tr)).trans
      (thm9Excuse_iff_exists_case b a ikB ikA spk pqpk opk i tr).symm
  constructor
  · intro h tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv k hk hKnows
    exact (h tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv k hk hKnows).imp
      (hEx b a ikB ikA spk pqpk opk i tr).mp id
  · intro h tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv k hk hKnows
    exact (h tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv k hk hKnows).imp
      (hEx b a ikB ikA spk pqpk opk i tr).mpr id

private theorem not_loggedBeforeGap_of_singleton {tr : ExecTrace} {p : PQXDHEvent → Bool}
    {e : PQXDHEvent} {g i k : Nat} (hidx : evIdx tr p = [k]) (hp : p e = true)
    (hg : i - k ≤ g) : ¬ LoggedBeforeGap g e i tr :=
  fun ⟨_, hj, hlt⟩ => not_gap_lt_of_singleton hj hidx hp hg hlt

private theorem not_loggedBeforeGap_of_none {tr : ExecTrace} {p : PQXDHEvent → Bool}
    {e : PQXDHEvent} {g i : Nat} (hidx : evIdx tr p = []) (hp : p e = true) :
    ¬ LoggedBeforeGap g e i tr :=
  fun ⟨j, hj, _⟩ => not_logged hidx hp ⟨j, hj⟩

/-- Tightening the pre-exchange `CompromisedIK` bound in `AliceHandshakeWasCompromised` to
`j + 11 < i` falsifies `AliceInitiatorSecrecy`. -/
theorem not_ResponderSecrecyGap_ik : ¬ ResponderSecrecyGap 11 0 := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trIKB p = (evIdx trIKB isCompromise).filter fun i =>
        match trIKB.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trIKB.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine not_ResponderSecrecyWith_of_witness trIKB_reach trIKB_aliceDone
    (Or.inl rfl) (trIKB_knows_block (Or.inl rfl)) (trIKB_no_sessionStateExposed _) ?_
  rintro (⟨j, hj, hlt | ⟨hS, _⟩⟩ | ⟨j, hj, _⟩)
  · exact not_gap_lt_of_singleton (p := isCompIK) (k := 22) hj
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trIKB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trIKB_compIK]; all_goals decide)
      rfl (by decide) hlt
  · exact not_logged (p := isCompSPK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trIKB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trIKB_compIK]; all_goals decide) rfl hS
  · exact not_logged (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trIKB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trIKB_compIK]; all_goals decide) rfl ⟨j, hj⟩

/-- Tightening the pre-exchange `BrokenDH` bound in `AliceHandshakeWasCompromised` to `j + 11 < i`
falsifies `AliceInitiatorSecrecy`. -/
theorem not_ResponderSecrecyGap_dh : ¬ ResponderSecrecyGap 0 11 := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trBrokenDHA p = (evIdx trBrokenDHA isCompromise).filter fun i =>
        match trBrokenDHA.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trBrokenDHA.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine not_ResponderSecrecyWith_of_witness trBrokenDHA_reach trBrokenDHA_aliceDone
    (Or.inl rfl) (trBrokenDHA_knows_block (Or.inl rfl)) (trBrokenDHA_no_sessionStateExposed _) ?_
  rintro (⟨j, hj, _⟩ | ⟨j, hj, hlt | hP | hK⟩)
  · exact not_logged (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHA_brokenDH]; all_goals decide) rfl ⟨j, hj⟩
  · exact not_gap_lt_of_singleton (p := isBrokenDH) (k := 22) hj
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHA_brokenDH]; all_goals decide)
      rfl (by decide) hlt
  · exact not_logged (p := isCompPQ)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHA_brokenDH]; all_goals decide) rfl hP
  · exact not_logged (p := isBrokenKEM)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHA_brokenDH]; all_goals decide) rfl hK

/-- Tightening the pre-exchange `CompromisedIK` bound in `Thm9Case 0` to `j + 7 < i` falsifies
`BobResponderSecrecy`. -/
theorem not_InitiatorSecrecyGap_ikA : ¬ InitiatorSecrecyGap 7 0 0 := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trIKA p = (evIdx trIKA isCompromise).filter fun i =>
        match trIKA.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trIKA.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine not_InitiatorSecrecyWith_of_witness trIKA_reach trIKA_bobDone
    (Or.inl rfl) (trIKA_knows_block (Or.inl rfl)) (trIKA_no_sessionStateExposed _) ?_
  rintro ⟨k, hk⟩
  revert hk; match k with
  | 0 =>
    exact not_loggedBeforeGap_of_singleton (p := isCompIK) (k := 22)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trIKA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trIKA_compIK]; all_goals decide)
      rfl (by decide)
  | 1 =>
    exact not_loggedBeforeGap_of_none (p := isCompSPK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trIKA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trIKA_compIK]; all_goals decide) rfl
  | 2 | 3 =>
    exact fun ⟨_, hS, _⟩ => not_logged (p := isCompSPK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trIKA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trIKA_compIK]; all_goals decide) rfl hS
  | 4 =>
    exact not_loggedBeforeGap_of_none (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trIKA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trIKA_compIK]; all_goals decide) rfl
  | 5 | 6 =>
    exact fun ⟨hD, _⟩ => not_logged (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trIKA_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trIKA_compIK]; all_goals decide) rfl hD

/-- Tightening the pre-exchange `CompromisedSPK` bound in `Thm9Case 1` to `j + 7 < i` falsifies
`BobResponderSecrecy`. -/
theorem not_InitiatorSecrecyGap_spk : ¬ InitiatorSecrecyGap 0 7 0 := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trSPKB p = (evIdx trSPKB isCompromise).filter fun i =>
        match trSPKB.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trSPKB.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine not_InitiatorSecrecyWith_of_witness trSPKB_reach trSPKB_bobDone
    (Or.inl rfl) (trSPKB_knows_block (Or.inl rfl)) (trSPKB_no_sessionStateExposed _) ?_
  rintro ⟨k, hk⟩
  revert hk; match k with
  | 0 =>
    exact not_loggedBeforeGap_of_none (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trSPKB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trSPKB_compSPK]; all_goals decide) rfl
  | 1 =>
    exact not_loggedBeforeGap_of_singleton (p := isCompSPK) (k := 22)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trSPKB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trSPKB_compSPK]; all_goals decide)
      rfl (by decide)
  | 2 | 3 =>
    exact fun ⟨hI, _⟩ => not_logged (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trSPKB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trSPKB_compSPK]; all_goals decide) rfl hI
  | 4 =>
    exact not_loggedBeforeGap_of_none (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trSPKB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trSPKB_compSPK]; all_goals decide) rfl
  | 5 | 6 =>
    exact fun ⟨hD, _⟩ => not_logged (p := isBrokenDH)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trSPKB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trSPKB_compSPK]; all_goals decide) rfl hD

/-- Tightening the pre-exchange `BrokenDH` bound in `Thm9Case 4` to `j + 7 < i` falsifies
`BobResponderSecrecy`. -/
theorem not_InitiatorSecrecyGap_dh : ¬ InitiatorSecrecyGap 0 0 7 := by
  have hf (p : PQXDHEvent → Bool) (hp : ∀ e, p e = true → isCompromise e = true) :
      evIdx trBrokenDHB p = (evIdx trBrokenDHB isCompromise).filter fun i =>
        match trBrokenDHB.getEventAt PQXDHEvent i with | some e => p e | none => false := by
    dsimp only [evIdx]; rw [List.filter_filter]; congr 1; funext i
    cases trBrokenDHB.getEventAt PQXDHEvent i with | none => rfl | some e => cases hc : p e <;> simp_all
  refine not_InitiatorSecrecyWith_of_witness trBrokenDHB_reach trBrokenDHB_bobDone
    (Or.inl rfl) (trBrokenDHB_knows_block (Or.inl rfl)) (trBrokenDHB_no_sessionStateExposed _) ?_
  rintro ⟨k, hk⟩
  revert hk; match k with
  | 0 =>
    exact not_loggedBeforeGap_of_none (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHB_brokenDH]; all_goals decide) rfl
  | 1 =>
    exact not_loggedBeforeGap_of_none (p := isCompSPK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHB_brokenDH]; all_goals decide) rfl
  | 2 | 3 =>
    exact fun ⟨hI, _⟩ => not_logged (p := isCompIK)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHB_brokenDH]; all_goals decide) rfl hI
  | 4 =>
    exact not_loggedBeforeGap_of_singleton (p := isBrokenDH) (k := 22)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHB_brokenDH]; all_goals decide)
      rfl (by decide)
  | 5 =>
    exact fun ⟨_, hP⟩ => not_logged (p := isCompPQ)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHB_brokenDH]; all_goals decide) rfl hP
  | 6 =>
    exact fun ⟨_, hK⟩ => not_logged (p := isBrokenKEM)
      (by rw [hf _ (by intro e he; cases e <;> first | rfl | nomatch he), trBrokenDHB_compromise_indices]; simp only [List.filter, (DY.Trace.EventLoggedAt_eq_getEventAt _ _ _).mp trBrokenDHB_brokenDH]; all_goals decide) rfl hK

end BoundsGap

end Symbolic.Proofs.Tests.Model.ExplanationTightness.PQXDHSecrecy
