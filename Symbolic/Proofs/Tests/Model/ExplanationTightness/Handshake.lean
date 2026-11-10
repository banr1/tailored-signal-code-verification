/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
import Init.Data.String.Defs
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Bytes.AttackerKnowledge
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
import Symbolic.Proofs.Tests.Shared.ExplanationTightness.HandshakeDead
import Symbolic.Proofs.Tests.Shared.ExplanationTightness.HandshakeTraces
import Symbolic.Proofs.Tests.Shared.ExplanationTightness.CompromisedTraces
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

@[expose] public section

set_option autoImplicit false

/-!
# Tightness of `SessionStateExposed` in Handshake Secrecy

Mutant analysis of `SessionStateExposed` in `AliceInitiatorSecrecy` and `BobResponderSecrecy`
over reachable traces of the composed model. Omitting `SessionStateExposed`, omitting the
`ExposedSpqr` or `ExposedCKr` disjuncts, omitting either branch of `HandshakeKeysAt`, or
restricting the session witness to the queried handshake index `j = i` falsifies both secrecy
properties, whereas the `ExposedCKs` and `ExposedRK` disjuncts are unreachable on handshake-initial
keys and hence equivalent to the full specification.
-/

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.Handshake

open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (ikA ikB keys1 o1 pqskB spkB)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.HandshakeDead (
  exposedCKs_handshakeCk_dead_shared exposedRK_handshakeRk_dead_shared)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.HandshakeTraces (eventsOn hs_mem no_ev
  not_thm7Excuse_of_noCompromise not_thm9Excuse_of_noCompromise trExpCkrA trExpCkrA_aliceDone_at
  trExpCkrA_bobDone_at trExpCkrA_knows_ck trExpCkrA_noCompromise trExpCkrA_reach
  trExpCkrA_sessions trExpSpqrA trExpSpqrA_aliceDone_at trExpSpqrA_bobDone_at trExpSpqrA_knows_pqr
  trExpSpqrA_noCompromise trExpSpqrA_reach trExpSpqrA_sessions trExpSpqrB trExpSpqrB_aliceDone_at
  trExpSpqrB_bobDone_at trExpSpqrB_knows_pqr trExpSpqrB_noCompromise trExpSpqrB_reach
  trExpSpqrB_sessions)
open DY DY.Libsignal DY.Libsignal.Composed

open DY.DiffieHellman DY.PQKem
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys IsHandshakeBlock HandshakeKeysAt
  SessionStateExposed AliceHandshakeWasCompromised BobHandshakeWasCompromised AliceInitiatorSecrecyQuery BobResponderSecrecyQuery)
open DY.Libsignal.TripleRatchet (TREvent)

/-! ## Parameterized secrecy predicates -/

/-- `AliceInitiatorSecrecyQuery` parameterized by the session-exposure predicate `SSE`. -/
def ResponderSecrecyQueryWith (SSE : ExecTrace → HandshakeKeys → Bytes → Prop)
    (tr : ExecTrace) (Knows : Bytes → Prop) : Prop :=
  ∀ a b ikA ikB spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i →
    ∀ k, IsHandshakeBlock keys k → Knows k →
    AliceHandshakeWasCompromised b ikB spk pqpk i tr ∨ SSE tr keys k

/-- `BobResponderSecrecyQuery` parameterized by the session-exposure predicate `SSE`. -/
def InitiatorSecrecyQueryWith (SSE : ExecTrace → HandshakeKeys → Bytes → Prop)
    (tr : ExecTrace) (Knows : Bytes → Prop) : Prop :=
  ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    ∀ k, IsHandshakeBlock keys k → Knows k →
    BobHandshakeWasCompromised b a ikB ikA spk pqpk opk i tr ∨ SSE tr keys k

theorem responderSecrecyQueryWith_real (tr : ExecTrace) (Knows : Bytes → Prop) :
    ResponderSecrecyQueryWith SessionStateExposed tr Knows ↔ AliceInitiatorSecrecyQuery tr Knows :=
  Iff.rfl

theorem initiatorSecrecyQueryWith_real (tr : ExecTrace) (Knows : Bytes → Prop) :
    InitiatorSecrecyQueryWith SessionStateExposed tr Knows ↔ BobResponderSecrecyQuery tr Knows :=
  Iff.rfl

def ResponderSecrecyWith (SSE : ExecTrace → HandshakeKeys → Bytes → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    ResponderSecrecyQueryWith SSE tr (fun t => t.AttackerKnows tr)

def InitiatorSecrecyWith (SSE : ExecTrace → HandshakeKeys → Bytes → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    InitiatorSecrecyQueryWith SSE tr (fun t => t.AttackerKnows tr)

theorem responderSecrecyWith_real : ResponderSecrecyWith SessionStateExposed ↔ AliceInitiatorSecrecy :=
  Iff.rfl

theorem initiatorSecrecyWith_real : InitiatorSecrecyWith SessionStateExposed ↔ BobResponderSecrecy :=
  Iff.rfl

theorem ResponderSecrecyWith.mono {SSE SSE' : ExecTrace → HandshakeKeys → Bytes → Prop}
    (h : ∀ tr : ExecTrace, tr.Reachable reachability → ∀ keys k, SSE tr keys k → SSE' tr keys k)
    (hS : ResponderSecrecyWith SSE) : ResponderSecrecyWith SSE' := by
  intro tr hR a b ikA ikB spk pqpk opk ek ct keys i hEv k hk hK
  rcases hS tr hR a b ikA ikB spk pqpk opk ek ct keys i hEv k hk hK with h7 | hE
  · exact Or.inl h7
  · exact Or.inr (h tr hR keys k hE)

theorem InitiatorSecrecyWith.mono {SSE SSE' : ExecTrace → HandshakeKeys → Bytes → Prop}
    (h : ∀ tr : ExecTrace, tr.Reachable reachability → ∀ keys k, SSE tr keys k → SSE' tr keys k)
    (hS : InitiatorSecrecyWith SSE) : InitiatorSecrecyWith SSE' := by
  intro tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv k hk hK
  rcases hS tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv k hk hK with h9 | hE
  · exact Or.inl h9
  · exact Or.inr (h tr hR keys k hE)

/-! ## Exposure-event disjunct mutants -/

/-- `SessionStateExposed` omitting the `ExposedSpqr` disjunct. -/
def SessionStateExposed_withoutPqr (tr : ExecTrace) (keys : HandshakeKeys) (k : Bytes) : Prop :=
  ∃ s j, tr.EventLogged (ComposedEvent.HandshakeSession s j) ∧ HandshakeKeysAt tr j keys ∧
    ((k = keys.ck ∧ ∃ n r, tr.EventLogged (TREvent.ExposedCKr s keys.ck n r)) ∨
     (k = keys.ck ∧ ∃ n r, tr.EventLogged (TREvent.ExposedCKs s keys.ck n r)) ∨
     (k = keys.rk ∧ ∃ r, tr.EventLogged (TREvent.ExposedRK s keys.rk r)))

theorem sessionStateExposed_withoutPqr_iff (tr : ExecTrace) (keys : HandshakeKeys) (k : Bytes) :
    SessionStateExposed tr keys k ↔
      (∃ s j, tr.EventLogged (ComposedEvent.HandshakeSession s j) ∧ HandshakeKeysAt tr j keys ∧
        k = keys.pqr ∧ ∃ sp r, tr.EventLogged (TREvent.ExposedSpqr s sp r)) ∨
      SessionStateExposed_withoutPqr tr keys k := by
  constructor
  · rintro ⟨s, j, hS, hK, hp | hrest⟩
    · exact Or.inl ⟨s, j, hS, hK, hp⟩
    · exact Or.inr ⟨s, j, hS, hK, hrest⟩
  · rintro (⟨s, j, hS, hK, hp⟩ | ⟨s, j, hS, hK, hrest⟩)
    · exact ⟨s, j, hS, hK, Or.inl hp⟩
    · exact ⟨s, j, hS, hK, Or.inr hrest⟩

/-- `SessionStateExposed` omitting the `ExposedCKr` disjunct. -/
def SessionStateExposed_withoutCkr (tr : ExecTrace) (keys : HandshakeKeys) (k : Bytes) : Prop :=
  ∃ s j, tr.EventLogged (ComposedEvent.HandshakeSession s j) ∧ HandshakeKeysAt tr j keys ∧
    ((k = keys.pqr ∧ ∃ sp r, tr.EventLogged (TREvent.ExposedSpqr s sp r)) ∨
     (k = keys.ck ∧ ∃ n r, tr.EventLogged (TREvent.ExposedCKs s keys.ck n r)) ∨
     (k = keys.rk ∧ ∃ r, tr.EventLogged (TREvent.ExposedRK s keys.rk r)))

theorem sessionStateExposed_withoutCkr_iff (tr : ExecTrace) (keys : HandshakeKeys) (k : Bytes) :
    SessionStateExposed tr keys k ↔
      (∃ s j, tr.EventLogged (ComposedEvent.HandshakeSession s j) ∧ HandshakeKeysAt tr j keys ∧
        k = keys.ck ∧ ∃ n r, tr.EventLogged (TREvent.ExposedCKr s keys.ck n r)) ∨
      SessionStateExposed_withoutCkr tr keys k := by
  constructor
  · rintro ⟨s, j, hS, hK, hp | hckr | hrest⟩
    · exact Or.inr ⟨s, j, hS, hK, Or.inl hp⟩
    · exact Or.inl ⟨s, j, hS, hK, hckr⟩
    · exact Or.inr ⟨s, j, hS, hK, Or.inr hrest⟩
  · rintro (⟨s, j, hS, hK, hckr⟩ | ⟨s, j, hS, hK, hp | hrest⟩)
    · exact ⟨s, j, hS, hK, Or.inr (Or.inl hckr)⟩
    · exact ⟨s, j, hS, hK, Or.inl hp⟩
    · exact ⟨s, j, hS, hK, Or.inr (Or.inr hrest)⟩

/-- `SessionStateExposed` omitting the `ExposedCKs` disjunct. -/
def SessionStateExposed_withoutCks (tr : ExecTrace) (keys : HandshakeKeys) (k : Bytes) : Prop :=
  ∃ s j, tr.EventLogged (ComposedEvent.HandshakeSession s j) ∧ HandshakeKeysAt tr j keys ∧
    ((k = keys.pqr ∧ ∃ sp r, tr.EventLogged (TREvent.ExposedSpqr s sp r)) ∨
     (k = keys.ck ∧ ∃ n r, tr.EventLogged (TREvent.ExposedCKr s keys.ck n r)) ∨
     (k = keys.rk ∧ ∃ r, tr.EventLogged (TREvent.ExposedRK s keys.rk r)))

theorem sessionStateExposed_withoutCks_iff_real (tr : ExecTrace) (keys : HandshakeKeys) (k : Bytes) :
    SessionStateExposed tr keys k ↔
      (∃ s j, tr.EventLogged (ComposedEvent.HandshakeSession s j) ∧ HandshakeKeysAt tr j keys ∧
        k = keys.ck ∧ ∃ n r, tr.EventLogged (TREvent.ExposedCKs s keys.ck n r)) ∨
      SessionStateExposed_withoutCks tr keys k := by
  constructor
  · rintro ⟨s, j, hS, hK, hp | hckr | hcks | hrk⟩
    · exact Or.inr ⟨s, j, hS, hK, Or.inl hp⟩
    · exact Or.inr ⟨s, j, hS, hK, Or.inr (Or.inl hckr)⟩
    · exact Or.inl ⟨s, j, hS, hK, hcks⟩
    · exact Or.inr ⟨s, j, hS, hK, Or.inr (Or.inr hrk)⟩
  · rintro (⟨s, j, hS, hK, hcks⟩ | ⟨s, j, hS, hK, hp | hckr | hrk⟩)
    · exact ⟨s, j, hS, hK, Or.inr (Or.inr (Or.inl hcks))⟩
    · exact ⟨s, j, hS, hK, Or.inl hp⟩
    · exact ⟨s, j, hS, hK, Or.inr (Or.inl hckr)⟩
    · exact ⟨s, j, hS, hK, Or.inr (Or.inr (Or.inr hrk))⟩

/-- `SessionStateExposed` omitting the `ExposedRK` disjunct. -/
def SessionStateExposed_withoutRk (tr : ExecTrace) (keys : HandshakeKeys) (k : Bytes) : Prop :=
  ∃ s j, tr.EventLogged (ComposedEvent.HandshakeSession s j) ∧ HandshakeKeysAt tr j keys ∧
    ((k = keys.pqr ∧ ∃ sp r, tr.EventLogged (TREvent.ExposedSpqr s sp r)) ∨
     (k = keys.ck ∧ ∃ n r, tr.EventLogged (TREvent.ExposedCKr s keys.ck n r)) ∨
     (k = keys.ck ∧ ∃ n r, tr.EventLogged (TREvent.ExposedCKs s keys.ck n r)))

theorem sessionStateExposed_withoutRk_iff_real (tr : ExecTrace) (keys : HandshakeKeys) (k : Bytes) :
    SessionStateExposed tr keys k ↔
      (∃ s j, tr.EventLogged (ComposedEvent.HandshakeSession s j) ∧ HandshakeKeysAt tr j keys ∧
        k = keys.rk ∧ ∃ r, tr.EventLogged (TREvent.ExposedRK s keys.rk r)) ∨
      SessionStateExposed_withoutRk tr keys k := by
  constructor
  · rintro ⟨s, j, hS, hK, hp | hckr | hcks | hrk⟩
    · exact Or.inr ⟨s, j, hS, hK, Or.inl hp⟩
    · exact Or.inr ⟨s, j, hS, hK, Or.inr (Or.inl hckr)⟩
    · exact Or.inr ⟨s, j, hS, hK, Or.inr (Or.inr hcks)⟩
    · exact Or.inl ⟨s, j, hS, hK, hrk⟩
  · rintro (⟨s, j, hS, hK, hrk⟩ | ⟨s, j, hS, hK, hp | hckr | hcks⟩)
    · exact ⟨s, j, hS, hK, Or.inr (Or.inr (Or.inr hrk))⟩
    · exact ⟨s, j, hS, hK, Or.inl hp⟩
    · exact ⟨s, j, hS, hK, Or.inr (Or.inl hckr)⟩
    · exact ⟨s, j, hS, hK, Or.inr (Or.inr (Or.inl hcks))⟩

abbrev ResponderSecrecy_withoutPqr : Prop := ResponderSecrecyWith SessionStateExposed_withoutPqr
abbrev ResponderSecrecy_withoutCkr : Prop := ResponderSecrecyWith SessionStateExposed_withoutCkr
abbrev ResponderSecrecy_withoutCks : Prop := ResponderSecrecyWith SessionStateExposed_withoutCks
abbrev ResponderSecrecy_withoutRk : Prop := ResponderSecrecyWith SessionStateExposed_withoutRk
abbrev InitiatorSecrecy_withoutPqr : Prop := InitiatorSecrecyWith SessionStateExposed_withoutPqr
abbrev InitiatorSecrecy_withoutCkr : Prop := InitiatorSecrecyWith SessionStateExposed_withoutCkr
abbrev InitiatorSecrecy_withoutCks : Prop := InitiatorSecrecyWith SessionStateExposed_withoutCks
abbrev InitiatorSecrecy_withoutRk : Prop := InitiatorSecrecyWith SessionStateExposed_withoutRk

/-! ## Refutation of `ExposedSpqr` and `ExposedCKr` omissions -/

private def isNonSpqrExposure : TREvent → Bool
  | .ExposedCKr .. | .ExposedCKs .. | .ExposedRK .. => true
  | _ => false

private theorem trExpSpqrA_not_sse_withoutPqr :
    ¬ SessionStateExposed_withoutPqr trExpSpqrA keys1 keys1.pqr := by
  have h_app : ∀ {tr : ExecTrace} {E : Type} [ExecTraceTypes.Has E] (e : E) {ev : TREvent},
      tr.EventLogged ev → (tr.append e).EventLogged ev := by
    rintro tr E _ e ev ⟨i, hi⟩
    have hlt : i < tr.length := DY.Trace.EventLoggedAt_implies_i_le_length ev i tr hi
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
    refine ⟨i, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr ?_⟩
    rwa [Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.at?_append_of_lt tr e hlt]
  have hpeel : ∀ {ev : TREvent}, isNonSpqrExposure ev = true → ¬ trExpSpqrA.EventLogged ev := by
    intro ev hp hlog
    dsimp only [trExpSpqrA, Symbolic.Proofs.Tests.Shared.Composed.Runs.exposeSpqrTr] at hlog
    rcases Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_ev
        (Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_other rfl hlog) with hlog | rfl
    · have hexp : Symbolic.Proofs.Tests.Shared.Composed.Adversary.isAnyTRExposure ev = true := by
        cases ev <;> simp_all [isNonSpqrExposure,
          Symbolic.Proofs.Tests.Shared.Composed.Adversary.isAnyTRExposure]
      exact Symbolic.Proofs.Tests.Shared.Composed.Adversary.not_tr_logged
        Symbolic.Proofs.Tests.Shared.Composed.Adversary.trThm9Case2_trExposure_indices hexp
        (h_app _ (h_app _ (h_app _ (h_app _ (h_app _ (h_app _ hlog))))))
    · nomatch hp
  rintro ⟨_, _, _, _, ⟨_, _, _, hckr⟩ | ⟨_, _, _, hcks⟩ | ⟨_, _, hrk⟩⟩
  · exact hpeel rfl hckr
  · exact hpeel rfl hcks
  · exact hpeel rfl hrk

private def isNonCkrExposure : TREvent → Bool
  | .ExposedSpqr .. | .ExposedCKs .. | .ExposedRK .. => true
  | _ => false

private theorem trExpCkrA_not_sse_withoutCkr :
    ¬ SessionStateExposed_withoutCkr trExpCkrA keys1 keys1.ck := by
  have h_app : ∀ {tr : ExecTrace} {E : Type} [ExecTraceTypes.Has E] (e : E) {ev : TREvent},
      tr.EventLogged ev → (tr.append e).EventLogged ev := by
    rintro tr E _ e ev ⟨i, hi⟩
    have hlt : i < tr.length := DY.Trace.EventLoggedAt_implies_i_le_length ev i tr hi
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
    refine ⟨i, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr ?_⟩
    rwa [Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.at?_append_of_lt tr e hlt]
  have hpeel : ∀ {ev : TREvent}, isNonCkrExposure ev = true → ¬ trExpCkrA.EventLogged ev := by
    intro ev hp hlog
    dsimp only [trExpCkrA, Symbolic.Proofs.Tests.Shared.Composed.Runs.exposeCkrTr] at hlog
    rcases Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_ev
        (Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_other rfl hlog) with hlog | rfl
    · have hexp : Symbolic.Proofs.Tests.Shared.Composed.Adversary.isAnyTRExposure ev = true := by
        cases ev <;> simp_all [isNonCkrExposure,
          Symbolic.Proofs.Tests.Shared.Composed.Adversary.isAnyTRExposure]
      exact Symbolic.Proofs.Tests.Shared.Composed.Adversary.not_tr_logged
        Symbolic.Proofs.Tests.Shared.Composed.Adversary.trThm9Case2_trExposure_indices hexp
        (h_app _ (h_app _ (h_app _ (h_app _ (h_app _ (h_app _ hlog))))))
    · nomatch hp
  rintro ⟨_, _, _, _, ⟨_, _, _, hspqr⟩ | ⟨_, _, _, hcks⟩ | ⟨_, _, hrk⟩⟩
  · exact hpeel rfl hspqr
  · exact hpeel rfl hcks
  · exact hpeel rfl hrk

/-- Omitting the `ExposedSpqr` disjunct of `SessionStateExposed` falsifies `AliceInitiatorSecrecy`. -/
theorem not_ResponderSecrecy_withoutPqr : ¬ ResponderSecrecy_withoutPqr := by
  intro h
  rcases h trExpSpqrA trExpSpqrA_reach "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB)
    (kemPk pqskB) none o1.ek o1.ct keys1 27 trExpSpqrA_aliceDone_at keys1.pqr
    (Or.inr (Or.inr rfl)) trExpSpqrA_knows_pqr with h7 | hsse
  · exact not_thm7Excuse_of_noCompromise trExpSpqrA_noCompromise h7
  · exact trExpSpqrA_not_sse_withoutPqr hsse

/-- Omitting the `ExposedSpqr` disjunct of `SessionStateExposed` falsifies `BobResponderSecrecy`. -/
theorem not_InitiatorSecrecy_withoutPqr : ¬ InitiatorSecrecy_withoutPqr := by
  intro h
  rcases h trExpSpqrA trExpSpqrA_reach "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
    (kemPk pqskB) none o1.ek o1.ct keys1 47 trExpSpqrA_bobDone_at keys1.pqr
    (Or.inr (Or.inr rfl)) trExpSpqrA_knows_pqr with h9 | hsse
  · exact not_thm9Excuse_of_noCompromise trExpSpqrA_noCompromise h9
  · exact trExpSpqrA_not_sse_withoutPqr hsse

/-- Omitting the `ExposedCKr` disjunct of `SessionStateExposed` falsifies `AliceInitiatorSecrecy`. -/
theorem not_ResponderSecrecy_withoutCkr : ¬ ResponderSecrecy_withoutCkr := by
  intro h
  rcases h trExpCkrA trExpCkrA_reach "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB)
    (kemPk pqskB) none o1.ek o1.ct keys1 27 trExpCkrA_aliceDone_at keys1.ck
    (Or.inr (Or.inl rfl)) trExpCkrA_knows_ck with h7 | hsse
  · exact not_thm7Excuse_of_noCompromise trExpCkrA_noCompromise h7
  · exact trExpCkrA_not_sse_withoutCkr hsse

/-- Omitting the `ExposedCKr` disjunct of `SessionStateExposed` falsifies `BobResponderSecrecy`. -/
theorem not_InitiatorSecrecy_withoutCkr : ¬ InitiatorSecrecy_withoutCkr := by
  intro h
  rcases h trExpCkrA trExpCkrA_reach "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
    (kemPk pqskB) none o1.ek o1.ct keys1 47 trExpCkrA_bobDone_at keys1.ck
    (Or.inr (Or.inl rfl)) trExpCkrA_knows_ck with h9 | hsse
  · exact not_thm9Excuse_of_noCompromise trExpCkrA_noCompromise h9
  · exact trExpCkrA_not_sse_withoutCkr hsse

/-! ## Refutation of omitting `SessionStateExposed` -/

def ResponderSecrecyQuery_withoutSSE (tr : ExecTrace) (Knows : Bytes → Prop) : Prop :=
  ∀ a b ikA ikB spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i →
    ∀ k, IsHandshakeBlock keys k → Knows k →
    AliceHandshakeWasCompromised b ikB spk pqpk i tr

def InitiatorSecrecyQuery_withoutSSE (tr : ExecTrace) (Knows : Bytes → Prop) : Prop :=
  ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    ∀ k, IsHandshakeBlock keys k → Knows k →
    BobHandshakeWasCompromised b a ikB ikA spk pqpk opk i tr

abbrev ResponderSecrecy_withoutSSE : Prop := ResponderSecrecyWith fun _ _ _ => False

abbrev InitiatorSecrecy_withoutSSE : Prop := InitiatorSecrecyWith fun _ _ _ => False

theorem responderSecrecyQuery_withoutSSE_iff (tr : ExecTrace) (Knows : Bytes → Prop) :
    ResponderSecrecyQueryWith (fun _ _ _ => False) tr Knows ↔
      ResponderSecrecyQuery_withoutSSE tr Knows := by
  simp [ResponderSecrecyQueryWith, ResponderSecrecyQuery_withoutSSE]

theorem initiatorSecrecyQuery_withoutSSE_iff (tr : ExecTrace) (Knows : Bytes → Prop) :
    InitiatorSecrecyQueryWith (fun _ _ _ => False) tr Knows ↔
      InitiatorSecrecyQuery_withoutSSE tr Knows := by
  simp [InitiatorSecrecyQueryWith, InitiatorSecrecyQuery_withoutSSE]

/-- Omitting `SessionStateExposed` altogether falsifies `AliceInitiatorSecrecy`. -/
theorem not_ResponderSecrecy_withoutSSE : ¬ ResponderSecrecy_withoutSSE := fun h =>
  not_ResponderSecrecy_withoutCkr (h.mono fun _ _ _ _ hF => hF.elim)

/-- Omitting `SessionStateExposed` altogether falsifies `BobResponderSecrecy`. -/
theorem not_InitiatorSecrecy_withoutSSE : ¬ InitiatorSecrecy_withoutSSE := fun h =>
  not_InitiatorSecrecy_withoutCkr (h.mono fun _ _ _ _ hF => hF.elim)

/-! ## `HandshakeKeysAt` branch mutants -/

def SessionStateExposedWithKeysAt (HK : ExecTrace → Nat → HandshakeKeys → Prop)
    (tr : ExecTrace) (keys : HandshakeKeys) (k : Bytes) : Prop :=
  ∃ s j, tr.EventLogged (ComposedEvent.HandshakeSession s j) ∧ HK tr j keys ∧
    ((k = keys.pqr ∧ ∃ sp r, tr.EventLogged (TREvent.ExposedSpqr s sp r)) ∨
     (k = keys.ck ∧ ∃ n r, tr.EventLogged (TREvent.ExposedCKr s keys.ck n r)) ∨
     (k = keys.ck ∧ ∃ n r, tr.EventLogged (TREvent.ExposedCKs s keys.ck n r)) ∨
     (k = keys.rk ∧ ∃ r, tr.EventLogged (TREvent.ExposedRK s keys.rk r)))

theorem sessionStateExposedWithKeysAt_real (tr : ExecTrace) (keys : HandshakeKeys) (k : Bytes) :
    SessionStateExposedWithKeysAt HandshakeKeysAt tr keys k ↔ SessionStateExposed tr keys k :=
  Iff.rfl

/-- `HandshakeKeysAt` restricted to `AliceDone` events. -/
def HandshakeKeysAt_noBobDone (tr : ExecTrace) (j : Nat) (keys : HandshakeKeys) : Prop :=
  ∃ a b ikA ikB spk pqpk opk ek ct,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) j

theorem handshakeKeysAt_noBobDone_iff (tr : ExecTrace) (j : Nat) (keys : HandshakeKeys) :
    HandshakeKeysAt tr j keys ↔ HandshakeKeysAt_noBobDone tr j keys ∨
      ∃ b a ikB ikA spk pqpk opk ek ct,
        tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) j := by
  constructor
  · rintro ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, h⟩ | ⟨ek, ct, h⟩⟩
    · exact .inl ⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, h⟩
    · exact .inr ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, h⟩
  · rintro (⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, h⟩ |
        ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, h⟩)
    · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inl ⟨ek, ct, h⟩⟩
    · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inr ⟨ek, ct, h⟩⟩

/-- `HandshakeKeysAt` restricted to `BobDone` events. -/
def HandshakeKeysAt_noAliceDone (tr : ExecTrace) (j : Nat) (keys : HandshakeKeys) : Prop :=
  ∃ b a ikB ikA spk pqpk opk ek ct,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) j

theorem handshakeKeysAt_noAliceDone_iff (tr : ExecTrace) (j : Nat) (keys : HandshakeKeys) :
    HandshakeKeysAt tr j keys ↔
      (∃ a b ikA ikB spk pqpk opk ek ct,
        tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) j) ∨
      HandshakeKeysAt_noAliceDone tr j keys := by
  constructor
  · rintro ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, h⟩ | ⟨ek, ct, h⟩⟩
    · exact .inl ⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, h⟩
    · exact .inr ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, h⟩
  · rintro (⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, h⟩ |
        ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, h⟩)
    · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inl ⟨ek, ct, h⟩⟩
    · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inr ⟨ek, ct, h⟩⟩

def SessionStateExposed_noBobDoneKeys (tr : ExecTrace) (keys : HandshakeKeys) (k : Bytes) :
    Prop :=
  SessionStateExposedWithKeysAt HandshakeKeysAt_noBobDone tr keys k

def SessionStateExposed_noAliceDoneKeys (tr : ExecTrace) (keys : HandshakeKeys) (k : Bytes) :
    Prop :=
  SessionStateExposedWithKeysAt HandshakeKeysAt_noAliceDone tr keys k

abbrev ResponderSecrecy_noBobDoneKeys : Prop :=
  ResponderSecrecyWith SessionStateExposed_noBobDoneKeys

abbrev InitiatorSecrecy_noBobDoneKeys : Prop :=
  InitiatorSecrecyWith SessionStateExposed_noBobDoneKeys

abbrev ResponderSecrecy_noAliceDoneKeys : Prop :=
  ResponderSecrecyWith SessionStateExposed_noAliceDoneKeys

abbrev InitiatorSecrecy_noAliceDoneKeys : Prop :=
  InitiatorSecrecyWith SessionStateExposed_noAliceDoneKeys

private def isExposureNotOf (p : Participant) : TREvent → Bool
  | .ExposedSpqr s .. | .ExposedCKr s .. | .ExposedCKs s .. | .ExposedRK s .. => s.me != p
  | _ => false

private theorem trExpSpqrB_noExposureNotBob :
    (eventsOn TREvent trExpSpqrB).filter (isExposureNotOf "bob") = [] := by
  have h_snoc : ∀ {tr : ExecTrace} (entry : ExecTrace.Entry) {ev : TREvent},
      tr.EventLogged ev → (DY.Trace.snoc tr entry).EventLogged ev := by
    rintro tr entry ev ⟨i, hi⟩
    have hlt : i < tr.length := DY.Trace.EventLoggedAt_implies_i_le_length ev i tr hi
    have hlt' : i < (DY.Trace.snoc tr entry).length := by
      rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
    have hne : i ≠ tr.length := Nat.ne_of_lt hlt
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
    refine ⟨i, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr ?_⟩
    simp only [DY.Trace.at?, hlt, ↓reduceDIte] at hi
    simp only [DY.Trace.at?, hlt', ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2, hne]
    exact hi
  have hmem_ev : ∀ {tr : ExecTrace} {ev : TREvent},
      ev ∈ eventsOn TREvent tr → tr.EventLogged ev := by
    intro tr
    induction tr with
    | nil => intro ev h; nomatch h
    | snoc tr entry ih =>
      intro ev h
      dsimp only [eventsOn] at h
      cases hproj : (TraceEntryHas.proj entry : Option (ProtocolEvent.ExecEntryT TREvent)) with
      | none =>
        rw [hproj] at h
        exact h_snoc entry (ih h)
      | some e0 =>
        rw [hproj] at h
        cases e0 with | mk e0 =>
        rcases List.mem_cons.mp h with rfl | h
        · refine ⟨tr.length, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr ?_⟩
          have hlt' : tr.length < (DY.Trace.snoc tr entry).length := by
            rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
          simp only [DY.Trace.at?, hlt', ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2]
          exact hproj
        · exact h_snoc entry (ih h)
  have h_app : ∀ {tr : ExecTrace} {E : Type} [ExecTraceTypes.Has E] (e : E) {ev : TREvent},
      tr.EventLogged ev → (tr.append e).EventLogged ev := by
    rintro tr E _ e ev ⟨i, hi⟩
    have hlt : i < tr.length := DY.Trace.EventLoggedAt_implies_i_le_length ev i tr hi
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
    refine ⟨i, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr ?_⟩
    rwa [Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.at?_append_of_lt tr e hlt]
  refine List.filter_eq_nil_iff.mpr fun ev hmem hp => ?_
  have hlog := hmem_ev hmem
  dsimp only [trExpSpqrB, Symbolic.Proofs.Tests.Shared.Composed.Runs.exposeSpqrTr] at hlog
  rcases Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_ev
      (Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_other rfl hlog) with hlog | rfl
  · have hexp : Symbolic.Proofs.Tests.Shared.Composed.Adversary.isAnyTRExposure ev = true := by
      cases ev <;> simp_all [isExposureNotOf,
        Symbolic.Proofs.Tests.Shared.Composed.Adversary.isAnyTRExposure]
    exact Symbolic.Proofs.Tests.Shared.Composed.Adversary.not_tr_logged
      Symbolic.Proofs.Tests.Shared.Composed.Adversary.trThm9Case2_trExposure_indices hexp
      (h_app _ (h_app _ (h_app _ (h_app _ (h_app _ (h_app _ hlog))))))
  · nomatch hp

private theorem trExpSpqrA_noExposureNotAlice :
    (eventsOn TREvent trExpSpqrA).filter (isExposureNotOf "alice") = [] := by
  have h_snoc : ∀ {tr : ExecTrace} (entry : ExecTrace.Entry) {ev : TREvent},
      tr.EventLogged ev → (DY.Trace.snoc tr entry).EventLogged ev := by
    rintro tr entry ev ⟨i, hi⟩
    have hlt : i < tr.length := DY.Trace.EventLoggedAt_implies_i_le_length ev i tr hi
    have hlt' : i < (DY.Trace.snoc tr entry).length := by
      rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
    have hne : i ≠ tr.length := Nat.ne_of_lt hlt
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
    refine ⟨i, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr ?_⟩
    simp only [DY.Trace.at?, hlt, ↓reduceDIte] at hi
    simp only [DY.Trace.at?, hlt', ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2, hne]
    exact hi
  have hmem_ev : ∀ {tr : ExecTrace} {ev : TREvent},
      ev ∈ eventsOn TREvent tr → tr.EventLogged ev := by
    intro tr
    induction tr with
    | nil => intro ev h; nomatch h
    | snoc tr entry ih =>
      intro ev h
      dsimp only [eventsOn] at h
      cases hproj : (TraceEntryHas.proj entry : Option (ProtocolEvent.ExecEntryT TREvent)) with
      | none =>
        rw [hproj] at h
        exact h_snoc entry (ih h)
      | some e0 =>
        rw [hproj] at h
        cases e0 with | mk e0 =>
        rcases List.mem_cons.mp h with rfl | h
        · refine ⟨tr.length, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr ?_⟩
          have hlt' : tr.length < (DY.Trace.snoc tr entry).length := by
            rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
          simp only [DY.Trace.at?, hlt', ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2]
          exact hproj
        · exact h_snoc entry (ih h)
  have h_app : ∀ {tr : ExecTrace} {E : Type} [ExecTraceTypes.Has E] (e : E) {ev : TREvent},
      tr.EventLogged ev → (tr.append e).EventLogged ev := by
    rintro tr E _ e ev ⟨i, hi⟩
    have hlt : i < tr.length := DY.Trace.EventLoggedAt_implies_i_le_length ev i tr hi
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
    refine ⟨i, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr ?_⟩
    rwa [Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.at?_append_of_lt tr e hlt]
  refine List.filter_eq_nil_iff.mpr fun ev hmem hp => ?_
  have hlog := hmem_ev hmem
  dsimp only [trExpSpqrA, Symbolic.Proofs.Tests.Shared.Composed.Runs.exposeSpqrTr] at hlog
  rcases Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_ev
      (Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_other rfl hlog) with hlog | rfl
  · have hexp : Symbolic.Proofs.Tests.Shared.Composed.Adversary.isAnyTRExposure ev = true := by
      cases ev <;> simp_all [isExposureNotOf,
        Symbolic.Proofs.Tests.Shared.Composed.Adversary.isAnyTRExposure]
    exact Symbolic.Proofs.Tests.Shared.Composed.Adversary.not_tr_logged
      Symbolic.Proofs.Tests.Shared.Composed.Adversary.trThm9Case2_trExposure_indices hexp
      (h_app _ (h_app _ (h_app _ (h_app _ (h_app _ (h_app _ hlog))))))
  · nomatch hp

private theorem trExpCkrA_noExposureNotAlice :
    (eventsOn TREvent trExpCkrA).filter (isExposureNotOf "alice") = [] := by
  have h_snoc : ∀ {tr : ExecTrace} (entry : ExecTrace.Entry) {ev : TREvent},
      tr.EventLogged ev → (DY.Trace.snoc tr entry).EventLogged ev := by
    rintro tr entry ev ⟨i, hi⟩
    have hlt : i < tr.length := DY.Trace.EventLoggedAt_implies_i_le_length ev i tr hi
    have hlt' : i < (DY.Trace.snoc tr entry).length := by
      rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
    have hne : i ≠ tr.length := Nat.ne_of_lt hlt
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
    refine ⟨i, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr ?_⟩
    simp only [DY.Trace.at?, hlt, ↓reduceDIte] at hi
    simp only [DY.Trace.at?, hlt', ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2, hne]
    exact hi
  have hmem_ev : ∀ {tr : ExecTrace} {ev : TREvent},
      ev ∈ eventsOn TREvent tr → tr.EventLogged ev := by
    intro tr
    induction tr with
    | nil => intro ev h; nomatch h
    | snoc tr entry ih =>
      intro ev h
      dsimp only [eventsOn] at h
      cases hproj : (TraceEntryHas.proj entry : Option (ProtocolEvent.ExecEntryT TREvent)) with
      | none =>
        rw [hproj] at h
        exact h_snoc entry (ih h)
      | some e0 =>
        rw [hproj] at h
        cases e0 with | mk e0 =>
        rcases List.mem_cons.mp h with rfl | h
        · refine ⟨tr.length, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr ?_⟩
          have hlt' : tr.length < (DY.Trace.snoc tr entry).length := by
            rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
          simp only [DY.Trace.at?, hlt', ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2]
          exact hproj
        · exact h_snoc entry (ih h)
  have h_app : ∀ {tr : ExecTrace} {E : Type} [ExecTraceTypes.Has E] (e : E) {ev : TREvent},
      tr.EventLogged ev → (tr.append e).EventLogged ev := by
    rintro tr E _ e ev ⟨i, hi⟩
    have hlt : i < tr.length := DY.Trace.EventLoggedAt_implies_i_le_length ev i tr hi
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
    refine ⟨i, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr ?_⟩
    rwa [Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.at?_append_of_lt tr e hlt]
  refine List.filter_eq_nil_iff.mpr fun ev hmem hp => ?_
  have hlog := hmem_ev hmem
  dsimp only [trExpCkrA, Symbolic.Proofs.Tests.Shared.Composed.Runs.exposeCkrTr] at hlog
  rcases Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_ev
      (Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon.eventLogged_append_other rfl hlog) with hlog | rfl
  · have hexp : Symbolic.Proofs.Tests.Shared.Composed.Adversary.isAnyTRExposure ev = true := by
      cases ev <;> simp_all [isExposureNotOf,
        Symbolic.Proofs.Tests.Shared.Composed.Adversary.isAnyTRExposure]
    exact Symbolic.Proofs.Tests.Shared.Composed.Adversary.not_tr_logged
      Symbolic.Proofs.Tests.Shared.Composed.Adversary.trThm9Case2_trExposure_indices hexp
      (h_app _ (h_app _ (h_app _ (h_app _ (h_app _ (h_app _ hlog))))))
  · nomatch hp

private theorem trExpSpqrB_not_sse_noBobDoneKeys (k : Bytes) :
    ¬ SessionStateExposed_noBobDoneKeys trExpSpqrB keys1 k := by
  rintro ⟨s, j, hhs, ⟨_, _, _, _, _, _, _, _, _, hAD⟩, hexp⟩
  have hmem := hs_mem trExpSpqrB_sessions hhs
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hAD
    have hbob := trExpSpqrB_bobDone_at
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hbob
    nomatch hAD.symm.trans hbob
  · rcases hexp with ⟨_, _, _, hx⟩ | ⟨_, _, _, hx⟩ | ⟨_, _, _, hx⟩ | ⟨_, _, hx⟩ <;>
      exact no_ev trExpSpqrB_noExposureNotBob hx rfl

private theorem trExpSpqrA_not_sse_noAliceDoneKeys (k : Bytes) :
    ¬ SessionStateExposed_noAliceDoneKeys trExpSpqrA keys1 k := by
  rintro ⟨s, j, hhs, ⟨_, _, _, _, _, _, _, _, _, hBD⟩, hexp⟩
  have hmem := hs_mem trExpSpqrA_sessions hhs
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hexp with ⟨_, _, _, hx⟩ | ⟨_, _, _, hx⟩ | ⟨_, _, _, hx⟩ | ⟨_, _, hx⟩ <;>
      exact no_ev trExpSpqrA_noExposureNotAlice hx rfl
  · rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hBD
    have halice := trExpSpqrA_aliceDone_at
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at halice
    nomatch hBD.symm.trans halice

/-- Omitting the `BobDone` branch of `HandshakeKeysAt` in `SessionStateExposed` falsifies
`AliceInitiatorSecrecy`. -/
theorem not_ResponderSecrecy_noBobDoneKeys : ¬ ResponderSecrecy_noBobDoneKeys := by
  intro h
  rcases h trExpSpqrB trExpSpqrB_reach "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB)
    (kemPk pqskB) none o1.ek o1.ct keys1 27 trExpSpqrB_aliceDone_at keys1.pqr
    (Or.inr (Or.inr rfl)) trExpSpqrB_knows_pqr with h7 | hsse
  · exact not_thm7Excuse_of_noCompromise trExpSpqrB_noCompromise h7
  · exact trExpSpqrB_not_sse_noBobDoneKeys _ hsse

/-- Omitting the `BobDone` branch of `HandshakeKeysAt` in `SessionStateExposed` falsifies
`BobResponderSecrecy`. -/
theorem not_InitiatorSecrecy_noBobDoneKeys : ¬ InitiatorSecrecy_noBobDoneKeys := by
  intro h
  rcases h trExpSpqrB trExpSpqrB_reach "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
    (kemPk pqskB) none o1.ek o1.ct keys1 47 trExpSpqrB_bobDone_at keys1.pqr
    (Or.inr (Or.inr rfl)) trExpSpqrB_knows_pqr with h9 | hsse
  · exact not_thm9Excuse_of_noCompromise trExpSpqrB_noCompromise h9
  · exact trExpSpqrB_not_sse_noBobDoneKeys _ hsse

/-- Omitting the `AliceDone` branch of `HandshakeKeysAt` in `SessionStateExposed` falsifies
`AliceInitiatorSecrecy`. -/
theorem not_ResponderSecrecy_noAliceDoneKeys : ¬ ResponderSecrecy_noAliceDoneKeys := by
  intro h
  rcases h trExpSpqrA trExpSpqrA_reach "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB)
    (kemPk pqskB) none o1.ek o1.ct keys1 27 trExpSpqrA_aliceDone_at keys1.pqr
    (Or.inr (Or.inr rfl)) trExpSpqrA_knows_pqr with h7 | hsse
  · exact not_thm7Excuse_of_noCompromise trExpSpqrA_noCompromise h7
  · exact trExpSpqrA_not_sse_noAliceDoneKeys _ hsse

/-- Omitting the `AliceDone` branch of `HandshakeKeysAt` in `SessionStateExposed` falsifies
`BobResponderSecrecy`. -/
theorem not_InitiatorSecrecy_noAliceDoneKeys : ¬ InitiatorSecrecy_noAliceDoneKeys := by
  intro h
  rcases h trExpSpqrA trExpSpqrA_reach "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
    (kemPk pqskB) none o1.ek o1.ct keys1 47 trExpSpqrA_bobDone_at keys1.pqr
    (Or.inr (Or.inr rfl)) trExpSpqrA_knows_pqr with h9 | hsse
  · exact not_thm9Excuse_of_noCompromise trExpSpqrA_noCompromise h9
  · exact trExpSpqrA_not_sse_noAliceDoneKeys _ hsse

/-! ## Same-handshake index restriction -/

def ResponderSecrecyWithAt (SSE : ExecTrace → Nat → HandshakeKeys → Bytes → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    ∀ a b ikA ikB spk pqpk opk ek ct keys i,
      tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i →
      ∀ k, IsHandshakeBlock keys k → k.AttackerKnows tr →
      AliceHandshakeWasCompromised b ikB spk pqpk i tr ∨ SSE tr i keys k

def InitiatorSecrecyWithAt (SSE : ExecTrace → Nat → HandshakeKeys → Bytes → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    ∀ b a ikB ikA spk pqpk opk ek ct keys i,
      tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
      ∀ k, IsHandshakeBlock keys k → k.AttackerKnows tr →
      BobHandshakeWasCompromised b a ikB ikA spk pqpk opk i tr ∨ SSE tr i keys k

theorem responderSecrecyWithAt_real :
    ResponderSecrecyWithAt (fun tr _ => SessionStateExposed tr) ↔ AliceInitiatorSecrecy :=
  Iff.rfl

theorem initiatorSecrecyWithAt_real :
    InitiatorSecrecyWithAt (fun tr _ => SessionStateExposed tr) ↔ BobResponderSecrecy :=
  Iff.rfl

/-- `SessionStateExposed` restricted to sessions initialized by the handshake at index `i` itself. -/
def SessionStateExposed_sameHandshake (tr : ExecTrace) (i : Nat) (keys : HandshakeKeys)
    (k : Bytes) : Prop :=
  ∃ s, tr.EventLogged (ComposedEvent.HandshakeSession s i) ∧ HandshakeKeysAt tr i keys ∧
    ((k = keys.pqr ∧ ∃ sp r, tr.EventLogged (TREvent.ExposedSpqr s sp r)) ∨
     (k = keys.ck ∧ ∃ n r, tr.EventLogged (TREvent.ExposedCKr s keys.ck n r)) ∨
     (k = keys.ck ∧ ∃ n r, tr.EventLogged (TREvent.ExposedCKs s keys.ck n r)) ∨
     (k = keys.rk ∧ ∃ r, tr.EventLogged (TREvent.ExposedRK s keys.rk r)))

theorem sessionStateExposed_iff_exists_sameHandshake (tr : ExecTrace) (keys : HandshakeKeys)
    (k : Bytes) :
    SessionStateExposed tr keys k ↔ ∃ j, SessionStateExposed_sameHandshake tr j keys k :=
  ⟨fun ⟨s, j, h⟩ => ⟨j, s, h⟩, fun ⟨j, s, h⟩ => ⟨s, j, h⟩⟩

abbrev ResponderSecrecy_sameHandshake : Prop :=
  ResponderSecrecyWithAt SessionStateExposed_sameHandshake

abbrev InitiatorSecrecy_sameHandshake : Prop :=
  InitiatorSecrecyWithAt SessionStateExposed_sameHandshake

/-- Restricting `SessionStateExposed` to the queried handshake index `j = i` falsifies
`AliceInitiatorSecrecy`. -/
theorem not_ResponderSecrecy_sameHandshake : ¬ ResponderSecrecy_sameHandshake := by
  intro h
  rcases h trExpSpqrB trExpSpqrB_reach "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB)
    (kemPk pqskB) none o1.ek o1.ct keys1 27 trExpSpqrB_aliceDone_at keys1.pqr
    (Or.inr (Or.inr rfl)) trExpSpqrB_knows_pqr with h7 | ⟨s, hhs, _, hexp⟩
  · exact not_thm7Excuse_of_noCompromise trExpSpqrB_noCompromise h7
  · have hmem := hs_mem trExpSpqrB_sessions hhs
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, and_true] at hmem
    rcases hmem with ⟨_, hj⟩ | rfl
    · exact absurd hj (by decide)
    · rcases hexp with ⟨_, _, _, hx⟩ | ⟨_, _, _, hx⟩ | ⟨_, _, _, hx⟩ | ⟨_, _, hx⟩ <;>
        exact no_ev trExpSpqrB_noExposureNotBob hx rfl

/-- Restricting `SessionStateExposed` to the queried handshake index `j = i` falsifies
`BobResponderSecrecy`. -/
theorem not_InitiatorSecrecy_sameHandshake : ¬ InitiatorSecrecy_sameHandshake := by
  intro h
  rcases h trExpCkrA trExpCkrA_reach "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
    (kemPk pqskB) none o1.ek o1.ct keys1 47 trExpCkrA_bobDone_at keys1.ck
    (Or.inr (Or.inl rfl)) trExpCkrA_knows_ck with h9 | ⟨s, hhs, _, hexp⟩
  · exact not_thm9Excuse_of_noCompromise trExpCkrA_noCompromise h9
  · have hmem := hs_mem trExpCkrA_sessions hhs
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, and_true] at hmem
    rcases hmem with rfl | ⟨_, hj⟩
    · rcases hexp with ⟨_, _, _, hx⟩ | ⟨_, _, _, hx⟩ | ⟨_, _, _, hx⟩ | ⟨_, _, hx⟩ <;>
        exact no_ev trExpCkrA_noExposureNotAlice hx rfl
    · exact absurd hj (by decide)

/-! ## Redundancy of `ExposedCKs` and `ExposedRK` on handshake keys -/

/-- No reachable trace logs `ExposedCKs` for the initial handshake chain key `keys.ck` of a
`HandshakeSession`. -/
theorem exposedCKs_handshakeCk_dead : ∀ tr : ExecTrace, tr.Reachable reachability →
    ¬ ∃ s j keys n r, tr.EventLogged (ComposedEvent.HandshakeSession s j) ∧ HandshakeKeysAt tr j keys ∧
      tr.EventLogged (TREvent.ExposedCKs s keys.ck n r) :=
  exposedCKs_handshakeCk_dead_shared

/-- No reachable trace logs `ExposedRK` for the initial handshake root key `keys.rk` of a
`HandshakeSession`. -/
theorem exposedRK_handshakeRk_dead : ∀ tr : ExecTrace, tr.Reachable reachability →
    ¬ ∃ s j keys r, tr.EventLogged (ComposedEvent.HandshakeSession s j) ∧ HandshakeKeysAt tr j keys ∧
      tr.EventLogged (TREvent.ExposedRK s keys.rk r) :=
  exposedRK_handshakeRk_dead_shared

theorem sessionStateExposed_withoutCks_of_real (tr : ExecTrace) (hR : tr.Reachable reachability)
    (keys : HandshakeKeys) (k : Bytes) (h : SessionStateExposed tr keys k) :
    SessionStateExposed_withoutCks tr keys k := by
  obtain ⟨s, j, hS, hK, hp | hckr | ⟨_, n, r, hcks⟩ | hrk⟩ := h
  · exact ⟨s, j, hS, hK, Or.inl hp⟩
  · exact ⟨s, j, hS, hK, Or.inr (Or.inl hckr)⟩
  · exact (exposedCKs_handshakeCk_dead tr hR ⟨s, j, keys, n, r, hS, hK, hcks⟩).elim
  · exact ⟨s, j, hS, hK, Or.inr (Or.inr hrk)⟩

theorem sessionStateExposed_withoutCks_iff (tr : ExecTrace) (hR : tr.Reachable reachability)
    (keys : HandshakeKeys) (k : Bytes) :
    SessionStateExposed_withoutCks tr keys k ↔ SessionStateExposed tr keys k :=
  ⟨fun h => (sessionStateExposed_withoutCks_iff_real tr keys k).mpr (Or.inr h),
   sessionStateExposed_withoutCks_of_real tr hR keys k⟩

theorem sessionStateExposed_withoutRk_of_real (tr : ExecTrace) (hR : tr.Reachable reachability)
    (keys : HandshakeKeys) (k : Bytes) (h : SessionStateExposed tr keys k) :
    SessionStateExposed_withoutRk tr keys k := by
  obtain ⟨s, j, hS, hK, hp | hckr | hcks | ⟨_, r, hrk⟩⟩ := h
  · exact ⟨s, j, hS, hK, Or.inl hp⟩
  · exact ⟨s, j, hS, hK, Or.inr (Or.inl hckr)⟩
  · exact ⟨s, j, hS, hK, Or.inr (Or.inr hcks)⟩
  · exact (exposedRK_handshakeRk_dead tr hR ⟨s, j, keys, r, hS, hK, hrk⟩).elim

theorem sessionStateExposed_withoutRk_iff (tr : ExecTrace) (hR : tr.Reachable reachability)
    (keys : HandshakeKeys) (k : Bytes) :
    SessionStateExposed_withoutRk tr keys k ↔ SessionStateExposed tr keys k :=
  ⟨fun h => (sessionStateExposed_withoutRk_iff_real tr keys k).mpr (Or.inr h),
   sessionStateExposed_withoutRk_of_real tr hR keys k⟩

theorem responderSecrecy_withoutCks_of_real (h : AliceInitiatorSecrecy) : ResponderSecrecy_withoutCks :=
  ResponderSecrecyWith.mono sessionStateExposed_withoutCks_of_real h

theorem responderSecrecy_withoutCks_iff : ResponderSecrecy_withoutCks ↔ AliceInitiatorSecrecy :=
  ⟨ResponderSecrecyWith.mono fun tr hR keys k h =>
    (sessionStateExposed_withoutCks_iff tr hR keys k).mp h,
   responderSecrecy_withoutCks_of_real⟩

theorem initiatorSecrecy_withoutCks_of_real (h : BobResponderSecrecy) : InitiatorSecrecy_withoutCks :=
  InitiatorSecrecyWith.mono sessionStateExposed_withoutCks_of_real h

theorem initiatorSecrecy_withoutCks_iff : InitiatorSecrecy_withoutCks ↔ BobResponderSecrecy :=
  ⟨InitiatorSecrecyWith.mono fun tr hR keys k h =>
    (sessionStateExposed_withoutCks_iff tr hR keys k).mp h,
   initiatorSecrecy_withoutCks_of_real⟩

theorem responderSecrecy_withoutRk_of_real (h : AliceInitiatorSecrecy) : ResponderSecrecy_withoutRk :=
  ResponderSecrecyWith.mono sessionStateExposed_withoutRk_of_real h

theorem responderSecrecy_withoutRk_iff : ResponderSecrecy_withoutRk ↔ AliceInitiatorSecrecy :=
  ⟨ResponderSecrecyWith.mono fun tr hR keys k h =>
    (sessionStateExposed_withoutRk_iff tr hR keys k).mp h,
   responderSecrecy_withoutRk_of_real⟩

theorem initiatorSecrecy_withoutRk_of_real (h : BobResponderSecrecy) : InitiatorSecrecy_withoutRk :=
  InitiatorSecrecyWith.mono sessionStateExposed_withoutRk_of_real h

theorem initiatorSecrecy_withoutRk_iff : InitiatorSecrecy_withoutRk ↔ BobResponderSecrecy :=
  ⟨InitiatorSecrecyWith.mono fun tr hR keys k h =>
    (sessionStateExposed_withoutRk_iff tr hR keys k).mp h,
   initiatorSecrecy_withoutRk_of_real⟩

end Symbolic.Proofs.Tests.Model.ExplanationTightness.Handshake
