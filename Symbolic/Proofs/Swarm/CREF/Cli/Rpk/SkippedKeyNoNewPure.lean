/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public meta import Mathlib.Tactic.ToAdditive
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

cref_hide_foreign_instances

/-!
# Computations Without New `SkippedKeyStored` Events

Defines `NoNewSk` for traceful computations that log no new `TREvent.SkippedKeyStored`
events and proves closure under monadic combinators and protocol actions.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure.RpkCli.Skr

open Symbolic.Swarm.CREF.TR

cref_open
open DY.DiffieHellman
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir)
open DY.Libsignal.TripleRatchet
open Symbolic.Swarm.CREF.TR.RecvDec
  (at?_append_of_lt at?_eq_none_of_le at?_append_non_entry
   logSkippedKeysTr logSkippedKeysTr_length
   at?_trEntry_logSkippedKeysTr_lt at?_trEntry_logSkippedKeysTr_add
   at?_trEntry_logSkippedKeysTr_exists at?_stEntry_logSkippedKeysTr
   decTailTr getLocalState_snd decrypt_next_noRatchet_eq)

abbrev StEntry :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
abbrev TREntry := DY.ProtocolEvent.ExecEntryT TREvent
private abbrev PQStEntry :=
  PersistentGlobalState.State.ExecEntryT
    (PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)
private abbrev PQEvEntry :=
  DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent
private abbrev CEvEntry :=
  DY.ProtocolEvent.ExecEntryT DY.Libsignal.Composed.ComposedEvent

/-! ## Trace event helpers -/

private theorem eventLoggedAt_append_trEntry_iff (tr : ExecTrace) (ev₀ ev : TREvent) (i : Nat) :
    (tr.append (⟨ev₀⟩ : TREntry)).EventLoggedAt ev i ↔
      tr.EventLoggedAt ev i ∨ (i = tr.length ∧ ev = ev₀) := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  by_cases hlt : i < tr.length
  · rw [at?_append_of_lt tr (⟨ev₀⟩ : TREntry) hlt]
    exact ⟨Or.inl, fun h => h.elim id (fun ⟨heq, _⟩ => absurd heq (Nat.ne_of_lt hlt))⟩
  · by_cases heq : i = tr.length
    · subst heq
      rw [Trace.at?_append]
      constructor
      · intro h; injection h with h; injection h with h; exact Or.inr ⟨rfl, h.symm⟩
      · rintro (h | ⟨_, rfl⟩)
        · rw [at?_eq_none_of_le tr (Nat.le_refl _)] at h; cases h
        · rfl
    · rw [at?_eq_none_of_le (tr.append (⟨ev₀⟩ : TREntry))
            (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
                  Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
          at?_eq_none_of_le tr (by omega)]
      constructor
      · intro h; cases h
      · rintro (h | ⟨h, _⟩)
        · cases h
        · exact absurd h heq

theorem eventLoggedAt_append_trEntry_ne (tr : ExecTrace) (ev₀ ev : TREvent)
    (hne : ev ≠ ev₀) (i : Nat) :
    (tr.append (⟨ev₀⟩ : TREntry)).EventLoggedAt ev i → tr.EventLoggedAt ev i := by
  intro h
  rcases (eventLoggedAt_append_trEntry_iff tr ev₀ ev i).mp h with h1 | ⟨_, heq⟩
  · exact h1
  · exact absurd heq hne

theorem eventLoggedAt_logSkippedKeysTr_iff (s : SessionInfo) (pk : DY.Bytes)
    (rIdx sourceStateIdx : Nat) (ck : DY.Bytes) (n₀ : UInt32) (k : Nat)
    (tr : ExecTrace) (ev : TREvent) (i : Nat) :
    (logSkippedKeysTr s pk rIdx sourceStateIdx ck n₀ k tr).EventLoggedAt ev i →
      tr.EventLoggedAt ev i ∨
        ∃ n' seed', ev = TREvent.SkippedKeyStored s pk n' seed' rIdx sourceStateIdx := by
  intro hev
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev ⊢
  by_cases hlt : i < tr.length
  · left
    rw [at?_trEntry_logSkippedKeysTr_lt s pk rIdx sourceStateIdx ck n₀ k tr hlt] at hev
    exact hev
  · by_cases hhi : i < tr.length + k
    · right
      obtain ⟨n', seed', hat⟩ := at?_trEntry_logSkippedKeysTr_exists
        s pk rIdx sourceStateIdx ck n₀ k tr (by omega) hhi
      rw [hat] at hev
      injection hev with hev_eq
      injection hev_eq with hev_eq
      exact ⟨n', seed', hev_eq.symm⟩
    · have hlen := logSkippedKeysTr_length s pk rIdx sourceStateIdx ck n₀ k tr
      rw [at?_eq_none_of_le _ (by omega)] at hev
      cases hev

/-! ## Closure of `NoNewSk` -/

/-- `x` logs no new `TREvent.SkippedKeyStored` event: any such event on the
post-trace was already at the same index on the pre-trace. -/
def NoNewSk {α : Type} (x : Traceful α) : Prop :=
  ∀ (tr : ExecTrace) (s : SessionInfo) (pk : DY.Bytes) (n : UInt32)
    (seed : DY.Bytes) (rIdx src i : Nat),
    ((x.run tr).2.val).EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i →
    tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i

theorem NoNewSk.of_id {α : Type} {x : Traceful α}
    (h : ∀ tr, (x.run tr).2.val = tr) : NoNewSk x := by
  intro tr s pk n seed rIdx src i hev; rw [h tr] at hev; exact hev

theorem NoNewSk.pure {α : Type} (a : α) : NoNewSk (Pure.pure a : Traceful α) :=
  NoNewSk.of_id fun _ => by simp only [DY.Traceful.run_pure]

theorem NoNewSk.failure {α : Type} : NoNewSk (Alternative.failure : Traceful α) :=
  NoNewSk.of_id fun _ => by simp only [DY.Traceful.run_failure]

theorem NoNewSk.getEntry {E : Type} [ExecTraceTypes.Has E] (i : Nat) :
    NoNewSk (DY.getEntry i : Traceful E) :=
  NoNewSk.of_id fun _ => by simp only [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]

theorem NoNewSk.getLocalState (p : Participant) (h : Nat) :
    NoNewSk (PersistentLocalState.getLocalState p h : Traceful TRState) :=
  NoNewSk.of_id (getLocalState_snd p h)

theorem NoNewSk.receiveMessage (h : Nat) :
    NoNewSk (Network.receiveMessage h) := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact NoNewSk.of_id fun tr => by
    simp only [Traceful.run_bind, Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk, DY.Traceful.run_pure]
    split <;> rfl

theorem NoNewSk.guardP (p : Prop) [Decidable p] :
    NoNewSk (_root_.guard p : Traceful Unit) := by
  unfold _root_.guard; split
  · exact NoNewSk.pure _
  · exact NoNewSk.failure

theorem NoNewSk.guardTrace (p : ExecTrace → Bool) :
    NoNewSk (TripleRatchet.guardTrace p) :=
  NoNewSk.of_id fun _ => by simp only [TripleRatchet.guardTrace, DY.Traceful.run_mk]

theorem NoNewSk.requireTracePredicate (p : ExecTrace → Bool) :
    NoNewSk (DY.Libsignal.PQXDH.guardTrace p) :=
  NoNewSk.of_id fun _ => by simp only [DY.Libsignal.PQXDH.guardTrace, DY.Traceful.run_mk]

theorem NoNewSk.monadLiftErr {α : Type} (x : Err α) :
    NoNewSk (monadLift x : Traceful α) :=
  NoNewSk.of_id fun _ => by
    cases x <;> simp only [monadLift, MonadLift.monadLift, DY.Traceful.run_mk]

theorem NoNewSk.traceLength : NoNewSk TripleRatchet.traceLength :=
  NoNewSk.of_id fun _ => by simp only [TripleRatchet.traceLength, DY.Traceful.run_mk]

theorem NoNewSk.bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : NoNewSk x) (hf : ∀ a, NoNewSk (f a)) :
    NoNewSk (x >>= f) := by
  intro tr s pk n seed rIdx src i hev
  have h1 := hx tr s pk n seed rIdx src i
  rw [Traceful.run_bind] at hev
  rcases h : x.run tr with ⟨_ | a, trMid, _⟩
  · rw [h] at hev h1; exact h1 hev
  · rw [h] at hev h1; exact h1 (hf a trMid s pk n seed rIdx src i hev)

theorem NoNewSk.prodCasesOn {α β γ : Type} (p : α × β) (f : α → β → Traceful γ)
    (hf : ∀ a b, NoNewSk (f a b)) :
    NoNewSk (Prod.casesOn p f) := by
  rcases p with ⟨a, b⟩; exact hf a b

theorem NoNewSk.optionCasesOn {α β : Type} (o : Option α)
    (noneCase : Traceful β) (someCase : α → Traceful β)
    (hn : NoNewSk noneCase) (hs : ∀ a, NoNewSk (someCase a)) :
    NoNewSk (Option.casesOn o noneCase someCase) := by
  rcases o with _ | a
  · exact hn
  · exact hs a

theorem NoNewSk.getLocalStatePQ (p : Participant) (h : Nat) :
    NoNewSk (PersistentLocalState.getLocalState p h :
      Traceful DY.Libsignal.PQXDH.PQXDHState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine NoNewSk.bind (NoNewSk.bind (NoNewSk.getEntry h) fun _ => NoNewSk.pure _) fun _ => ?_
  exact NoNewSk.bind (NoNewSk.guardP _) fun _ => NoNewSk.pure _

theorem NoNewSk.getKey (p : Participant) (h : Nat)
    (kind : DY.Libsignal.PQXDH.KeyKind) :
    NoNewSk (DY.Libsignal.PQXDH.getKey p h kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  refine NoNewSk.bind (NoNewSk.getLocalStatePQ p h) fun _ => ?_
  exact NoNewSk.bind (NoNewSk.guardP _) fun _ => NoNewSk.pure _

theorem NoNewSk.lookupIdentity (p : Participant) (h : Nat) :
    NoNewSk (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine NoNewSk.bind (NoNewSk.getEntry h) fun _ => ?_
  split
  · exact NoNewSk.bind (NoNewSk.guardP _) fun _ => NoNewSk.pure _
  · exact NoNewSk.failure

theorem NoNewSk.genRand (n : Nat) :
    NoNewSk (Random.genRand n : Traceful DY.Bytes) := by
  intro tr _ _ _ _ _ _ i hev
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure,
    Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev ⊢
  rwa [at?_append_non_entry tr (⟨n⟩ : Random.ExecEntryT) rfl i] at hev

theorem NoNewSk.sendMessage (m : DY.Bytes) :
    NoNewSk (Network.sendMessage m) := by
  intro tr _ _ _ _ _ _ i hev
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk,
    Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev ⊢
  rwa [at?_append_non_entry tr (⟨m⟩ : Network.ExecEntryT) rfl i] at hev

theorem NoNewSk.storeLocalState (p : Participant) (st : TRState) :
    NoNewSk (PersistentLocalState.storeLocalState p st) := by
  intro tr _ _ _ _ _ _ i hev
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk,
    Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev ⊢
  rwa [at?_append_non_entry tr (⟨⟨p, st⟩⟩ : StEntry) rfl i] at hev

theorem NoNewSk.storeLocalStatePQ (p : Participant)
    (st : DY.Libsignal.PQXDH.PQXDHState) :
    NoNewSk (PersistentLocalState.storeLocalState p st) := by
  intro tr _ _ _ _ _ _ i hev
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk,
    Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev ⊢
  rwa [at?_append_non_entry tr (⟨⟨p, st⟩⟩ : PQStEntry) rfl i] at hev

theorem NoNewSk.logEventPQ (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    NoNewSk (DY.ProtocolEvent.logEvent ev) := by
  intro tr _ _ _ _ _ _ i hev
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure,
    Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev ⊢
  rwa [at?_append_non_entry tr (⟨ev⟩ : PQEvEntry) rfl i] at hev

theorem NoNewSk.logEventC (ev : DY.Libsignal.Composed.ComposedEvent) :
    NoNewSk (DY.ProtocolEvent.logEvent ev) := by
  intro tr _ _ _ _ _ _ i hev
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure,
    Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev ⊢
  rwa [at?_append_non_entry tr (⟨ev⟩ : CEvEntry) rfl i] at hev

@[reducible] def isSkippedKeyStored : TREvent → Bool
  | .SkippedKeyStored _ _ _ _ _ _ => true
  | _ => false

private theorem ne_skippedKeyStored_of_eq_false {ev : TREvent}
    (h : isSkippedKeyStored ev = false) :
    ∀ s pk n seed rIdx src, ev ≠ TREvent.SkippedKeyStored s pk n seed rIdx src := by
  rintro s pk n seed rIdx src rfl; cases h

theorem NoNewSk.logEvent (ev : TREvent)
    (hne : isSkippedKeyStored ev = false) :
    NoNewSk (DY.ProtocolEvent.logEvent ev) := by
  intro tr s pk n seed rIdx src i hev
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure] at hev
  exact eventLoggedAt_append_trEntry_ne tr ev _
    (Ne.symm (ne_skippedKeyStored_of_eq_false hne s pk n seed rIdx src)) i hev

theorem NoNewSk.logMessageKeyAndStore (me : Participant)
    (s : SessionInfo) (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32)
    (r par : Nat) (st : TRState) :
    NoNewSk (TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) := by
  unfold TripleRatchet.logMessageKeyAndStore
  exact NoNewSk.bind (NoNewSk.logEvent _ (by rfl)) fun _ =>
    NoNewSk.storeLocalState _ _

theorem NoNewSk.receiveSignalMsg (msgIdx : Nat) :
    NoNewSk (TripleRatchet.receiveSignalMsg msgIdx) := by
  unfold TripleRatchet.receiveSignalMsg
  refine NoNewSk.bind (NoNewSk.receiveMessage msgIdx) fun _ => ?_
  split
  · exact NoNewSk.bind (NoNewSk.guardP _) fun _ => NoNewSk.pure _
  · exact NoNewSk.failure

theorem NoNewSk.verifyMacAndDecrypt (st : TRState)
    (msg : TRSignalMsg) (pqSalt seed : DY.Bytes) :
    NoNewSk (TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold TripleRatchet.verifyMacAndDecrypt
  exact NoNewSk.bind (NoNewSk.guardP _) fun _ => NoNewSk.monadLiftErr _

theorem NoNewSk.dhRatchetStep (st : TRState) (pk : DY.Bytes) :
    NoNewSk (TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact NoNewSk.bind (NoNewSk.guardP _) fun _ =>
    NoNewSk.bind (NoNewSk.genRand 32) fun _ =>
      NoNewSk.pure _

theorem NoNewSk.ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    NoNewSk (TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact NoNewSk.pure _
  · exact NoNewSk.bind (NoNewSk.dhRatchetStep st pk) fun _ => NoNewSk.pure _
  · exact NoNewSk.failure

macro "tr_nosk" : tactic => `(tactic| repeat (first
  | with_reducible apply NoNewSk.bind
  | with_reducible apply NoNewSk.prodCasesOn
  | with_reducible apply NoNewSk.optionCasesOn
  | with_reducible apply NoNewSk.pure | with_reducible apply NoNewSk.failure
  | with_reducible apply NoNewSk.genRand
  | with_reducible apply NoNewSk.storeLocalState
  | with_reducible apply NoNewSk.storeLocalStatePQ
  | with_reducible apply NoNewSk.sendMessage
  | with_reducible apply NoNewSk.getLocalState
  | with_reducible apply NoNewSk.getLocalStatePQ
  | with_reducible apply NoNewSk.getKey
  | with_reducible apply NoNewSk.lookupIdentity
  | with_reducible apply NoNewSk.receiveMessage
  | with_reducible apply NoNewSk.getEntry
  | with_reducible apply NoNewSk.receiveSignalMsg
  | with_reducible apply NoNewSk.verifyMacAndDecrypt
  | with_reducible apply NoNewSk.dhRatchetStep
  | with_reducible apply NoNewSk.ensureReceiverChain
  | with_reducible apply NoNewSk.guardP | with_reducible apply NoNewSk.monadLiftErr
  | with_reducible apply NoNewSk.guardTrace | with_reducible apply NoNewSk.requireTracePredicate
  | with_reducible apply NoNewSk.traceLength
  | with_reducible apply NoNewSk.logMessageKeyAndStore
  | with_reducible apply NoNewSk.logEventPQ
  | with_reducible apply NoNewSk.logEventC
  | with_reducible apply NoNewSk.logEvent _ (by rfl)
  | split | with_reducible intro))

theorem NoNewSk.registerIdentity (p : Participant) :
    NoNewSk (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity; tr_nosk

theorem NoNewSk.genSignedPrekey (b : Participant) (j : Nat) :
    NoNewSk (DY.Libsignal.PQXDH.genSignedPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey; tr_nosk

theorem NoNewSk.genPQPrekey (b : Participant) (j : Nat) :
    NoNewSk (DY.Libsignal.PQXDH.genPQPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey; tr_nosk

theorem NoNewSk.genOneTimePrekey (b : Participant) :
    NoNewSk (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey; tr_nosk

theorem NoNewSk.setupAct (a b : Participant) (withOpk : Bool) :
    NoNewSk (DY.Libsignal.Composed.Refinement.setupAct a b withOpk) := by
  unfold DY.Libsignal.Composed.Refinement.setupAct
  with_reducible apply NoNewSk.bind
  · exact NoNewSk.registerIdentity a
  · intro _
    with_reducible apply NoNewSk.bind
    · exact NoNewSk.registerIdentity b
    · intro hB
      with_reducible apply NoNewSk.bind
      · exact NoNewSk.genSignedPrekey b hB
      · intro _
        with_reducible apply NoNewSk.bind
        · exact NoNewSk.genPQPrekey b hB
        · intro _
          cases withOpk
          · exact NoNewSk.pure _
          · change NoNewSk (do let _ ← PQXDH.genOneTimePrekey b; Pure.pure ())
            with_reducible apply NoNewSk.bind
            · exact NoNewSk.genOneTimePrekey b
            · intro _; exact NoNewSk.pure _

theorem NoNewSk.aliceHandshake (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    NoNewSk (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake; tr_nosk

theorem NoNewSk.aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    NoNewSk (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  with_reducible apply NoNewSk.bind
  · exact NoNewSk.aliceHandshake a b idStateIdx regIdxB h
  · intro _; tr_nosk

theorem NoNewSk.bobHandshake (b a : Participant)
    (h : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    NoNewSk (DY.Libsignal.PQXDH.bobHandshake b a h regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake; tr_nosk

theorem NoNewSk.compromiseIK (p : Participant) (j : Nat) :
    NoNewSk (DY.Libsignal.PQXDH.compromiseIK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseIK; tr_nosk

theorem NoNewSk.compromiseSPK (p : Participant) (j : Nat) :
    NoNewSk (DY.Libsignal.PQXDH.compromiseSPK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK; tr_nosk

theorem NoNewSk.compromisePQSPK (p : Participant) (j : Nat) :
    NoNewSk (DY.Libsignal.PQXDH.compromisePQSPK p j) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK; tr_nosk

theorem NoNewSk.compromiseOPK (p : Participant) (j : Nat) :
    NoNewSk (DY.Libsignal.PQXDH.compromiseOPK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK; tr_nosk

end Symbolic.Swarm.CREF.CliPure.RpkCli.Skr
