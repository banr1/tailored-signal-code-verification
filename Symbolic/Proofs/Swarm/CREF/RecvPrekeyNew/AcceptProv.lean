/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Mathlib.Data.List.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.Prelude
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

/-!
# Key and Identity Provenance in Composed Pre-Key Runs

Proves that non-`setup` moves preserve the `PQXDHState` projection and `IdentityRegistered` events
of `setupTrace r`, so Bob's identity, signed, PQ, and one-time pre-key secrets and Alice's
registered identity key on `runTraceMoves r ms` equal the setup values.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open Symbolic.Swarm.CREF.TR (StE EvE NetE)
open DY.Libsignal.TripleRatchet (SessionInfo)
open DY.Libsignal.TripleRatchet

private abbrev PQStEntry :=
  PersistentGlobalState.State.ExecEntryT
    (PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)
private abbrev TREntryP := DY.ProtocolEvent.ExecEntryT TREvent
private abbrev StEntryP :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
private abbrev PQEvEntryP :=
  DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent
private abbrev CEvEntryP :=
  DY.ProtocolEvent.ExecEntryT DY.Libsignal.Composed.ComposedEvent

/-! ## Setup Trace Helpers -/

private theorem rpkP_at?_eq_none_of_le {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) {i : Nat} (h : tr.length ≤ i) :
    (tr.at? i : Option E) = none := by
  have hlt : ¬ i < tr.length := Nat.not_lt.mpr h
  simp [Trace.at?, hlt]

private theorem rpkP_at?_append_non_entry {E1 E2 : Type} [ExecTraceTypes.Has E1]
    [ExecTraceTypes.Has E2] (tr : ExecTrace) (e : E1)
    (hproj : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = none)
    (i : Nat) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  by_cases hlt : i < tr.length
  · exact TR.at?_append_of_lt tr e hlt
  · by_cases heq : i = tr.length
    · rw [TR.at?_append_eq_of_proj tr e heq none hproj,
        rpkP_at?_eq_none_of_le tr (Nat.le_of_eq heq.symm)]
    · have hge1 : tr.length ≤ i := Nat.le_of_not_lt hlt
      have hge2 : (tr.append e).length ≤ i := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
      rw [rpkP_at?_eq_none_of_le (tr.append e) hge2, rpkP_at?_eq_none_of_le tr hge1]

private abbrev rpkP_sent (tr : ExecTrace) : List DY.Bytes :=
  List.filterMap (fun x => Trace.getMessageSentAt x tr) (newIndices Trace.nil tr)

private theorem rpkP_newSent_append_aux {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) :
    rpkP_sent (tr.append e) =
      rpkP_sent tr ++
        (((tr.append e).at? tr.length : Option DY.Network.ExecEntryT).map (·.msg)).toList := by
  have hlen0 : (Trace.nil : ExecTrace).length = 0 := Symbolic.DYBridge.DY.Trace.length_eq_1
  have hcongr :
      List.filterMap (fun i => Trace.getMessageSentAt i (tr.append e)) (newIndices Trace.nil tr) =
      rpkP_sent tr := by
    unfold rpkP_sent
    refine List.filterMap_congr fun i hi => ?_
    have hlt : i < tr.length := by
      simp only [newIndices, hlen0, Nat.sub_zero, List.mem_range'_1] at hi
      omega
    simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
    rw [TR.at?_append_of_lt tr e hlt]
  conv_lhs => unfold rpkP_sent
  rw [TR.newIndices_nil_append, List.filterMap_append, hcongr, List.filterMap_cons, List.filterMap_nil]
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  cases ((tr.append e).at? tr.length : Option DY.Network.ExecEntryT) <;> rfl

private theorem rpkP_newSent_append_net (tr : ExecTrace) (b : DY.Bytes) :
    rpkP_sent (tr.append (NetE b)) = rpkP_sent tr ++ [b] := by
  rw [rpkP_newSent_append_aux, TR.at?_append_self]
  rfl

private theorem rpkP_newSent_append_nonNet {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hproj : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Network.ExecEntryT) = none) :
    rpkP_sent (tr.append e) = rpkP_sent tr := by
  rw [rpkP_newSent_append_aux, TR.at?_append_eq_of_proj tr e rfl none hproj]
  simp

private theorem rpkP_newSent_setupTr1 (a : Participant) :
    rpkP_sent (TR.setupTr1 a) =
      [DY.DiffieHellman.dhPk (randTerm 0 32), DY.Signature.vk (randTerm 0 32)] := by
  unfold TR.setupTr1
  rw [rpkP_newSent_append_nonNet _ _ rfl,
    rpkP_newSent_append_net, rpkP_newSent_append_net,
    rpkP_newSent_append_nonNet _ _ rfl, rpkP_newSent_append_nonNet _ _ rfl]
  unfold rpkP_sent newIndices
  simp [Symbolic.DYBridge.DY.Trace.length_eq_1]

private theorem rpkP_newSent_setupTr2 (a b : Participant) :
    rpkP_sent (TR.setupTr2 a b) =
      [DY.DiffieHellman.dhPk (randTerm 0 32), DY.Signature.vk (randTerm 0 32),
       DY.DiffieHellman.dhPk (randTerm 5 32), DY.Signature.vk (randTerm 5 32)] := by
  unfold TR.setupTr2
  rw [rpkP_newSent_append_nonNet _ _ rfl,
    rpkP_newSent_append_net, rpkP_newSent_append_net,
    rpkP_newSent_append_nonNet _ _ rfl, rpkP_newSent_append_nonNet _ _ rfl,
    rpkP_newSent_setupTr1]
  rfl

private theorem rpkP_newSent_setupTr3 (a b : Participant) :
    rpkP_sent (TR.setupTr3 a b) =
      rpkP_sent (TR.setupTr2 a b) ++
        [DY.DiffieHellman.dhPk (randTerm 10 32),
         DY.Signature.sign (randTerm 5 32) (randTerm 11 64)
           (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk (randTerm 10 32)))] := by
  unfold TR.setupTr3
  rw [rpkP_newSent_append_net, rpkP_newSent_append_net,
    rpkP_newSent_append_nonNet _ _ rfl, rpkP_newSent_append_nonNet _ _ rfl,
    rpkP_newSent_append_nonNet _ _ rfl, rpkP_newSent_append_nonNet _ _ rfl]
  simp [List.append_assoc]

private theorem rpkP_newSent_setupTr4 (a b : Participant) :
    rpkP_sent (TR.setupTr4 a b) =
      rpkP_sent (TR.setupTr3 a b) ++
        [DY.PQKem.kemPk (randTerm 16 64),
         DY.Signature.sign (randTerm 5 32) (randTerm 17 64)
           (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk (randTerm 16 64)))] := by
  unfold TR.setupTr4
  rw [rpkP_newSent_append_net, rpkP_newSent_append_net,
    rpkP_newSent_append_nonNet _ _ rfl, rpkP_newSent_append_nonNet _ _ rfl,
    rpkP_newSent_append_nonNet _ _ rfl, rpkP_newSent_append_nonNet _ _ rfl]
  simp [List.append_assoc]

private theorem rpkP_newSent_setupTr5 (a b : Participant) :
    rpkP_sent (TR.setupTr5 a b) =
      rpkP_sent (TR.setupTr4 a b) ++ [DY.DiffieHellman.dhPk (randTerm 22 32)] := by
  unfold TR.setupTr5
  rw [rpkP_newSent_append_net, rpkP_newSent_append_nonNet _ _ rfl,
    rpkP_newSent_append_nonNet _ _ rfl, rpkP_newSent_append_nonNet _ _ rfl]

private theorem rpkP_setupSecret_eq (r : ProtocolSetup) (hne : r.alice ≠ r.bob) :
    setupSecret r 0 = randTerm 0 32 ∧
    setupSecret r 1 = randTerm 5 32 ∧
    setupSecret r 2 = randTerm 10 32 ∧
    setupSecret r 4 = randTerm 16 64 ∧
    (r.withOpk = true → setupSecret r 6 = randTerm 22 32) := by
  simp only [setupSecret, TR.setupRandoms_eq r hne]
  cases r.withOpk <;> simp

private theorem rpkP_setupPublic_eq (r : ProtocolSetup) (hne : r.alice ≠ r.bob) :
    setupPublic r 0 = DY.DiffieHellman.dhPk (randTerm 0 32) ∧
    setupPublic r 2 = DY.DiffieHellman.dhPk (randTerm 5 32) := by
  change (rpkP_sent (setupTrace r))[0]?.getD (randTerm 0 0) =
      DY.DiffieHellman.dhPk (randTerm 0 32) ∧
    (rpkP_sent (setupTrace r))[2]?.getD (randTerm 0 0) =
      DY.DiffieHellman.dhPk (randTerm 5 32)
  rw [TR.setupTrace_eq r hne]
  cases r.withOpk <;>
    simp [rpkP_newSent_setupTr5, rpkP_newSent_setupTr4, rpkP_newSent_setupTr3,
      rpkP_newSent_setupTr2]

/-! ## `PQFrame` and `NoPQ` -/

private def PQFrame (t t' : ExecTrace) : Prop :=
  (∀ i : Nat, (t'.at? i : Option PQStEntry) = (t.at? i : Option PQStEntry)) ∧
  (∀ (i : Nat) (p : Participant) (pk vk : DY.Bytes) (hh : Bool),
    (t'.at? i : Option PQEvEntryP) = some (EvE (.IdentityRegistered p pk vk hh)) →
    (t.at? i : Option PQEvEntryP) = some (EvE (.IdentityRegistered p pk vk hh)))

private theorem PQFrame.refl (t : ExecTrace) : PQFrame t t :=
  ⟨fun _ => rfl, fun _ _ _ _ _ h => h⟩

private theorem PQFrame.trans {t₁ t₂ t₃ : ExecTrace} (h₁ : PQFrame t₁ t₂) (h₂ : PQFrame t₂ t₃) :
    PQFrame t₁ t₃ :=
  ⟨fun i => (h₂.1 i).trans (h₁.1 i), fun i p pk vk hh h => h₁.2 i p pk vk hh (h₂.2 i p pk vk hh h)⟩

private theorem rpkP_at?_append_cases {E1 E2 : Type} [ExecTraceTypes.Has E1]
    [ExecTraceTypes.Has E2] {tr : ExecTrace} {e : E1} {x : E2} {i : Nat}
    (h : ((tr.append e).at? i : Option E2) = some x) :
    (tr.at? i : Option E2) = some x ∨
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = some x := by
  by_cases hlt : i < tr.length
  · left; rwa [TR.at?_append_of_lt (E2 := E2) tr e hlt] at h
  · by_cases heq : i = tr.length
    · right; rwa [TR.at?_append_eq_of_proj (E2 := E2) tr e heq _ rfl] at h
    · rw [rpkP_at?_eq_none_of_le (E := E2) (tr.append e)
        (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)] at h
      cases h

private theorem PQFrame.append {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (hst : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option PQStEntry) = none)
    (hev : ∀ (p : Participant) (pk vk : DY.Bytes) (hh : Bool),
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option PQEvEntryP) ≠
        some (EvE (.IdentityRegistered p pk vk hh))) :
    PQFrame tr (tr.append e) := by
  refine ⟨fun i => rpkP_at?_append_non_entry tr e hst i, fun i p pk vk hh h => ?_⟩
  rcases rpkP_at?_append_cases h with h1 | h2
  · exact h1
  · exact absurd h2 (hev p pk vk hh)

@[reducible] private def isIdRegEv : DY.Libsignal.PQXDH.PQXDHEvent → Bool
  | .IdentityRegistered _ _ _ _ => true
  | _ => false

private def NoPQ {α : Type} (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, PQFrame tr (x.run tr).2.val

private theorem NoPQ.of_id {α : Type} {x : Traceful α}
    (h : ∀ tr, (x.run tr).2.val = tr) : NoPQ x := by
  intro tr; rw [h tr]; exact PQFrame.refl tr

private theorem NoPQ.pure {α : Type} (a : α) : NoPQ (Pure.pure a : Traceful α) :=
  NoPQ.of_id fun _ => by rw [DY.Traceful.run_pure]

private theorem NoPQ.failure {α : Type} : NoPQ (Alternative.failure : Traceful α) :=
  NoPQ.of_id fun _ => by rw [DY.Traceful.run_failure]

private theorem NoPQ.getEntry {E : Type} [ExecTraceTypes.Has E] (i : Nat) :
    NoPQ (DY.getEntry i : Traceful E) :=
  NoPQ.of_id fun _ => by rw [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]

private theorem NoPQ.getLocalState (p : Participant) (h : Nat) :
    NoPQ (PersistentLocalState.getLocalState p h : Traceful TRState) :=
  NoPQ.of_id (Symbolic.Swarm.COMPOSED.CompTrace.getLocalState_tr_snd p h)

private theorem NoPQ.receiveMessage (h : Nat) :
    NoPQ (Network.receiveMessage h) :=
  NoPQ.of_id (Symbolic.Swarm.COMPOSED.CompTrace.receiveMessage_snd h)

private theorem NoPQ.guardP (p : Prop) [Decidable p] :
    NoPQ (_root_.guard p : Traceful Unit) := by
  unfold _root_.guard; split
  · exact NoPQ.pure _
  · exact NoPQ.failure

private theorem NoPQ.guardTrace (p : ExecTrace → Bool) :
    NoPQ (TripleRatchet.guardTrace p) :=
  NoPQ.of_id fun _ => by unfold TripleRatchet.guardTrace; rw [DY.Traceful.run_mk]

private theorem NoPQ.requireTracePredicate (p : ExecTrace → Bool) :
    NoPQ (DY.Libsignal.PQXDH.guardTrace p) :=
  NoPQ.of_id fun _ => by unfold DY.Libsignal.PQXDH.guardTrace; rw [DY.Traceful.run_mk]

private theorem NoPQ.monadLiftErr {α : Type} (x : Err α) :
    NoPQ (monadLift x : Traceful α) :=
  NoPQ.of_id fun _ => by dsimp only [monadLift, MonadLift.monadLift]; rw [DY.Traceful.run_mk]

private theorem NoPQ.traceLength : NoPQ TripleRatchet.traceLength :=
  NoPQ.of_id fun _ => by unfold TripleRatchet.traceLength; rw [DY.Traceful.run_mk]

private theorem NoPQ.bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : NoPQ x) (hf : ∀ a, NoPQ (f a)) :
    NoPQ (x >>= f) := by
  intro tr
  have h1 := hx tr
  rw [Traceful.run_bind]
  rcases h : x.run tr with ⟨_ | a, trMid, _⟩
  · rw [h] at h1; exact h1
  · rw [h] at h1; exact PQFrame.trans h1 (hf a trMid)

private theorem NoPQ.prodCasesOn {α β γ : Type} (p : α × β) (f : α → β → Traceful γ)
    (hf : ∀ a b, NoPQ (f a b)) :
    NoPQ (Prod.casesOn p f) := by
  rcases p with ⟨a, b⟩; exact hf a b

private theorem NoPQ.optionCasesOn {α β : Type} (o : Option α)
    (noneCase : Traceful β) (someCase : α → Traceful β)
    (hn : NoPQ noneCase) (hs : ∀ a, NoPQ (someCase a)) :
    NoPQ (Option.casesOn o noneCase someCase) := by
  rcases o with _ | a
  · exact hn
  · exact hs a

private theorem NoPQ.getLocalStatePQ (p : Participant) (h : Nat) :
    NoPQ (PersistentLocalState.getLocalState p h :
      Traceful DY.Libsignal.PQXDH.PQXDHState) :=
  NoPQ.of_id (Symbolic.Swarm.COMPOSED.CompTrace.getLocalState_pq_snd p h)

private theorem NoPQ.getKey (p : Participant) (h : Nat)
    (kind : DY.Libsignal.PQXDH.KeyKind) :
    NoPQ (DY.Libsignal.PQXDH.getKey p h kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  refine NoPQ.bind (NoPQ.getLocalStatePQ p h) fun _ => ?_
  exact NoPQ.bind (NoPQ.guardP _) fun _ => NoPQ.pure _

private theorem NoPQ.lookupIdentity (p : Participant) (h : Nat) :
    NoPQ (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine NoPQ.bind (NoPQ.getEntry h) fun _ => ?_
  split
  · exact NoPQ.bind (NoPQ.guardP _) fun _ => NoPQ.pure _
  · exact NoPQ.failure

private theorem NoPQ.genRand (n : Nat) :
    NoPQ (Random.genRand n : Traceful DY.Bytes) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact PQFrame.append tr (⟨n⟩ : Random.ExecEntryT) rfl (fun _ _ _ _ h => by cases h)

private theorem NoPQ.sendMessage (m : DY.Bytes) :
    NoPQ (Network.sendMessage m) := by
  intro tr
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_mk]
  exact PQFrame.append tr (⟨m⟩ : Network.ExecEntryT) rfl (fun _ _ _ _ h => by cases h)

private theorem NoPQ.storeLocalState (p : Participant) (st : TRState) :
    NoPQ (PersistentLocalState.storeLocalState p st) := by
  intro tr
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact PQFrame.append tr (⟨⟨p, st⟩⟩ : StEntryP) rfl (fun _ _ _ _ h => by cases h)

private theorem NoPQ.logEventPQ (ev : DY.Libsignal.PQXDH.PQXDHEvent)
    (hne : isIdRegEv ev = false) :
    NoPQ (DY.ProtocolEvent.logEvent ev) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact PQFrame.append tr (⟨ev⟩ : PQEvEntryP) rfl (fun _ _ _ _ h => by cases h; cases hne)

private theorem NoPQ.logEventC (ev : DY.Libsignal.Composed.ComposedEvent) :
    NoPQ (DY.ProtocolEvent.logEvent ev) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact PQFrame.append tr (⟨ev⟩ : CEvEntryP) rfl (fun _ _ _ _ h => by cases h)

private theorem NoPQ.logEventTR (ev : TREvent) :
    NoPQ (DY.ProtocolEvent.logEvent ev) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact PQFrame.append tr (⟨ev⟩ : TREntryP) rfl (fun _ _ _ _ h => by cases h)

private theorem NoPQ.logMessageKeyAndStore (me : Participant)
    (s : SessionInfo) (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes)
    (n : UInt32) (r par : Nat) (st : TRState) :
    NoPQ (TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) := by
  unfold TripleRatchet.logMessageKeyAndStore
  exact NoPQ.bind (NoPQ.logEventTR _) fun _ => NoPQ.storeLocalState _ _

private theorem NoPQ.receiveSignalMsg (msgIdx : Nat) :
    NoPQ (TripleRatchet.receiveSignalMsg msgIdx) := by
  unfold TripleRatchet.receiveSignalMsg
  refine NoPQ.bind (NoPQ.receiveMessage msgIdx) fun _ => ?_
  split
  · exact NoPQ.bind (NoPQ.guardP _) fun _ => NoPQ.pure _
  · exact NoPQ.failure

private theorem NoPQ.verifyMacAndDecrypt (st : TRState)
    (msg : TRSignalMsg) (pqSalt seed : DY.Bytes) :
    NoPQ (TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold TripleRatchet.verifyMacAndDecrypt
  exact NoPQ.bind (NoPQ.guardP _) fun _ => NoPQ.monadLiftErr _

private theorem NoPQ.dhRatchetStep (st : TRState) (pk : DY.Bytes) :
    NoPQ (TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact NoPQ.bind (NoPQ.guardP _) fun _ =>
    NoPQ.bind (NoPQ.genRand 32) fun _ => NoPQ.pure _

private theorem NoPQ.ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    NoPQ (TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact NoPQ.pure _
  · exact NoPQ.bind (NoPQ.dhRatchetStep st pk) fun _ => NoPQ.pure _
  · exact NoPQ.failure

private theorem NoPQ.logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    NoPQ (TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => exact NoPQ.pure _
  | succ k ih =>
    unfold TripleRatchet.logSkippedKeys
    exact NoPQ.bind (NoPQ.logEventTR _) fun _ => ih _ _

local macro "rpkP_tac" : tactic => `(tactic|
  repeat (first
    | with_reducible apply NoPQ.bind
    | with_reducible apply NoPQ.prodCasesOn
    | with_reducible apply NoPQ.optionCasesOn
    | with_reducible apply NoPQ.pure | with_reducible apply NoPQ.failure
    | with_reducible apply NoPQ.genRand
    | with_reducible apply NoPQ.storeLocalState
    | with_reducible apply NoPQ.sendMessage
    | with_reducible apply NoPQ.getLocalState
    | with_reducible apply NoPQ.getLocalStatePQ
    | with_reducible apply NoPQ.getKey
    | with_reducible apply NoPQ.lookupIdentity
    | with_reducible apply NoPQ.receiveMessage
    | with_reducible apply NoPQ.getEntry
    | with_reducible apply NoPQ.receiveSignalMsg
    | with_reducible apply NoPQ.verifyMacAndDecrypt
    | with_reducible apply NoPQ.dhRatchetStep
    | with_reducible apply NoPQ.ensureReceiverChain
    | with_reducible apply NoPQ.logSkippedKeys
    | with_reducible apply NoPQ.guardP | with_reducible apply NoPQ.monadLiftErr
    | with_reducible apply NoPQ.guardTrace | with_reducible apply NoPQ.requireTracePredicate
    | with_reducible apply NoPQ.traceLength
    | with_reducible apply NoPQ.logMessageKeyAndStore
    | with_reducible apply NoPQ.logEventPQ _ (by rfl)
    | with_reducible apply NoPQ.logEventC
    | with_reducible apply NoPQ.logEventTR
    | split | with_reducible intro))

private theorem NoPQ.aliceHandshake (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    NoPQ (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake; rpkP_tac

private theorem NoPQ.aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    NoPQ (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine NoPQ.bind (NoPQ.aliceHandshake a b idStateIdx regIdxB h) fun _ => ?_
  rpkP_tac

private theorem NoPQ.bobHandshake (b a : Participant)
    (h : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    NoPQ (DY.Libsignal.PQXDH.bobHandshake b a h regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake; rpkP_tac

private theorem NoPQ.bobStart (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    NoPQ (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine NoPQ.bind (NoPQ.bobHandshake b a kh regIdxA mh.ek mh.ct) fun _ => ?_
  rpkP_tac

private theorem NoPQ.compromiseIK (p : Participant) (j : Nat) :
    NoPQ (DY.Libsignal.PQXDH.compromiseIK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseIK; rpkP_tac

private theorem NoPQ.compromiseSPK (p : Participant) (j : Nat) :
    NoPQ (DY.Libsignal.PQXDH.compromiseSPK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK; rpkP_tac

private theorem NoPQ.compromisePQSPK (p : Participant) (j : Nat) :
    NoPQ (DY.Libsignal.PQXDH.compromisePQSPK p j) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK; rpkP_tac

private theorem NoPQ.compromiseOPK (p : Participant) (j : Nat) :
    NoPQ (DY.Libsignal.PQXDH.compromiseOPK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK; rpkP_tac

/-! ## Non-`setup` Moves and Composed Run Traces -/

private theorem rpkP_noPQ_move (m : Move) (hm : m.isSetup = false) : NoPQ m.act := by
  cases m with
  | setup a b withOpk => cases hm
  | aliceStart a b idStateIdx regIdxB bh shown =>
    unfold Move.act
    exact NoPQ.bind (NoPQ.aliceStart a b idStateIdx regIdxB bh) fun _ => NoPQ.pure _
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown =>
    unfold Move.act
    exact NoPQ.bind (NoPQ.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) fun _ => NoPQ.pure _
  | encrypt me stateIdx coinsLen pqIdx wrap =>
    unfold Move.act TripleRatchet.messageEncrypt; rpkP_tac
  | encryptAbort me stateIdx =>
    unfold Move.act TripleRatchet.messageEncryptAbort; rpkP_tac
  | encryptFail me stateIdx coinsLen =>
    unfold Move.act TripleRatchet.messageEncrypt; rpkP_tac
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    unfold Move.act; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]; rpkP_tac
  | decryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx wrapped =>
    unfold Move.act TripleRatchet.messageDecryptSkipped; rpkP_tac
  | reject draws => unfold Move.act; rpkP_tac
  | compromiseIK p stateIdx =>
    unfold Move.act
    exact NoPQ.bind (NoPQ.compromiseIK p stateIdx) fun _ => NoPQ.pure _
  | compromiseSPK p stateIdx =>
    unfold Move.act
    exact NoPQ.bind (NoPQ.compromiseSPK p stateIdx) fun _ => NoPQ.pure _
  | compromisePQSPK p stateIdx =>
    unfold Move.act
    exact NoPQ.bind (NoPQ.compromisePQSPK p stateIdx) fun _ => NoPQ.pure _
  | compromiseOPK p stateIdx =>
    unfold Move.act
    exact NoPQ.bind (NoPQ.compromiseOPK p stateIdx) fun _ => NoPQ.pure _
  | exposeKey me stateIdx k => unfold Move.act TripleRatchet.exposeKey; rpkP_tac
  | exposeSpqr me stateIdx => unfold Move.act TripleRatchet.exposeSpqr; rpkP_tac
  | exposeSkipped skippedKeyEventIdx => unfold Move.act TripleRatchet.exposeSkipped; rpkP_tac
  | attackerSend msg => unfold Move.act; rpkP_tac
  | brkDH =>
    exact NoPQ.logEventPQ .BrokenDH rfl
  | brkKEM =>
    exact NoPQ.logEventPQ .BrokenKEM rfl

private theorem rpkP_runMoves_frame :
    ∀ (ms : List Move) (tr : ExecTrace),
      (∀ m ∈ ms, m.isSetup = false) → PQFrame tr (runMoves ms tr).1
  | [], tr, _ => PQFrame.refl tr
  | m :: ms, tr, hms =>
    PQFrame.trans (rpkP_noPQ_move m (hms m (.head _)) tr)
      (rpkP_runMoves_frame ms (m.next tr) (fun m' hm' => hms m' (.tail _ hm')))

private theorem rpkP_runTrace_frame (r : ProtocolSetup) (ms : List Move)
    (hms : ∀ m ∈ ms, m.isSetup = false) : PQFrame (setupTrace r) (runTraceMoves r ms) :=
  rpkP_runMoves_frame ms (setupTrace r) hms

/-! ## Setup Trace Entries and Identity Registrations -/

private def PQSetupOk (a b : Participant) (opk : Bool) (p : Participant)
    (st : DY.Libsignal.PQXDH.PQXDHState) : Prop :=
  (p = a ∧ st = { kind := .identity, sk := randTerm 0 32 }) ∨
  (p = b ∧ st = { kind := .identity, sk := randTerm 5 32 }) ∨
  (p = b ∧ st = { kind := .signedPrekey, sk := randTerm 10 32 }) ∨
  (p = b ∧ st = { kind := .pqPrekey, sk := randTerm 16 64 }) ∨
  (p = b ∧ st = { kind := .oneTimePrekey, sk := randTerm 22 32 } ∧ opk = true)

private def IdSetupOk (a b : Participant) (p : Participant) (pk : DY.Bytes) : Prop :=
  (p = a ∧ pk = DY.DiffieHellman.dhPk (randTerm 0 32)) ∨
  (p = b ∧ pk = DY.DiffieHellman.dhPk (randTerm 5 32))

private def SetupPQ (a b : Participant) (opk : Bool) (tr : ExecTrace) : Prop :=
  (∀ (i : Nat) (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState),
    (tr.at? i : Option PQStEntry) = some (StE p st) → PQSetupOk a b opk p st) ∧
  (∀ (i : Nat) (p : Participant) (pk vk : DY.Bytes) (hh : Bool),
    (tr.at? i : Option PQEvEntryP) = some (EvE (.IdentityRegistered p pk vk hh)) →
    IdSetupOk a b p pk)

private theorem SetupPQ.nil (a b : Participant) (opk : Bool) : SetupPQ a b opk Trace.nil := by
  have hle : ∀ i : Nat, (Trace.nil : ExecTrace).length ≤ i := fun i => by
    rw [Symbolic.DYBridge.DY.Trace.length_eq_1]; exact Nat.zero_le i
  refine ⟨fun i p st h => ?_, fun i p pk vk hh h => ?_⟩
  · rw [rpkP_at?_eq_none_of_le Trace.nil (hle i)] at h; cases h
  · rw [rpkP_at?_eq_none_of_le Trace.nil (hle i)] at h; cases h

private theorem SetupPQ.append {a b : Participant} {opk : Bool} {tr : ExecTrace} {E : Type}
    [ExecTraceTypes.Has E] {e : E}
    (h : SetupPQ a b opk tr)
    (hst : ∀ (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState),
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option PQStEntry) =
        some (StE p st) → PQSetupOk a b opk p st)
    (hev : ∀ (p : Participant) (pk vk : DY.Bytes) (hh : Bool),
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option PQEvEntryP) =
        some (EvE (.IdentityRegistered p pk vk hh)) → IdSetupOk a b p pk) :
    SetupPQ a b opk (tr.append e) := by
  refine ⟨fun i p st hat => ?_, fun i p pk vk hh hat => ?_⟩
  · rcases rpkP_at?_append_cases hat with h1 | h2
    · exact h.1 i p st h1
    · exact hst p st h2
  · rcases rpkP_at?_append_cases hat with h1 | h2
    · exact h.2 i p pk vk hh h1
    · exact hev p pk vk hh h2

local macro "rpkP_setup_step" : tactic => `(tactic|
  (repeat (first
     | (with_reducible assumption)
     | refine SetupPQ.append ?_
         (fun p st h => by first | (cases h; done) | (cases h; simp [PQSetupOk]))
         (fun p pk vk hh h => by first | (cases h; done) | (cases h; simp [IdSetupOk]))
     | exact SetupPQ.nil _ _ _)))

private theorem rpkP_setupPQ_tr1 (a b : Participant) (opk : Bool) :
    SetupPQ a b opk (TR.setupTr1 a) := by
  simp only [TR.setupTr1]
  rpkP_setup_step

private theorem rpkP_setupPQ_tr2 (a b : Participant) (opk : Bool) :
    SetupPQ a b opk (TR.setupTr2 a b) := by
  have := rpkP_setupPQ_tr1 a b opk
  simp only [TR.setupTr2]
  rpkP_setup_step

private theorem rpkP_setupPQ_tr3 (a b : Participant) (opk : Bool) :
    SetupPQ a b opk (TR.setupTr3 a b) := by
  have := rpkP_setupPQ_tr2 a b opk
  simp only [TR.setupTr3]
  rpkP_setup_step

private theorem rpkP_setupPQ_tr4 (a b : Participant) (opk : Bool) :
    SetupPQ a b opk (TR.setupTr4 a b) := by
  have := rpkP_setupPQ_tr3 a b opk
  simp only [TR.setupTr4]
  rpkP_setup_step

private theorem rpkP_setupPQ_tr5 (a b : Participant) : SetupPQ a b true (TR.setupTr5 a b) := by
  have := rpkP_setupPQ_tr4 a b true
  simp only [TR.setupTr5]
  rpkP_setup_step

private theorem rpkP_setupPQ (r : ProtocolSetup) (hne : r.alice ≠ r.bob) :
    SetupPQ r.alice r.bob r.withOpk (setupTrace r) := by
  rw [TR.setupTrace_eq r hne]
  cases hw : r.withOpk
  · exact rpkP_setupPQ_tr4 _ _ _
  · exact rpkP_setupPQ_tr5 _ _

/-! ## Key and Identity Provenance -/

/-- Bob's identity entries on composed traces hold the setup identity secret. -/
theorem rpkP_bob_identity {r : ProtocolSetup} (hne : r.alice ≠ r.bob) (ms : List Move)
    (hms : ∀ m ∈ ms, m.isSetup = false) {i : Nat}
    {sk : DY.Bytes} (h : (runTraceMoves r ms).at? i = some (StE r.bob { kind := .identity, sk := sk })) :
    sk = setupSecret r 1 := by
  rw [(rpkP_runTrace_frame r ms hms).1 i] at h
  rw [(rpkP_setupSecret_eq r hne).2.1]
  rcases (rpkP_setupPQ r hne).1 i _ _ h with
    ⟨hp, _⟩ | ⟨_, hst⟩ | ⟨_, hst⟩ | ⟨_, hst⟩ | ⟨_, hst, _⟩
  · exact absurd hp.symm hne
  · cases hst; rfl
  · cases hst
  · cases hst
  · cases hst

/-- Bob's signed pre-key entries on composed traces hold the setup signed pre-key secret. -/
theorem rpkP_bob_spk {r : ProtocolSetup} (hne : r.alice ≠ r.bob) (ms : List Move)
    (hms : ∀ m ∈ ms, m.isSetup = false) {i : Nat}
    {sk : DY.Bytes}
    (h : (runTraceMoves r ms).at? i = some (StE r.bob { kind := .signedPrekey, sk := sk })) :
    sk = setupSecret r 2 := by
  rw [(rpkP_runTrace_frame r ms hms).1 i] at h
  rw [(rpkP_setupSecret_eq r hne).2.2.1]
  rcases (rpkP_setupPQ r hne).1 i _ _ h with
    ⟨_, hst⟩ | ⟨_, hst⟩ | ⟨_, hst⟩ | ⟨_, hst⟩ | ⟨_, hst, _⟩
  · cases hst
  · cases hst
  · cases hst; rfl
  · cases hst
  · cases hst

/-- Bob's PQ pre-key entries on composed traces hold the setup PQ pre-key secret. -/
theorem rpkP_bob_pq {r : ProtocolSetup} (hne : r.alice ≠ r.bob) (ms : List Move)
    (hms : ∀ m ∈ ms, m.isSetup = false) {i : Nat}
    {sk : DY.Bytes} (h : (runTraceMoves r ms).at? i = some (StE r.bob { kind := .pqPrekey, sk := sk })) :
    sk = setupSecret r 4 := by
  rw [(rpkP_runTrace_frame r ms hms).1 i] at h
  rw [(rpkP_setupSecret_eq r hne).2.2.2.1]
  rcases (rpkP_setupPQ r hne).1 i _ _ h with
    ⟨_, hst⟩ | ⟨_, hst⟩ | ⟨_, hst⟩ | ⟨_, hst⟩ | ⟨_, hst, _⟩
  · cases hst
  · cases hst
  · cases hst
  · cases hst; rfl
  · cases hst

/-- Bob's one-time pre-key entries on composed traces: only with `r.withOpk`, holding the setup
one-time pre-key secret. -/
theorem rpkP_bob_opk_at {r : ProtocolSetup} (hne : r.alice ≠ r.bob) (ms : List Move)
    (hms : ∀ m ∈ ms, m.isSetup = false) {i : Nat} {sk : DY.Bytes}
    (h : (runTraceMoves r ms).at? i = some (StE r.bob { kind := .oneTimePrekey, sk := sk })) :
    r.withOpk = true ∧ sk = setupSecret r 6 := by
  rw [(rpkP_runTrace_frame r ms hms).1 i] at h
  rcases (rpkP_setupPQ r hne).1 i _ _ h with
    ⟨_, hst⟩ | ⟨_, hst⟩ | ⟨_, hst⟩ | ⟨_, hst⟩ | ⟨_, hst, hopk⟩
  · cases hst
  · cases hst
  · cases hst
  · cases hst
  · cases hst
    exact ⟨hopk, ((rpkP_setupSecret_eq r hne).2.2.2.2 hopk).symm⟩

/-- `StOpt`-shaped one-time pre-key provenance (`StOpt (runTraceMoves r ms) r.bob kh.opk opk`
unfolds to the hypothesis). -/
theorem rpkP_bob_opk {r : ProtocolSetup} (hne : r.alice ≠ r.bob) (ms : List Move)
    (hms : ∀ m ∈ ms, m.isSetup = false) (oi : Option Nat) (opk : Option DY.Bytes)
    (h : match oi, opk with
      | none, none => True
      | some i, some o => (runTraceMoves r ms).at? i = some (StE r.bob { kind := .oneTimePrekey, sk := o })
      | _, _ => False) :
    opk = none ∨ (r.withOpk = true ∧ opk = some (setupSecret r 6)) := by
  rcases oi with _ | i <;> rcases opk with _ | o
  · exact Or.inl rfl
  · exact (h : False).elim
  · exact Or.inl rfl
  · obtain ⟨hw, ho⟩ := rpkP_bob_opk_at hne ms hms h
    exact Or.inr ⟨hw, by rw [ho]⟩

/-- Identity registrations on composed traces are the two setup registrations. -/
theorem rpkP_reg {r : ProtocolSetup} (hne : r.alice ≠ r.bob) (ms : List Move)
    (hms : ∀ m ∈ ms, m.isSetup = false) {i : Nat} {p : Participant} {pk vk : DY.Bytes}
    {hh : Bool}
    (h : (runTraceMoves r ms).at? i = some (EvE (.IdentityRegistered p pk vk hh))) :
    (p = r.alice ∧ pk = setupPublic r 0) ∨ (p = r.bob ∧ pk = setupPublic r 2) := by
  have h' := (rpkP_runTrace_frame r ms hms).2 i p pk vk hh h
  obtain ⟨hp0, hp2⟩ := rpkP_setupPublic_eq r hne
  rw [hp0, hp2]
  exact (rpkP_setupPQ r hne).2 i p pk vk hh h'

/-- Alice's identity registration on composed traces carries the setup identity key. -/
theorem rpkP_reg_alice {r : ProtocolSetup} (hne : r.alice ≠ r.bob) (ms : List Move)
    (hms : ∀ m ∈ ms, m.isSetup = false) {i : Nat} {pk vk : DY.Bytes} {hh : Bool}
    (h : (runTraceMoves r ms).at? i = some (EvE (.IdentityRegistered r.alice pk vk hh))) :
    pk = setupPublic r 0 := by
  rcases rpkP_reg hne ms hms h with ⟨_, hpk⟩ | ⟨hp, _⟩
  · exact hpk
  · exact absurd hp hne

end Symbolic.Swarm.CREF
