/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Identity-Key Shape Invariant

Proves `availableIkShapeId_all`: every `TRState` in `availableStates r₀ (runTraceMoves r₀ ms)`
satisfies `ShapeId st.myIk` and `ShapeId st.peerIk`, established via the trace invariant
`TraceIkOk`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Ik

cref_open
open DY.DiffieHellman
open DY.Libsignal.TripleRatchet (SessionInfo KeyComponent KeyDir RecvChain setRecvChain kdfCk
  createChain)
open DY.Libsignal.TripleRatchet
open Symbolic.Swarm.CREF.TR.G1 (ShapeId)

abbrev IkStEntry :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
abbrev IkPQStEntry :=
  PersistentGlobalState.State.ExecEntryT
    (PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)
abbrev IkPQEvEntry := DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent

theorem proj_inj_ik {E : Type} [ExecTraceTypes.Has E] (e : E) :
    (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by
  rw [TraceEntryHas.inj_proj_eq]

/-! ## Entry predicate -/

/-- A session state's identity-key fields are `ShapeId`. -/
def TrStateIkOk (st : TRState) : Prop := ShapeId st.myIk ∧ ShapeId st.peerIk

/-- A PQXDH identity key state holds a `ShapeId` secret. -/
def PQStateIkOk (st : DY.Libsignal.PQXDH.PQXDHState) : Prop :=
  st.kind = .identity → ShapeId st.sk

/-- An `IdentityRegistered` event carries a `ShapeId` identity public key. -/
def PQEventIkOk (ev : DY.Libsignal.PQXDH.PQXDHEvent) : Prop :=
  ∀ (p : Participant) (ikPk vkPk : DY.Bytes) (honest : Bool),
    ev = .IdentityRegistered p ikPk vkPk honest → ShapeId ikPk

/-- The per-entry invariant (trace-independent). -/
def IkEntryOk (ent : ExecTrace.Entry) : Prop :=
  (∀ e : IkStEntry, TraceEntryHas.proj ent = some e → TrStateIkOk e.st.state) ∧
  (∀ e : IkPQStEntry, TraceEntryHas.proj ent = some e → PQStateIkOk e.st.state) ∧
  (∀ e : IkPQEvEntry, TraceEntryHas.proj ent = some e → PQEventIkOk e.ev)

/-- Every entry of `tr` satisfies `IkEntryOk`. -/
def TraceIkOk (tr : ExecTrace) : Prop :=
  ∀ j (hj : j < tr.length), IkEntryOk (tr.at j hj)

theorem traceIkOk_nil : TraceIkOk (DY.Trace.nil : ExecTrace) :=
  fun _ hj => by simp [Symbolic.DYBridge.DY.Trace.length_eq_1] at hj

theorem traceIkOk_append {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hent : IkEntryOk (TraceEntryHas.inj e)) (htr : TraceIkOk tr) :
    TraceIkOk (tr.append e) := by
  have hle : tr ≤ tr.append e := DY.Trace.append_le tr e
  intro j hj
  by_cases hlt : j < tr.length
  · rw [← DY.Trace.at_le tr (tr.append e) j hlt hle]
    exact htr j hlt
  · have heq : j = tr.length := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hj
      omega
    subst heq
    simpa [Symbolic.DYBridge.DY.Trace.append_eq_1, DY.Trace.snoc, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.nil_length_not_lt, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] using hent

/-! ## `TracefulIk` combinators -/

/-- Monad combinator for `TraceIkOk` with a trace-free result predicate. -/
def TracefulIk {α : Type} (Q : α → Prop) (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, TraceIkOk tr →
    TraceIkOk (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q a

theorem TracefulIk.pure {α : Type} {Q : α → Prop} {a : α} (ha : Q a) :
    TracefulIk Q (Pure.pure a) := by
  unfold TracefulIk
  intro tr htr
  simp only [Traceful.run_pure]
  refine ⟨htr, fun b hb => ?_⟩
  cases hb
  exact ha

theorem TracefulIk.failure {α : Type} {Q : α → Prop} :
    TracefulIk Q (Alternative.failure : Traceful α) := by
  unfold TracefulIk
  intro _ htr
  simp only [Traceful.run_failure]
  exact ⟨htr, fun _ hb => by cases hb⟩

private theorem run_bind_fst_ik {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

private theorem run_bind_snd_ik {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem TracefulIk.bind {α β : Type} {Q₁ : α → Prop} {Q₂ : β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulIk Q₁ x) (hf : ∀ a : α, Q₁ a → TracefulIk Q₂ (f a)) :
    TracefulIk Q₂ (x >>= f) := by
  intro tr htr
  rw [run_bind_snd_ik, run_bind_fst_ik]
  have h1 := hx tr htr
  cases hres : (x.run tr).1 with
  | none => exact ⟨h1.1, fun _ hb => by cases hb⟩
  | some a => exact hf a (h1.2 a hres) _ h1.1

theorem tracefulIk_run_snd {α : Type} {Q : α → Prop} {x : Traceful α}
    (hx : TracefulIk Q x) {tr : ExecTrace} (htr : TraceIkOk tr) :
    TraceIkOk ((x >>= fun _ => Pure.pure ()).run tr).2.val :=
  (TracefulIk.bind hx (fun _ _ => TracefulIk.pure (Q := fun _ => True) trivial) tr htr).1

theorem TracefulIk.guardP (p : Prop) [Decidable p] :
    TracefulIk (fun _ => True) (_root_.guard p) := by
  unfold _root_.guard
  split
  · exact TracefulIk.pure trivial
  · exact TracefulIk.failure

/-! ## Primitive steps -/

theorem tracefulIk_guardTrace (p : ExecTrace → Bool) :
    TracefulIk (fun _ => True) (guardTrace p) := by
  unfold TracefulIk guardTrace
  intro _ htr
  simp only [Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulIk_traceLength : TracefulIk (fun _ => True) traceLength := by
  unfold TracefulIk traceLength
  intro _ htr
  simp only [Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulIk.getEntry_any {E : Type} [ExecTraceTypes.Has E] (j : Nat) :
    TracefulIk (fun (_ : E) => True) (getEntry j : Traceful E) := by
  unfold TracefulIk
  intro _ htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulIk.getEntry_st (j : Nat) :
    TracefulIk (fun (e : IkStEntry) => TrStateIkOk e.st.state) (getEntry j) := by
  unfold TracefulIk
  intro tr htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  refine ⟨htr, fun e he => ?_⟩
  unfold DY.Trace.at? at he
  split at he
  · next hj => exact (htr j hj).1 e he
  · cases he

theorem TracefulIk.getEntry_pq (j : Nat) :
    TracefulIk (fun (e : IkPQStEntry) => PQStateIkOk e.st.state) (getEntry j) := by
  unfold TracefulIk
  intro tr htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  refine ⟨htr, fun e he => ?_⟩
  unfold DY.Trace.at? at he
  split at he
  · next hj => exact (htr j hj).2.1 e he
  · cases he

theorem TracefulIk.getEntry_ev (j : Nat) :
    TracefulIk (fun (e : IkPQEvEntry) => PQEventIkOk e.ev) (getEntry j) := by
  unfold TracefulIk
  intro tr htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  refine ⟨htr, fun e he => ?_⟩
  unfold DY.Trace.at? at he
  split at he
  · next hj => exact (htr j hj).2.2 e he
  · cases he

theorem TracefulIk.receiveMessage (j : Nat) :
    TracefulIk (fun _ => True) (Network.receiveMessage j) := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact TracefulIk.bind (TracefulIk.getEntry_any j) fun _ _ => TracefulIk.pure trivial

theorem tracefulIk_receiveSignalMsg (msgIdx : Nat) :
    TracefulIk (fun _ => True) (receiveSignalMsg msgIdx) := by
  unfold receiveSignalMsg
  refine TracefulIk.bind (TracefulIk.receiveMessage msgIdx) fun _ _ => ?_
  split
  · exact TracefulIk.bind (TracefulIk.guardP _) fun _ _ => TracefulIk.pure trivial
  · exact TracefulIk.failure

theorem TracefulIk.getLocalState (p : Participant) (j : Nat) :
    TracefulIk (fun (st : TRState) => TrStateIkOk st) (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine TracefulIk.bind
    (TracefulIk.bind (TracefulIk.getEntry_st j) fun _ he =>
      TracefulIk.pure
        (Q := fun (ls : PersistentLocalState.LocalState TRState) => TrStateIkOk ls.state) he)
    fun _ hst => ?_
  exact TracefulIk.bind (TracefulIk.guardP _) fun _ _ => TracefulIk.pure hst

theorem TracefulIk.getLocalStatePQ (p : Participant) (j : Nat) :
    TracefulIk (fun (st : DY.Libsignal.PQXDH.PQXDHState) => PQStateIkOk st)
      (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine TracefulIk.bind
    (TracefulIk.bind (TracefulIk.getEntry_pq j) fun _ he =>
      TracefulIk.pure
        (Q := fun (ls : PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState) =>
          PQStateIkOk ls.state) he)
    fun _ hst => ?_
  exact TracefulIk.bind (TracefulIk.guardP _) fun _ _ => TracefulIk.pure hst

theorem TracefulIk.getKey (p : Participant) (j : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    TracefulIk (fun (sk : DY.Bytes) => kind = .identity → ShapeId sk)
      (DY.Libsignal.PQXDH.getKey p j kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  refine TracefulIk.bind (TracefulIk.getLocalStatePQ p j) fun st hst => ?_
  refine TracefulIk.bind (Q₁ := fun _ => st.kind = kind) ?_ fun _ hk =>
    TracefulIk.pure fun hkind => hst (hk.trans hkind)
  unfold _root_.guard
  split
  · next h => exact TracefulIk.pure h
  · exact TracefulIk.failure

theorem TracefulIk.lookupIdentity (p : Participant) (j : Nat) :
    TracefulIk (fun (kv : DY.Bytes × DY.Bytes) => ShapeId kv.1)
      (DY.Libsignal.PQXDH.lookupIdentity p j) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine TracefulIk.bind (TracefulIk.getEntry_ev j) fun e hev => ?_
  split
  · next p' ikPk vkPk honest heq =>
    exact TracefulIk.bind (TracefulIk.guardP _) fun _ _ =>
      TracefulIk.pure (hev p' ikPk vkPk honest heq)
  · exact TracefulIk.failure

theorem TracefulIk.genRand_shapeId :
    TracefulIk (fun (b : DY.Bytes) => ShapeId b) (DY.Random.genRand 32) := by
  unfold TracefulIk
  intro tr htr
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    run_bind_fst_ik, run_bind_snd_ik, Traceful.run_mk]
  dsimp only
  rw [Traceful.run_pure]
  dsimp only
  refine ⟨traceIkOk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun a ha => ?_⟩
  injection ha with ha
  subst ha
  exact Symbolic.Swarm.CREF.TR.G1.shapeId_randTerm32 tr.length

theorem TracefulIk.genRand (n : Nat) : TracefulIk (fun _ => True) (DY.Random.genRand n) := by
  unfold TracefulIk
  intro _ htr
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceIkOk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulIk.sendMessage (msg : DY.Bytes) :
    TracefulIk (fun _ => True) (Network.sendMessage msg) := by
  unfold TracefulIk
  intro _ htr
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_mk]
  exact ⟨traceIkOk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulIk.logEvent (ev : TREvent) :
    TracefulIk (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulIk
  intro _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceIkOk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulIk.logEventPQ {ev : DY.Libsignal.PQXDH.PQXDHEvent} (hev : PQEventIkOk ev) :
    TracefulIk (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulIk
  intro tr htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  refine ⟨traceIkOk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h), ?_⟩ htr, fun _ _ => trivial⟩
  intro e h
  rw [proj_inj_ik] at h
  injection h with h
  subst h
  exact hev

theorem TracefulIk.logEventC (ev : DY.Libsignal.Composed.ComposedEvent) :
    TracefulIk (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulIk
  intro _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceIkOk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulIk.storeLocalState (p : Participant) {st : TRState} (hst : TrStateIkOk st) :
    TracefulIk (fun _ => True) (PersistentLocalState.storeLocalState p st) := by
  unfold TracefulIk
  intro tr htr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  refine ⟨traceIkOk_append ⟨?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩
  intro e h
  rw [proj_inj_ik] at h
  injection h with h
  subst h
  exact hst

theorem TracefulIk.storeLocalStatePQ (p : Participant) {st : DY.Libsignal.PQXDH.PQXDHState}
    (hst : PQStateIkOk st) :
    TracefulIk (fun _ => True) (PersistentLocalState.storeLocalState p st) := by
  unfold TracefulIk
  intro tr htr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  refine ⟨traceIkOk_append ⟨fun _ h => (by cases h), ?_, fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩
  intro e h
  rw [proj_inj_ik] at h
  injection h with h
  subst h
  exact hst

theorem tracefulIk_guardOnTrace (p : ExecTrace → Bool) :
    TracefulIk (fun _ => True) (DY.Libsignal.PQXDH.guardTrace p) := by
  unfold TracefulIk DY.Libsignal.PQXDH.guardTrace
  intro tr htr
  by_cases hp : p tr = true <;> simp only [Traceful.run_mk, hp, Bool.false_eq_true, ↓reduceIte] <;>
    exact ⟨htr, fun _ _ => trivial⟩

/-! ## Triple Ratchet transitions -/

theorem tracefulIk_logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) {st : TRState}
    (hst : TrStateIkOk st) :
    TracefulIk (fun _ => True) (logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold logMessageKeyAndStore
  exact TracefulIk.bind (TracefulIk.logEvent _) fun _ _ =>
    TracefulIk.storeLocalState me hst

theorem tracefulIk_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    TracefulIk (fun _ => True) (logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero =>
    unfold logSkippedKeys
    exact TracefulIk.pure trivial
  | succ k ih =>
    unfold logSkippedKeys
    exact TracefulIk.bind (TracefulIk.logEvent _) fun _ _ => ih (kdfCk ck).1 (n + 1)

theorem tracefulIk_verifyMacAndDecrypt (st : TRState) (msg : TRSignalMsg) (pqSalt seed : DY.Bytes) :
    TracefulIk (fun _ => True) (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold verifyMacAndDecrypt
  refine TracefulIk.bind (TracefulIk.guardP _) fun _ _ => ?_
  unfold TracefulIk
  intro _ htr
  dsimp [liftM, monadLift, MonadLift.monadLift]
  simp only [Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulIk_dhRatchetStep {st : TRState} (pk : DY.Bytes) (hst : TrStateIkOk st) :
    TracefulIk (fun (p : TRState × RecvChain) => TrStateIkOk p.1) (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine TracefulIk.bind (TracefulIk.guardP _) fun _ _ =>
    TracefulIk.bind (TracefulIk.genRand 32) fun _ _ =>
      TracefulIk.pure hst

theorem tracefulIk_ensureReceiverChain {st : TRState} (pk : DY.Bytes) (hst : TrStateIkOk st) :
    TracefulIk (fun (p : TRState × RecvChain × Bool) => TrStateIkOk p.1)
      (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact TracefulIk.pure hst
  · exact TracefulIk.bind (tracefulIk_dhRatchetStep pk hst) fun ⟨_, _⟩ h => TracefulIk.pure h
  · exact TracefulIk.failure

theorem tracefulIk_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    TracefulIk (fun _ => True) (messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold messageEncrypt
  refine TracefulIk.bind (TracefulIk.getLocalState me stateIdx) fun st hst =>
    TracefulIk.bind (TracefulIk.guardP _) fun _ _ =>
    TracefulIk.bind (TracefulIk.genRand 32) fun _ _ =>
    TracefulIk.bind (TracefulIk.genRand coinsLen) fun _ _ =>
    TracefulIk.bind (TracefulIk.sendMessage _) fun _ _ =>
    TracefulIk.bind (TracefulIk.receiveMessage pqIdx) fun _ _ =>
    TracefulIk.bind (TracefulIk.logEvent _) fun _ _ =>
    TracefulIk.bind (tracefulIk_logMessageKeyAndStore me _ .sender _ _ _ _ _ hst) fun _ _ =>
      TracefulIk.sendMessage _

theorem tracefulIk_messageEncryptAbort (me : Participant) (stateIdx : Nat) :
    TracefulIk (fun _ => True) (messageEncryptAbort me stateIdx) := by
  unfold messageEncryptAbort
  exact TracefulIk.bind (TracefulIk.getLocalState me stateIdx) fun _ _ =>
    TracefulIk.bind (TracefulIk.genRand 32) fun _ _ => TracefulIk.failure

theorem tracefulIk_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    TracefulIk (fun _ => True) (messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine TracefulIk.bind (TracefulIk.getLocalState me stateIdx) fun st₀ hst₀ =>
    TracefulIk.bind (tracefulIk_receiveSignalMsg msgIdx) fun msg _ =>
    TracefulIk.bind (tracefulIk_ensureReceiverChain msg.ratchetKey hst₀)
      fun ⟨st, c, ratcheted⟩ hst => ?_
  dsimp only
  split
  · next seed c' _ =>
    split
    · next spqr' key _ =>
      refine TracefulIk.bind (TracefulIk.sendMessage key) fun _ _ =>
        TracefulIk.bind (TracefulIk.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulIk.bind (tracefulIk_verifyMacAndDecrypt st msg pqSalt seed) fun m _ => ?_
      have hrest :
          TracefulIk (fun _ => True)
            (do logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
                  (msg.counter.toNat - c.index.toNat)
                DY.ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
                logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx stateIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
        TracefulIk.bind (tracefulIk_logSkippedKeys _ _ _ _ _ _ _) fun _ _ =>
          TracefulIk.bind (TracefulIk.logEvent _) fun _ _ =>
            tracefulIk_logMessageKeyAndStore me _ .receiver _ _ _ _ _ hst
      split
      · exact TracefulIk.bind (TracefulIk.logEvent _) fun _ _ =>
          TracefulIk.bind (TracefulIk.logEvent _) fun _ _ => hrest
      · exact hrest
    · exact TracefulIk.failure
  · exact TracefulIk.failure

theorem tracefulIk_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulIk (fun _ => True)
      (messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold messageDecryptSkipped
  refine TracefulIk.bind (TracefulIk.getLocalState me stateIdx) fun st hst =>
    TracefulIk.bind (tracefulIk_receiveSignalMsg msgIdx) fun msg _ =>
    TracefulIk.bind (TracefulIk.getEntry_any skippedKeyEventIdx) fun _ _ => ?_
  split
  · refine TracefulIk.bind (TracefulIk.guardP _) fun _ _ =>
      TracefulIk.bind (tracefulIk_guardTrace _) fun _ _ => ?_
    split
    · next spqr' key _ =>
      exact TracefulIk.bind (TracefulIk.sendMessage key) fun _ _ =>
        TracefulIk.bind (TracefulIk.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulIk.bind (tracefulIk_verifyMacAndDecrypt st msg pqSalt _) fun _ _ =>
        TracefulIk.bind (TracefulIk.logEvent _) fun _ _ =>
        TracefulIk.bind (TracefulIk.logEvent _) fun _ _ =>
        tracefulIk_logMessageKeyAndStore me _ .receiver _ _ _ _ _ hst
    · exact TracefulIk.failure
  · exact TracefulIk.failure

theorem tracefulIk_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    TracefulIk (fun _ => True) (exposeKey me stateIdx k) := by
  unfold exposeKey
  refine TracefulIk.bind (TracefulIk.getLocalState me stateIdx) fun _ _ => ?_
  cases k with
  | rk => exact TracefulIk.bind (TracefulIk.logEvent _) fun _ _ => TracefulIk.sendMessage _
  | dhs => exact TracefulIk.bind (TracefulIk.logEvent _) fun _ _ => TracefulIk.sendMessage _
  | cks => exact TracefulIk.bind (TracefulIk.logEvent _) fun _ _ => TracefulIk.sendMessage _
  | ckr pk =>
    dsimp only; split
    · exact TracefulIk.bind (TracefulIk.logEvent _) fun _ _ => TracefulIk.sendMessage _
    · exact TracefulIk.failure

theorem tracefulIk_exposeSpqr (me : Participant) (stateIdx : Nat) :
    TracefulIk (fun _ => True) (exposeSpqr me stateIdx) := by
  unfold exposeSpqr
  exact TracefulIk.bind (TracefulIk.getLocalState me stateIdx) fun _ _ =>
    TracefulIk.bind (TracefulIk.logEvent _) fun _ _ => TracefulIk.sendMessage _

theorem tracefulIk_exposeSkipped (skippedKeyEventIdx : Nat) :
    TracefulIk (fun _ => True) (exposeSkipped skippedKeyEventIdx) := by
  unfold exposeSkipped
  refine TracefulIk.bind (TracefulIk.getEntry_any skippedKeyEventIdx) fun _ _ => ?_
  split
  · exact TracefulIk.bind (tracefulIk_guardTrace _) fun _ _ =>
      TracefulIk.bind (TracefulIk.logEvent _) fun _ _ =>
      TracefulIk.sendMessage _
  · exact TracefulIk.failure

/-! ## PQXDH steps -/

theorem tracefulIk_compromiseIK (p : Participant) (j : Nat) :
    TracefulIk (fun _ => True) (DY.Libsignal.PQXDH.compromiseIK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseIK
  exact TracefulIk.bind (TracefulIk.getKey p j _) fun _ _ =>
    TracefulIk.bind (TracefulIk.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulIk.sendMessage _

theorem tracefulIk_compromiseSPK (p : Participant) (j : Nat) :
    TracefulIk (fun _ => True) (DY.Libsignal.PQXDH.compromiseSPK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  exact TracefulIk.bind (TracefulIk.getKey p j _) fun _ _ =>
    TracefulIk.bind (TracefulIk.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulIk.sendMessage _

theorem tracefulIk_compromisePQSPK (p : Participant) (j : Nat) :
    TracefulIk (fun _ => True) (DY.Libsignal.PQXDH.compromisePQSPK p j) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  exact TracefulIk.bind (TracefulIk.getKey p j _) fun _ _ =>
    TracefulIk.bind (TracefulIk.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulIk.sendMessage _

theorem tracefulIk_compromiseOPK (p : Participant) (j : Nat) :
    TracefulIk (fun _ => True) (DY.Libsignal.PQXDH.compromiseOPK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  exact TracefulIk.bind (TracefulIk.getKey p j _) fun _ _ =>
    TracefulIk.bind (tracefulIk_guardOnTrace _) fun _ _ =>
    TracefulIk.bind (TracefulIk.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulIk.sendMessage _

theorem tracefulIk_registerIdentity (p : Participant) :
    TracefulIk (fun _ => True) (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine TracefulIk.bind (tracefulIk_guardOnTrace _) fun _ _ =>
    TracefulIk.bind TracefulIk.genRand_shapeId fun ik hik =>
    TracefulIk.bind (TracefulIk.logEventPQ ?_) fun _ _ =>
    TracefulIk.bind (TracefulIk.sendMessage _) fun _ _ =>
    TracefulIk.bind (TracefulIk.sendMessage _) fun _ _ =>
    TracefulIk.storeLocalStatePQ p (fun _ => hik)
  intro _ _ _ _ h
  cases h
  exact Symbolic.Swarm.CREF.TR.G1.shapeId_dhPk hik

theorem tracefulIk_genSignedPrekey (b : Participant) (j : Nat) :
    TracefulIk (fun _ => True) (DY.Libsignal.PQXDH.genSignedPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  exact TracefulIk.bind (TracefulIk.getKey b j _) fun _ _ =>
    TracefulIk.bind (TracefulIk.genRand 32) fun _ _ =>
    TracefulIk.bind (TracefulIk.genRand 64) fun _ _ =>
    TracefulIk.bind (TracefulIk.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulIk.bind (TracefulIk.storeLocalStatePQ b fun h => by cases h) fun _ _ =>
    TracefulIk.bind (TracefulIk.sendMessage _) fun _ _ =>
    TracefulIk.bind (TracefulIk.sendMessage _) fun _ _ => TracefulIk.pure trivial

theorem tracefulIk_genPQPrekey (b : Participant) (j : Nat) :
    TracefulIk (fun _ => True) (DY.Libsignal.PQXDH.genPQPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  exact TracefulIk.bind (TracefulIk.getKey b j _) fun _ _ =>
    TracefulIk.bind (TracefulIk.genRand 64) fun _ _ =>
    TracefulIk.bind (TracefulIk.genRand 64) fun _ _ =>
    TracefulIk.bind (TracefulIk.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulIk.bind (TracefulIk.storeLocalStatePQ b fun h => by cases h) fun _ _ =>
    TracefulIk.bind (TracefulIk.sendMessage _) fun _ _ =>
    TracefulIk.bind (TracefulIk.sendMessage _) fun _ _ => TracefulIk.pure trivial

theorem tracefulIk_genOneTimePrekey (b : Participant) :
    TracefulIk (fun _ => True) (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  exact TracefulIk.bind (TracefulIk.genRand 32) fun _ _ =>
    TracefulIk.bind (TracefulIk.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulIk.bind (TracefulIk.storeLocalStatePQ b fun h => by cases h) fun _ _ =>
    TracefulIk.bind (TracefulIk.sendMessage _) fun _ _ => TracefulIk.pure trivial

theorem tracefulIk_setupAct (a b : Participant) (withOpk : Bool) :
    TracefulIk (fun _ => True) (setupAct a b withOpk) := by
  unfold setupAct
  apply TracefulIk.bind (Q₁ := fun _ => True) (tracefulIk_registerIdentity a)
  intro _ _
  apply TracefulIk.bind (Q₁ := fun _ => True) (tracefulIk_registerIdentity b)
  intro hB _
  apply TracefulIk.bind (Q₁ := fun _ => True) (tracefulIk_genSignedPrekey b hB)
  intro _ _
  apply TracefulIk.bind (Q₁ := fun _ => True) (tracefulIk_genPQPrekey b hB)
  intro _ _
  split
  · apply TracefulIk.bind (Q₁ := fun _ => True) (tracefulIk_genOneTimePrekey b)
    intro _ _
    exact TracefulIk.pure trivial
  · exact TracefulIk.pure trivial

theorem tracefulIk_aliceHandshake (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulIk (fun (o : DY.Libsignal.PQXDH.AliceHandshakeOut) => ShapeId o.ikA ∧ ShapeId o.ikB)
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  apply TracefulIk.bind (TracefulIk.getKey a idStateIdx _); intro ikA hikA
  apply TracefulIk.bind (TracefulIk.lookupIdentity b regIdxB); intro ikv hikB
  rcases ikv with ⟨ikB, vkB⟩
  dsimp only at hikB ⊢
  apply TracefulIk.bind (TracefulIk.receiveMessage h.spk); intro spk _
  apply TracefulIk.bind (TracefulIk.receiveMessage h.spkSig); intro _ _
  apply TracefulIk.bind (TracefulIk.receiveMessage h.pqpk); intro pqpk _
  apply TracefulIk.bind (TracefulIk.receiveMessage h.pqpkSig); intro _ _
  apply TracefulIk.bind (TracefulIk.guardP _); intro _ _
  apply TracefulIk.bind (TracefulIk.guardP _); intro _ _
  split
  all_goals first
    | (apply TracefulIk.bind (TracefulIk.receiveMessage _); intro _ _)
    | skip
  all_goals
    apply TracefulIk.bind (TracefulIk.pure (Q := fun _ => True) trivial)
    intro opk _
    apply TracefulIk.bind (TracefulIk.genRand 32); intro ek _
    apply TracefulIk.bind (TracefulIk.guardP _); intro _ _
    apply TracefulIk.bind (TracefulIk.guardP _); intro _ _
    apply TracefulIk.bind (TracefulIk.genRand 32); intro entropy _
    rcases DY.Libsignal.PQXDH.aliceAgreement ikA ek ikB spk pqpk opk entropy with ⟨ct, keys⟩
    try dsimp only
    exact TracefulIk.pure ⟨Symbolic.Swarm.CREF.TR.G1.shapeId_dhPk (hikA rfl), hikB⟩

theorem tracefulIk_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulIk (fun _ => True)
      (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine TracefulIk.bind (tracefulIk_aliceHandshake a b idStateIdx regIdxB h) fun o ho =>
    TracefulIk.bind (TracefulIk.genRand 32) fun dhsA _ => ?_
  rcases createChain o.keys.rk o.spk dhsA with ⟨rkA, cksA⟩
  dsimp only
  refine TracefulIk.bind (TracefulIk.sendMessage _) fun _ _ =>
    TracefulIk.bind (TracefulIk.sendMessage _) fun _ _ =>
    TracefulIk.bind tracefulIk_traceLength fun _ _ =>
    TracefulIk.bind (TracefulIk.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ =>
    TracefulIk.bind (TracefulIk.logEvent _) fun _ _ =>
    TracefulIk.bind (TracefulIk.logEventC _) fun _ _ =>
    TracefulIk.storeLocalState a
      ⟨Symbolic.Swarm.CREF.TR.G1.shapeId_concat
        (Symbolic.Swarm.CREF.TR.G1.shapeId_literalToBytes _) ho.1,
       Symbolic.Swarm.CREF.TR.G1.shapeId_concat
        (Symbolic.Swarm.CREF.TR.G1.shapeId_literalToBytes _) ho.2⟩

theorem tracefulIk_bobHandshake (b a : Participant)
    (h : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    TracefulIk (fun (o : DY.Libsignal.PQXDH.BobHandshakeOut) => ShapeId o.ikA ∧ ShapeId o.ikB)
      (DY.Libsignal.PQXDH.bobHandshake b a h regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  apply TracefulIk.bind (TracefulIk.getKey b h.ik _); intro ikB hikB
  apply TracefulIk.bind (TracefulIk.getKey b h.spk _); intro spkSk _
  apply TracefulIk.bind (TracefulIk.getKey b h.pqspk _); intro pqsk _
  dsimp only
  split
  all_goals first
    | (apply TracefulIk.bind (TracefulIk.getKey b _ _); intro _ _)
    | skip
  all_goals
    apply TracefulIk.bind (TracefulIk.pure (Q := fun _ => True) trivial)
    intro opkSk _
    apply TracefulIk.bind (TracefulIk.lookupIdentity a regIdxA); intro ikv hikA
    rcases ikv with ⟨ikA, vkA⟩
    dsimp only at hikA ⊢
    apply TracefulIk.bind (TracefulIk.receiveMessage ekIdx); intro ek _
    apply TracefulIk.bind (TracefulIk.receiveMessage ctIdx); intro ct _
    apply TracefulIk.bind (TracefulIk.guardP _); intro _ _
    split
    · exact TracefulIk.pure ⟨hikA, Symbolic.Swarm.CREF.TR.G1.shapeId_dhPk (hikB rfl)⟩
    · exact TracefulIk.failure

theorem tracefulIk_bobStart (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulIk (fun _ => True)
      (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine TracefulIk.bind (tracefulIk_bobHandshake b a kh regIdxA mh.ek mh.ct) fun o ho =>
    TracefulIk.bind (tracefulIk_receiveSignalMsg mh.msg) fun msg _ => ?_
  refine TracefulIk.bind (tracefulIk_ensureReceiverChain msg.ratchetKey ?hst0)
    fun x hst => ?_
  case hst0 =>
    exact ⟨Symbolic.Swarm.CREF.TR.G1.shapeId_concat
      (Symbolic.Swarm.CREF.TR.G1.shapeId_literalToBytes _) ho.2,
     Symbolic.Swarm.CREF.TR.G1.shapeId_concat
      (Symbolic.Swarm.CREF.TR.G1.shapeId_literalToBytes _) ho.1⟩
  rcases x with ⟨st, c, ratcheted⟩
  dsimp only at hst ⊢
  split
  · next seed c' _ =>
    split
    · next spqr' key _ =>
      refine TracefulIk.bind (TracefulIk.sendMessage key) fun _ _ =>
        TracefulIk.bind (TracefulIk.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulIk.bind (tracefulIk_verifyMacAndDecrypt st msg pqSalt seed) fun m _ => ?_
      split
      all_goals first
        | refine TracefulIk.bind (tracefulIk_guardOnTrace _) fun _ _ =>
            TracefulIk.bind (TracefulIk.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ => ?_
        | skip
      all_goals refine TracefulIk.bind tracefulIk_traceLength fun _ _ =>
        TracefulIk.bind (TracefulIk.logEventPQ fun _ _ _ _ h => by cases h) fun _ _ => ?_
      all_goals split
      all_goals first
        | refine TracefulIk.bind (TracefulIk.logEvent _) fun _ _ =>
            TracefulIk.bind (TracefulIk.logEvent _) fun _ _ => ?_
        | skip
      all_goals exact TracefulIk.bind (TracefulIk.logEventC _) fun _ _ =>
          TracefulIk.bind tracefulIk_traceLength fun _ _ =>
          TracefulIk.bind (tracefulIk_logSkippedKeys _ _ _ _ _ _ _) fun _ _ =>
          TracefulIk.bind (TracefulIk.logEvent _) fun _ _ =>
          tracefulIk_logMessageKeyAndStore b _ .receiver _ _ _ _ _ hst
    · exact TracefulIk.failure
  · exact TracefulIk.failure

theorem shapeId_serializedIk {pk : DY.Bytes} (hpk : ShapeId pk) :
    ShapeId (DY.Libsignal.PQXDH.serializedIk pk) :=
  Symbolic.Swarm.CREF.TR.G1.shapeId_concat
    (Symbolic.Swarm.CREF.TR.G1.shapeId_literalToBytes _) hpk

/-! ## Moves induction -/

theorem traceIkOk_move_next {tr : ExecTrace} {m : Move} (htr : TraceIkOk tr) :
    TraceIkOk (m.next tr) := by
  unfold Move.next Move.act
  cases m with
  | setup a b withOpk => exact (tracefulIk_setupAct a b withOpk tr htr).1
  | aliceStart a b idStateIdx regIdxB h _ =>
    exact tracefulIk_run_snd (tracefulIk_aliceStart a b idStateIdx regIdxB h) htr
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ =>
    exact tracefulIk_run_snd (tracefulIk_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) htr
  | encrypt me stateIdx coinsLen pqIdx _ =>
    exact tracefulIk_run_snd (tracefulIk_messageEncrypt me stateIdx coinsLen pqIdx) htr
  | encryptAbort me stateIdx =>
    exact tracefulIk_run_snd (tracefulIk_messageEncryptAbort me stateIdx) htr
  | encryptFail me stateIdx coinsLen =>
    dsimp only
    have h_assoc :
        ((do let n ← traceLength; let _ ← messageEncrypt me stateIdx coinsLen (n + 3); Pure.pure ()).run tr).2.val =
        (((do let n ← traceLength; messageEncrypt me stateIdx coinsLen (n + 3)) >>= fun _ => Pure.pure ()).run tr).2.val := by
      rw [run_bind_snd_ik, run_bind_snd_ik, run_bind_fst_ik]
      rcases ht : (traceLength.run tr).1 with _ | n
      · dsimp only; rw [run_bind_snd_ik, ht]
      · dsimp only; rw [run_bind_snd_ik, run_bind_snd_ik, ht]
    rw [h_assoc]
    exact tracefulIk_run_snd
      (TracefulIk.bind tracefulIk_traceLength
        fun n _ => tracefulIk_messageEncrypt me stateIdx coinsLen (n + 3)) htr
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ =>
    exact tracefulIk_run_snd (tracefulIk_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) htr
  | decryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ =>
    exact tracefulIk_run_snd
      (tracefulIk_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) htr
  | reject _ =>
    dsimp only
    rw [Traceful.run_pure]
    exact htr
  | compromiseIK p stateIdx =>
    exact tracefulIk_run_snd (tracefulIk_compromiseIK p stateIdx) htr
  | compromiseSPK p stateIdx =>
    exact tracefulIk_run_snd (tracefulIk_compromiseSPK p stateIdx) htr
  | compromisePQSPK p stateIdx =>
    exact tracefulIk_run_snd (tracefulIk_compromisePQSPK p stateIdx) htr
  | compromiseOPK p stateIdx =>
    exact tracefulIk_run_snd (tracefulIk_compromiseOPK p stateIdx) htr
  | exposeKey me stateIdx k =>
    exact tracefulIk_run_snd (tracefulIk_exposeKey me stateIdx k) htr
  | exposeSpqr me stateIdx =>
    exact tracefulIk_run_snd (tracefulIk_exposeSpqr me stateIdx) htr
  | exposeSkipped skippedKeyEventIdx =>
    exact tracefulIk_run_snd (tracefulIk_exposeSkipped skippedKeyEventIdx) htr
  | attackerSend msg =>
    exact tracefulIk_run_snd (TracefulIk.sendMessage msg) htr
  | brkDH =>
    exact (TracefulIk.logEventPQ (ev := .BrokenDH) (fun _ _ _ _ h => by cases h) tr htr).1
  | brkKEM =>
    exact (TracefulIk.logEventPQ (ev := .BrokenKEM) (fun _ _ _ _ h => by cases h) tr htr).1

theorem traceIkOk_runMoves :
    ∀ (L : List Move) (tr : ExecTrace), TraceIkOk tr → TraceIkOk (runMoves L tr).1
  | [], _, htr => htr
  | _ :: ms, _, htr => traceIkOk_runMoves ms _ (traceIkOk_move_next htr)

theorem traceIkOk_runTrace (r₀ : ProtocolSetup) (ms : List Move) : TraceIkOk (runTraceMoves r₀ ms) :=
  traceIkOk_runMoves (r₀.setupMove :: ms) DY.Trace.nil traceIkOk_nil

theorem trStateIkOk_of_mem_availableStates {r₀ : ProtocolSetup} {tr : ExecTrace} (htr : TraceIkOk tr)
    {st : TRState} (hst : st ∈ availableStates r₀ tr) : TrStateIkOk st := by
  unfold availableStates storedStates DY.ExecTrace.getLocalStateAt at hst
  obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hst
  obtain ⟨j, _, he⟩ := List.mem_filterMap.mp hls
  simp only [Option.map_eq_some_iff] at he
  obtain ⟨e, hat, rfl⟩ := he
  unfold DY.Trace.at? at hat
  split at hat
  · next hj => exact (htr j hj).1 e hat
  · cases hat

/-- Every available session state on `runTraceMoves r₀ ms` has `ShapeId` identity keys. -/
theorem availableIkShapeId_all (r₀ : ProtocolSetup) (ms : List Move) :
    ∀ st ∈ availableStates r₀ (runTraceMoves r₀ ms), ShapeId st.myIk ∧ ShapeId st.peerIk :=
  fun _ hst => trStateIkOk_of_mem_availableStates (traceIkOk_runTrace r₀ ms) hst

end Symbolic.Swarm.CREF.TR.G1.Ik
