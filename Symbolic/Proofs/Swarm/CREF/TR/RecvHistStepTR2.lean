/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvHistStepTR
import DY.Trace.Basic
import DY.Trace.Monad
import DY.ALaCarte.Basic
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Stage1Wire
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Trace-Level Preservation of Receiver Ratchet-Key History

Introduces `TraceStatesP` and the monadic invariant combinator `TracefulP`, equates `RecvHistInvTR`
with `TraceStatesP (RecvNodupP ...)` over `runTraceMoves`, and proves preservation across
`Move.encrypt`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR.RecvHistStep2

cref_open
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir)
open DY.Libsignal.TripleRatchet (TRState TREvent logMessageKeyAndStore
  messageEncrypt messageEncryptAbort)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent)
open CryptoProofLib.Refinement (ExternInterpretation)

private theorem runMoves_append_rhs2 (ms₁ ms₂ : List Move) (tr : ExecTrace) :
    runMoves (ms₁ ++ ms₂) tr =
      ((runMoves ms₂ (runMoves ms₁ tr).1).1,
        (runMoves ms₁ tr).2 ++ (runMoves ms₂ (runMoves ms₁ tr).1).2) := by
  induction ms₁ generalizing tr with
  | nil => simp [runMoves]
  | cons m ms₁ ih => simp only [List.cons_append, runMoves, ih, List.append_assoc]

private theorem runTrace_snoc_rhs2 (r₀ : ProtocolSetup) (ms : List Move) (m : Move) :
    runTraceMoves r₀ (ms ++ [m]) = m.next (runTraceMoves r₀ ms) := by
  unfold runTraceMoves
  rw [← List.cons_append, runMoves_append_rhs2]
  rfl

abbrev StEntry := PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)

/-! ## `TraceStatesP` and `TracefulP` -/

/-- A trace entry whose stored `TRState` (if it is a `StEntry`) satisfies `P`. -/
def EntryStatesP (P : TRState → Prop) (ent : ExecTrace.Entry) : Prop :=
  ∀ e : StEntry, TraceEntryHas.proj ent = some e → P e.st.state

/-- Every stored `TRState` entry on `tr` satisfies `P`. -/
def TraceStatesP (P : TRState → Prop) (tr : ExecTrace) : Prop :=
  ∀ j (hj : j < tr.length), EntryStatesP P (tr.at j hj)

theorem traceStatesP_append {P : TRState → Prop} {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hent : EntryStatesP P (TraceEntryHas.inj e))
    (htr : TraceStatesP P tr) :
    TraceStatesP P (tr.append e) := by
  intro j hj
  by_cases hlt : j < tr.length
  · rw [← DY.Trace.at_le tr (tr.append e) j hlt (DY.Trace.append_le tr e)]
    exact htr j hlt
  · have heq : j = tr.length := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hj
      omega
    subst heq
    simpa [Symbolic.DYBridge.DY.Trace.append_eq_1, DY.Trace.snoc, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.nil_length_not_lt, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] using hent

theorem traceStatesP_at?_st {P : TRState → Prop} {tr : ExecTrace} (htr : TraceStatesP P tr)
    {j : Nat} {e : StEntry} (h : (tr.at? j : Option StEntry) = some e) :
    P e.st.state := by
  unfold DY.Trace.at? at h
  split at h
  · next hj => exact htr j hj e h
  · cases h

theorem traceStatesP_of_at? {P : TRState → Prop} {tr : ExecTrace}
    (h : ∀ j (e : StEntry), (tr.at? j : Option StEntry) = some e → P e.st.state) :
    TraceStatesP P tr := by
  intro j hj e he
  refine h j e ?_
  simp only [DY.Trace.at?, hj, ↓reduceDIte]
  exact he

/-- Monad combinator: running `x` from a `TraceStatesP P` trace preserves `TraceStatesP P` and
establishes `Q` on any returned value. -/
def TracefulP (P : TRState → Prop) {α : Type} (Q : α → Prop) (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, TraceStatesP P tr →
    TraceStatesP P (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q a

theorem TracefulP.pure {P : TRState → Prop} {α : Type} {Q : α → Prop} {a : α} (ha : Q a) :
    TracefulP P Q (Pure.pure a) := by
  unfold TracefulP
  intro tr htr
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1]
  refine ⟨htr, fun b hb => ?_⟩
  cases hb
  exact ha

theorem TracefulP.failure {P : TRState → Prop} {α : Type} {Q : α → Prop} :
    TracefulP P Q (failure : Traceful α) := by
  unfold TracefulP
  intro tr htr
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨htr, fun _ hb => by cases hb⟩

theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem TracefulP.bind {P : TRState → Prop} {α β : Type} {Q₁ : α → Prop} {Q₂ : β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulP P Q₁ x) (hf : ∀ a, Q₁ a → TracefulP P Q₂ (f a)) :
    TracefulP P Q₂ (x >>= f) := by
  intro tr htr
  rw [run_bind_snd, run_bind_fst]
  have h1 := hx tr htr
  cases hres : (x.run tr).1 with
  | none => exact ⟨h1.1, fun _ hb => by cases hb⟩
  | some a => exact hf a (h1.2 a hres) (x.run tr).2.val h1.1

theorem tracefulP_run_snd {P : TRState → Prop} {α : Type} {Q : α → Prop} {x : Traceful α}
    (hx : TracefulP P Q x) {tr : ExecTrace} (htr : TraceStatesP P tr) :
    TraceStatesP P ((x >>= fun _ => Pure.pure ()).run tr).2.val :=
  (TracefulP.bind hx (fun _ _ => TracefulP.pure (Q := fun _ => True) trivial) tr htr).1

theorem TracefulP.guardP {P : TRState → Prop} (p : Prop) [Decidable p] :
    TracefulP P (fun _ => True) (_root_.guard p) := by
  unfold _root_.guard
  split
  · exact TracefulP.pure trivial
  · exact TracefulP.failure

theorem tracefulP_traceLength {P : TRState → Prop} :
    TracefulP P (fun _ => True) TripleRatchet.traceLength := by
  unfold TracefulP TripleRatchet.traceLength
  intro tr htr
  simp only [DY.Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulP.getEntry_any {P : TRState → Prop} {E : Type} [ExecTraceTypes.Has E] (j : Nat) :
    TracefulP P (fun _ : E => True) (getEntry j : Traceful E) := by
  unfold TracefulP
  intro tr htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]
  exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulP.getEntry_st {P : TRState → Prop} (j : Nat) :
    TracefulP P (fun e : StEntry => P e.st.state) (getEntry j) := by
  unfold TracefulP
  intro tr htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]
  exact ⟨htr, fun e he => traceStatesP_at?_st htr he⟩

theorem TracefulP.receiveMessage {P : TRState → Prop} (j : Nat) :
    TracefulP P (fun _ => True) (Network.receiveMessage j) := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact TracefulP.bind (TracefulP.getEntry_any j) fun _ _ => TracefulP.pure trivial

theorem TracefulP.getLocalState {P : TRState → Prop} (p : Participant) (j : Nat) :
    TracefulP P P (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine TracefulP.bind
    (TracefulP.bind (TracefulP.getEntry_st j) fun _ he =>
      TracefulP.pure (Q := fun ls : PersistentLocalState.LocalState TRState => P ls.state) he)
    fun _ hst => ?_
  exact TracefulP.bind (TracefulP.guardP _) fun _ _ => TracefulP.pure hst

theorem TracefulP.genRand {P : TRState → Prop} (n : Nat) :
    TracefulP P (fun _ => True) (DY.Random.genRand n) := by
  unfold TracefulP
  intro tr htr
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceStatesP_append (fun _ h => by cases h) htr, fun _ _ => trivial⟩

theorem TracefulP.sendMessage {P : TRState → Prop} (msg : DY.Bytes) :
    TracefulP P (fun _ => True) (Network.sendMessage msg) := by
  unfold TracefulP
  intro tr htr
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_mk]
  exact ⟨traceStatesP_append (fun _ h => by cases h) htr, fun _ _ => trivial⟩

theorem TracefulP.logEvent {P : TRState → Prop} (ev : TREvent) :
    TracefulP P (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulP
  intro tr htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceStatesP_append (fun _ h => by cases h) htr, fun _ _ => trivial⟩

theorem TracefulP.logEventPQ {P : TRState → Prop} (ev : PQXDHEvent) :
    TracefulP P (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulP
  intro tr htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact ⟨traceStatesP_append (fun _ h => by cases h) htr, fun _ _ => trivial⟩

theorem TracefulP.storeLocalStatePQ {P : TRState → Prop} (p : Participant) (st : PQXDHState) :
    TracefulP P (fun _ => True) (PersistentLocalState.storeLocalState p st) := by
  unfold TracefulP
  intro tr htr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_mk]
  exact ⟨traceStatesP_append (fun _ h => by cases h) htr, fun _ _ => trivial⟩

theorem TracefulP.storeLocalState {P : TRState → Prop} (p : Participant) {st : TRState}
    (hst : P st) :
    TracefulP P (fun _ => True) (PersistentLocalState.storeLocalState p st) := by
  unfold TracefulP
  intro tr htr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_mk]
  refine ⟨traceStatesP_append ?_ htr, fun _ _ => trivial⟩
  intro e h
  have hinj : (TraceEntryHas.proj (TraceEntryHas.inj (⟨⟨p, st⟩⟩ : StEntry) : ExecTrace.Entry) : Option StEntry) =
      some ⟨⟨p, st⟩⟩ := rfl
  rw [hinj] at h
  injection h with h
  subst h
  exact hst

theorem tracefulP_logMessageKeyAndStore {P : TRState → Prop} (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) {st : TRState}
    (hst : P st) :
    TracefulP P (fun _ => True)
      (logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold logMessageKeyAndStore
  exact TracefulP.bind (TracefulP.logEvent _) fun _ _ =>
    TracefulP.storeLocalState me hst

/-- `P` depends only on the receiver chains `recv`. -/
def RecvDetermined (P : TRState → Prop) : Prop :=
  ∀ st st' : TRState, st'.recv = st.recv → P st → P st'

theorem tracefulP_messageEncrypt {P : TRState → Prop} (hP : RecvDetermined P)
    (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    TracefulP P (fun _ => True) (messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold messageEncrypt
  refine TracefulP.bind (TracefulP.getLocalState me stateIdx) fun st hst =>
    TracefulP.bind (TracefulP.guardP _) fun _ _ =>
    TracefulP.bind (TracefulP.genRand 32) fun _ _ =>
    TracefulP.bind (TracefulP.genRand coinsLen) fun _ _ =>
    TracefulP.bind (TracefulP.sendMessage _) fun _ _ =>
    TracefulP.bind (TracefulP.receiveMessage pqIdx) fun _ _ =>
    TracefulP.bind (TracefulP.logEvent _) fun _ _ => ?_
  refine TracefulP.bind
    (tracefulP_logMessageKeyAndStore me _ .sender _ _ _ _ _ ?_)
    fun _ _ => TracefulP.sendMessage _
  refine hP st _ ?_ hst
  rfl

theorem tracefulP_messageEncryptAbort {P : TRState → Prop} (me : Participant) (stateIdx : Nat) :
    TracefulP P (fun _ => True) (messageEncryptAbort me stateIdx) := by
  unfold messageEncryptAbort
  exact TracefulP.bind (TracefulP.getLocalState me stateIdx) fun _ _ =>
    TracefulP.bind (TracefulP.genRand 32) fun _ _ => TracefulP.failure

/-! ## Equivalence Between `RecvHistInvTR` and `TraceStatesP` -/

/-- The receiver chains of `st` have pairwise distinct concretized ratchet keys at ghost `g`. -/
def RecvNodupP (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (st : TRState) :
    Prop :=
  (st.recv.map fun c => gamma interpretation S g c.ratchetKey).Nodup

theorem recvDetermined_recvNodupP (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) : RecvDetermined (RecvNodupP interpretation S g) := by
  intro st st' heq h
  unfold RecvNodupP at h ⊢
  rw [heq]
  exact h

theorem TracefulP.requireTracePredicate {P : TRState → Prop} (p : ExecTrace → Bool) :
    TracefulP P (fun _ => True) (PQXDH.guardTrace p) := by
  intro tr htr
  unfold PQXDH.guardTrace
  simp only [Traceful.run_mk]
  split <;> exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulP.getKey {P : TRState → Prop} (me : Participant) (h : Nat)
    (kind : PQXDH.KeyKind) :
    TracefulP P (fun _ => True) (PQXDH.getKey me h kind) := by
  (unfold PQXDH.getKey; simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1])
  exact TracefulP.bind (Q₂ := fun _ => True)
    (TracefulP.bind (Q₂ := fun _ => True)
      (TracefulP.bind (Q₂ := fun _ => True) (TracefulP.getEntry_any h)
        fun _ _ => TracefulP.pure (Q := fun _ => True) trivial)
      fun _ _ => TracefulP.bind (Q₂ := fun _ => True) (TracefulP.guardP _)
        fun _ _ => TracefulP.pure (Q := fun _ => True) trivial)
    fun _ _ => TracefulP.bind (Q₂ := fun _ => True) (TracefulP.guardP _)
      fun _ _ => TracefulP.pure (Q := fun _ => True) trivial

theorem tracefulP_registerIdentity {P : TRState → Prop} (p : Participant) :
    TracefulP P (fun _ => True) (PQXDH.registerIdentity p) := by
  unfold PQXDH.registerIdentity
  exact TracefulP.bind (TracefulP.requireTracePredicate _) fun _ _ =>
    TracefulP.bind (TracefulP.genRand _) fun _ _ =>
    TracefulP.bind (TracefulP.logEventPQ _) fun _ _ =>
    TracefulP.bind (TracefulP.sendMessage _) fun _ _ =>
    TracefulP.bind (TracefulP.sendMessage _) fun _ _ =>
      TracefulP.storeLocalStatePQ _ _

theorem tracefulP_genSignedPrekey {P : TRState → Prop} (p : Participant) (idx : Nat) :
    TracefulP P (fun _ => True) (PQXDH.genSignedPrekey p idx) := by
  unfold PQXDH.genSignedPrekey
  exact TracefulP.bind (TracefulP.getKey p idx _) fun _ _ =>
    TracefulP.bind (TracefulP.genRand _) fun _ _ =>
    TracefulP.bind (TracefulP.genRand _) fun _ _ =>
    TracefulP.bind (TracefulP.logEventPQ _) fun _ _ =>
    TracefulP.bind (TracefulP.storeLocalStatePQ _ _) fun _ _ =>
    TracefulP.bind (TracefulP.sendMessage _) fun _ _ =>
    TracefulP.bind (TracefulP.sendMessage _) fun _ _ =>
      TracefulP.pure (Q := fun _ => True) trivial

theorem tracefulP_genPQPrekey {P : TRState → Prop} (p : Participant) (idx : Nat) :
    TracefulP P (fun _ => True) (PQXDH.genPQPrekey p idx) := by
  unfold PQXDH.genPQPrekey
  exact TracefulP.bind (TracefulP.getKey p idx _) fun _ _ =>
    TracefulP.bind (TracefulP.genRand _) fun _ _ =>
    TracefulP.bind (TracefulP.genRand _) fun _ _ =>
    TracefulP.bind (TracefulP.logEventPQ _) fun _ _ =>
    TracefulP.bind (TracefulP.storeLocalStatePQ _ _) fun _ _ =>
    TracefulP.bind (TracefulP.sendMessage _) fun _ _ =>
    TracefulP.bind (TracefulP.sendMessage _) fun _ _ =>
      TracefulP.pure (Q := fun _ => True) trivial

theorem tracefulP_genOneTimePrekey {P : TRState → Prop} (p : Participant) :
    TracefulP P (fun _ => True) (PQXDH.genOneTimePrekey p) := by
  unfold PQXDH.genOneTimePrekey
  exact TracefulP.bind (TracefulP.genRand _) fun _ _ =>
    TracefulP.bind (TracefulP.logEventPQ _) fun _ _ =>
    TracefulP.bind (TracefulP.storeLocalStatePQ _ _) fun _ _ =>
    TracefulP.bind (TracefulP.sendMessage _) fun _ _ =>
      TracefulP.pure (Q := fun _ => True) trivial

theorem traceStatesP_setupTrace {P : TRState → Prop} (r₀ : ProtocolSetup) :
    TraceStatesP P (setupTrace r₀) := by
  have hnil : TraceStatesP P Trace.nil := fun j hj =>
    absurd hj (Symbolic.DYBridge.DY.Trace.nil_length_not_lt j)
  have hact : TracefulP P (fun _ => True) (setupAct r₀.alice r₀.bob r₀.withOpk) := by
    unfold setupAct
    refine TracefulP.bind (Q₂ := fun _ => True) (tracefulP_registerIdentity r₀.alice) fun _ _ =>
      TracefulP.bind (Q₂ := fun _ => True) (tracefulP_registerIdentity r₀.bob) fun _ _ =>
      TracefulP.bind (Q₂ := fun _ => True) (tracefulP_genSignedPrekey r₀.bob _) fun _ _ =>
      TracefulP.bind (Q₂ := fun _ => True) (tracefulP_genPQPrekey r₀.bob _) fun _ _ => ?_
    split
    · exact TracefulP.bind (Q₂ := fun _ => True) (tracefulP_genOneTimePrekey r₀.bob) fun _ _ =>
        TracefulP.pure (Q := fun _ => True) trivial
    · exact TracefulP.pure (Q := fun _ => True) trivial
  exact (hact Trace.nil hnil).1

theorem le_runMoves_fst : ∀ (ms : List Move) (tr : ExecTrace), tr ≤ (runMoves ms tr).1
  | [], tr => Trace.le_refl tr
  | m :: ms, tr => by
    unfold runMoves
    exact Trace.le_trans tr (m.next tr) (runMoves ms (m.next tr)).1
      (m.act.run tr).2.property (le_runMoves_fst ms (m.next tr))

/-- A stored snapshot of the run trace is an available state (`setupTrace r₀` stores no `TRState`). -/
theorem mem_availableStates_of_at? (r₀ : ProtocolSetup) (ms : List Move) {j : Nat} {e : StEntry}
    (he : ((runTraceMoves r₀ ms).at? j : Option StEntry) = some e) :
    e.st.state ∈ availableStates r₀ (runTraceMoves r₀ ms) := by
  have hlt : j < (runTraceMoves r₀ ms).length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) (runTraceMoves r₀ ms) j
    rw [he] at this; exact this
  have hge : (setupTrace r₀).length ≤ j := by
    by_contra hlt0
    have hlt0' : j < (setupTrace r₀).length := Nat.lt_of_not_ge hlt0
    have hle : setupTrace r₀ ≤ runTraceMoves r₀ ms := by
      unfold runTraceMoves setupTrace
      exact le_runMoves_fst ms _
    have hat0 : ((setupTrace r₀).at? j : Option StEntry) = some e := by
      simp only [Trace.at?, hlt0', hlt, ↓reduceDIte] at he ⊢
      rw [Trace.at_le (setupTrace r₀) (runTraceMoves r₀ ms) j hlt0' hle]
      exact he
    exact traceStatesP_at?_st (traceStatesP_setupTrace (P := fun _ => False) r₀) hat0
  unfold availableStates
  rw [List.mem_map]
  refine ⟨e.st, ?_, rfl⟩
  unfold storedStates DY.Libsignal.Composed.Refinement.newIndices DY.ExecTrace.getLocalStateAt
  rw [List.mem_filterMap]
  refine ⟨j, List.mem_range'.mpr ⟨j - (setupTrace r₀).length, by omega, by omega⟩, ?_⟩
  rw [he]; rfl

theorem traceStatesP_runTrace_of_forall {P : TRState → Prop} (r₀ : ProtocolSetup) (ms : List Move)
    (h : ∀ st ∈ availableStates r₀ (runTraceMoves r₀ ms), P st) :
    TraceStatesP P (runTraceMoves r₀ ms) :=
  traceStatesP_of_at? fun _ _ he => h _ (mem_availableStates_of_at? r₀ ms he)

theorem forall_availableStates_of_traceStatesP {P : TRState → Prop} (r₀ : ProtocolSetup)
    {tr : ExecTrace} (htr : TraceStatesP P tr) :
    ∀ st ∈ availableStates r₀ tr, P st := by
  intro st hst
  unfold availableStates at hst
  obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hst
  unfold storedStates DY.Libsignal.Composed.Refinement.newIndices DY.ExecTrace.getLocalStateAt at hls
  obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hls
  cases he : (tr.at? i : Option StEntry) with
  | none => rw [he] at hi; cases hi
  | some e =>
    rw [he] at hi
    injection hi with hi
    subst hi
    exact traceStatesP_at?_st htr he

theorem traceStatesP_of_recvHistInvTR {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {r₀ : ProtocolSetup} {ms : List Move}
    (h : Symbolic.Swarm.CREF.TR.G1.RecvHistInvTR interpretation S g r₀ ms) :
    TraceStatesP (RecvNodupP interpretation S g) (runTraceMoves r₀ ms) :=
  traceStatesP_runTrace_of_forall r₀ ms h

theorem recvHistInvTR_of_traceStatesP {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {r₀ : ProtocolSetup} {ms : List Move}
    (h : TraceStatesP (RecvNodupP interpretation S g) (runTraceMoves r₀ ms)) :
    Symbolic.Swarm.CREF.TR.G1.RecvHistInvTR interpretation S g r₀ ms :=
  forall_availableStates_of_traceStatesP r₀ h

/-! ## Preservation Across `Move.encrypt` -/

theorem recvHistInvTR_snoc_of_traceStatesP {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {r₀ : ProtocolSetup} {ms : List Move} {m : Move}
    (hstep : ∀ tr, TraceStatesP (RecvNodupP interpretation S g) tr →
      TraceStatesP (RecvNodupP interpretation S g) (m.next tr))
    (h : Symbolic.Swarm.CREF.TR.G1.RecvHistInvTR interpretation S g r₀ ms) :
    Symbolic.Swarm.CREF.TR.G1.RecvHistInvTR interpretation S g r₀ (ms ++ [m]) := by
  apply recvHistInvTR_of_traceStatesP
  rw [runTrace_snoc_rhs2]
  exact hstep _ (traceStatesP_of_recvHistInvTR h)

theorem traceStatesP_encrypt_next {P : TRState → Prop} (hP : RecvDetermined P)
    (me : Participant) (stateIdx coinsLen pqIdx : Nat)
    (wrap : Option (Nat × Nat) := none) {tr : ExecTrace}
    (htr : TraceStatesP P tr) :
    TraceStatesP P ((Move.encrypt me stateIdx coinsLen pqIdx wrap).next tr) := by
  unfold Move.next Move.act
  exact tracefulP_run_snd (tracefulP_messageEncrypt hP me stateIdx coinsLen pqIdx) htr

/-- `Move.encrypt` preserves `RecvHistInvTR` at the same ghost. -/
theorem recvHistInvTR_encrypt {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {r₀ : ProtocolSetup} {ms : List Move}
    (me : Participant) (stateIdx coinsLen pqIdx : Nat)
    (wrap : Option (Nat × Nat) := none)
    (h : Symbolic.Swarm.CREF.TR.G1.RecvHistInvTR interpretation S g r₀ ms) :
    Symbolic.Swarm.CREF.TR.G1.RecvHistInvTR interpretation S g r₀
      (ms ++ [Move.encrypt me stateIdx coinsLen pqIdx wrap]) :=
  recvHistInvTR_snoc_of_traceStatesP
    (fun _ htr => traceStatesP_encrypt_next (recvDetermined_recvNodupP interpretation S g)
      me stateIdx coinsLen pqIdx wrap htr) h

end Symbolic.Swarm.CREF.TR.RecvHistStep2
