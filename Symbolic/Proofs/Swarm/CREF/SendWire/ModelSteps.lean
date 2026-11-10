/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.SendWire.Ghosts
import DY.Trace.Basic
import DY.Trace.Monad
import DY.ALaCarte.Basic
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Stage1Wire
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Trace and `ModelRun` Step Lemmas for `SendWire`

Proves `ExecTrace` step equations, visible-entry projections, and `ModelRun` preservation across
`Move.encryptAbort`, `Move.encryptFail`, and `Move.encrypt` (with or without prekey wrapping).
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.SendWire

cref_open
open DY DY.Comparse
open DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet (TRState TREvent SessionInfo isCurrentSnapshot skippedKeyUsedB
  receiverKeyUsedB anyEventOnTrace kdfCk u32Max)
open Symbolic.Swarm.CREF.Stage1Wire

abbrev StEntry := PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
abbrev TREntry := DY.ProtocolEvent.ExecEntryT TREvent

/-! ## `ExecTrace.at?` and `Traceful` step algebra -/

private theorem sw_append_length {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by rw [sw_append_length]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]

theorem at?_append_eq_some {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) {i : Nat} (hi : i = tr.length) :
    ((tr.append e).at? i : Option E) = some e := by
  subst hi; exact Trace.at?_append tr e

theorem at?_append_eq_none {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i = tr.length)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = none) :
    ((tr.append e).at? i : Option E2) = none := by
  subst hi; simp [Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_2, hnone]

theorem at?_eq_none_of_not_lt {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) {i : Nat}
    (h : ¬ i < tr.length) : (tr.at? i : Option E) = none := by
  simp [Trace.at?, h]

theorem at?_append_non_entry {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = none)
    (i : Nat) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  by_cases hlt : i < tr.length
  · exact at?_append_of_lt tr e hlt
  · by_cases heq : i = tr.length
    · rw [at?_append_eq_none tr e heq hnone, at?_eq_none_of_not_lt tr hlt]
    · have h1 : ¬ i < (tr.append e).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
      rw [at?_eq_none_of_not_lt _ h1, at?_eq_none_of_not_lt _ hlt]

private theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

private theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

theorem run_bind_pure_val {α : Type} (x : Traceful α) (tr : ExecTrace) :
    ((x >>= fun _ => pure ()).run tr).2.val = (x.run tr).2.val := by
  rw [run_bind_snd]
  rcases (x.run tr).1 with _ | _
  · rfl
  · rw [Traceful.run_pure]

theorem getLocalState_fst (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 =
      match (tr.at? stH : Option StEntry) with
      | some ⟨⟨p, st⟩⟩ => if p = me then some st else none
      | none => none := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1,
    Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [run_bind_fst, run_bind_fst, run_bind_snd, Traceful.run_mk]
  rcases (tr.at? stH : Option StEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · dsimp only
    rw [Traceful.run_pure]
    dsimp only
    rw [run_bind_fst]
    by_cases hp : p = me
    · simp only [_root_.guard, hp, ↓reduceIte, Traceful.run_pure]
    · simp only [_root_.guard, hp, ↓reduceIte, Traceful.run_failure]

theorem getLocalState_run_eq_self (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1,
    Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [run_bind_snd, run_bind_fst, run_bind_snd, Traceful.run_mk]
  rcases (tr.at? stH : Option StEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · dsimp only
    rw [Traceful.run_pure]
    dsimp only
    rw [run_bind_snd]
    by_cases hp : p = me
    · simp only [_root_.guard, hp, ↓reduceIte, Traceful.run_pure]
    · simp only [_root_.guard, hp, ↓reduceIte, Traceful.run_failure]

private def Runs {α : Type} (x : Traceful α) (tr : ExecTrace) (a : α) (tr' : ExecTrace) : Prop :=
  (x.run tr).1 = some a ∧ (x.run tr).2.val = tr'

private def Fails {α : Type} (x : Traceful α) (tr tr' : ExecTrace) : Prop :=
  (x.run tr).1 = none ∧ (x.run tr).2.val = tr'

private theorem Runs.bind {α β : Type} {x : Traceful α} {f : α → Traceful β} {tr tr1 tr2 : ExecTrace}
    {a : α} {b : β} (h1 : Runs x tr a tr1) (h2 : Runs (f a) tr1 b tr2) :
    Runs (x >>= f) tr b tr2 := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  rcases hx : x.run tr with ⟨o, t, ht⟩
  rw [hx] at h1a h1b; cases h1a; cases h1b
  rcases hf : (f a).run t with ⟨o', t', ht'⟩
  rw [hf] at h2a h2b; cases h2a; cases h2b
  refine ⟨?_, ?_⟩ <;> rw [Traceful.run_bind, hx] <;> dsimp only <;> rw [hf]

private theorem Fails.bind_left {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr tr' : ExecTrace} (h : Fails x tr tr') : Fails (x >>= f) tr tr' := by
  obtain ⟨h1, h2⟩ := h
  rcases hx : x.run tr with ⟨o, t, ht⟩
  rw [hx] at h1 h2; cases h1; cases h2
  refine ⟨?_, ?_⟩ <;> rw [Traceful.run_bind, hx]

private theorem Fails.bind_right {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr tr1 tr2 : ExecTrace} {a : α} (h1 : Runs x tr a tr1) (h2 : Fails (f a) tr1 tr2) :
    Fails (x >>= f) tr tr2 := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  rcases hx : x.run tr with ⟨o, t, ht⟩
  rw [hx] at h1a h1b; cases h1a; cases h1b
  rcases hf : (f a).run t with ⟨o', t', ht'⟩
  rw [hf] at h2a h2b; cases h2a; cases h2b
  refine ⟨?_, ?_⟩ <;> rw [Traceful.run_bind, hx] <;> dsimp only <;> rw [hf]

private theorem Runs.of_eq {α : Type} {x : Traceful α} {tr tr1 tr2 : ExecTrace} {a1 a2 : α}
    (h : Runs x tr a1 tr1) (ha : a1 = a2) (ht : tr1 = tr2) : Runs x tr a2 tr2 := by
  subst ha; subst ht; exact h

private theorem Runs.pure {α : Type} (a : α) (tr : ExecTrace) :
    Runs (pure a : Traceful α) tr a tr := by
  unfold Runs; rw [Traceful.run_pure]; exact ⟨rfl, rfl⟩

private theorem Runs.appendEntry {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    Runs (DY.appendEntry e) tr tr.length (tr.append e) := by
  unfold Runs; rw [Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]; exact ⟨rfl, rfl⟩

private theorem Runs.guard {p : Prop} [Decidable p] (tr : ExecTrace) (h : p) :
    Runs (_root_.guard p : Traceful Unit) tr () tr := by
  simp only [_root_.guard, h, ↓reduceIte]; exact Runs.pure () tr

private theorem Fails.guard {p : Prop} [Decidable p] (tr : ExecTrace) (h : ¬ p) :
    Fails (_root_.guard p : Traceful Unit) tr tr := by
  unfold Fails; simp only [_root_.guard, h, ↓reduceIte]; rw [Traceful.run_failure]; exact ⟨rfl, rfl⟩

private theorem Runs.traceLength (tr : ExecTrace) :
    Runs TripleRatchet.traceLength tr tr.length tr := by
  unfold Runs TripleRatchet.traceLength; rw [Traceful.run_mk]; exact ⟨rfl, rfl⟩

private theorem Runs.getLocalState {me : Participant} {stH : Nat} {tr : ExecTrace} {st : TRState}
    (h : ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 = some st) :
    Runs (PersistentLocalState.getLocalState me stH : Traceful TRState) tr st tr :=
  ⟨h, getLocalState_run_eq_self me stH tr⟩

private theorem Fails.getLocalState {me : Participant} {stH : Nat} {tr : ExecTrace}
    (h : ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 = none) :
    Fails (PersistentLocalState.getLocalState me stH : Traceful TRState) tr tr :=
  ⟨h, getLocalState_run_eq_self me stH tr⟩

private theorem Runs.genRand (n : Nat) (tr : ExecTrace) :
    Runs (DY.Random.genRand n : Traceful DY.Bytes) tr (randTerm tr.length n)
      (tr.append (⟨n⟩ : DY.Random.ExecEntryT)) := by
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1]
  exact Runs.bind (Runs.appendEntry tr (⟨n⟩ : DY.Random.ExecEntryT)) (Runs.pure _ _)

private theorem Runs.sendMessage (m : DY.Bytes) (tr : ExecTrace) :
    Runs (Network.sendMessage m : Traceful Nat) tr tr.length
      (tr.append (⟨m⟩ : Network.ExecEntryT)) := by
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1]
  exact Runs.appendEntry tr (⟨m⟩ : Network.ExecEntryT)

private theorem Runs.receiveMessage {idx : Nat} {tr : ExecTrace} {m : DY.Bytes}
    (h : (tr.at? idx : Option Network.ExecEntryT) = some ⟨m⟩) :
    Runs (Network.receiveMessage idx : Traceful DY.Bytes) tr m tr := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1]
  refine ⟨?_, ?_⟩
  · rw [run_bind_fst, Traceful.run_mk, h]; (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)
  · rw [run_bind_snd, Traceful.run_mk, h]; (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem Fails.receiveMessage {idx : Nat} {tr : ExecTrace}
    (h : (tr.at? idx : Option Network.ExecEntryT) = none) :
    Fails (Network.receiveMessage idx : Traceful DY.Bytes) tr tr := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1]
  refine ⟨?_, ?_⟩
  · rw [run_bind_fst, Traceful.run_mk, h]
  · rw [run_bind_snd, Traceful.run_mk, h]

private theorem Runs.logEvent (ev : TREvent) (tr : ExecTrace) :
    Runs (DY.ProtocolEvent.logEvent ev : Traceful Unit) tr ()
      (tr.append (⟨ev⟩ : TREntry)) := by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
  exact Runs.bind (Runs.appendEntry tr (⟨ev⟩ : TREntry)) (Runs.pure () _)

private theorem Runs.storeLocalState (me : Participant) (st : TRState) (tr : ExecTrace) :
    Runs (PersistentLocalState.storeLocalState me st : Traceful Nat) tr tr.length
      (tr.append (⟨⟨me, st⟩⟩ : StEntry)) := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1]
  exact Runs.appendEntry tr (⟨⟨me, st⟩⟩ : StEntry)

private theorem Runs.logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (r parentStateIdx : Nat)
    (st : TRState) (tr : ExecTrace) :
    Runs (TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r parentStateIdx st)
      tr (tr.length + 1)
      ((tr.append (⟨TREvent.MessageKey s dir seed pqSalt n r parentStateIdx⟩ : TREntry)).append (⟨⟨me, st⟩⟩ : StEntry)) := by
  unfold TripleRatchet.logMessageKeyAndStore
  refine Runs.bind (Runs.logEvent _ _) ?_
  exact Runs.of_eq (Runs.storeLocalState me st _) (sw_append_length tr _) rfl

/-! ## Next-trace equations for `encryptAbort`, `encryptFail`, and `encrypt` -/

theorem encryptAbort_next_of_some {me : Participant} {stateIdx : Nat} {tr : ExecTrace}
    {st : TRState}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st) :
    (Move.encryptAbort me stateIdx).next tr = tr.append (⟨32⟩ : DY.Random.ExecEntryT) := by
  have h : Fails (Move.encryptAbort me stateIdx).act tr
      (tr.append (⟨32⟩ : DY.Random.ExecEntryT)) := by
    show Fails (TripleRatchet.messageEncryptAbort me stateIdx >>= fun _ => pure ()) tr _
    refine Fails.bind_left ?_
    unfold TripleRatchet.messageEncryptAbort
    refine Fails.bind_right (Runs.getLocalState hst) ?_
    refine Fails.bind_right (Runs.genRand 32 tr) ?_
    unfold Fails; rw [Traceful.run_failure]; exact ⟨rfl, rfl⟩
  exact h.2

theorem encryptFail_next_of_none {me : Participant} {stateIdx coinsLen : Nat} {tr : ExecTrace}
    (hnone : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = none) :
    (Move.encryptFail me stateIdx coinsLen).next tr = tr := by
  have h : Fails (Move.encryptFail me stateIdx coinsLen).act tr tr := by
    show Fails (TripleRatchet.traceLength >>= fun n =>
      (TripleRatchet.messageEncrypt me stateIdx coinsLen (n + 3) >>= fun _ => pure ())) tr _
    refine Fails.bind_right (Runs.traceLength tr) (Fails.bind_left ?_)
    unfold TripleRatchet.messageEncrypt
    exact Fails.bind_left (Fails.getLocalState hnone)
  exact h.2

theorem encryptFail_next_of_some {me : Participant} {stateIdx coinsLen : Nat} {tr : ExecTrace}
    {st : TRState}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hns : st.ns ≠ TripleRatchet.u32Max) :
    (Move.encryptFail me stateIdx coinsLen).next tr =
      ((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append
        (⟨coinsLen⟩ : DY.Random.ExecEntryT)).append
        (⟨(Spqr.spqrSend st.spqr (randTerm (tr.length + 1) coinsLen)).2.1⟩ : Network.ExecEntryT) := by
  let tr3 := ((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append
    (⟨coinsLen⟩ : DY.Random.ExecEntryT)).append
    (⟨(Spqr.spqrSend st.spqr (randTerm (tr.length + 1) coinsLen)).2.1⟩ : Network.ExecEntryT)
  have hlen3 : ¬ tr.length + 3 < tr3.length := by
    simp only [tr3, sw_append_length]; omega
  have h : Fails (Move.encryptFail me stateIdx coinsLen).act tr tr3 := by
    show Fails (TripleRatchet.traceLength >>= fun n =>
      (TripleRatchet.messageEncrypt me stateIdx coinsLen (n + 3) >>= fun _ => pure ())) tr _
    refine Fails.bind_right (Runs.traceLength tr) (Fails.bind_left ?_)
    unfold TripleRatchet.messageEncrypt
    refine Fails.bind_right (Runs.getLocalState hst) ?_
    refine Fails.bind_right (Runs.guard _ hns) ?_
    refine Fails.bind_right (Runs.genRand 32 tr) ?_
    refine Fails.bind_right (Runs.of_eq (Runs.genRand coinsLen _) (by rw [sw_append_length]) rfl) ?_
    refine Fails.bind_right (Runs.sendMessage _ _) ?_
    exact Fails.bind_left (Fails.receiveMessage (at?_eq_none_of_not_lt tr3 hlen3))
  exact h.2

theorem encryptFail_next_of_ns_max {me : Participant} {stateIdx coinsLen : Nat} {tr : ExecTrace}
    {st : TRState}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hns : st.ns = TripleRatchet.u32Max) :
    (Move.encryptFail me stateIdx coinsLen).next tr = tr := by
  have h : Fails (Move.encryptFail me stateIdx coinsLen).act tr tr := by
    show Fails (TripleRatchet.traceLength >>= fun n =>
      (TripleRatchet.messageEncrypt me stateIdx coinsLen (n + 3) >>= fun _ => pure ())) tr _
    refine Fails.bind_right (Runs.traceLength tr) (Fails.bind_left ?_)
    unfold TripleRatchet.messageEncrypt
    exact Fails.bind_right (Runs.getLocalState hst)
      (Fails.bind_left (Fails.guard _ (fun h => h hns)))
  exact h.2

theorem encryptFail_next_cases (me : Participant) (stateIdx coinsLen : Nat) (tr : ExecTrace) :
    (Move.encryptFail me stateIdx coinsLen).next tr = tr ∨
      ∃ st : TRState,
        (Move.encryptFail me stateIdx coinsLen).next tr =
          ((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append
            (⟨coinsLen⟩ : DY.Random.ExecEntryT)).append
            (⟨(Spqr.spqrSend st.spqr (randTerm (tr.length + 1) coinsLen)).2.1⟩ : Network.ExecEntryT) := by
  rcases hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 with _ | st
  · exact Or.inl (encryptFail_next_of_none hst)
  · by_cases hns : st.ns = TripleRatchet.u32Max
    · exact Or.inl (encryptFail_next_of_ns_max hst hns)
    · exact Or.inr ⟨st, encryptFail_next_of_some hst hns⟩

/-- The 7-entry trace resulting from `Move.encrypt me stateIdx coinsLen (tr.length + 2) wrap`. -/
def encTr (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) : ExecTrace :=
  let m := randTerm tr.length 32
  let coinsTerm := randTerm (tr.length + 1) coinsLen
  let (_, key, _) := Spqr.spqrSend st.spqr coinsTerm
  let (_, seed) := TripleRatchet.kdfCk st.cks
  ((((((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨coinsLen⟩ : DY.Random.ExecEntryT)).append
    (⟨key⟩ : Network.ExecEntryT)).append
    (⟨TREvent.Sent me st.peer (DY.DiffieHellman.dhPk st.dhs) st.ns m⟩ : TREntry)).append
    (⟨TREvent.MessageKey (st.sessionInfo me) .sender seed key st.ns
      st.rIdx stateIdx⟩ : TREntry)).append
    (⟨⟨me, encSt st coinsLen tr.length⟩⟩ : StEntry)).append (⟨encMsg st coinsLen tr.length⟩ : Network.ExecEntryT)

theorem encTr_length (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) :
    (encTr tr me stateIdx coinsLen st).length = tr.length + 7 := by
  unfold encTr; simp only [sw_append_length]

private theorem messageEncrypt_runs_of_some {me : Participant} {stateIdx coinsLen : Nat}
    {tr : ExecTrace} {st : TRState}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hns : st.ns ≠ TripleRatchet.u32Max) :
    Runs (TripleRatchet.messageEncrypt me stateIdx coinsLen (tr.length + 2)) tr
      (tr.length + 6) (encTr tr me stateIdx coinsLen st) := by
  have hkey : ((((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨coinsLen⟩ : DY.Random.ExecEntryT)).append
      (⟨(Spqr.spqrSend st.spqr (randTerm (tr.length + 1) coinsLen)).2.1⟩ : Network.ExecEntryT)).at? (tr.length + 2) :
      Option Network.ExecEntryT) = some ⟨(Spqr.spqrSend st.spqr (randTerm (tr.length + 1) coinsLen)).2.1⟩ :=
    at?_append_eq_some _ _ (by simp only [sw_append_length])
  unfold TripleRatchet.messageEncrypt encTr encSt encMsg encMac encWire; dsimp only
  refine Runs.bind (Runs.getLocalState hst) ?_
  refine Runs.bind (Runs.guard _ hns) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.of_eq (Runs.genRand _ _) (by rw [sw_append_length]) rfl) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.receiveMessage hkey) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _) ?_
  exact Runs.of_eq (Runs.sendMessage _ _) (by simp only [sw_append_length]) rfl

theorem encrypt_wrap_next_eq (me : Participant) (stateIdx coinsLen pqIdx : Nat)
    (wrap : Option (Nat × Nat)) (tr : ExecTrace) :
    (Move.encrypt me stateIdx coinsLen pqIdx wrap).next tr =
      (Move.encrypt me stateIdx coinsLen pqIdx none).next tr := rfl

theorem encrypt_next_of_some {me : Participant} {stateIdx coinsLen : Nat} {tr : ExecTrace} {st : TRState}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hns : st.ns ≠ TripleRatchet.u32Max) :
    (Move.encrypt me stateIdx coinsLen (tr.length + 2) none).next tr = encTr tr me stateIdx coinsLen st := by
  show ((TripleRatchet.messageEncrypt me stateIdx coinsLen (tr.length + 2) >>= fun _ => pure ()).run tr).2.val = _
  rw [run_bind_pure_val]
  exact (messageEncrypt_runs_of_some (coinsLen := coinsLen) hst hns).2

theorem encrypt_wrap_next_of_some {me : Participant} {stateIdx coinsLen : Nat}
    {wrap : Option (Nat × Nat)} {tr : ExecTrace} {st : TRState}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hns : st.ns ≠ TripleRatchet.u32Max) :
    (Move.encrypt me stateIdx coinsLen (tr.length + 2) wrap).next tr = encTr tr me stateIdx coinsLen st :=
  encrypt_next_of_some hst hns

/-! ## `ModelRun` preservation -/

theorem movesAnchored_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    MovesAnchored (ms₁ ++ ms₂) tr ↔
      MovesAnchored ms₁ tr ∧ MovesAnchored ms₂ (runMoves ms₁ tr).1
  | [], _, _ => by simp [MovesAnchored, runMoves]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, MovesAnchored, runMoves_cons_fst,
      movesAnchored_append ms₁ ms₂ (m.next tr), and_assoc]

theorem compromisesCurrentFrom_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    compromisesCurrentFrom tr (ms₁ ++ ms₂) =
      (compromisesCurrentFrom tr ms₁ && compromisesCurrentFrom (runMoves ms₁ tr).1 ms₂)
  | [], _, _ => by simp [compromisesCurrentFrom, runMoves]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, compromisesCurrentFrom, runMoves_cons_fst,
      compromisesCurrentFrom_append ms₁ ms₂ (m.next tr), Bool.and_assoc]

theorem ownSaltsFrom_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
    ownSaltsFrom tr (ms₁ ++ ms₂) =
      (ownSaltsFrom tr ms₁ && ownSaltsFrom (runMoves ms₁ tr).1 ms₂)
  | [], _, _ => by simp [ownSaltsFrom, runMoves]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, ownSaltsFrom, runMoves_cons_fst,
      ownSaltsFrom_append ms₁ ms₂ (m.next tr), Bool.and_assoc]

theorem runTrace_snoc (r : ProtocolSetup) (ms : List Move) (m : Move) :
    runTraceMoves r (ms ++ [m]) = m.next (runTraceMoves r ms) := by
  have happ : ∀ (xs ys : List Move) (tr : ExecTrace),
      (runMoves (xs ++ ys) tr).1 = (runMoves ys (runMoves xs tr).1).1 := by
    intro xs ys tr
    induction xs generalizing tr with
    | nil => rfl
    | cons x xs ih => exact ih (x.next tr)
  unfold runTraceMoves
  rw [← List.cons_append, happ]
  rfl

/-- `ModelRun` snoc combinator for non-start wire moves. -/
theorem modelRun_snoc_wire {r : ProtocolSetup} {ms : List Move} {m : Move}
    (hrun : ModelRun r ms)
    (hset : m.isSetup = false)
    (hreach : (m.next (runTraceMoves r ms)).Reachable reachability)
    (hanch : m.LogsSessionCompletion (runTraceMoves r ms))
    (hcc : compromisesCurrentFrom (runTraceMoves r ms) [m] = true)
    (hos : ownSaltsFrom (runTraceMoves r ms) [m] = true)
    (hpeer : m.MatchesSetupPeer r)
    (hcur : ∀ p k b, m.stateLoad? = some (p, k, b) → isCurrentSnapshot (runTraceMoves r ms) k = true) :
    ModelRun r (ms ++ [m]) := by
  obtain ⟨hlen, hns, ⟨_, hanc, hpref⟩, hcomp, hsalt, hpf, hsf⟩ := hrun
  have htr_eq : (runMoves ms (setupTrace r)).1 = runTraceMoves r ms := rfl
  refine ⟨hlen, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro m' hm'
    rcases List.mem_append.mp hm' with hm' | hm'
    · exact hns m' hm'
    · rw [List.mem_singleton.mp hm']; exact hset
  · rw [runTrace_snoc]; exact hreach
  · rw [movesAnchored_append, htr_eq]
    exact ⟨hanc, hanch, trivial⟩
  · intro k
    by_cases hk : k ≤ ms.length
    · rw [List.take_append_of_le_length hk]
      exact hpref k
    · have hk_ge : (ms ++ [m]).length ≤ k := by simp only [List.length_append, List.length_singleton]; omega
      rw [List.take_of_length_le hk_ge, runTrace_snoc]
      exact hreach
  · rw [compromisesCurrentFrom_append, hcomp, htr_eq]; exact hcc
  · rw [ownSaltsFrom_append, hsalt, htr_eq]; exact hos
  · exact Stage1Wire.peerFaithful_append.mpr ⟨hpf, fun m' hm' => List.mem_singleton.mp hm' ▸ hpeer⟩
  · exact stateFaithful_snoc_of_isCurrentSnapshot hsf hcur

theorem modelRun_snoc_encryptAbort {r₀ : ProtocolSetup} {ms : List Move} {p : Participant}
    {stateIdx : Nat}
    (hrun : ModelRun r₀ ms) (hcur : isCurrentSnapshot (runTraceMoves r₀ ms) stateIdx = true) :
    ModelRun r₀ (ms ++ [Move.encryptAbort p stateIdx]) := by
  refine modelRun_snoc_wire hrun rfl ?_ trivial rfl rfl
    (peerOk_of_not_start r₀ (m := Move.encryptAbort p stateIdx)
      (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ _ h => by cases h))
    (fun q k b h => by
      simp only [Move.stateLoad?, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl, _⟩; exact hcur)
  dsimp only [Move.next, Move.act]
  rw [run_bind_pure_val]
  exact (Traceful.PreservesReachability_base TripleRatchet.messageEncryptAbort.reachability
    reachability (p, stateIdx) (runTraceMoves r₀ ms) hrun.2.2.1.1 hcur).1

theorem modelRun_snoc_encrypt_wrap {r₀ : ProtocolSetup} {ms : List Move} {p : Participant}
    {stateIdx coinsLen : Nat} {wrap : Option (Nat × Nat)}
    (hrun : ModelRun r₀ ms) (hcur : isCurrentSnapshot (runTraceMoves r₀ ms) stateIdx = true) :
    ModelRun r₀ (ms ++ [Move.encrypt p stateIdx coinsLen ((runTraceMoves r₀ ms).length + 2) wrap]) := by
  refine modelRun_snoc_wire hrun rfl ?_ trivial rfl (by simp [ownSaltsFrom])
    (peerOk_of_not_start r₀ (m := Move.encrypt p stateIdx coinsLen ((runTraceMoves r₀ ms).length + 2) wrap)
      (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ _ h => by cases h))
    (fun q k b h => by
      simp only [Move.stateLoad?, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl, _⟩; exact hcur)
  rw [encrypt_wrap_next_eq]
  change ((TripleRatchet.messageEncrypt p stateIdx coinsLen ((runTraceMoves r₀ ms).length + 2) >>=
    fun _ => pure ()).run (runTraceMoves r₀ ms)).2.val.Reachable reachability
  rw [run_bind_pure_val]
  exact (Traceful.PreservesReachability_base TripleRatchet.messageEncrypt.reachability
    reachability (p, stateIdx, coinsLen, (runTraceMoves r₀ ms).length + 2)
    (runTraceMoves r₀ ms) hrun.2.2.1.1 hcur).1

theorem modelRun_snoc_encrypt {r₀ : ProtocolSetup} {ms : List Move} {p : Participant}
    {stateIdx coinsLen : Nat}
    (hrun : ModelRun r₀ ms) (hcur : isCurrentSnapshot (runTraceMoves r₀ ms) stateIdx = true) :
    ModelRun r₀ (ms ++ [Move.encrypt p stateIdx coinsLen ((runTraceMoves r₀ ms).length + 2) none]) :=
  modelRun_snoc_encrypt_wrap hrun hcur

/-! ## Visible entries, exposures, and `encTr` invariance -/

def trLayout : VisEventKind → VisByteLayout
  | .send | .recv => .whisper
  | .leak => .leakRecord
  | _ => .single

def trEntry (k : VisEventKind) (t : DY.Bytes) : VisEntry := ⟨k, [t], trLayout k, none⟩

theorem vis_encryptAbort {me : Participant} {stateIdx : Nat} {tr tr' : ExecTrace}
    (h : (Move.encryptAbort me stateIdx).next tr = tr') :
    (Move.encryptAbort me stateIdx).vis tr = encDraws (newRandoms tr tr') ++ exposures tr tr' := by
  subst h
  show encVis tr _ none false ++ exposures tr _ = _
  simp only [encVis, Bool.false_eq_true, ↓reduceIte, List.append_nil]

theorem newIndices_encTr (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) :
    newIndices tr (encTr tr me stateIdx coinsLen st) =
      [tr.length, tr.length + 1, tr.length + 2, tr.length + 3, tr.length + 4, tr.length + 5, tr.length + 6] := by
  unfold newIndices; rw [encTr_length, Nat.add_sub_cancel_left]; rfl

private theorem encTr_rnd_0 (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) :
    ((encTr tr me stateIdx coinsLen st).at? tr.length : Option DY.Random.ExecEntryT) = some ⟨32⟩ := by
  unfold encTr; dsimp only
  rw [at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_eq_some _ _ rfl]

private theorem encTr_rnd_1 (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) :
    ((encTr tr me stateIdx coinsLen st).at? (tr.length + 1) : Option DY.Random.ExecEntryT) = some ⟨coinsLen⟩ := by
  unfold encTr; dsimp only
  rw [at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_eq_some _ _ (by simp only [sw_append_length])]

private theorem encTr_rnd_2 (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) :
    ((encTr tr me stateIdx coinsLen st).at? (tr.length + 2) : Option DY.Random.ExecEntryT) = none := by
  unfold encTr; dsimp only
  rw [at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega)]
  exact at?_append_eq_none _ _ (by simp only [sw_append_length]) rfl

private theorem encTr_rnd_3 (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) :
    ((encTr tr me stateIdx coinsLen st).at? (tr.length + 3) : Option DY.Random.ExecEntryT) = none := by
  unfold encTr; dsimp only
  rw [at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega)]
  exact at?_append_eq_none _ _ (by simp only [sw_append_length]) rfl

private theorem encTr_rnd_4 (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) :
    ((encTr tr me stateIdx coinsLen st).at? (tr.length + 4) : Option DY.Random.ExecEntryT) = none := by
  unfold encTr; dsimp only
  rw [at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega)]
  exact at?_append_eq_none _ _ (by simp only [sw_append_length]) rfl

private theorem encTr_rnd_5 (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) :
    ((encTr tr me stateIdx coinsLen st).at? (tr.length + 5) : Option DY.Random.ExecEntryT) = none := by
  unfold encTr; dsimp only; rw [at?_append_of_lt _ _ (by simp only [sw_append_length]; omega)]
  exact at?_append_eq_none _ _ (by simp only [sw_append_length]) rfl

private theorem encTr_rnd_6 (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) :
    ((encTr tr me stateIdx coinsLen st).at? (tr.length + 6) : Option DY.Random.ExecEntryT) = none := by
  unfold encTr; exact at?_append_eq_none _ _ (by simp only [sw_append_length]) rfl

theorem newRandoms_encTr (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) :
    newRandoms tr (encTr tr me stateIdx coinsLen st) =
      [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) coinsLen, coinsLen)] := by
  unfold newRandoms; rw [newIndices_encTr]
  simp only [List.filterMap_cons, List.filterMap_nil, encTr_rnd_0, encTr_rnd_1,
    encTr_rnd_2, encTr_rnd_3, encTr_rnd_4, encTr_rnd_5, encTr_rnd_6, Option.map]

theorem encSend_encTr (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) :
    encSend tr (encTr tr me stateIdx coinsLen st) none = [trEntry .send (encMsg st coinsLen tr.length)] := by
  have hlt : tr.length < (encTr tr me stateIdx coinsLen st).length := by rw [encTr_length]; omega
  have hsub : (encTr tr me stateIdx coinsLen st).length - 1 = tr.length + 6 := by rw [encTr_length]; omega
  have hm : ((encTr tr me stateIdx coinsLen st).at? (tr.length + 6) : Option Network.ExecEntryT) =
      some ⟨encMsg st coinsLen tr.length⟩ := by
    unfold encTr; exact at?_append_eq_some _ _ (by simp only [sw_append_length])
  (unfold encSend lastSent; simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1])
  rw [ite_eq_left_iff.mpr fun h => absurd hlt h, hsub, hm]; rfl

theorem encSend_encTr_some (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat)
    (st : TRState) (ekIdx ctIdx : Nat) (ek ct : DY.Bytes)
    (hek : tr.getMessageSentAt ekIdx = some ek) (hct : tr.getMessageSentAt ctIdx = some ct) :
    encSend tr (encTr tr me stateIdx coinsLen st) (some (ekIdx, ctIdx)) =
      [⟨.send, [ek, ct, encMsg st coinsLen tr.length], .preKeySend, none⟩] := by
  have hlt : tr.length < (encTr tr me stateIdx coinsLen st).length := by rw [encTr_length]; omega
  have hsub : (encTr tr me stateIdx coinsLen st).length - 1 = tr.length + 6 := by rw [encTr_length]; omega
  have hm : ((encTr tr me stateIdx coinsLen st).at? (tr.length + 6) : Option Network.ExecEntryT) =
      some ⟨encMsg st coinsLen tr.length⟩ := by
    unfold encTr; exact at?_append_eq_some _ _ (by simp only [sw_append_length])
  (unfold encSend lastSent; simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1])
  rw [ite_eq_left_iff.mpr fun h => absurd hlt h, hsub, hm]
  simp [received, hek, hct]

private theorem getEventAt_append_non_ev (EventT : Type)
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)]
    {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT EventT)) = none) (j : Nat) :
    (tr.append e).getEventAt EventT j = tr.getEventAt EventT j := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_non_entry tr e hnone]

private theorem pqExposureAt_encTr_ge (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat)
    (st : TRState) {j : Nat} (hj : ¬ j < tr.length) :
    pqExposureAt (encTr tr me stateIdx coinsLen st) j = none := by
  have hge : tr.getEventAt PQXDH.PQXDHEvent j = none := by simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_eq_none_of_not_lt tr hj]
  unfold pqExposureAt encTr; dsimp only
  rw [getEventAt_append_non_ev _ _ _ rfl, getEventAt_append_non_ev _ _ _ rfl,
      getEventAt_append_non_ev _ _ _ rfl, getEventAt_append_non_ev _ _ _ rfl,
      getEventAt_append_non_ev _ _ _ rfl, getEventAt_append_non_ev _ _ _ rfl,
      getEventAt_append_non_ev _ _ _ rfl, hge]

private theorem trExposureAt_encTr_012 (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat)
    (st : TRState) {j : Nat} (hj1 : j < tr.length + 3) (hj0 : ¬ j < tr.length) :
    trExposureAt (encTr tr me stateIdx coinsLen st) j = none := by
  unfold trExposureAt encTr; dsimp only
  rw [getEventAt_append_non_ev _ _ _ rfl, getEventAt_append_non_ev _ _ _ rfl]
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  rw [at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
      at?_append_non_entry _ _ rfl, at?_eq_none_of_not_lt tr hj0]

private theorem trExposureAt_encTr_3 (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) :
    trExposureAt (encTr tr me stateIdx coinsLen st) (tr.length + 3) = none := by
  unfold trExposureAt encTr; dsimp only
  rw [getEventAt_append_non_ev _ _ _ rfl, getEventAt_append_non_ev _ _ _ rfl]
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  rw [at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_eq_some _ _ (by simp only [sw_append_length])]

private theorem trExposureAt_encTr_4 (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) :
    trExposureAt (encTr tr me stateIdx coinsLen st) (tr.length + 4) = none := by
  unfold trExposureAt encTr; dsimp only
  rw [getEventAt_append_non_ev _ _ _ rfl, getEventAt_append_non_ev _ _ _ rfl]
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  rw [at?_append_eq_some _ _ (by simp only [sw_append_length])]

private theorem trExposureAt_encTr_56 (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat)
    (st : TRState) {j : Nat} (hj : ¬ j < tr.length + 5) :
    trExposureAt (encTr tr me stateIdx coinsLen st) j = none := by
  unfold trExposureAt encTr; dsimp only
  rw [getEventAt_append_non_ev _ _ _ rfl, getEventAt_append_non_ev _ _ _ rfl]
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  rw [at?_eq_none_of_not_lt _ (by simp only [sw_append_length]; omega)]

theorem exposures_encTr (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat) (st : TRState) :
    exposures tr (encTr tr me stateIdx coinsLen st) = [] := by
  have hp0 := pqExposureAt_encTr_ge tr me stateIdx coinsLen st (j := tr.length) (by omega)
  have hp1 := pqExposureAt_encTr_ge tr me stateIdx coinsLen st (j := tr.length + 1) (by omega)
  have hp2 := pqExposureAt_encTr_ge tr me stateIdx coinsLen st (j := tr.length + 2) (by omega)
  have hp3 := pqExposureAt_encTr_ge tr me stateIdx coinsLen st (j := tr.length + 3) (by omega)
  have hp4 := pqExposureAt_encTr_ge tr me stateIdx coinsLen st (j := tr.length + 4) (by omega)
  have hp5 := pqExposureAt_encTr_ge tr me stateIdx coinsLen st (j := tr.length + 5) (by omega)
  have hp6 := pqExposureAt_encTr_ge tr me stateIdx coinsLen st (j := tr.length + 6) (by omega)
  have ht0 := trExposureAt_encTr_012 tr me stateIdx coinsLen st (j := tr.length) (by omega) (by omega)
  have ht1 := trExposureAt_encTr_012 tr me stateIdx coinsLen st (j := tr.length + 1) (by omega) (by omega)
  have ht2 := trExposureAt_encTr_012 tr me stateIdx coinsLen st (j := tr.length + 2) (by omega) (by omega)
  have ht3 := trExposureAt_encTr_3 tr me stateIdx coinsLen st
  have ht4 := trExposureAt_encTr_4 tr me stateIdx coinsLen st
  have ht5 := trExposureAt_encTr_56 tr me stateIdx coinsLen st (j := tr.length + 5) (by omega)
  have ht6 := trExposureAt_encTr_56 tr me stateIdx coinsLen st (j := tr.length + 6) (by omega)
  unfold exposures; rw [newIndices_encTr]
  simp only [List.filterMap_cons, List.filterMap_nil,
    hp0, hp1, hp2, hp3, hp4, hp5, hp6, ht0, ht1, ht2, ht3, ht4, ht5, ht6, List.nil_append]

theorem visOf_encrypt_zero {me : Participant} {stateIdx : Nat} {tr : ExecTrace} {st : TRState}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hns : st.ns ≠ TripleRatchet.u32Max) :
    (Move.encrypt me stateIdx 0 (tr.length + 2) none).vis tr =
      [trEntry .pt (randTerm tr.length 32), trEntry .send (encMsg st 0 tr.length)] := by
  have hnext := encrypt_next_of_some (coinsLen := 0) hst hns
  show encVis tr _ none true ++ exposures tr _ = _
  rw [hnext, exposures_encTr, List.append_nil]; unfold encVis; rw [newRandoms_encTr, encSend_encTr]; rfl

theorem visOf_encrypt_ne_zero {me : Participant} {stateIdx coinsLen : Nat} {tr : ExecTrace} {st : TRState}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hns : st.ns ≠ TripleRatchet.u32Max) (hc : coinsLen ≠ 0) :
    (Move.encrypt me stateIdx coinsLen (tr.length + 2) none).vis tr =
      [trEntry .pt (randTerm tr.length 32), trEntry .rng (randTerm (tr.length + 1) coinsLen),
        trEntry .send (encMsg st coinsLen tr.length)] := by
  have hnext := encrypt_next_of_some (coinsLen := coinsLen) hst hns
  show encVis tr _ none true ++ exposures tr _ = _
  rw [hnext, exposures_encTr, List.append_nil]; unfold encVis
  rw [newRandoms_encTr, encSend_encTr]; simp [encDraws, hc, rngEntry, trEntry, trLayout]

theorem visOf_encrypt_wrap_zero {me : Participant} {stateIdx ekIdx ctIdx : Nat}
    {tr : ExecTrace} {st : TRState} {ek ct : DY.Bytes}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hns : st.ns ≠ TripleRatchet.u32Max)
    (hek : tr.getMessageSentAt ekIdx = some ek) (hct : tr.getMessageSentAt ctIdx = some ct) :
    (Move.encrypt me stateIdx 0 (tr.length + 2) (some (ekIdx, ctIdx))).vis tr =
      [trEntry .pt (randTerm tr.length 32),
       ⟨.send, [ek, ct, encMsg st 0 tr.length], .preKeySend, none⟩] := by
  have hnext := encrypt_wrap_next_of_some (coinsLen := 0) (wrap := some (ekIdx, ctIdx)) hst hns
  show encVis tr _ (some (ekIdx, ctIdx)) true ++ exposures tr _ = _
  rw [hnext, exposures_encTr, List.append_nil]; unfold encVis
  rw [newRandoms_encTr, encSend_encTr_some tr me stateIdx 0 st ekIdx ctIdx ek ct hek hct]; rfl

theorem visOf_encrypt_wrap_ne_zero {me : Participant} {stateIdx coinsLen ekIdx ctIdx : Nat}
    {tr : ExecTrace} {st : TRState} {ek ct : DY.Bytes}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hns : st.ns ≠ TripleRatchet.u32Max) (hc : coinsLen ≠ 0)
    (hek : tr.getMessageSentAt ekIdx = some ek) (hct : tr.getMessageSentAt ctIdx = some ct) :
    (Move.encrypt me stateIdx coinsLen (tr.length + 2) (some (ekIdx, ctIdx))).vis tr =
      [trEntry .pt (randTerm tr.length 32),
       trEntry .rng (randTerm (tr.length + 1) coinsLen),
       ⟨.send, [ek, ct, encMsg st coinsLen tr.length], .preKeySend, none⟩] := by
  have hnext := encrypt_wrap_next_of_some (coinsLen := coinsLen) (wrap := some (ekIdx, ctIdx)) hst hns
  show encVis tr _ (some (ekIdx, ctIdx)) true ++ exposures tr _ = _
  rw [hnext, exposures_encTr, List.append_nil]; unfold encVis
  rw [newRandoms_encTr, encSend_encTr_some tr me stateIdx coinsLen st ekIdx ctIdx ek ct hek hct]
  simp [encDraws, hc, rngEntry, trEntry, trLayout]

private theorem list_any_eq_of_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp only [List.any_cons, h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem someEventOnTraceB_append_non_tr {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (p : TREvent → Bool) :
    (DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.TripleRatchet.TREvent) (tr.append e) p = (DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.TripleRatchet.TREvent) tr p := by
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?,
      DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  have hlen : (tr.append e).length = tr.length + 1 := sw_append_length tr e
  have hlast : (tr.at? tr.length : Option TREntry) = none := by simp [Trace.at?]
  rw [hlen, List.range_succ]
  simp only [List.any_append, List.any_cons, List.any_nil, at?_append_non_entry tr e hnone, hlast, Bool.or_false]

theorem someEventOnTraceB_append_tr_false (tr : ExecTrace) (ev : TREvent) (p : TREvent → Bool)
    (hp : p ev = false) :
    (DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.TripleRatchet.TREvent) (tr.append (⟨ev⟩ : TREntry)) p = (DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.TripleRatchet.TREvent) tr p := by
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?,
      DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  have hlen : (tr.append (⟨ev⟩ : TREntry)).length = tr.length + 1 := sw_append_length tr _
  rw [hlen, List.range_succ, List.any_append, List.any_cons, List.any_nil, at?_append_eq_some _ _ rfl]
  dsimp only; rw [hp, Bool.or_false, Bool.or_false]
  exact list_any_eq_of_mem fun i hi => by rw [at?_append_of_lt _ _ (List.mem_range.mp hi)]

theorem someEventOnTraceB_encTr (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat)
    (st : TRState) (p : TREvent → Bool)
    (hp1 : p (.Sent me st.peer (DY.DiffieHellman.dhPk st.dhs) st.ns (randTerm tr.length 32)) = false)
    (hp2 : p (.MessageKey (st.sessionInfo me) .sender
      (TripleRatchet.kdfCk st.cks).2 (Spqr.spqrSend st.spqr (randTerm (tr.length + 1) coinsLen)).2.1
      st.ns st.rIdx stateIdx) = false) :
    (DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.TripleRatchet.TREvent) (encTr tr me stateIdx coinsLen st) p = (DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.TripleRatchet.TREvent) tr p := by
  unfold encTr; dsimp only
  rw [someEventOnTraceB_append_non_tr _ _ rfl, someEventOnTraceB_append_non_tr _ _ rfl,
      someEventOnTraceB_append_tr_false _ _ _ hp2, someEventOnTraceB_append_tr_false _ _ _ hp1,
      someEventOnTraceB_append_non_tr _ _ rfl, someEventOnTraceB_append_non_tr _ _ rfl,
      someEventOnTraceB_append_non_tr _ _ rfl]

theorem skippedKeyUsedB_encTr (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat)
    (st : TRState) (skIdx : Nat) :
    skippedKeyUsedB (encTr tr me stateIdx coinsLen st) skIdx = skippedKeyUsedB tr skIdx :=
  someEventOnTraceB_encTr tr me stateIdx coinsLen st _ rfl rfl

theorem receiverKeyUsedB_encTr (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat)
    (st : TRState) (s : SessionInfo) (seed : DY.Bytes) (cnt : UInt32) (rIdx : Nat) :
    receiverKeyUsedB (encTr tr me stateIdx coinsLen st) s seed cnt rIdx = receiverKeyUsedB tr s seed cnt rIdx :=
  someEventOnTraceB_encTr tr me stateIdx coinsLen st _ rfl rfl

theorem at?_encTr_of_lt {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (me : Participant)
    (stateIdx coinsLen : Nat) (st : TRState) {i : Nat} (hi : i < tr.length) :
    ((encTr tr me stateIdx coinsLen st).at? i : Option E) = (tr.at? i : Option E) := by
  unfold encTr; dsimp only
  rw [at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ (by simp only [sw_append_length]; omega),
      at?_append_of_lt _ _ hi]

end Symbolic.Swarm.CREF.SendWire
