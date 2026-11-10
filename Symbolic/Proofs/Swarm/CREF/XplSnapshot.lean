/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Trace.Basic
import DY.Trace.Monad
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Aesop.BuiltinRules
public import Mathlib.Data.Subtype
public import Mathlib.Tactic.ToAdditive
public import Symbolic.Specifications.Model.Instance
import Mathlib.Tactic.Push
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
/-!
# Snapshot Lineage on Composed Traces

Proves `snapshotChain_of_reachable`: on a reachable composed trace, every `TREvent.MessageKey`
event at index `k` with parent snapshot `par` stores a child snapshot for the same participant and
role at `k + 1` with no intervening same-role snapshot in `(par, k + 1)`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

cref_open
open DY
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg isCurrentSnapshot logSkippedKeys
  logMessageKeyAndStore ensureReceiverChain verifyMacAndDecrypt receiveSignalMsg traceLength)
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir RecvChain findRecvChain setRecvChain
  recvChainFor x25519LowOrder kdfCk)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent KeyKind BundleHandles BobKeyHandles PreKeyMsgHandles
  extractDhSecretKey)
open DY.Libsignal.Composed (ComposedEvent reachability)

abbrev XplStEntry :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)

abbrev XplEvEntry := DY.ProtocolEvent.ExecEntryT TREvent

/-! ## Trace append and `Preserves` helpers -/

def Preserves (Inv : ExecTrace → Prop) {α : Type} (x : Traceful α) : Prop :=
  ∀ tr, Inv tr → Inv (x.run tr).2.val

private theorem Preserves.pure (Inv : ExecTrace → Prop) {α : Type} (a : α) :
    Preserves Inv (Pure.pure a : Traceful α) := by
  intro _ h; rw [DY.Traceful.run_pure]; exact h

private theorem Preserves.failure {Inv : ExecTrace → Prop} {α : Type} :
    Preserves Inv ( Alternative.failure : Traceful α) := by
  intro _ h; rw [DY.Traceful.run_failure]; exact h

private theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩ <;> rfl

private theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩ <;> rfl

private theorem Preserves.bind {Inv : ExecTrace → Prop} {α β : Type}
    {x : Traceful α} {f : α → Traceful β}
    (hx : Preserves Inv x) (hf : ∀ a, Preserves Inv (f a)) :
    Preserves Inv (x >>= f) := by
  intro tr h
  rw [run_bind_snd]
  rcases (x.run tr).1 with _ | a
  · exact hx tr h
  · exact hf a _ (hx tr h)

private theorem Preserves.and {P Q : ExecTrace → Prop} {α : Type} {x : Traceful α}
    (hP : Preserves P x) (hQ : Preserves Q x) :
    Preserves (fun tr => P tr ∧ Q tr) x :=
  fun tr ⟨hp, hq⟩ => ⟨hP tr hp, hQ tr hq⟩

private theorem Preserves.guardP {Inv : ExecTrace → Prop} (p : Prop) {_ : Decidable p} :
    Preserves Inv (@_root_.guard Traceful _ p _) := by
  intro tr h; unfold _root_.guard; split
  · rw [DY.Traceful.run_pure]; exact h
  · rw [DY.Traceful.run_failure]; exact h

private theorem Preserves.requireTracePredicate {Inv : ExecTrace → Prop} (p : ExecTrace → Bool) :
    Preserves Inv (DY.Libsignal.PQXDH.guardTrace p) := by
  intro _ h; unfold DY.Libsignal.PQXDH.guardTrace; rw [DY.Traceful.run_mk]; exact h

private theorem Preserves.guardTrace {Inv : ExecTrace → Prop} (p : ExecTrace → Bool) :
    Preserves Inv (DY.Libsignal.TripleRatchet.guardTrace p) := by
  intro _ h; unfold DY.Libsignal.TripleRatchet.guardTrace; rw [DY.Traceful.run_mk]; exact h

private theorem Preserves.inv_traceLength {Inv : ExecTrace → Prop} :
    Preserves Inv traceLength := by
  intro _ h; unfold traceLength; rw [DY.Traceful.run_mk]; exact h

private theorem Preserves.getEntry {Inv : ExecTrace → Prop} {E : Type} [ExecTraceTypes.Has E]
    (i : Nat) : Preserves Inv (DY.getEntry i : Traceful E) := by
  intro _ h; simp only [Symbolic.DYBridge.DY.getEntry_eq_1]; rw [DY.Traceful.run_mk]; exact h

private theorem Preserves.receiveMessage {Inv : ExecTrace → Prop} (i : Nat) :
    Preserves Inv (DY.Network.receiveMessage i) := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact Preserves.bind (Preserves.getEntry i) fun _ => Preserves.pure Inv _

private theorem Preserves.receiveSignalMsg {Inv : ExecTrace → Prop} (i : Nat) :
    Preserves Inv (receiveSignalMsg i) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine Preserves.bind (Preserves.receiveMessage i) fun raw => ?_
  rcases DY.Libsignal.TripleRatchet.parseTrSignalMsg raw with _ | msg
  · exact Preserves.failure
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure Inv msg

private theorem Preserves.getLocalState {Inv : ExecTrace → Prop} {S : Type}
    [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT S)]
    (p : Participant) (i : Nat) :
    Preserves Inv (PersistentLocalState.getLocalState p i : Traceful S) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact Preserves.bind
    (Preserves.bind (Preserves.getEntry i) fun _ => Preserves.pure Inv _) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure Inv _

private theorem Preserves.getKey {Inv : ExecTrace → Prop} (p : Participant) (i : Nat) (k : KeyKind) :
    Preserves Inv (DY.Libsignal.PQXDH.getKey p i k) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState p i) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure Inv _

private theorem Preserves.lookupIdentity {Inv : ExecTrace → Prop} (p : Participant) (i : Nat) :
    Preserves Inv (DY.Libsignal.PQXDH.lookupIdentity p i) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry i) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure Inv _
  · exact Preserves.failure

private theorem Preserves.verifyMacAndDecrypt {Inv : ExecTrace → Prop}
    (st : TRState) (msg : TRSignalMsg) (pqSalt seed : Bytes) :
    Preserves Inv (verifyMacAndDecrypt st msg pqSalt seed) :=
  COMPOSED.CompTrace.Preserves.verifyMacAndDecrypt st msg pqSalt seed

private theorem proj_inj {E : Type} [ExecTraceTypes.Has E] (x : E) :
    (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) : Option E) = some x := by
  rw [DY.TraceEntryHas.inj_proj_eq]

private theorem at?_lt_length {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {idx : Nat} {e : E}
    (h : (tr.at? idx : Option E) = some e) : idx < tr.length := by
  have h0 := DY.Trace.at?_eq_some_implies_length_le (EntryT := E) tr idx
  rw [h] at h0
  exact h0

private theorem at?_append_of_lt {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {x : E}
    {E' : Type} [ExecTraceTypes.Has E'] {idx : Nat} (hlt : idx < tr.length) :
    ((tr.append x).at? idx : Option E') = (tr.at? idx : Option E') := by
  have hlt' : idx < (tr.append x).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hlt, hlt', ↓reduceDIte]
  rw [← DY.Trace.at_le tr (tr.append x) idx hlt (DY.Trace.append_le tr x)]

private theorem at?_append_cases {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {x : E}
    {E' : Type} [ExecTraceTypes.Has E'] {idx : Nat} {e' : E'}
    (h : ((tr.append x).at? idx : Option E') = some e') :
    (idx < tr.length ∧ (tr.at? idx : Option E') = some e') ∨
    (idx = tr.length ∧ DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) = some e') := by
  have hlt : idx < (tr.append x).length := at?_lt_length h
  have hlen : (tr.append x).length = tr.length + 1 := by
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rcases (show idx < tr.length ∨ idx = tr.length by omega) with hi | rfl
  · rw [at?_append_of_lt hi] at h
    exact .inl ⟨hi, h⟩
  · simp only [DY.Trace.at?, hlt, ↓reduceDIte] at h
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte] at h
    exact .inr ⟨rfl, h⟩

/-! ## `SnapshotChainInv` -/

/-- Inductive invariant for `snapshotChain_of_reachable`: every logged `TREvent.MessageKey` at `k`
with parent `par` satisfies `par ≤ k + 1 < tr.length` and links `par` directly to `k + 1` with no
intervening snapshot for the same `(participant, initiator)`. -/
def SnapshotChainInv (tr : ExecTrace) : Prop :=
  ∀ k (ev : XplEvEntry) (s : SessionInfo) (dir : KeyDir) (seed pqSalt : Bytes)
    (n : UInt32) (rIdx par : Nat),
    (tr.at? k : Option XplEvEntry) = some ev →
    ev.ev = TREvent.MessageKey s dir seed pqSalt n rIdx par →
    par ≤ k + 1 ∧ k + 1 < tr.length ∧
    ∀ (e : XplStEntry), (tr.at? par : Option XplStEntry) = some e →
      (∃ e' : XplStEntry, (tr.at? (k + 1) : Option XplStEntry) = some e' ∧
        e'.st.participant = e.st.participant ∧ e'.st.state.initiator = e.st.state.initiator) ∧
      ∀ j, par < j → j < k + 1 → ∀ e'' : XplStEntry, (tr.at? j : Option XplStEntry) = some e'' →
        (e''.st.participant != e.st.participant ||
          e''.st.state.initiator != e.st.state.initiator) = true

theorem SnapshotChainInv.nil : SnapshotChainInv DY.Trace.nil := by
  intro k ev _ _ _ _ _ _ _ hk
  obtain ⟨hlt, _⟩ := (DY.Trace.at?_eq_some (DY.Trace.nil : ExecTrace) k ev).mp hk
  exact absurd hlt (Symbolic.DYBridge.DY.Trace.nil_length_not_lt k)

theorem SnapshotChainInv.append_non_mk {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {x : E}
    (hnon : ∀ (ev : XplEvEntry) s dir seed pqSalt n rIdx par,
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) : Option XplEvEntry) = some ev →
      ev.ev ≠ TREvent.MessageKey s dir seed pqSalt n rIdx par)
    (hInv : SnapshotChainInv tr) :
    SnapshotChainInv (tr.append x) := by
  intro k ev s dir seed pqSalt n rIdx par hk hev
  rcases at?_append_cases hk with ⟨hk_lt, hk_tr⟩ | ⟨_, hproj⟩
  · obtain ⟨hpar_le, hch_lt, hbody⟩ := hInv k ev s dir seed pqSalt n rIdx par hk_tr hev
    have hlen : (tr.append x).length = tr.length + 1 := by
      simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    have hpar_lt : par < tr.length := Nat.lt_of_le_of_lt hpar_le hch_lt
    refine ⟨hpar_le, by omega, fun e hpar => ?_⟩
    rw [at?_append_of_lt hpar_lt] at hpar
    obtain ⟨⟨e', hch, hp, hi⟩, hmid⟩ := hbody e hpar
    refine ⟨⟨e', ?_, hp, hi⟩, fun j hj1 hj2 e'' hj => ?_⟩
    · rw [at?_append_of_lt hch_lt]; exact hch
    · have hj_lt : j < tr.length := Nat.lt_trans hj2 hch_lt
      rw [at?_append_of_lt hj_lt] at hj
      exact hmid j hj1 hj2 e'' hj
  · exact False.elim (hnon ev s dir seed pqSalt n rIdx par hproj hev)

theorem SnapshotChainInv.append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {x : E}
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) : Option XplEvEntry) = none)
    (hInv : SnapshotChainInv tr) :
    SnapshotChainInv (tr.append x) :=
  SnapshotChainInv.append_non_mk (fun _ _ _ _ _ _ _ _ hp => by rw [hnone] at hp; cases hp) hInv

theorem Preserves.inv_logEvent_other (ev : TREvent)
    (hne : ∀ s dir seed pqSalt n rIdx par,
      ev ≠ TREvent.MessageKey s dir seed pqSalt n rIdx par) :
    Preserves SnapshotChainInv (DY.ProtocolEvent.logEvent ev) := by
  intro tr hInv
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
    DY.Traceful.run_pure]
  refine SnapshotChainInv.append_non_mk (fun ev' s dir seed pqSalt n rIdx par hp => ?_) hInv
  rw [proj_inj] at hp
  injection hp with hp
  subst hp
  exact hne s dir seed pqSalt n rIdx par

theorem Preserves.inv_sendMessage (m : Bytes) :
    Preserves SnapshotChainInv (DY.Network.sendMessage m) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_mk]
  exact SnapshotChainInv.append_other rfl h

theorem Preserves.inv_genRand (n : Nat) :
    Preserves SnapshotChainInv (DY.Random.genRand n) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact SnapshotChainInv.append_other rfl h

theorem Preserves.inv_storeTRState (p : Participant) (st : TRState) :
    Preserves SnapshotChainInv (PersistentLocalState.storeLocalState p st) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact SnapshotChainInv.append_other rfl h

theorem Preserves.inv_storePQState (p : Participant) (st : PQXDHState) :
    Preserves SnapshotChainInv (PersistentLocalState.storeLocalState p st) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact SnapshotChainInv.append_other rfl h

theorem Preserves.inv_logPQEvent (ev : PQXDHEvent) :
    Preserves SnapshotChainInv (DY.ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
    DY.Traceful.run_pure]
  exact SnapshotChainInv.append_other rfl h

theorem Preserves.inv_logCEvent (ev : ComposedEvent) :
    Preserves SnapshotChainInv (DY.ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
    DY.Traceful.run_pure]
  exact SnapshotChainInv.append_other rfl h

theorem Preserves.inv_logSkippedKeys (s : SessionInfo) (pk : Bytes) (rIdx src : Nat) :
    ∀ (ck : Bytes) (idx : UInt32) (k : Nat),
      Preserves SnapshotChainInv (logSkippedKeys s pk rIdx src ck idx k)
  | _, _, 0 => Preserves.pure _ ()
  | ck, idx, k + 1 => by
    unfold logSkippedKeys
    exact Preserves.bind
      (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h)) fun _ =>
      Preserves.inv_logSkippedKeys s pk rIdx src _ _ k

/-! ## `IsLatestRoleSnapshot` and `logMessageKeyAndStore` -/

def IsLatestRoleSnapshot (me : Participant) (st₀ : TRState) (stH : Nat) (tr : ExecTrace) : Prop :=
  (tr.at? stH : Option XplStEntry) = some ⟨⟨me, st₀⟩⟩ ∧
  ∀ j, stH < j → ∀ e'' : XplStEntry, (tr.at? j : Option XplStEntry) = some e'' →
    (e''.st.participant != me || e''.st.state.initiator != st₀.initiator) = true

theorem isLatestRoleSnapshot_of_isCurrentSnapshot {tr : ExecTrace} {me : Participant}
    {st₀ : TRState} {stH : Nat}
    (hcur : isCurrentSnapshot tr stH = true)
    (hst₀ : (tr.at? stH : Option XplStEntry) = some ⟨⟨me, st₀⟩⟩) :
    IsLatestRoleSnapshot me st₀ stH tr := by
  refine ⟨hst₀, fun j hj e'' he'' => ?_⟩
  have hlt : j < tr.length := at?_lt_length he''
  have hmem : j ∈ List.range' (stH + 1) (tr.length - (stH + 1)) := by
    rw [List.mem_range'_1]; omega
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur
  rw [hst₀, List.all_eq_true] at hcur
  have h := hcur j hmem
  rw [he''] at h
  exact h

theorem IsLatestRoleSnapshot.append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {x : E}
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) : Option XplStEntry) = none)
    {me : Participant} {st₀ : TRState} {stH : Nat}
    (h : IsLatestRoleSnapshot me st₀ stH tr) :
    IsLatestRoleSnapshot me st₀ stH (tr.append x) := by
  have hlt : stH < tr.length := at?_lt_length h.1
  refine ⟨by rw [at?_append_of_lt hlt]; exact h.1, fun j hj e'' he'' => ?_⟩
  rcases at?_append_cases he'' with ⟨_, he_tr⟩ | ⟨_, hp⟩
  · exact h.2 j hj e'' he_tr
  · rw [hnone] at hp; cases hp

theorem Preserves.latest_logSkippedKeys (me : Participant) (st₀ : TRState) (stH : Nat)
    (s : SessionInfo) (pk : Bytes) (rIdx src : Nat) :
    ∀ (ck : Bytes) (idx : UInt32) (k : Nat),
      Preserves (IsLatestRoleSnapshot me st₀ stH) (logSkippedKeys s pk rIdx src ck idx k)
  | _, _, 0 => Preserves.pure _ ()
  | ck, idx, k + 1 => by
    unfold logSkippedKeys
    exact Preserves.bind
      (by
        intro tr h
        simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
          Symbolic.DYBridge.DY.Traceful.mk_eq_1]
        exact IsLatestRoleSnapshot.append_other rfl h) fun _ =>
      Preserves.latest_logSkippedKeys me st₀ stH s pk rIdx src _ _ k

theorem SnapshotChainInv.logMessageKeyAndStore_of_latest
    {tr : ExecTrace} {me : Participant} {s : SessionInfo} {dir : KeyDir}
    {seed pqSalt : Bytes} {n : UInt32} {rIdx stH : Nat} {st₀ stC : TRState}
    (hInv : SnapshotChainInv tr)
    (hlat : IsLatestRoleSnapshot me st₀ stH tr)
    (hinit : stC.initiator = st₀.initiator) :
    SnapshotChainInv
      ((logMessageKeyAndStore me s dir seed pqSalt n rIdx stH stC).run tr).2.val := by
  have hstH_lt : stH < tr.length := at?_lt_length hlat.1
  let ev₀ := TREvent.MessageKey s dir seed pqSalt n rIdx stH
  let tr1 := tr.append (⟨ev₀⟩ : XplEvEntry)
  let tr2 := tr1.append (⟨⟨me, stC⟩⟩ : XplStEntry)
  unfold logMessageKeyAndStore
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  change SnapshotChainInv tr2
  have hlen1 : tr1.length = tr.length + 1 := by
    simp [tr1, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hlen2 : tr2.length = tr1.length + 1 := by
    simp [tr2, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  intro k ev s' dir' seed' pqSalt' n' rIdx' par hk hev
  rcases at?_append_cases hk with ⟨_, hk1⟩ | ⟨_, hp⟩
  · rcases at?_append_cases hk1 with ⟨hk_lt, hk_tr⟩ | ⟨rfl, hp1⟩
    · obtain ⟨hpar_le, hch_lt, hbody⟩ := hInv k ev s' dir' seed' pqSalt' n' rIdx' par hk_tr hev
      have hpar_lt : par < tr.length := Nat.lt_of_le_of_lt hpar_le hch_lt
      refine ⟨hpar_le, by omega, fun e hpar => ?_⟩
      rw [at?_append_of_lt (by omega : par < tr1.length), at?_append_of_lt hpar_lt] at hpar
      obtain ⟨⟨e', hch, hp, hi⟩, hmid⟩ := hbody e hpar
      refine ⟨⟨e', ?_, hp, hi⟩, fun j hj1 hj2 e'' hj => ?_⟩
      · rw [at?_append_of_lt (by omega : k + 1 < tr1.length), at?_append_of_lt hch_lt]; exact hch
      · have hj_lt : j < tr.length := Nat.lt_trans hj2 hch_lt
        rw [at?_append_of_lt (by omega : j < tr1.length), at?_append_of_lt hj_lt] at hj
        exact hmid j hj1 hj2 e'' hj
    · rw [proj_inj] at hp1
      injection hp1 with hp1
      subst hp1
      dsimp only at hev
      injection hev with _ _ _ _ _ _ hpar_eq
      subst hpar_eq
      refine ⟨by omega, by omega, fun e hpar => ?_⟩
      rw [at?_append_of_lt (by omega : stH < tr1.length), at?_append_of_lt hstH_lt] at hpar
      rw [hlat.1] at hpar
      injection hpar with he_eq
      subst he_eq
      refine ⟨⟨⟨⟨me, stC⟩⟩, ?_, rfl, hinit⟩, fun j hj1 hj2 e'' hj => ?_⟩
      · rw [← hlen1]; exact DY.Trace.at?_append tr1 (⟨⟨me, stC⟩⟩ : XplStEntry)
      · rw [at?_append_of_lt (by omega : j < tr1.length)] at hj
        rcases at?_append_cases hj with ⟨_, hj_tr⟩ | ⟨_, hp_ev⟩
        · exact hlat.2 j hj1 e'' hj_tr
        · cases hp_ev
  · cases hp

theorem SnapshotChainInv.logMessageKeyAndStore_self
    {tr : ExecTrace} {me : Participant} {s : SessionInfo} {dir : KeyDir}
    {seed pqSalt : Bytes} {n : UInt32} {rIdx : Nat} {stC : TRState}
    (hInv : SnapshotChainInv tr) :
    SnapshotChainInv
      ((logMessageKeyAndStore me s dir seed pqSalt n rIdx (tr.length + 1) stC).run tr).2.val := by
  let ev₀ := TREvent.MessageKey s dir seed pqSalt n rIdx (tr.length + 1)
  let tr1 := tr.append (⟨ev₀⟩ : XplEvEntry)
  let tr2 := tr1.append (⟨⟨me, stC⟩⟩ : XplStEntry)
  unfold logMessageKeyAndStore
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  change SnapshotChainInv tr2
  have hlen1 : tr1.length = tr.length + 1 := by
    simp [tr1, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hlen2 : tr2.length = tr1.length + 1 := by
    simp [tr2, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  intro k ev s' dir' seed' pqSalt' n' rIdx' par hk hev
  rcases at?_append_cases hk with ⟨_, hk1⟩ | ⟨_, hp⟩
  · rcases at?_append_cases hk1 with ⟨hk_lt, hk_tr⟩ | ⟨rfl, hp1⟩
    · obtain ⟨hpar_le, hch_lt, hbody⟩ := hInv k ev s' dir' seed' pqSalt' n' rIdx' par hk_tr hev
      have hpar_lt : par < tr.length := Nat.lt_of_le_of_lt hpar_le hch_lt
      refine ⟨hpar_le, by omega, fun e hpar => ?_⟩
      rw [at?_append_of_lt (by omega : par < tr1.length), at?_append_of_lt hpar_lt] at hpar
      obtain ⟨⟨e', hch, hp, hi⟩, hmid⟩ := hbody e hpar
      refine ⟨⟨e', ?_, hp, hi⟩, fun j hj1 hj2 e'' hj => ?_⟩
      · rw [at?_append_of_lt (by omega : k + 1 < tr1.length), at?_append_of_lt hch_lt]; exact hch
      · have hj_lt : j < tr.length := Nat.lt_trans hj2 hch_lt
        rw [at?_append_of_lt (by omega : j < tr1.length), at?_append_of_lt hj_lt] at hj
        exact hmid j hj1 hj2 e'' hj
    · rw [proj_inj] at hp1
      injection hp1 with hp1
      subst hp1
      dsimp only at hev
      injection hev with _ _ _ _ _ _ hpar_eq
      subst hpar_eq
      refine ⟨Nat.le_refl _, by omega, fun e hpar => ?_⟩
      exact ⟨⟨e, hpar, rfl, rfl⟩, fun j hj1 hj2 _ _ => by omega⟩
  · cases hp

/-! ## Triple Ratchet transition preservation -/

private theorem getLocalState_fst (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 =
      match (tr.at? stH : Option XplStEntry) with
      | some ⟨⟨p, st⟩⟩ => if p = me then some st else none
      | none => none := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1,
    Symbolic.DYBridge.DY.getEntry_eq_1]
  unfold _root_.guard
  rw [run_bind_fst, run_bind_fst, run_bind_snd, Traceful.run_mk]
  rcases (tr.at? stH : Option XplStEntry) with _ | ⟨⟨p, st⟩⟩
  · dsimp only
  · dsimp only
    rw [DY.Traceful.run_pure]
    change (((if p = me then Pure.pure () else Alternative.failure : Traceful Unit) >>= fun _ => Pure.pure st).run tr).1 =
      if p = me then some st else none
    by_cases hp : p = me
    · rw [ite_eq_left_iff.mpr fun h => absurd hp h, ite_eq_left_iff.mpr fun h => absurd hp h]
      rw [run_bind_fst, DY.Traceful.run_pure]
      dsimp only
      rw [DY.Traceful.run_pure]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hp, ite_eq_right_iff.mpr fun h => absurd h hp]
      rw [run_bind_fst, DY.Traceful.run_failure]

private theorem getLocalState_snd (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).2.val = tr :=
  Preserves.getLocalState (S := TRState) (Inv := fun t => t = tr) me stH tr rfl

private theorem bind_getLocalState_cur {P : ExecTrace → Prop}
    (me : Participant) (stH : Nat) {β : Type} {f : TRState → Traceful β}
    (tr : ExecTrace) (hP : P tr) (hcur : isCurrentSnapshot tr stH = true)
    (hf : ∀ st t, P t ∧ IsLatestRoleSnapshot me st stH t → P ((f st).run t).2.val) :
    P ((PersistentLocalState.getLocalState me stH >>= f).run tr).2.val := by
  rw [run_bind_snd, getLocalState_fst, getLocalState_snd]
  rcases he : (tr.at? stH : Option XplStEntry) with _ | ⟨⟨p, st⟩⟩
  · exact hP
  · dsimp only
    by_cases hp : p = me
    · subst hp
      simp only [↓reduceIte]
      exact hf st tr ⟨hP, isLatestRoleSnapshot_of_isCurrentSnapshot hcur he⟩
    · simp only [hp, ↓reduceIte]
      exact hP

private theorem bind_from {P Q : ExecTrace → Prop} {α β : Type}
    {x : Traceful α} {f : α → Traceful β}
    (hx : Preserves (fun t => P t ∧ Q t) x)
    (hf : ∀ a t, P t ∧ Q t → P ((f a).run t).2.val) :
    ∀ t, P t ∧ Q t → P ((x >>= f).run t).2.val := by
  intro t hPQ
  rw [run_bind_snd]
  have hPQ' := hx t hPQ
  rcases (x.run t).1 with _ | a
  · exact hPQ'.1
  · exact hf a _ hPQ'

private theorem bind_guard_from {P Q : ExecTrace → Prop} {q : Prop} [Decidable q]
    {β : Type} {f : Unit → Traceful β}
    (hf : q → ∀ t, P t ∧ Q t → P ((f ()).run t).2.val) :
    ∀ t, P t ∧ Q t → P ((_root_.guard q >>= f).run t).2.val := by
  intro t hPQ
  rw [run_bind_snd]
  unfold _root_.guard
  by_cases hq : q
  · rw [ite_eq_left_iff.mpr fun h => absurd hq h]
    rw [DY.Traceful.run_pure]
    exact hf hq t hPQ
  · rw [ite_eq_right_iff.mpr fun h => absurd h hq]
    rw [DY.Traceful.run_failure]
    exact hPQ.1

theorem inv_messageEncrypt (me : Participant) (stH coinsLen pqIdx : Nat) (tr : ExecTrace)
    (hcur : isCurrentSnapshot tr stH = true) (hInv : SnapshotChainInv tr) :
    SnapshotChainInv ((DY.Libsignal.TripleRatchet.messageEncrypt me stH coinsLen pqIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine bind_getLocalState_cur me stH tr hInv hcur fun st => ?_
  refine bind_from (Preserves.and (Preserves.guardP _) (Preserves.guardP _)) fun _ => ?_
  refine bind_from
    (Preserves.and (Preserves.inv_genRand 32)
      (by intro t h; simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1]; exact IsLatestRoleSnapshot.append_other rfl h)) fun _ => ?_
  refine bind_from
    (Preserves.and (Preserves.inv_genRand coinsLen)
      (by intro t h; simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1]; exact IsLatestRoleSnapshot.append_other rfl h)) fun coins => ?_
  refine bind_from
    (Preserves.and (Preserves.inv_sendMessage _)
      (by intro t h; rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]; exact IsLatestRoleSnapshot.append_other rfl h)) fun _ => ?_
  refine bind_from
    (Preserves.and (Preserves.receiveMessage _) (Preserves.receiveMessage _)) fun pqSalt => ?_
  refine bind_from
    (Preserves.and
      (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h))
      (by intro t h; simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]; exact IsLatestRoleSnapshot.append_other rfl h)) fun _ => ?_
  intro t ⟨hIt, hLt⟩
  rw [run_bind_snd]
  have hIt' :=
    SnapshotChainInv.logMessageKeyAndStore_of_latest
      (s := st.sessionInfo me) (dir := .sender)
      (seed := (kdfCk st.cks).2) (pqSalt := pqSalt) (n := st.ns) (rIdx := st.rIdx)
      (stC := { st with cks := (kdfCk st.cks).1, ns := st.ns + 1,
                        spqr := (DY.Spqr.spqrSend st.spqr coins).1 })
      hIt hLt rfl
  split
  · exact Preserves.inv_sendMessage _ _ hIt'
  · exact hIt'

private theorem bind_ensureReceiverChain_latest {α : Type}
    (me : Participant) (st₀ : TRState) (stH : Nat) (pk : Bytes)
    {f : TRState × RecvChain × Bool → Traceful α}
    (hf : ∀ st c ratcheted,
      st.initiator = st₀.initiator →
      ∀ t, SnapshotChainInv t ∧ IsLatestRoleSnapshot me st₀ stH t →
        SnapshotChainInv ((f (st, c, ratcheted)).run t).2.val) :
    ∀ t, SnapshotChainInv t ∧ IsLatestRoleSnapshot me st₀ stH t →
      SnapshotChainInv ((ensureReceiverChain st₀ pk >>= f).run t).2.val := by
  intro tr ⟨hInv, hlat⟩
  cases hfind : findRecvChain st₀.recv pk with
  | some c =>
    rw [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
    unfold recvChainFor
    dsimp only [TRState.toDRState]
    rw [hfind]
    dsimp only
    rw [run_bind_snd, DY.Traceful.run_pure]
    exact hf st₀ c false rfl tr ⟨hInv, hlat⟩
  | none =>
    by_cases hlo : x25519LowOrder pk = true
    · rw [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
      unfold recvChainFor
      dsimp only [TRState.toDRState]
      rw [hfind]
      dsimp only
      rw [ite_eq_left_iff.mpr fun h => absurd hlo h, run_bind_snd, DY.Traceful.run_failure]
      exact hInv
    · have hlo' : (!x25519LowOrder pk) = true := by
        cases h : x25519LowOrder pk <;> simp_all
      have htr : ((ensureReceiverChain st₀ pk).run tr).2.val =
          tr.append (DY.Random.ExecEntryT.mk 32) := by
        simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]; unfold _root_.guard
        rw [hfind]
        dsimp only
        rw [ite_eq_right_iff.mpr fun h => absurd h hlo]
        dsimp only
        rw [ite_eq_left_iff.mpr fun h => absurd hlo' h]
        simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
          DY.Traceful.run_pure]
      rw [run_bind_snd, htr]
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]; unfold _root_.guard
      rw [hfind]
      dsimp only
      rw [ite_eq_right_iff.mpr fun h => absurd h hlo]
      dsimp only
      rw [ite_eq_left_iff.mpr fun h => absurd hlo' h]
      simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
        DY.Traceful.run_pure]
      refine hf _ _ true ?_ (tr.append (DY.Random.ExecEntryT.mk 32))
        ⟨SnapshotChainInv.append_other rfl hInv, IsLatestRoleSnapshot.append_other rfl hlat⟩
      rfl

private theorem inv_decryptTail (me : Participant) (stH : Nat) (st₀ st : TRState)
    (msg : TRSignalMsg) (c c' : RecvChain) (seed pqSalt spqr' m : Bytes)
    (hinit : st.initiator = st₀.initiator) :
    ∀ t, SnapshotChainInv t ∧ IsLatestRoleSnapshot me st₀ stH t →
      SnapshotChainInv ((do
        logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stH c.chainKey c.index
          (msg.counter.toNat - c.index.toNat)
        DY.ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
        logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter
          c.rIdx stH { st with recv := setRecvChain st.recv c', spqr := spqr' }).run t).2.val := by
  refine bind_from
    (Preserves.and
      (Preserves.inv_logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stH c.chainKey c.index
        (msg.counter.toNat - c.index.toNat))
      (Preserves.latest_logSkippedKeys me st₀ stH (st.sessionInfo me) msg.ratchetKey c.rIdx stH c.chainKey c.index
        (msg.counter.toNat - c.index.toNat))) fun _ => ?_
  refine bind_from
    (Preserves.and
      (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h))
      (by
        intro t h
        simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
          Symbolic.DYBridge.DY.Traceful.mk_eq_1]
        exact IsLatestRoleSnapshot.append_other rfl h)) fun _ t ⟨hIt, hLt⟩ => ?_
  exact SnapshotChainInv.logMessageKeyAndStore_of_latest hIt hLt hinit

theorem inv_messageDecrypt (me : Participant) (stH msgH pqIdx : Nat)
    (spqrMsgIdx : UInt32) (tr : ExecTrace)
    (hcur : isCurrentSnapshot tr stH = true) (hInv : SnapshotChainInv tr) :
    SnapshotChainInv ((DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine bind_getLocalState_cur me stH tr hInv hcur fun st₀ => ?_
  refine bind_from
    (Preserves.and (Preserves.receiveSignalMsg _) (Preserves.receiveSignalMsg _))
    fun msg => ?_
  refine bind_ensureReceiverChain_latest me st₀ stH msg.ratchetKey
    fun st c ratcheted hinit => ?_
  dsimp only
  split
  · next seed c' _ =>
    split
    · next spqr' key _ =>
      refine bind_from
        (Preserves.and (Preserves.inv_sendMessage _)
          (by intro t h; rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]; exact IsLatestRoleSnapshot.append_other rfl h)) fun _ => ?_
      refine bind_from
        (Preserves.and (Preserves.receiveMessage _) (Preserves.receiveMessage _))
        fun pqSalt => ?_
      refine bind_from
        (Preserves.and (Preserves.verifyMacAndDecrypt _ _ _ _)
          (Preserves.verifyMacAndDecrypt _ _ _ _))
        fun m => ?_
      split
      · refine bind_from
          (Preserves.and
            (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h))
            (by
              intro t h
              simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
                Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
                DY.Traceful.run_pure]
              exact IsLatestRoleSnapshot.append_other rfl h)) fun _ => ?_
        refine bind_from
          (Preserves.and
            (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h))
            (by
              intro t h
              simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
                Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
                DY.Traceful.run_pure]
              exact IsLatestRoleSnapshot.append_other rfl h)) fun _ => ?_
        exact inv_decryptTail me stH st₀ st msg c c' seed pqSalt spqr' m hinit
      · exact inv_decryptTail me stH st₀ st msg c c' seed pqSalt spqr' m hinit
    · intro t h; rw [DY.Traceful.run_failure]; exact h.1
  · intro t h; rw [DY.Traceful.run_failure]; exact h.1

theorem inv_messageDecryptSkipped (me : Participant) (stH msgH evH pqIdx : Nat)
    (spqrMsgIdx : UInt32) (tr : ExecTrace)
    (hcur : isCurrentSnapshot tr stH = true) (hInv : SnapshotChainInv tr) :
    SnapshotChainInv ((DY.Libsignal.TripleRatchet.messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine bind_getLocalState_cur me stH tr hInv hcur fun st => ?_
  refine bind_from
    (Preserves.and (Preserves.receiveSignalMsg _) (Preserves.receiveSignalMsg _))
    fun msg => ?_
  refine bind_from
    (Preserves.and (Preserves.getEntry _) (Preserves.getEntry _))
    fun e => ?_
  rcases e with ⟨ev⟩
  cases ev with
  | SkippedKeyStored s pk n seed rIdx sourceStateIdx =>
    dsimp only
    refine bind_guard_from (q := (s = st.sessionInfo me ∧ pk = msg.ratchetKey ∧ n = msg.counter ∧
        (DY.Libsignal.TripleRatchet.findRecvChain st.toDRState.recv pk).isSome = true))
      fun _ => ?_
    refine bind_from
      (Preserves.and (Preserves.guardTrace _) (Preserves.guardTrace _)) fun _ => ?_
    split
    · next spqr' key _ =>
      refine bind_from
        (Preserves.and (Preserves.inv_sendMessage _)
          (by intro t h; rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]; exact IsLatestRoleSnapshot.append_other rfl h)) fun _ => ?_
      refine bind_from
        (Preserves.and (Preserves.receiveMessage _) (Preserves.receiveMessage _))
        fun pqSalt => ?_
      refine bind_from
        (Preserves.and (Preserves.verifyMacAndDecrypt _ _ _ _)
          (Preserves.verifyMacAndDecrypt _ _ _ _)) fun _ => ?_
      refine bind_from
        (Preserves.and
          (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h))
          (by
            intro t h
            simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
              Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
              DY.Traceful.run_pure]
            exact IsLatestRoleSnapshot.append_other rfl h)) fun _ => ?_
      refine bind_from
        (Preserves.and
          (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h))
          (by
            intro t h
            simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
              Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
              DY.Traceful.run_pure]
            exact IsLatestRoleSnapshot.append_other rfl h)) fun _ t' ⟨hIt', hLt'⟩ => ?_
      exact SnapshotChainInv.logMessageKeyAndStore_of_latest hIt' hLt' rfl
    · intro t h; rw [DY.Traceful.run_failure]; exact h.1
  | _ => intro t h; dsimp only; rw [DY.Traceful.run_failure]; exact h.1

/-! ## PQXDH, session-start, and exposure transitions -/

theorem Preserves.inv_ensureReceiverChain (st₀ : TRState) (pk : Bytes) :
    Preserves SnapshotChainInv (ensureReceiverChain st₀ pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  split
  · exact Preserves.pure _ _
  · exact Preserves.bind
      (Preserves.bind (Preserves.guardP _) fun _ =>
        Preserves.bind (Preserves.inv_genRand 32) fun _ => Preserves.pure _ _)
      fun _ => Preserves.pure _ _
  · exact Preserves.failure

theorem Preserves.inv_aliceHandshake (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : BundleHandles) :
    Preserves SnapshotChainInv (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  intro tr hInv
  have h1 : SnapshotChainInv (tr.append (COMPOSED.CompTrace.RndE 32)) :=
    SnapshotChainInv.append_other rfl hInv
  have h2 : SnapshotChainInv
      ((tr.append (COMPOSED.CompTrace.RndE 32)).append (COMPOSED.CompTrace.RndE 32)) :=
    SnapshotChainInv.append_other rfl h1
  have hbind := COMPOSED.CompTrace.bind_aliceHandshake_at (Inv := SnapshotChainInv)
    a b idStateIdx regIdxB h (f := Pure.pure) tr hInv h1
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by rw [DY.Traceful.run_pure]; exact h2)
  have hp : (((DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) >>= Pure.pure).run tr).2.val =
      ((DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h).run tr).2.val := by
    rw [Traceful.run_bind]
    rcases (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h).run tr with ⟨_ | _, _⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)
  rwa [hp] at hbind

theorem Preserves.inv_bobHandshake (b a : Participant) (kh : BobKeyHandles)
    (regIdxA ekIdx ctIdx : Nat) :
    Preserves SnapshotChainInv
      (DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  refine Preserves.bind (Preserves.getKey b kh.ik .identity) fun _ =>
    Preserves.bind (Preserves.getKey b kh.spk .signedPrekey) fun _ =>
    Preserves.bind (Preserves.getKey b kh.pqspk .pqPrekey) fun _ => ?_
  cases kh.opk <;> dsimp only
  · refine Preserves.bind (Preserves.pure _ none) fun _ =>
      Preserves.bind (Preserves.lookupIdentity a regIdxA) fun p => ?_
    rcases p with ⟨_, _⟩; dsimp only
    refine Preserves.bind (Preserves.receiveMessage ekIdx) fun _ =>
      Preserves.bind (Preserves.receiveMessage ctIdx) fun _ =>
      Preserves.bind (Preserves.guardP _) fun _ => ?_
    split
    · exact Preserves.pure _ _
    · exact Preserves.failure
  · refine Preserves.bind (Preserves.getKey b _ .oneTimePrekey) fun o =>
      Preserves.bind (Preserves.pure _ (some o)) fun _ =>
      Preserves.bind (Preserves.lookupIdentity a regIdxA) fun p => ?_
    rcases p with ⟨_, _⟩; dsimp only
    refine Preserves.bind (Preserves.receiveMessage ekIdx) fun _ =>
      Preserves.bind (Preserves.receiveMessage ctIdx) fun _ =>
      Preserves.bind (Preserves.guardP _) fun _ => ?_
    split
    · exact Preserves.pure _ _
    · exact Preserves.failure

theorem Preserves.inv_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : BundleHandles) :
    Preserves SnapshotChainInv (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  exact Preserves.bind (Preserves.inv_aliceHandshake a b idStateIdx regIdxB h) fun _ =>
    Preserves.bind (Preserves.inv_genRand 32) fun _ =>
    Preserves.bind (Preserves.inv_sendMessage _) fun _ =>
    Preserves.bind (Preserves.inv_sendMessage _) fun _ =>
    Preserves.bind Preserves.inv_traceLength fun _ =>
    Preserves.bind (Preserves.inv_logPQEvent _) fun _ =>
    Preserves.bind (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h)) fun _ =>
    Preserves.bind (Preserves.inv_logCEvent _) fun _ =>
    Preserves.inv_storeTRState a _

private theorem logSkippedKeys_run_fst_and_len (s : SessionInfo) (pk : Bytes) (rIdx src : Nat) :
    ∀ (ck : Bytes) (idx : UInt32) (k : Nat) (tr : ExecTrace),
      ((logSkippedKeys s pk rIdx src ck idx k).run tr).1 = some () ∧
      ((logSkippedKeys s pk rIdx src ck idx k).run tr).2.val.length = tr.length + k
  | _, _, 0, tr => by
    unfold logSkippedKeys
    rw [DY.Traceful.run_pure]
    exact ⟨rfl, rfl⟩
  | ck, idx, k + 1, tr => by
    unfold logSkippedKeys
    rw [run_bind_fst, run_bind_snd]
    have hlog1 : ((DY.ProtocolEvent.logEvent
        (TREvent.SkippedKeyStored s pk idx (kdfCk ck).2 rIdx src)).run tr).1 = some () := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
        DY.Traceful.run_pure]
    have hlog2 : ((DY.ProtocolEvent.logEvent
        (TREvent.SkippedKeyStored s pk idx (kdfCk ck).2 rIdx src)).run tr).2.val.length =
        tr.length + 1 := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
        DY.Traceful.run_pure, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2]
    rw [hlog1]
    dsimp only
    obtain ⟨hfst, hlen⟩ := logSkippedKeys_run_fst_and_len s pk rIdx src (kdfCk ck).1 (idx + 1) k
      ((DY.ProtocolEvent.logEvent
        (TREvent.SkippedKeyStored s pk idx (kdfCk ck).2 rIdx src)).run tr).2.val
    exact ⟨hfst, by omega⟩

private theorem Preserves.inv_bobStart_storeTail (b : Participant) (st : TRState)
    (msg : TRSignalMsg) (c c' : RecvChain) (seed pqSalt spqr' m : Bytes) :
    Preserves SnapshotChainInv (do
      let skipped := msg.counter.toNat - c.index.toNat
      let childIdx := (← traceLength) + skipped + 2
      logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
      DY.ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
        msg.counter c.rIdx childIdx
        { st with recv := setRecvChain st.recv c', spqr := spqr' }) := by
  intro tr0 hInv0
  dsimp only
  rw [run_bind_snd]
  have htl1 : (traceLength.run tr0).1 = some tr0.length := by
    unfold traceLength; rw [DY.Traceful.run_mk]
  have htl2 : (traceLength.run tr0).2.val = tr0 := by
    unfold traceLength; rw [DY.Traceful.run_mk]
  rw [htl1, htl2]
  dsimp only
  let skipped := msg.counter.toNat - c.index.toNat
  let childIdx := tr0.length + skipped + 2
  rw [run_bind_snd]
  obtain ⟨hsk_fst, hsk_len⟩ := logSkippedKeys_run_fst_and_len
    (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped tr0
  have hInv1 : SnapshotChainInv
      ((logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped).run tr0).2.val :=
    Preserves.inv_logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped tr0 hInv0
  rw [hsk_fst]
  dsimp only
  let tr1 := ((logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped).run tr0).2.val
  have hlen1 : tr1.length = tr0.length + (msg.counter.toNat - c.index.toNat) := hsk_len
  rw [run_bind_snd]
  have hrec_fst : ((DY.ProtocolEvent.logEvent
      (TREvent.Received b st.peer msg.ratchetKey msg.counter m)).run tr1).1 = some () := by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
      DY.Traceful.run_pure]
  rw [hrec_fst]
  dsimp only
  let tr2 := ((DY.ProtocolEvent.logEvent
      (TREvent.Received b st.peer msg.ratchetKey msg.counter m)).run tr1).2.val
  have hInv2 : SnapshotChainInv tr2 :=
    Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h) tr1 hInv1
  have hlen2 : tr2.length = tr1.length + 1 := by
    simp only [tr2, Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
      DY.Traceful.run_pure, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hchild_eq : childIdx = tr2.length + 1 := by omega
  change SnapshotChainInv
    ((logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
      msg.counter c.rIdx childIdx
      { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr2).2.val
  rw [hchild_eq]
  exact SnapshotChainInv.logMessageKeyAndStore_self hInv2

theorem Preserves.inv_bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves SnapshotChainInv
      (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine Preserves.bind (Preserves.inv_bobHandshake b a kh regIdxA mh.ek mh.ct) fun o =>
    Preserves.bind (Preserves.receiveSignalMsg mh.msg) fun msg =>
    Preserves.bind (Preserves.inv_ensureReceiverChain _ msg.ratchetKey) fun r => ?_
  rcases r with ⟨st, c, ratcheted⟩; dsimp only
  split
  · next seed c' _ =>
    split
    · next spqr' key _ =>
      refine Preserves.bind (Preserves.inv_sendMessage key) fun _ =>
        Preserves.bind (Preserves.receiveMessage pqIdx) fun pqSalt =>
        Preserves.bind (Preserves.verifyMacAndDecrypt st msg pqSalt seed) fun m => ?_
      cases o.opk <;> dsimp only
      · refine Preserves.bind Preserves.inv_traceLength fun _ =>
          Preserves.bind (Preserves.inv_logPQEvent _) fun _ => ?_
        split
        · exact Preserves.bind
            (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h)) fun _ =>
            Preserves.bind
              (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h)) fun _ =>
            Preserves.bind (Preserves.inv_logCEvent _) fun _ =>
            Preserves.inv_bobStart_storeTail b st msg c c' seed pqSalt spqr' m
        · exact Preserves.bind (Preserves.inv_logCEvent _) fun _ =>
            Preserves.inv_bobStart_storeTail b st msg c c' seed pqSalt spqr' m
      · refine Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
          Preserves.bind (Preserves.inv_logPQEvent _) fun _ =>
          Preserves.bind Preserves.inv_traceLength fun _ =>
          Preserves.bind (Preserves.inv_logPQEvent _) fun _ => ?_
        split
        · exact Preserves.bind
            (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h)) fun _ =>
            Preserves.bind
              (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h)) fun _ =>
            Preserves.bind (Preserves.inv_logCEvent _) fun _ =>
            Preserves.inv_bobStart_storeTail b st msg c c' seed pqSalt spqr' m
        · exact Preserves.bind (Preserves.inv_logCEvent _) fun _ =>
            Preserves.inv_bobStart_storeTail b st msg c c' seed pqSalt spqr' m
    · exact Preserves.failure
  · exact Preserves.failure

theorem Preserves.inv_messageEncryptAbort (me : Participant) (stH : Nat) :
    Preserves SnapshotChainInv (DY.Libsignal.TripleRatchet.messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  exact Preserves.bind (Preserves.getLocalState me stH) fun _ =>
    Preserves.bind (Preserves.inv_genRand 32) fun _ => Preserves.failure

theorem Preserves.inv_exposeKey (me : Participant) (stH : Nat)
    (comp : DY.Libsignal.TripleRatchet.KeyComponent) :
    Preserves SnapshotChainInv (DY.Libsignal.TripleRatchet.exposeKey me stH comp) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine Preserves.bind (Preserves.getLocalState me stH) fun st => ?_
  cases comp <;> dsimp only
  · exact Preserves.bind
      (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h)) fun _ =>
      Preserves.inv_sendMessage _
  · exact Preserves.bind
      (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h)) fun _ =>
      Preserves.inv_sendMessage _
  · exact Preserves.bind
      (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h)) fun _ =>
      Preserves.inv_sendMessage _
  · next pk =>
    rcases findRecvChain st.recv pk with _ | c
    · exact Preserves.failure
    · exact Preserves.bind
        (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h)) fun _ =>
        Preserves.inv_sendMessage _

theorem Preserves.inv_exposeSpqr (me : Participant) (stH : Nat) :
    Preserves SnapshotChainInv (DY.Libsignal.TripleRatchet.exposeSpqr me stH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  exact Preserves.bind (Preserves.getLocalState me stH) fun _ =>
    Preserves.bind
      (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h)) fun _ =>
      Preserves.inv_sendMessage _

theorem Preserves.inv_exposeSkipped (evH : Nat) :
    Preserves SnapshotChainInv (DY.Libsignal.TripleRatchet.exposeSkipped evH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine Preserves.bind (Preserves.getEntry evH) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardTrace _) fun _ =>
      Preserves.bind
        (Preserves.inv_logEvent_other _ (by intro _ _ _ _ _ _ _ h; cases h)) fun _ =>
        Preserves.inv_sendMessage _
  · exact Preserves.failure

theorem Preserves.inv_registerIdentity (p : Participant) :
    Preserves SnapshotChainInv (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  exact Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
    Preserves.bind (Preserves.inv_genRand 32) fun _ =>
    Preserves.bind (Preserves.inv_logPQEvent _) fun _ =>
    Preserves.bind (Preserves.inv_sendMessage _) fun _ =>
    Preserves.bind (Preserves.inv_sendMessage _) fun _ =>
    Preserves.inv_storePQState p _

theorem Preserves.inv_registerCorruptIdentity (p : Participant) (ikIdx : Nat) :
    Preserves SnapshotChainInv (DY.Libsignal.PQXDH.registerCorruptIdentity p ikIdx) := by
  unfold DY.Libsignal.PQXDH.registerCorruptIdentity
  exact Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
    Preserves.bind (Preserves.receiveMessage ikIdx) fun _ =>
    Preserves.bind (Preserves.inv_logPQEvent _) fun _ =>
    Preserves.inv_logPQEvent _

theorem Preserves.inv_genSignedPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves SnapshotChainInv (DY.Libsignal.PQXDH.genSignedPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  exact Preserves.bind (Preserves.getKey b idStateIdx .identity) fun _ =>
    Preserves.bind (Preserves.inv_genRand 32) fun _ =>
    Preserves.bind (Preserves.inv_genRand 64) fun _ =>
    Preserves.bind (Preserves.inv_logPQEvent _) fun _ =>
    Preserves.bind (Preserves.inv_storePQState b _) fun _ =>
    Preserves.bind (Preserves.inv_sendMessage _) fun _ =>
    Preserves.bind (Preserves.inv_sendMessage _) fun _ =>
    Preserves.pure _ _

theorem Preserves.inv_genPQPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves SnapshotChainInv (DY.Libsignal.PQXDH.genPQPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  exact Preserves.bind (Preserves.getKey b idStateIdx .identity) fun _ =>
    Preserves.bind (Preserves.inv_genRand 64) fun _ =>
    Preserves.bind (Preserves.inv_genRand 64) fun _ =>
    Preserves.bind (Preserves.inv_logPQEvent _) fun _ =>
    Preserves.bind (Preserves.inv_storePQState b _) fun _ =>
    Preserves.bind (Preserves.inv_sendMessage _) fun _ =>
    Preserves.bind (Preserves.inv_sendMessage _) fun _ =>
    Preserves.pure _ _

theorem Preserves.inv_genOneTimePrekey (b : Participant) :
    Preserves SnapshotChainInv (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  exact Preserves.bind (Preserves.inv_genRand 32) fun _ =>
    Preserves.bind (Preserves.inv_logPQEvent _) fun _ =>
    Preserves.bind (Preserves.inv_storePQState b _) fun _ =>
    Preserves.bind (Preserves.inv_sendMessage _) fun _ =>
    Preserves.pure _ _

theorem Preserves.inv_compromiseIK (p : Participant) (stateIdx : Nat) :
    Preserves SnapshotChainInv (DY.Libsignal.PQXDH.compromiseIK p stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseIK
  exact Preserves.bind (Preserves.getKey p stateIdx .identity) fun _ =>
    Preserves.bind (Preserves.inv_logPQEvent _) fun _ =>
    Preserves.inv_sendMessage _

theorem Preserves.inv_compromiseSPK (b : Participant) (stateIdx : Nat) :
    Preserves SnapshotChainInv (DY.Libsignal.PQXDH.compromiseSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  exact Preserves.bind (Preserves.getKey b stateIdx .signedPrekey) fun _ =>
    Preserves.bind (Preserves.inv_logPQEvent _) fun _ =>
    Preserves.inv_sendMessage _

theorem Preserves.inv_compromisePQSPK (b : Participant) (stateIdx : Nat) :
    Preserves SnapshotChainInv (DY.Libsignal.PQXDH.compromisePQSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  exact Preserves.bind (Preserves.getKey b stateIdx .pqPrekey) fun _ =>
    Preserves.bind (Preserves.inv_logPQEvent _) fun _ =>
    Preserves.inv_sendMessage _

theorem Preserves.inv_compromiseOPK (b : Participant) (stateIdx : Nat) :
    Preserves SnapshotChainInv (DY.Libsignal.PQXDH.compromiseOPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  exact Preserves.bind (Preserves.getKey b stateIdx .oneTimePrekey) fun _ =>
    Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
    Preserves.bind (Preserves.inv_logPQEvent _) fun _ =>
    Preserves.inv_sendMessage _

theorem Preserves.inv_breakDH : Preserves SnapshotChainInv DY.Libsignal.PQXDH.breakDH := by
  unfold DY.Libsignal.PQXDH.breakDH; exact Preserves.inv_logPQEvent _

theorem Preserves.inv_breakKEM : Preserves SnapshotChainInv DY.Libsignal.PQXDH.breakKEM := by
  unfold DY.Libsignal.PQXDH.breakKEM; exact Preserves.inv_logPQEvent _

theorem Preserves.inv_invertDH (pkIdx : Nat) :
    Preserves SnapshotChainInv (DY.Libsignal.PQXDH.invertDH pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertDH
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
    Preserves.bind (Preserves.receiveMessage pkIdx) fun pk => ?_
  rcases extractDhSecretKey (DY.X25519.normalizeX25519Key pk) with _ | sk
  · exact Preserves.failure
  · exact Preserves.inv_sendMessage sk

theorem Preserves.inv_invertKEM (pkIdx : Nat) :
    Preserves SnapshotChainInv (DY.Libsignal.PQXDH.invertKEM pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertKEM
  exact Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
    Preserves.bind (Preserves.receiveMessage pkIdx) fun _ =>
    Preserves.bind
      (by intro tr h; dsimp only [liftM, monadLift, MonadLift.monadLift]; rw [DY.Traceful.run_mk]; exact h)
      fun _ =>
    Preserves.inv_sendMessage _

/-! ## Composed reachability induction -/

theorem snapshotChainInv_step (input : reachability.Input) (tr : ExecTrace)
    (hpre : reachability.PreCond input tr) (hInv : SnapshotChainInv tr) :
    SnapshotChainInv (((reachability.step input).snd).run tr).2.val := by
  rcases input with ⟨⟨k, hk⟩, inp⟩
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k'
  · exact Preserves.inv_sendMessage inp tr hInv
  · exact Preserves.inv_registerIdentity inp tr hInv
  · rcases inp with ⟨p, skIdx⟩
    exact Preserves.inv_registerCorruptIdentity p skIdx tr hInv
  · rcases inp with ⟨b, idStateIdx⟩
    exact Preserves.inv_genSignedPrekey b idStateIdx tr hInv
  · rcases inp with ⟨b, idStateIdx⟩
    exact Preserves.inv_genPQPrekey b idStateIdx tr hInv
  · exact Preserves.inv_genOneTimePrekey inp tr hInv
  · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩
    exact Preserves.inv_aliceStart a b idStateIdx regIdxB bh tr hInv
  · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩
    exact Preserves.inv_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx tr hInv
  · rcases inp with ⟨me, stH, coinsLen, pqIdx⟩
    exact inv_messageEncrypt me stH coinsLen pqIdx tr hpre hInv
  · rcases inp with ⟨me, stH⟩
    exact Preserves.inv_messageEncryptAbort me stH tr hInv
  · rcases inp with ⟨me, stH, msgH, pqIdx, spqrMsgIdx⟩
    exact inv_messageDecrypt me stH msgH pqIdx spqrMsgIdx tr hpre hInv
  · rcases inp with ⟨me, stH, msgH, evH, pqIdx, spqrMsgIdx⟩
    exact inv_messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx tr hpre hInv
  · rcases inp with ⟨me, stH, comp⟩
    exact Preserves.inv_exposeKey me stH comp tr hInv
  · rcases inp with ⟨me, stH⟩
    exact Preserves.inv_exposeSpqr me stH tr hInv
  · exact Preserves.inv_exposeSkipped inp tr hInv
  · rcases inp with ⟨p, stateIdx⟩
    exact Preserves.inv_compromiseIK p stateIdx tr hInv
  · rcases inp with ⟨b, stateIdx⟩
    exact Preserves.inv_compromiseSPK b stateIdx tr hInv
  · rcases inp with ⟨b, stateIdx⟩
    exact Preserves.inv_compromisePQSPK b stateIdx tr hInv
  · rcases inp with ⟨b, stateIdx⟩
    exact Preserves.inv_compromiseOPK b stateIdx tr hInv
  · exact Preserves.inv_breakDH tr hInv
  · exact Preserves.inv_breakKEM tr hInv
  · exact Preserves.inv_invertDH inp tr hInv
  · exact Preserves.inv_invertKEM inp tr hInv
  · omega

theorem snapshotChainInv_of_reachable {tr : ExecTrace}
    (hreach : tr.Reachable DY.Libsignal.Composed.reachability) :
    SnapshotChainInv tr := by
  induction hreach with
  | Base => exact SnapshotChainInv.nil
  | Step input hpre _ ih => exact snapshotChainInv_step input _ hpre ih

/-- On a reachable composed trace, every `TREvent.MessageKey` event at index `k` links its input
snapshot `par` to its output snapshot `k + 1` with no intervening same-role snapshot. -/
theorem snapshotChain_of_reachable {tr : ExecTrace} (hreach : tr.Reachable DY.Libsignal.Composed.reachability)
    {k : Nat} {ev : XplEvEntry}
    {s : DY.Libsignal.TripleRatchet.SessionInfo} {dir : DY.Libsignal.TripleRatchet.KeyDir}
    {seed pqSalt : Bytes} {n : UInt32} {rIdx par : Nat}
    (hk : (tr.at? k : Option XplEvEntry) = some ev)
    (hev : ev.ev = TREvent.MessageKey s dir seed pqSalt n rIdx par)
    {e : XplStEntry} (hpar : (tr.at? par : Option XplStEntry) = some e) :
    par ≤ k + 1 ∧
    (∃ e' : XplStEntry, (tr.at? (k + 1) : Option XplStEntry) = some e' ∧
      e'.st.participant = e.st.participant ∧ e'.st.state.initiator = e.st.state.initiator) ∧
    ∀ j, par < j → j < k + 1 → ∀ e'' : XplStEntry, (tr.at? j : Option XplStEntry) = some e'' →
      (e''.st.participant != e.st.participant ||
        e''.st.state.initiator != e.st.state.initiator) = true := by
  obtain ⟨hpar_le, _, hbody⟩ :=
    snapshotChainInv_of_reachable hreach k ev s dir seed pqSalt n rIdx par hk hev
  exact ⟨hpar_le, hbody e hpar⟩

end Symbolic.Swarm.CREF
