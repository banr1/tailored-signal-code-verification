/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Xpl.Faithful
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
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Move Visibility and Session-Effect Lemmas

Splits `Move.vis` into move-local entries (`xpl_ownVis`) and exposures (`xpl_vis_eq`), characterizes
the head entry kind of a non-setup move (`XplSteps.xpl_vis_head_kind'`), and proves that a move
emitting no visible entries has `NoSessionEffect` (`XplSteps.noSessionEffect_of_vis_nil'`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open

/-! ## Own entries and exposures -/

/-- A move's own entries (`Move.vis` without the exposures). -/
def xpl_ownVis (m : Move) (tr : ExecTrace) : List VisEntry :=
  let tr' := m.next tr
  match m with
  | .aliceStart _ _ _ _ h shown => (aliceVis tr tr' h).take shown
  | .bobStart b _ kh _ mh _ _ shown => (bobVis tr tr' mh (bobOpkPk b kh tr)).take shown
  | .encrypt _ _ _ _ wrap => encVis tr tr' wrap true
  | .encryptAbort .. => encVis tr tr' none false
  | .encryptFail .. => encVis tr tr' none false
  | .decrypt _ stateIdx msgIdx _ _ wrapped => decVis tr tr' stateIdx msgIdx wrapped
  | .decryptSkipped _ stateIdx msgIdx _ _ _ wrapped => decVis tr tr' stateIdx msgIdx wrapped
  | .reject draws =>
    ⟨.recv, [], .unconstrained, none⟩ :: draws.map fun n => ⟨.rng, [], .fresh n, none⟩
  | _ => []

theorem xpl_vis_eq (m : Move) (tr : ExecTrace) :
    m.vis tr = xpl_ownVis m tr ++ exposures tr (m.next tr) := by
  cases m <;> rfl

theorem xpl_pqExposureAt_kind {tr' : ExecTrace} {j : Nat} {v : VisEntry}
    (h : pqExposureAt tr' j = some v) : v.kind = .leak := by
  simp only [pqExposureAt] at h
  split at h <;> (try simp only [Option.some.injEq] at h) <;> (try subst h) <;>
    first | rfl | cases h

theorem xpl_trExposureAt_kind {tr' : ExecTrace} {j : Nat} {v : VisEntry}
    (h : trExposureAt tr' j = some v) : v.kind = .leak := by
  simp only [trExposureAt] at h
  split at h <;> (try simp only [Option.some.injEq] at h) <;> (try subst h) <;>
    first | rfl | cases h

theorem xpl_exposures_kind {tr tr' : ExecTrace} {v : VisEntry} (h : v ∈ exposures tr tr') :
    v.kind = .leak := by
  simp only [exposures, List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨j, _, hj⟩ | ⟨j, _, hj⟩
  · exact xpl_pqExposureAt_kind hj
  · exact xpl_trExposureAt_kind hj

namespace XplSteps

open TripleRatchet (TREvent)
open PQXDH (PQXDHEvent)

theorem xrun_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩
    rfl

theorem xrun_le {α : Type} (x : Traceful α) (tr : ExecTrace) : tr ≤ (x.run tr).2.val :=
  (x.run tr).2.property

theorem xat?_le_some {E : Type} [ExecTraceTypes.Has E] {tr tr' : ExecTrace} (hle : tr ≤ tr')
    {i : Nat} {x : E} (h : (tr.at? i : Option E) = some x) :
    (tr'.at? i : Option E) = some x := by
  have hi : i < tr.length := by
    unfold DY.Trace.at? at h
    split at h
    · assumption
    · cases h
  have hi' : i < tr'.length := Nat.lt_of_lt_of_le hi (DY.Trace.length_le _ _ hle)
  rw [← h]
  simp only [DY.Trace.at?, hi, hi', ↓reduceDIte]
  rw [← DY.Trace.at_le tr tr' i hi hle]

theorem xbind_fix {α β : Type} {x : Traceful α} {f : α → Traceful β} {tr : ExecTrace}
    (P : ExecTrace → Prop) (hx : (x.run tr).2.val = tr) (h0 : P tr)
    (hf : ∀ a, P ((f a).run tr).2.val) : P ((x >>= f).run tr).2.val := by
  rw [xrun_bind_snd]
  split
  · rw [hx]; exact hf _
  · rw [hx]; exact h0

theorem xbind_mono {α β : Type} {x : Traceful α} {f : α → Traceful β} {tr : ExecTrace}
    (P : ExecTrace → Prop) (hP : ∀ t t', t ≤ t' → P t → P t') (hx : P (x.run tr).2.val) :
    P ((x >>= f).run tr).2.val := by
  rw [xrun_bind_snd]
  split
  · exact hP _ _ (xrun_le _ _) hx
  · exact hx

/-- `x` never changes the trace. -/
def XFix {α : Type} (x : Traceful α) : Prop := ∀ tr, (x.run tr).2.val = tr

theorem xfix_bind {α β : Type} {x : Traceful α} {f : α → Traceful β} (hx : XFix x)
    (hf : ∀ a, XFix (f a)) : XFix (x >>= f) := by
  intro tr; rw [xrun_bind_snd]; split
  · rw [hx]; exact hf _ _
  · exact hx tr

theorem xfix_pure {α : Type} (a : α) : XFix (pure a : Traceful α) :=
  fun _ => by simp only [DY.Traceful.run_pure]
theorem xfix_failure {α : Type} : XFix (failure : Traceful α) :=
  fun _ => by simp only [DY.Traceful.run_failure]
theorem xfix_getEntry {E : Type} [ExecTraceTypes.Has E] (i : Nat) :
    XFix (getEntry i : Traceful E) :=
  fun _ => by simp only [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]
theorem xfix_guard (p : Prop) [Decidable p] : XFix (_root_.guard p : Traceful Unit) := by
  intro tr; unfold _root_.guard; split <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

theorem xfix_getLocalState {StateT : Type}
    [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT StateT)] (me : Participant) (i : Nat) :
    XFix (PersistentLocalState.getLocalState me i : Traceful StateT) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact xfix_bind (xfix_bind (xfix_getEntry _) fun _ => xfix_pure _) fun _ =>
    xfix_bind (xfix_guard _) fun _ => xfix_pure _

theorem xrun_bind_unit {α : Type} (x : Traceful α) (tr : ExecTrace) :
    ((x >>= fun _ => (pure () : Traceful Unit)).run tr).2.val = (x.run tr).2.val := by
  rw [xrun_bind_snd]; split
  · rw [DY.Traceful.run_pure]
  · rfl

/-- A fresh value sits at index `tr.length` of `t`. -/
def XRandAt (tr t : ExecTrace) : Prop :=
  ∃ e : DY.Random.ExecEntryT, (t.at? tr.length : Option DY.Random.ExecEntryT) = some e

theorem xrandAt_mono (tr : ExecTrace) : ∀ t t', t ≤ t' → XRandAt tr t → XRandAt tr t' :=
  fun _ _ hle ⟨e, he⟩ => ⟨e, xat?_le_some hle he⟩

theorem xrandAt_genRand (n : Nat) (tr : ExecTrace) :
    XRandAt tr ((DY.Random.genRand n : Traceful DY.Bytes).run tr).2.val := by
  have h : ((DY.Random.genRand n : Traceful DY.Bytes).run tr).2.val =
      tr.append (⟨n⟩ : DY.Random.ExecEntryT) := by
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
  rw [h]
  exact ⟨⟨n⟩, Trace.at?_append tr (⟨n⟩ : DY.Random.ExecEntryT)⟩

theorem xpl_messageEncrypt_shape (me : Participant) (stateIdx coinsLen pqIdx : Nat)
    (tr : ExecTrace) :
    ((TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx).run tr).2.val = tr ∨
      XRandAt tr ((TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx).run tr).2.val := by
  unfold TripleRatchet.messageEncrypt
  refine xbind_fix (fun t => t = tr ∨ XRandAt tr t) (xfix_getLocalState _ _ tr) (Or.inl rfl)
    fun st => ?_
  refine xbind_fix (fun t => t = tr ∨ XRandAt tr t) (xfix_guard _ tr) (Or.inl rfl) fun _ => ?_
  exact Or.inr (xbind_mono (XRandAt tr) (xrandAt_mono tr) (xrandAt_genRand 32 tr))

/-- `x` fails and leaves the trace unchanged. -/
def XStuck {α : Type} (x : Traceful α) (tr : ExecTrace) : Prop :=
  (x.run tr).1 = none ∧ (x.run tr).2.val = tr

theorem xstuck_bind {α β : Type} {x : Traceful α} {f : α → Traceful β} {tr : ExecTrace}
    (hx : XStuck x tr) : XStuck (x >>= f) tr := by
  obtain ⟨h1, h2⟩ := hx
  constructor
  · rw [Traceful.run_bind]; rcases hxr : x.run tr with ⟨_ | a, t1⟩
    · rfl
    · rw [hxr] at h1; cases h1
  · rw [xrun_bind_snd, h1]; exact h2

theorem xstuck_receiveMessage {tr : ExecTrace} {i : Nat}
    (h : tr.getMessageSentAt i = none) : XStuck (Network.receiveMessage i : Traceful DY.Bytes) tr := by
  have h' : (tr.at? i : Option Network.ExecEntryT) = none := by
    simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at h; split at h
    · assumption
    · cases h
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact xstuck_bind ⟨by
    simp only [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]
    exact h', xfix_getEntry i tr⟩

theorem xstuck_receiveSignalMsg {tr : ExecTrace} {i : Nat}
    (h : tr.getMessageSentAt i = none) : XStuck (TripleRatchet.receiveSignalMsg i) tr := by
  unfold TripleRatchet.receiveSignalMsg
  exact xstuck_bind (xstuck_receiveMessage h)

theorem xpl_messageDecrypt_stuck {me : Participant} {stateIdx msgIdx pqIdx : Nat}
    {spqrMsgIdx : UInt32} {tr : ExecTrace} (h : tr.getMessageSentAt msgIdx = none) :
    ((TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val = tr := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  exact xbind_fix (· = tr) (xfix_getLocalState _ _ tr) rfl fun _ =>
    (xstuck_bind (xstuck_receiveSignalMsg h)).2

theorem xpl_messageDecryptSkipped_stuck {me : Participant} {stateIdx msgIdx k pqIdx : Nat}
    {spqrMsgIdx : UInt32} {tr : ExecTrace} (h : tr.getMessageSentAt msgIdx = none) :
    ((TripleRatchet.messageDecryptSkipped me stateIdx msgIdx k pqIdx spqrMsgIdx).run tr).2.val =
      tr := by
  unfold TripleRatchet.messageDecryptSkipped
  exact xbind_fix (· = tr) (xfix_getLocalState _ _ tr) rfl fun _ =>
    (xstuck_bind (xstuck_receiveSignalMsg h)).2

def xplPqLeakEv : PQXDH.PQXDHEvent → Bool
  | .CompromisedIK .. | .CompromisedSPK .. | .CompromisedOPK .. | .CompromisedPQSPK .. => true
  | _ => false

def xplTrLeakEv : TripleRatchet.TREvent → Bool
  | .ExposedRK .. | .ExposedDHs .. | .ExposedCKs .. | .ExposedCKr .. | .ExposedMK ..
  | .ExposedSpqr .. => true
  | _ => false

/-- A compromise or exposure event sits at index `tr.length` of `t`. -/
def XLeakAt (tr t : ExecTrace) : Prop :=
  (∃ e : ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent,
      (t.at? tr.length : Option _) = some e ∧ xplPqLeakEv e.ev = true) ∨
    (∃ e : ProtocolEvent.ExecEntryT TripleRatchet.TREvent,
      (t.at? tr.length : Option _) = some e ∧ xplTrLeakEv e.ev = true)

theorem xleakAt_mono (tr : ExecTrace) : ∀ t t', t ≤ t' → XLeakAt tr t → XLeakAt tr t' := by
  rintro t t' hle (⟨e, he, hl⟩ | ⟨e, he, hl⟩)
  · exact Or.inl ⟨e, xat?_le_some hle he, hl⟩
  · exact Or.inr ⟨e, xat?_le_some hle he, hl⟩

theorem xlt_of_at?_some {E : Type} [ExecTraceTypes.Has E] {t : ExecTrace} {i : Nat} {e : E}
    (h : (t.at? i : Option E) = some e) : i < t.length := by
  unfold DY.Trace.at? at h
  split at h
  · assumption
  · cases h

theorem xpl_exposures_ne_nil {tr t : ExecTrace} (h : XLeakAt tr t) : exposures tr t ≠ [] := by
  have hmem : ∀ {i}, tr.length ≤ i → i < t.length → i ∈ newIndices tr t := by
    intro i h1 h2; simp only [newIndices, List.mem_range']; exact ⟨i - tr.length, by omega, by omega⟩
  rcases h with ⟨e, he, hl⟩ | ⟨e, he, hl⟩
  · have hev : t.getEventAt PQXDH.PQXDHEvent tr.length = some e.ev := by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]; rw [he]
    obtain ⟨v, hv⟩ : ∃ v, pqExposureAt t tr.length = some v := by
      unfold pqExposureAt; rw [hev]
      revert hl; cases e.ev <;> simp [xplPqLeakEv]
    intro hnil
    have : v ∈ exposures tr t := by
      unfold exposures
      exact List.mem_append_left _
        (List.mem_filterMap.2 ⟨_, hmem (Nat.le_refl _) (xlt_of_at?_some he), hv⟩)
    rw [hnil] at this; cases this
  · have hev : t.getEventAt TripleRatchet.TREvent tr.length = some e.ev := by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]; rw [he]
    obtain ⟨v, hv⟩ : ∃ v, trExposureAt t tr.length = some v := by
      unfold trExposureAt; rw [hev]
      revert hl; cases e.ev <;> simp [xplTrLeakEv]
    intro hnil
    have : v ∈ exposures tr t := by
      unfold exposures
      exact List.mem_append_right _
        (List.mem_filterMap.2 ⟨_, hmem (Nat.le_refl _) (xlt_of_at?_some he), hv⟩)
    rw [hnil] at this; cases this

theorem xleakAt_logEvent_pq (ev : PQXDH.PQXDHEvent) (hl : xplPqLeakEv ev = true)
    (tr : ExecTrace) : XLeakAt tr ((ProtocolEvent.logEvent ev : Traceful Unit).run tr).2.val := by
  have h : ((ProtocolEvent.logEvent ev : Traceful Unit).run tr).2.val =
      tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent) := by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
  rw [h]
  exact Or.inl ⟨⟨ev⟩, Trace.at?_append tr (⟨ev⟩ : ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent), hl⟩

theorem xleakAt_logEvent_tr (ev : TripleRatchet.TREvent) (hl : xplTrLeakEv ev = true)
    (tr : ExecTrace) : XLeakAt tr ((ProtocolEvent.logEvent ev : Traceful Unit).run tr).2.val := by
  have h : ((ProtocolEvent.logEvent ev : Traceful Unit).run tr).2.val =
      tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT TripleRatchet.TREvent) := by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
  rw [h]
  exact Or.inr ⟨⟨ev⟩, Trace.at?_append tr (⟨ev⟩ : ProtocolEvent.ExecEntryT TripleRatchet.TREvent), hl⟩

theorem xfix_getKey (p : Participant) (i : Nat) (k : PQXDH.KeyKind) :
    XFix (PQXDH.getKey p i k) := by
  unfold PQXDH.getKey
  exact xfix_bind (xfix_getLocalState _ _) fun _ => xfix_bind (xfix_guard _) fun _ => xfix_pure _

theorem xpl_leak_shape {m : Move} (hk : LeakKind m) (tr : ExecTrace) :
    m.next tr = tr ∨ XLeakAt tr (m.next tr) := by
  have hP := xleakAt_mono tr
  cases m <;> simp only [LeakKind] at hk <;> unfold Move.next Move.act <;> rw [xrun_bind_unit]
  case compromiseIK =>
    unfold PQXDH.compromiseIK
    exact xbind_fix (fun t => t = tr ∨ XLeakAt tr t) (xfix_getKey _ _ _ tr) (Or.inl rfl) fun _ =>
      Or.inr (xbind_mono _ hP (xleakAt_logEvent_pq _ rfl tr))
  case compromiseSPK =>
    unfold PQXDH.compromiseSPK
    exact xbind_fix (fun t => t = tr ∨ XLeakAt tr t) (xfix_getKey _ _ _ tr) (Or.inl rfl) fun _ =>
      Or.inr (xbind_mono _ hP (xleakAt_logEvent_pq _ rfl tr))
  case compromisePQSPK =>
    unfold PQXDH.compromisePQSPK
    exact xbind_fix (fun t => t = tr ∨ XLeakAt tr t) (xfix_getKey _ _ _ tr) (Or.inl rfl) fun _ =>
      Or.inr (xbind_mono _ hP (xleakAt_logEvent_pq _ rfl tr))
  case compromiseOPK =>
    unfold PQXDH.compromiseOPK
    exact xbind_fix (fun t => t = tr ∨ XLeakAt tr t) (xfix_getKey _ _ _ tr) (Or.inl rfl) fun _ =>
      xbind_fix (fun t => t = tr ∨ XLeakAt tr t)
        (by unfold PQXDH.guardTrace; simp only [DY.Traceful.run_mk])
        (Or.inl rfl) fun _ =>
      Or.inr (xbind_mono _ hP (xleakAt_logEvent_pq _ rfl tr))
  case exposeKey me stateIdx k =>
    unfold TripleRatchet.exposeKey
    refine xbind_fix (fun t => t = tr ∨ XLeakAt tr t) (xfix_getLocalState _ _ tr) (Or.inl rfl)
      fun st => ?_
    cases k with
    | ckr pk =>
      dsimp only
      split
      · exact Or.inr (xbind_mono _ hP (xleakAt_logEvent_tr _ rfl tr))
      · exact Or.inl (xfix_failure tr)
    | _ => exact Or.inr (xbind_mono _ hP (xleakAt_logEvent_tr _ rfl tr))
  case exposeSpqr =>
    unfold TripleRatchet.exposeSpqr
    exact xbind_fix (fun t => t = tr ∨ XLeakAt tr t) (xfix_getLocalState _ _ tr) (Or.inl rfl)
      fun _ => Or.inr (xbind_mono _ hP (xleakAt_logEvent_tr _ rfl tr))
  case exposeSkipped =>
    unfold TripleRatchet.exposeSkipped
    refine xbind_fix (fun t => t = tr ∨ XLeakAt tr t) (xfix_getEntry _ tr) (Or.inl rfl) fun e => ?_
    split
    · exact xbind_fix (fun t => t = tr ∨ XLeakAt tr t)
        (by simp only [TripleRatchet.guardTrace, DY.Traceful.run_mk]) (Or.inl rfl) fun _ =>
        Or.inr (xbind_mono _ hP (xleakAt_logEvent_tr _ rfl tr))
    · exact Or.inl (xfix_failure tr)

theorem xtrace_append_at_length {Entry E1 : Type} [DY.TraceEntryHas E1 Entry]
    (tr : DY.Trace Entry) (e : E1) (h : tr.length < (tr.append e).length) :
    (tr.append e).at tr.length h = DY.TraceEntryHas.inj e := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

/-! ## Self-run lemmas -/

theorem xpl_newIndices_self (tr : ExecTrace) : newIndices tr tr = [] := by
  simp [newIndices]

theorem xpl_exposures_self (tr : ExecTrace) : exposures tr tr = [] := by
  simp [exposures, xpl_newIndices_self]

theorem xpl_newRandoms_self (tr : ExecTrace) : newRandoms tr tr = [] := by
  simp [newRandoms, xpl_newIndices_self]

theorem xpl_receivedPlaintext_self (tr : ExecTrace) : receivedPlaintext tr tr = none := by
  simp [receivedPlaintext, xpl_newIndices_self]

theorem xpl_encSend_self (tr : ExecTrace) (w : Option (Nat × Nat)) : encSend tr tr w = [] := by
  simp [encSend, lastSent]

theorem xpl_encVis_self (tr : ExecTrace) (w : Option (Nat × Nat)) (b : Bool) :
    encVis tr tr w b = [] := by
  cases b <;> simp [encVis, xpl_newRandoms_self, xpl_encSend_self, encDraws]

theorem xpl_decVis_self_none {tr : ExecTrace} {i : Nat} (h : tr.getMessageSentAt i = none)
    (si : Nat) (w : Bool) : decVis tr tr si i w = [] := by
  simp [decVis, h, xpl_newRandoms_self, xpl_receivedPlaintext_self]

theorem xpl_newRandoms_cons {tr t : ExecTrace} (h : XRandAt tr t) :
    ∃ x rest, newRandoms tr t = x :: rest := by
  obtain ⟨e, he⟩ := h
  have hlt := xlt_of_at?_some he
  obtain ⟨k, hk⟩ : ∃ k, t.length - tr.length = k + 1 := ⟨t.length - tr.length - 1, by omega⟩
  refine ⟨(randTerm tr.length e.length, e.length),
    (List.range' (tr.length + 1) k).filterMap fun i =>
      (t.at? i : Option DY.Random.ExecEntryT).map fun e => (randTerm i e.length, e.length), ?_⟩
  unfold newRandoms newIndices
  rw [hk, List.range'_succ, List.filterMap_cons, he]
  rfl

/-! ## Encrypt / decrypt shapes -/

theorem xpl_encrypt_next {me : Participant} {stateIdx coinsLen pqIdx : Nat}
    {w : Option (Nat × Nat)} (tr : ExecTrace) :
    (Move.encrypt me stateIdx coinsLen pqIdx w).next tr = tr ∨
      XRandAt tr ((Move.encrypt me stateIdx coinsLen pqIdx w).next tr) := by
  unfold Move.next Move.act
  rw [xrun_bind_unit]
  exact xpl_messageEncrypt_shape _ _ _ _ tr

theorem xpl_encryptAbort_next {me : Participant} {stateIdx : Nat} (tr : ExecTrace) :
    (Move.encryptAbort me stateIdx).next tr = tr ∨
      XRandAt tr ((Move.encryptAbort me stateIdx).next tr) := by
  unfold Move.next Move.act
  rw [xrun_bind_unit]
  unfold TripleRatchet.messageEncryptAbort
  refine xbind_fix (fun t => t = tr ∨ XRandAt tr t) (xfix_getLocalState _ _ tr) (Or.inl rfl)
    fun _ => ?_
  exact Or.inr (xbind_mono (XRandAt tr) (xrandAt_mono tr) (xrandAt_genRand _ tr))

theorem xpl_encryptFail_next {me : Participant} {stateIdx coinsLen : Nat} (tr : ExecTrace) :
    (Move.encryptFail me stateIdx coinsLen).next tr = tr ∨
      XRandAt tr ((Move.encryptFail me stateIdx coinsLen).next tr) := by
  unfold Move.next Move.act
  exact xbind_fix (fun t => t = tr ∨ XRandAt tr t)
    (by simp only [TripleRatchet.traceLength, DY.Traceful.run_mk]) (Or.inl rfl) fun n => by
    rw [xrun_bind_unit]; exact xpl_messageEncrypt_shape _ _ _ _ tr

theorem xpl_decrypt_next {me : Participant} {stateIdx msgIdx pqIdx : Nat}
    {spqrMsgIdx : UInt32} {w : Bool} {tr : ExecTrace} (h : tr.getMessageSentAt msgIdx = none) :
    (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx w).next tr = tr := by
  unfold Move.next Move.act
  rw [xrun_bind_unit]
  exact xpl_messageDecrypt_stuck h

theorem xpl_decryptSkipped_next {me : Participant} {stateIdx msgIdx k pqIdx : Nat}
    {spqrMsgIdx : UInt32} {w : Bool} {tr : ExecTrace} (h : tr.getMessageSentAt msgIdx = none) :
    (Move.decryptSkipped me stateIdx msgIdx k pqIdx spqrMsgIdx w).next tr = tr := by
  unfold Move.next Move.act
  rw [xrun_bind_unit]
  exact xpl_messageDecryptSkipped_stuck h

/-! ## Head of the own entries -/

theorem xpl_ownVis_head_kind {m : Move} {tr : ExecTrace} (hs : m.isSetup = false)
    (ha : m.LogsSessionCompletion tr) :
    ∀ v ∈ (xpl_ownVis m tr).head?, v.kind = .recv ∨ v.kind = .pt := by
  intro v hv
  cases m
  case setup => cases hs
  case aliceStart a b i j h shown =>
    obtain ⟨hsh, -⟩ := ha
    obtain ⟨k, rfl⟩ : ∃ k, shown = k + 1 := ⟨shown - 1, by omega⟩
    simp [xpl_ownVis, aliceVis] at hv
    subst hv; exact Or.inl rfl
  case bobStart b a kh i mh pq sp shown =>
    obtain ⟨hsh, -⟩ := ha
    obtain ⟨k, rfl⟩ : ∃ k, shown = k + 1 := ⟨shown - 1, by omega⟩
    simp [xpl_ownVis, bobVis] at hv
    subst hv; exact Or.inl rfl
  case encrypt me si cl pq w =>
    rcases xpl_encrypt_next (me := me) (stateIdx := si) (coinsLen := cl) (pqIdx := pq) (w := w) tr
      with h | h
    · simp [xpl_ownVis, h, xpl_encVis_self] at hv
    · obtain ⟨⟨m0, n0⟩, rest, hx⟩ := xpl_newRandoms_cons h
      simp [xpl_ownVis, encVis, hx, encDraws] at hv
      subst hv; exact Or.inr rfl
  case encryptAbort me si =>
    rcases xpl_encryptAbort_next (me := me) (stateIdx := si) tr with h | h
    · simp [xpl_ownVis, h, xpl_encVis_self] at hv
    · obtain ⟨⟨m0, n0⟩, rest, hx⟩ := xpl_newRandoms_cons h
      simp [xpl_ownVis, encVis, hx, encDraws] at hv
      subst hv; exact Or.inr rfl
  case encryptFail me si cl =>
    rcases xpl_encryptFail_next (me := me) (stateIdx := si) (coinsLen := cl) tr with h | h
    · simp [xpl_ownVis, h, xpl_encVis_self] at hv
    · obtain ⟨⟨m0, n0⟩, rest, hx⟩ := xpl_newRandoms_cons h
      simp [xpl_ownVis, encVis, hx, encDraws] at hv
      subst hv; exact Or.inr rfl
  case decrypt me si mi pq sp w =>
    rcases hm : tr.getMessageSentAt mi with _ | b
    · simp [xpl_ownVis, xpl_decrypt_next hm, xpl_decVis_self_none hm] at hv
    · simp [xpl_ownVis, decVis, hm] at hv
      subst hv; exact Or.inl rfl
  case decryptSkipped me si mi k pq sp w =>
    rcases hm : tr.getMessageSentAt mi with _ | b
    · simp [xpl_ownVis, xpl_decryptSkipped_next hm, xpl_decVis_self_none hm] at hv
    · simp [xpl_ownVis, decVis, hm] at hv
      subst hv; exact Or.inl rfl
  case reject draws =>
    simp [xpl_ownVis] at hv
    subst hv; exact Or.inl rfl
  all_goals simp [xpl_ownVis] at hv

theorem xpl_vis_head_kind' {m : Move} {tr : ExecTrace} (hs : m.isSetup = false)
    (ha : m.LogsSessionCompletion tr) :
    ∀ v ∈ (m.vis tr).head?, v.kind = .recv ∨ v.kind = .pt ∨ v.kind = .leak := by
  intro v hv
  rw [xpl_vis_eq] at hv
  rcases hown : xpl_ownVis m tr with _ | ⟨w, ws⟩
  · rw [hown, List.nil_append] at hv
    rcases hex : exposures tr (m.next tr) with _ | ⟨u, us⟩
    · rw [hex] at hv; cases hv
    · rw [hex] at hv
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hv
      subst hv
      exact Or.inr (Or.inr (xpl_exposures_kind (hex ▸ List.mem_cons_self ..)))
  · rw [hown, List.cons_append] at hv
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hv
    subst hv
    rcases xpl_ownVis_head_kind hs ha w (by rw [hown]; rfl) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-! ## No session effect of an invisible move -/

theorem xpl_noEff_of_next_eq {m : Move} {tr : ExecTrace} (h : m.next tr = tr) :
    NoSessionEffect tr m := by
  intro i hi
  rw [h, xpl_newIndices_self] at hi
  cases hi

theorem xpl_noEff_attackerSend (t : DY.Bytes) (tr : ExecTrace) :
    NoSessionEffect tr (.attackerSend t) := by
  have hn : (Move.attackerSend t).next tr = tr.append (⟨t⟩ : Network.ExecEntryT) := by
    unfold Move.next Move.act
    rw [xrun_bind_unit]
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  intro i hi
  rw [hn] at hi ⊢
  have hlen : (tr.append (⟨t⟩ : Network.ExecEntryT)).length = tr.length + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hlt : tr.length < (tr.append (⟨t⟩ : Network.ExecEntryT)).length := by omega
  have hi' : i = tr.length := by
    simp only [newIndices, List.mem_range'] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    omega
  subst hi'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length]; rfl
  · exact Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.nonSessionPQAt_of_eq_none
      (by simp only [Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length]; rfl)
  · simp only [Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length]; rfl
  · simp only [Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length]; rfl

theorem xpl_noEff_leak {m : Move} {tr : ExecTrace} (hk : LeakKind m)
    (hex : exposures tr (m.next tr) = []) : NoSessionEffect tr m := by
  rcases xpl_leak_shape hk tr with h | h
  · exact xpl_noEff_of_next_eq h
  · exact absurd hex (xpl_exposures_ne_nil h)

theorem noSessionEffect_of_vis_nil' {m : Move} {tr : ExecTrace} (hs : m.isSetup = false)
    (ha : m.LogsSessionCompletion tr) (hv : m.vis tr = []) : NoSessionEffect tr m := by
  rw [xpl_vis_eq, List.append_eq_nil_iff] at hv
  obtain ⟨hown, hex⟩ := hv
  cases m
  case setup => cases hs
  case aliceStart a b i j h shown =>
    obtain ⟨hsh, -⟩ := ha
    obtain ⟨k, rfl⟩ : ∃ k, shown = k + 1 := ⟨shown - 1, by omega⟩
    simp [xpl_ownVis, aliceVis] at hown
  case bobStart b a kh i mh pq sp shown =>
    obtain ⟨hsh, -⟩ := ha
    obtain ⟨k, rfl⟩ : ∃ k, shown = k + 1 := ⟨shown - 1, by omega⟩
    simp [xpl_ownVis, bobVis] at hown
  case encrypt me si cl pq w =>
    rcases xpl_encrypt_next (me := me) (stateIdx := si) (coinsLen := cl) (pqIdx := pq) (w := w) tr
      with h | h
    · exact xpl_noEff_of_next_eq h
    · obtain ⟨⟨m0, n0⟩, rest, hx⟩ := xpl_newRandoms_cons h
      simp [xpl_ownVis, encVis, hx, encDraws] at hown
  case encryptAbort me si =>
    rcases xpl_encryptAbort_next (me := me) (stateIdx := si) tr with h | h
    · exact xpl_noEff_of_next_eq h
    · obtain ⟨⟨m0, n0⟩, rest, hx⟩ := xpl_newRandoms_cons h
      simp [xpl_ownVis, encVis, hx, encDraws] at hown
  case encryptFail me si cl =>
    rcases xpl_encryptFail_next (me := me) (stateIdx := si) (coinsLen := cl) tr with h | h
    · exact xpl_noEff_of_next_eq h
    · obtain ⟨⟨m0, n0⟩, rest, hx⟩ := xpl_newRandoms_cons h
      simp [xpl_ownVis, encVis, hx, encDraws] at hown
  case decrypt me si mi pq sp w =>
    rcases hm : tr.getMessageSentAt mi with _ | b
    · exact xpl_noEff_of_next_eq (xpl_decrypt_next hm)
    · simp [xpl_ownVis, decVis, hm] at hown
  case decryptSkipped me si mi k pq sp w =>
    rcases hm : tr.getMessageSentAt mi with _ | b
    · exact xpl_noEff_of_next_eq (xpl_decryptSkipped_next hm)
    · simp [xpl_ownVis, decVis, hm] at hown
  case reject draws => simp [xpl_ownVis] at hown
  case attackerSend t => exact xpl_noEff_attackerSend t tr
  case brkDH =>
    unfold NoSessionEffect Move.next Move.act PQXDH.breakDH; dsimp only
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.break_append_noSessionAt tr .BrokenDH rfl
  case brkKEM =>
    unfold NoSessionEffect Move.next Move.act PQXDH.breakKEM; dsimp only
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.break_append_noSessionAt tr .BrokenKEM rfl
  all_goals exact xpl_noEff_leak trivial hex

end XplSteps

end Symbolic.Swarm.CREF
