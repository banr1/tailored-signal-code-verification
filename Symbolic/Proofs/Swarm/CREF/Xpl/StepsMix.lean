/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Xpl.Steps
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
# Quiet and Leak-Free Move Transitions

Establishes session-effect and exposure properties of composed `Move` transitions:
`noSessionEffect_of_vis_nil`, `noSessionEffect_aliceStart_short`, `noSessionEffect_of_no_accept`,
`exposures_nil_of_not_leakKind`, and `xpl_vis_head_kind`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open

namespace XplSteps

open TripleRatchet (TREvent TRState)
open PQXDH (PQXDHEvent)

/-! ## Quiet steps: no session entry from an index on -/

/-- No session entry (stored state, PQXDH / TR / composed event) at index `i` of `t`. -/
def XNone (t : ExecTrace) (i : Nat) : Prop :=
  (t.at? i : Option (PersistentGlobalState.State.ExecEntryT
      (PersistentLocalState.LocalState TRState))) = none ∧
    (t.at? i : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none ∧
    (t.at? i : Option (ProtocolEvent.ExecEntryT TREvent)) = none ∧
    (t.at? i : Option (ProtocolEvent.ExecEntryT ComposedEvent)) = none

/-- No session entry in `t` from index `n` on. -/
def XQuietFrom (n : Nat) (t : ExecTrace) : Prop := ∀ i, n ≤ i → XNone t i

/-- `x` never adds a session entry. -/
def XQuiet {α : Type} (x : Traceful α) : Prop :=
  ∀ tr, XQuietFrom tr.length (x.run tr).2.val

theorem xat?_le_eq {E : Type} [ExecTraceTypes.Has E] {t t' : ExecTrace} (hle : t ≤ t')
    {i : Nat} (hi : i < t.length) : (t'.at? i : Option E) = (t.at? i : Option E) := by
  have hi' : i < t'.length := Nat.lt_of_lt_of_le hi (DY.Trace.length_le _ _ hle)
  simp only [DY.Trace.at?, hi, hi', ↓reduceDIte]
  rw [← DY.Trace.at_le t t' i hi hle]

theorem xnone_le {t t' : ExecTrace} (hle : t ≤ t') {i : Nat} (hi : i < t.length)
    (h : XNone t i) : XNone t' i := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨(xat?_le_eq hle hi).trans h1, (xat?_le_eq hle hi).trans h2,
    (xat?_le_eq hle hi).trans h3, (xat?_le_eq hle hi).trans h4⟩

theorem xnone_of_ge {t : ExecTrace} {i : Nat} (hi : t.length ≤ i) : XNone t i := by
  have hn : ∀ {E : Type} [ExecTraceTypes.Has E], (t.at? i : Option E) = none := by
    intro E _; unfold DY.Trace.at?; split
    · omega
    · rfl
  exact ⟨hn, hn, hn, hn⟩

theorem xquietFrom_trans {n : Nat} {t t' : ExecTrace} (hle : t ≤ t')
    (h1 : XQuietFrom n t) (h2 : XQuietFrom t.length t') : XQuietFrom n t' := by
  intro i hi
  by_cases hlt : i < t.length
  · exact xnone_le hle hlt (h1 i hi)
  · exact h2 i (by omega)

theorem xquietFrom_self (t : ExecTrace) : XQuietFrom t.length t :=
  fun _ hi => xnone_of_ge hi

theorem xquiet_bind {α β : Type} {x : Traceful α} {f : α → Traceful β} (hx : XQuiet x)
    (hf : ∀ a, XQuiet (f a)) : XQuiet (x >>= f) := by
  intro tr
  rw [xrun_bind_snd]
  split
  · exact xquietFrom_trans (xrun_le _ _) (hx tr) (hf _ _)
  · exact hx tr

theorem xquiet_of_fix {α : Type} {x : Traceful α} (hx : XFix x) : XQuiet x := by
  intro tr; rw [hx tr]; exact xquietFrom_self tr

theorem xquietFrom_append {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (h1 : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (PersistentGlobalState.State.ExecEntryT
        (PersistentLocalState.LocalState TRState))) = none)
    (h2 : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none)
    (h3 : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT TREvent)) = none)
    (h4 : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT ComposedEvent)) = none) :
    XQuietFrom tr.length (tr.append e) := by
  intro i hi
  have hlen : (tr.append e).length = tr.length + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hlt : tr.length < (tr.append e).length := by omega
  rcases Nat.lt_or_ge tr.length i with hgt | hle
  · exact xnone_of_ge (by omega)
  · obtain rfl : i = tr.length := by omega
    simp only [XNone, DY.Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length]
    exact ⟨h1, h2, h3, h4⟩

theorem xquiet_genRand (n : Nat) : XQuiet (DY.Random.genRand n : Traceful DY.Bytes) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact xquietFrom_append tr (⟨n⟩ : DY.Random.ExecEntryT) rfl rfl rfl rfl

theorem xquiet_sendMessage (b : DY.Bytes) : XQuiet (Network.sendMessage b) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact xquietFrom_append tr (⟨b⟩ : Network.ExecEntryT) rfl rfl rfl rfl

theorem xfix_receiveMessage (i : Nat) : XFix (Network.receiveMessage i : Traceful DY.Bytes) := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact xfix_bind (xfix_getEntry _) fun _ => xfix_pure _

theorem xfix_traceLength : XFix TripleRatchet.traceLength :=
  fun _ => by simp only [TripleRatchet.traceLength, DY.Traceful.run_mk]
theorem xfix_guardOnTrace (p : ExecTrace → Bool) : XFix (PQXDH.guardTrace p) :=
  fun _ => by simp only [PQXDH.guardTrace, DY.Traceful.run_mk]
theorem xfix_guardTrace (p : ExecTrace → Bool) : XFix (TripleRatchet.guardTrace p) :=
  fun _ => by simp only [TripleRatchet.guardTrace, DY.Traceful.run_mk]

local macro "xquiet_step" : tactic =>
  `(tactic| first
    | with_reducible refine xquiet_bind ?_ fun _ => ?_
    | with_reducible exact xquiet_genRand _
    | with_reducible exact xquiet_sendMessage _
    | with_reducible exact xquiet_of_fix (xfix_receiveMessage _)
    | with_reducible exact xquiet_of_fix (xfix_getKey _ _ _)
    | with_reducible exact xquiet_of_fix (xfix_getLocalState _ _)
    | with_reducible exact xquiet_of_fix (xfix_getEntry _)
    | with_reducible exact xquiet_of_fix (xfix_guard _)
    | with_reducible exact xquiet_of_fix (xfix_traceLength)
    | with_reducible exact xquiet_of_fix (xfix_guardOnTrace _)
    | with_reducible exact xquiet_of_fix (xfix_guardTrace _)
    | with_reducible exact xquiet_of_fix (xfix_pure _)
    | with_reducible exact xquiet_of_fix xfix_failure
    | split)

theorem xquiet_receiveSignalMsg (i : Nat) : XQuiet (TripleRatchet.receiveSignalMsg i) := by
  unfold TripleRatchet.receiveSignalMsg
  repeat' xquiet_step

theorem xquiet_dhRatchetStep (st : TRState) (pk : DY.Bytes) :
    XQuiet (TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  repeat' xquiet_step

theorem xquiet_ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    XQuiet (TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  repeat' (first | with_reducible exact xquiet_dhRatchetStep _ _ | xquiet_step)

theorem xquiet_verifyMacAndDecrypt (st : TRState) (msg : TripleRatchet.TRSignalMsg)
    (s seed : DY.Bytes) : XQuiet (TripleRatchet.verifyMacAndDecrypt st msg s seed) := by
  unfold TripleRatchet.verifyMacAndDecrypt
  repeat' xquiet_step
  all_goals
    refine xquiet_of_fix fun _ => ?_
    cases DY.SymEnc.symDec (TripleRatchet.trMsgKeys s seed).cipherKey
      (TripleRatchet.trMsgKeys s seed).iv msg.ciphertext <;>
      simp only [liftM, monadLift, MonadLift.monadLift, DY.Traceful.run_mk]

/-! ## Quiet until a success event -/

/-- `x` adds no session entry, or reaches `Q`. -/
def XMix {α : Type} (Q : Nat → ExecTrace → Prop) (x : Traceful α) : Prop :=
  ∀ tr, XQuietFrom tr.length (x.run tr).2.val ∨ Q tr.length (x.run tr).2.val

def QAnti (Q : Nat → ExecTrace → Prop) : Prop := ∀ n n' t, n ≤ n' → Q n' t → Q n t
def QMono (Q : Nat → ExecTrace → Prop) : Prop := ∀ n t t', t ≤ t' → Q n t → Q n t'

theorem xmix_of_quiet {α : Type} {Q : Nat → ExecTrace → Prop} {x : Traceful α}
    (h : XQuiet x) : XMix Q x := fun tr => Or.inl (h tr)

theorem xmix_bind_quiet {α β : Type} {Q : Nat → ExecTrace → Prop} (hQ : QAnti Q)
    {x : Traceful α} {f : α → Traceful β} (hx : XQuiet x) (hf : ∀ a, XMix Q (f a)) :
    XMix Q (x >>= f) := by
  intro tr
  rw [xrun_bind_snd]
  split
  · rcases hf _ (x.run tr).2.val with h | h
    · exact Or.inl (xquietFrom_trans (xrun_le _ _) (hx tr) h)
    · exact Or.inr (hQ _ _ _ (DY.Trace.length_le _ _ (xrun_le _ _)) h)
  · exact Or.inl (hx tr)

/-- `x` always reaches `Q`. -/
def XEst {α : Type} (Q : Nat → ExecTrace → Prop) (x : Traceful α) : Prop :=
  ∀ tr, Q tr.length (x.run tr).2.val

theorem xmix_of_est {α : Type} {Q : Nat → ExecTrace → Prop} {x : Traceful α}
    (h : XEst Q x) : XMix Q x := fun tr => Or.inr (h tr)

theorem xest_bind_left {α β : Type} {Q : Nat → ExecTrace → Prop} (hQ : QMono Q)
    {x : Traceful α} {f : α → Traceful β} (hx : XEst Q x) : XEst Q (x >>= f) := by
  intro tr
  rw [xrun_bind_snd]
  split
  · exact hQ _ _ _ (xrun_le _ _) (hx tr)
  · exact hx tr

/-- `x` never fails. -/
def XTotal {α : Type} (x : Traceful α) : Prop := ∀ tr, ∃ a, (x.run tr).1 = some a

theorem xrun_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩
    rfl

theorem xtotal_bind {α β : Type} {x : Traceful α} {f : α → Traceful β} (hx : XTotal x)
    (hf : ∀ a, XTotal (f a)) : XTotal (x >>= f) := by
  intro tr
  obtain ⟨a, ha⟩ := hx tr
  rw [xrun_bind_fst, ha]
  exact hf a _

theorem xest_bind_total {α β : Type} {Q : Nat → ExecTrace → Prop} (hQ : QAnti Q)
    {x : Traceful α} {f : α → Traceful β} (hx : XTotal x) (hf : ∀ a, XEst Q (f a)) :
    XEst Q (x >>= f) := by
  intro tr
  obtain ⟨a, ha⟩ := hx tr
  rw [xrun_bind_snd, ha]
  exact hQ _ _ _ (DY.Trace.length_le _ _ (xrun_le x tr)) (hf a _)

theorem xtotal_logEvent_tr (ev : TREvent) :
    XTotal (ProtocolEvent.logEvent ev : Traceful Unit) :=
  fun _ => ⟨(), by simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    DY.Traceful.run_bind, Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk,
    DY.Traceful.run_pure]⟩
theorem xtotal_logEvent_pq (ev : PQXDHEvent) :
    XTotal (ProtocolEvent.logEvent ev : Traceful Unit) :=
  fun _ => ⟨(), by simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    DY.Traceful.run_bind, Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk,
    DY.Traceful.run_pure]⟩
theorem xtotal_traceLength : XTotal TripleRatchet.traceLength :=
  fun tr => ⟨tr.length, by simp only [TripleRatchet.traceLength, DY.Traceful.run_mk]⟩

theorem xtotal_logSkippedKeys (s : TripleRatchet.SessionInfo) (pk : DY.Bytes) (r src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32), XTotal (TripleRatchet.logSkippedKeys s pk r src ck n k)
  | 0, _, _ => fun _ => ⟨(), by unfold TripleRatchet.logSkippedKeys; simp only [DY.Traceful.run_pure]⟩
  | k + 1, ck, n => by
    rw [TripleRatchet.logSkippedKeys]
    exact xtotal_bind (xtotal_logEvent_tr _) fun _ => xtotal_logSkippedKeys s pk r src k _ _

/-! ## Success events -/

/-- A TR event `p` accepts sits at an index `≥ n` of `t`. -/
def XEvTR (p : TREvent → Bool) (n : Nat) (t : ExecTrace) : Prop :=
  ∃ i ev, n ≤ i ∧ t.getEventAt TREvent i = some ev ∧ p ev = true

/-- A PQXDH event `p` accepts sits at an index `≥ n` of `t`. -/
def XEvPQ (p : PQXDHEvent → Bool) (n : Nat) (t : ExecTrace) : Prop :=
  ∃ i ev, n ≤ i ∧ t.getEventAt PQXDHEvent i = some ev ∧ p ev = true

theorem xgetEventAt_le {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    {t t' : ExecTrace} (hle : t ≤ t') {i : Nat} {ev : E} (h : t.getEventAt E i = some ev) :
    t'.getEventAt E i = some ev := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h ⊢
  rcases he : (t.at? i : Option (ProtocolEvent.ExecEntryT E)) with _ | e
  · rw [he] at h; cases h
  · rw [he] at h; rw [xat?_le_some hle he]; exact h

theorem xlt_of_getEventAt {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    {t : ExecTrace} {i : Nat} {ev : E} (h : t.getEventAt E i = some ev) : i < t.length := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h
  rcases he : (t.at? i : Option (ProtocolEvent.ExecEntryT E)) with _ | e
  · rw [he] at h; cases h
  · exact xlt_of_at?_some he

theorem xevTR_anti (p : TREvent → Bool) : QAnti (XEvTR p) :=
  fun _ _ _ hle ⟨i, ev, hi, he, hp⟩ => ⟨i, ev, Nat.le_trans hle hi, he, hp⟩
theorem xevTR_mono (p : TREvent → Bool) : QMono (XEvTR p) :=
  fun _ _ _ hle ⟨i, ev, hi, he, hp⟩ => ⟨i, ev, hi, xgetEventAt_le hle he, hp⟩
theorem xevPQ_anti (p : PQXDHEvent → Bool) : QAnti (XEvPQ p) :=
  fun _ _ _ hle ⟨i, ev, hi, he, hp⟩ => ⟨i, ev, Nat.le_trans hle hi, he, hp⟩
theorem xevPQ_mono (p : PQXDHEvent → Bool) : QMono (XEvPQ p) :=
  fun _ _ _ hle ⟨i, ev, hi, he, hp⟩ => ⟨i, ev, hi, xgetEventAt_le hle he, hp⟩

theorem xest_logEvent_tr {p : TREvent → Bool} (ev : TREvent) (hp : p ev = true) :
    XEst (XEvTR p) (ProtocolEvent.logEvent ev : Traceful Unit) := by
  intro tr
  have h : ((((ProtocolEvent.logEvent ev : Traceful Unit).run tr).2.val).at? tr.length :
      Option (ProtocolEvent.ExecEntryT TREvent)) = some ⟨ev⟩ := by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact Trace.at?_append tr (⟨ev⟩ : ProtocolEvent.ExecEntryT TREvent)
  refine ⟨tr.length, ev, Nat.le_refl _, ?_, hp⟩
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]; rw [h]

theorem xest_logEvent_pq {p : PQXDHEvent → Bool} (ev : PQXDHEvent) (hp : p ev = true) :
    XEst (XEvPQ p) (ProtocolEvent.logEvent ev : Traceful Unit) := by
  intro tr
  have h : ((((ProtocolEvent.logEvent ev : Traceful Unit).run tr).2.val).at? tr.length :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = some ⟨ev⟩ := by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact Trace.at?_append tr (⟨ev⟩ : ProtocolEvent.ExecEntryT PQXDHEvent)
  refine ⟨tr.length, ev, Nat.le_refl _, ?_, hp⟩
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]; rw [h]

def isReceivedEv : TREvent → Bool
  | .Received .. => true
  | _ => false

/-! ## The four receive / start transitions -/

theorem xquiet_lookupIdentity (p : Participant) (i : Nat) :
    XQuiet (PQXDH.lookupIdentity p i) := by
  unfold PQXDH.lookupIdentity
  repeat' xquiet_step

theorem xquiet_bobHandshake (b a : Participant) (h : PQXDH.BobKeyHandles) (r e c : Nat) :
    XQuiet (PQXDH.bobHandshake b a h r e c) := by
  unfold PQXDH.bobHandshake
  repeat' (first | with_reducible exact xquiet_lookupIdentity _ _ | xquiet_step)

theorem xquiet_aliceHandshake (a b : Participant) (i r : Nat) (h : PQXDH.BundleHandles) :
    XQuiet (PQXDH.aliceHandshake a b i r h) := by
  unfold PQXDH.aliceHandshake
  repeat' (first | with_reducible exact xquiet_lookupIdentity _ _ | xquiet_step)

theorem xmix_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat) (sp : UInt32) :
    XMix (XEvTR isReceivedEv) (TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx sp) := by
  have hA := xevTR_anti isReceivedEv
  have hM := xevTR_mono isReceivedEv
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine xmix_bind_quiet hA (xquiet_of_fix (xfix_getLocalState _ _)) fun st => ?_
  refine xmix_bind_quiet hA (xquiet_receiveSignalMsg _) fun msg => ?_
  refine xmix_bind_quiet hA (xquiet_ensureReceiverChain _ _) fun x => ?_
  rcases x with ⟨st', c, r⟩
  dsimp only
  split
  · split
    · refine xmix_bind_quiet hA (xquiet_sendMessage _) fun _ => ?_
      refine xmix_bind_quiet hA (xquiet_of_fix (xfix_receiveMessage _)) fun _ => ?_
      refine xmix_bind_quiet hA (xquiet_verifyMacAndDecrypt _ _ _ _) fun _ => ?_
      refine xmix_of_est ?_
      try dsimp only
      split
      · refine xest_bind_total hA (xtotal_logEvent_tr _) fun _ => ?_
        refine xest_bind_total hA (xtotal_logEvent_tr _) fun _ => ?_
        refine xest_bind_total hA (xtotal_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
        exact xest_bind_left hM (xest_logEvent_tr _ rfl)
      · refine xest_bind_total hA (xtotal_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
        exact xest_bind_left hM (xest_logEvent_tr _ rfl)
    · exact xmix_of_quiet (xquiet_of_fix xfix_failure)
  · exact xmix_of_quiet (xquiet_of_fix xfix_failure)

/-! ## Compromise and exposure absence -/

/-- No compromise or exposure event at any index `≥ n` of `t`. -/
def XNL (n : Nat) (t : ExecTrace) : Prop :=
  (∀ i ev, n ≤ i → t.getEventAt PQXDHEvent i = some ev → xplPqLeakEv ev = false) ∧
    (∀ i ev, n ≤ i → t.getEventAt TREvent i = some ev → xplTrLeakEv ev = false)

/-- `x` never logs a compromise or exposure event. -/
def XNoLeak {α : Type} (x : Traceful α) : Prop := ∀ tr, XNL tr.length (x.run tr).2.val

theorem xnl_of_quietFrom {n : Nat} {t : ExecTrace} (h : XQuietFrom n t) : XNL n t := by
  refine ⟨fun i ev hi he => ?_, fun i ev hi he => ?_⟩
  · have h2 := (h i hi).2.1
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at he; rw [h2] at he; simp at he
  · have h3 := (h i hi).2.2.1
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at he; rw [h3] at he; simp at he

theorem xnoleak_of_quiet {α : Type} {x : Traceful α} (h : XQuiet x) : XNoLeak x :=
  fun tr => xnl_of_quietFrom (h tr)

theorem xgetEventAt_le_eq {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    {t t' : ExecTrace} (hle : t ≤ t') {i : Nat} (hi : i < t.length) :
    t'.getEventAt E i = t.getEventAt E i := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  rw [xat?_le_eq hle hi]

theorem xnl_trans {n : Nat} {t t' : ExecTrace} (hle : t ≤ t') (h1 : XNL n t)
    (h2 : XNL t.length t') : XNL n t' := by
  refine ⟨fun i ev hi he => ?_, fun i ev hi he => ?_⟩
  · by_cases hlt : i < t.length
    · rw [xgetEventAt_le_eq hle hlt] at he; exact h1.1 i ev hi he
    · exact h2.1 i ev (by omega) he
  · by_cases hlt : i < t.length
    · rw [xgetEventAt_le_eq hle hlt] at he; exact h1.2 i ev hi he
    · exact h2.2 i ev (by omega) he

theorem xnoleak_bind {α β : Type} {x : Traceful α} {f : α → Traceful β} (hx : XNoLeak x)
    (hf : ∀ a, XNoLeak (f a)) : XNoLeak (x >>= f) := by
  intro tr
  rw [xrun_bind_snd]
  split
  · exact xnl_trans (xrun_le _ _) (hx tr) (hf _ _)
  · exact hx tr

theorem xnl_append {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (h1 : ∀ ev, ((tr.append e).at? tr.length : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) =
      some ev → xplPqLeakEv ev.ev = false)
    (h2 : ∀ ev, ((tr.append e).at? tr.length : Option (ProtocolEvent.ExecEntryT TREvent)) =
      some ev → xplTrLeakEv ev.ev = false) :
    XNL tr.length (tr.append e) := by
  have hlen : (tr.append e).length = tr.length + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  refine ⟨fun i ev hi he => ?_, fun i ev hi he => ?_⟩
  · have hlt := xlt_of_getEventAt he
    obtain rfl : i = tr.length := by omega
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at he
    rcases hx : ((tr.append e).at? tr.length : Option (ProtocolEvent.ExecEntryT PQXDHEvent))
      with _ | x
    · rw [hx] at he; cases he
    · rw [hx] at he; simp only [Option.some.injEq] at he
      subst he; exact h1 x hx
  · have hlt := xlt_of_getEventAt he
    obtain rfl : i = tr.length := by omega
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at he
    rcases hx : ((tr.append e).at? tr.length : Option (ProtocolEvent.ExecEntryT TREvent))
      with _ | x
    · rw [hx] at he; cases he
    · rw [hx] at he; simp only [Option.some.injEq] at he
      subst he; exact h2 x hx

theorem xnoleak_logEvent_pq (ev : PQXDHEvent) (hl : xplPqLeakEv ev = false) :
    XNoLeak (ProtocolEvent.logEvent ev : Traceful Unit) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
  refine xnl_append tr (⟨ev⟩ : ProtocolEvent.ExecEntryT PQXDHEvent) (fun x hx => ?_) (fun x hx => ?_)
  · rw [Trace.at?_append] at hx; cases hx; exact hl
  · have hlt : tr.length < (tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT PQXDHEvent)).length := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      omega
    simp only [DY.Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length] at hx
    cases hx

theorem xnoleak_logEvent_tr (ev : TREvent) (hl : xplTrLeakEv ev = false) :
    XNoLeak (ProtocolEvent.logEvent ev : Traceful Unit) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
  refine xnl_append tr (⟨ev⟩ : ProtocolEvent.ExecEntryT TREvent) (fun x hx => ?_) (fun x hx => ?_)
  · have hlt : tr.length < (tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT TREvent)).length := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      omega
    simp only [DY.Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length] at hx
    cases hx
  · rw [Trace.at?_append] at hx; cases hx; exact hl

theorem xnoleak_logEvent_c (ev : ComposedEvent) :
    XNoLeak (ProtocolEvent.logEvent ev : Traceful Unit) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
  refine xnl_append tr (⟨ev⟩ : ProtocolEvent.ExecEntryT ComposedEvent) (fun x hx => ?_) (fun x hx => ?_)
  · have hlt : tr.length < (tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT ComposedEvent)).length := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      omega
    simp only [DY.Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length] at hx
    cases hx
  · have hlt : tr.length < (tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT ComposedEvent)).length := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      omega
    simp only [DY.Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length] at hx
    cases hx

theorem xnoleak_storeLocalState (p : Participant) (st : TRState) :
    XNoLeak (PersistentLocalState.storeLocalState p st) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  have hlt : tr.length < (tr.append (⟨⟨p, st⟩⟩ : PersistentGlobalState.State.ExecEntryT
      (PersistentLocalState.LocalState TRState))).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    omega
  have h1 : ((tr.append (⟨⟨p, st⟩⟩ : PersistentGlobalState.State.ExecEntryT
      (PersistentLocalState.LocalState TRState))).at? tr.length :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by
    simp only [DY.Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length]
    rfl
  have h2 : ((tr.append (⟨⟨p, st⟩⟩ : PersistentGlobalState.State.ExecEntryT
      (PersistentLocalState.LocalState TRState))).at? tr.length :
      Option (ProtocolEvent.ExecEntryT TREvent)) = none := by
    simp only [DY.Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length]
    rfl
  exact xnl_append tr _ (fun x hx => by rw [h1] at hx; cases hx)
    (fun x hx => by rw [h2] at hx; cases hx)

theorem xnoleak_logSkippedKeys (s : TripleRatchet.SessionInfo) (pk : DY.Bytes) (r src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32), XNoLeak (TripleRatchet.logSkippedKeys s pk r src ck n k)
  | 0, _, _ => xnoleak_of_quiet (xquiet_of_fix (xfix_pure _))
  | k + 1, ck, n => by
    rw [TripleRatchet.logSkippedKeys]
    exact xnoleak_bind (xnoleak_logEvent_tr _ rfl) fun _ => xnoleak_logSkippedKeys s pk r src k _ _

theorem xnoleak_logMessageKeyAndStore (me : Participant) (s : TripleRatchet.SessionInfo)
    (dir : TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (r p : Nat)
    (st : TRState) :
    XNoLeak (TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r p st) := by
  unfold TripleRatchet.logMessageKeyAndStore
  exact xnoleak_bind (xnoleak_logEvent_tr _ rfl) fun _ => xnoleak_storeLocalState _ _

local macro "xnl_step" : tactic =>
  `(tactic| first
    | with_reducible refine xnoleak_bind ?_ fun _ => ?_
    | with_reducible refine xnoleak_logEvent_tr _ ?_
    | with_reducible refine xnoleak_logEvent_pq _ ?_
    | with_reducible exact xnoleak_logEvent_c _
    | with_reducible exact xnoleak_storeLocalState _ _
    | with_reducible exact xnoleak_logSkippedKeys _ _ _ _ _ _ _
    | with_reducible exact xnoleak_logMessageKeyAndStore _ _ _ _ _ _ _ _ _
    | with_reducible exact xnoleak_of_quiet (xquiet_bobHandshake _ _ _ _ _ _)
    | with_reducible exact xnoleak_of_quiet (xquiet_aliceHandshake _ _ _ _ _)
    | with_reducible exact xnoleak_of_quiet (xquiet_receiveSignalMsg _)
    | with_reducible exact xnoleak_of_quiet (xquiet_ensureReceiverChain _ _)
    | with_reducible exact xnoleak_of_quiet (xquiet_verifyMacAndDecrypt _ _ _ _)
    | with_reducible exact xnoleak_of_quiet (xquiet_genRand _)
    | with_reducible exact xnoleak_of_quiet (xquiet_sendMessage _)
    | with_reducible exact xnoleak_of_quiet (xquiet_of_fix (xfix_receiveMessage _))
    | with_reducible exact xnoleak_of_quiet (xquiet_of_fix (xfix_getLocalState _ _))
    | with_reducible exact xnoleak_of_quiet (xquiet_of_fix (xfix_getEntry _))
    | with_reducible exact xnoleak_of_quiet (xquiet_of_fix (xfix_guard _))
    | with_reducible exact xnoleak_of_quiet (xquiet_of_fix xfix_traceLength)
    | with_reducible exact xnoleak_of_quiet (xquiet_of_fix (xfix_guardOnTrace _))
    | with_reducible exact xnoleak_of_quiet (xquiet_of_fix (xfix_guardTrace _))
    | with_reducible exact xnoleak_of_quiet (xquiet_of_fix (xfix_pure _))
    | with_reducible exact xnoleak_of_quiet (xquiet_of_fix xfix_failure)
    | split)

theorem xnoleak_messageEncrypt (me : Participant) (si cl pq : Nat) :
    XNoLeak (TripleRatchet.messageEncrypt me si cl pq) := by
  unfold TripleRatchet.messageEncrypt
  repeat' xnl_step
  all_goals rfl

theorem xnoleak_messageEncryptAbort (me : Participant) (si : Nat) :
    XNoLeak (TripleRatchet.messageEncryptAbort me si) := by
  unfold TripleRatchet.messageEncryptAbort
  repeat' xnl_step

theorem xnoleak_messageDecrypt (me : Participant) (si mi pq : Nat) (sp : UInt32) :
    XNoLeak (TripleRatchet.messageDecrypt me si mi pq sp) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  repeat' xnl_step
  all_goals rfl

theorem xnoleak_messageDecryptSkipped (me : Participant) (si mi k pq : Nat) (sp : UInt32) :
    XNoLeak (TripleRatchet.messageDecryptSkipped me si mi k pq sp) := by
  unfold TripleRatchet.messageDecryptSkipped
  repeat' xnl_step
  all_goals rfl

theorem xnoleak_aliceStart (a b : Participant) (i r : Nat) (h : PQXDH.BundleHandles) :
    XNoLeak (Composed.aliceStart a b i r h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  repeat' xnl_step
  all_goals rfl

theorem xnoleak_bobStart (b a : Participant) (kh : PQXDH.BobKeyHandles) (r : Nat)
    (mh : PQXDH.PreKeyMsgHandles) (pq : Nat) (sp : UInt32) :
    XNoLeak (Composed.bobStart b a kh r mh pq sp) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  repeat' xnl_step
  all_goals rfl

theorem xnoleak_move {m : Move} (hs : m.isSetup = false) (hk : ¬ LeakKind m) :
    XNoLeak m.act := by
  cases m
  case setup => cases hs
  case aliceStart a b i r h _ =>
    exact xnoleak_bind (xnoleak_aliceStart a b i r h) fun _ =>
      xnoleak_of_quiet (xquiet_of_fix (xfix_pure _))
  case bobStart b a kh r mh pq sp _ =>
    exact xnoleak_bind (xnoleak_bobStart b a kh r mh pq sp) fun _ =>
      xnoleak_of_quiet (xquiet_of_fix (xfix_pure _))
  case encrypt me si cl pq _ =>
    exact xnoleak_bind (xnoleak_messageEncrypt me si cl pq) fun _ =>
      xnoleak_of_quiet (xquiet_of_fix (xfix_pure _))
  case encryptAbort me si =>
    exact xnoleak_bind (xnoleak_messageEncryptAbort me si) fun _ =>
      xnoleak_of_quiet (xquiet_of_fix (xfix_pure _))
  case encryptFail me si cl =>
    exact xnoleak_bind (xnoleak_of_quiet (xquiet_of_fix xfix_traceLength)) fun _ =>
      xnoleak_bind (xnoleak_messageEncrypt me si cl _) fun _ =>
        xnoleak_of_quiet (xquiet_of_fix (xfix_pure _))
  case decrypt me si mi pq sp _ =>
    exact xnoleak_bind (xnoleak_messageDecrypt me si mi pq sp) fun _ =>
      xnoleak_of_quiet (xquiet_of_fix (xfix_pure _))
  case decryptSkipped me si mi k pq sp _ =>
    exact xnoleak_bind (xnoleak_messageDecryptSkipped me si mi k pq sp) fun _ =>
      xnoleak_of_quiet (xquiet_of_fix (xfix_pure _))
  case reject _ => exact xnoleak_of_quiet (xquiet_of_fix (xfix_pure _))
  case attackerSend t =>
    exact xnoleak_bind (xnoleak_of_quiet (xquiet_sendMessage t)) fun _ =>
      xnoleak_of_quiet (xquiet_of_fix (xfix_pure _))
  case brkDH =>
    exact xnoleak_logEvent_pq .BrokenDH rfl
  case brkKEM =>
    exact xnoleak_logEvent_pq .BrokenKEM rfl
  all_goals exact absurd trivial hk

theorem exposures_nil_of_not_leakKind' {m : Move} {tr : ExecTrace} (hs : m.isSetup = false)
    (hk : ¬ LeakKind m) : exposures tr (m.next tr) = [] := by
  have hn : XNL tr.length (m.next tr) := xnoleak_move hs hk tr
  have hge : ∀ i ∈ newIndices tr (m.next tr), tr.length ≤ i := by
    intro i hi
    simp only [newIndices, List.mem_range'] at hi
    obtain ⟨k, _, rfl⟩ := hi
    omega
  unfold exposures
  rw [List.append_eq_nil_iff, List.filterMap_eq_nil_iff, List.filterMap_eq_nil_iff]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · unfold pqExposureAt
    rcases he : (m.next tr).getEventAt PQXDHEvent i with _ | ev
    · rfl
    · have := hn.1 i ev (hge i hi) he
      cases ev <;> first | rfl | simp [xplPqLeakEv] at this
  · unfold trExposureAt
    rcases he : (m.next tr).getEventAt TREvent i with _ | ev
    · rfl
    · have := hn.2 i ev (hge i hi) he
      cases ev <;> first | rfl | simp [xplTrLeakEv] at this

/-! ## Receives and starts: quiet or success -/

theorem xmix_bind_fix {α β : Type} {Q : Nat → ExecTrace → Prop} {x : Traceful α}
    {f : α → Traceful β} (hx : XMix Q x) (hf : ∀ a, XFix (f a)) : XMix Q (x >>= f) := by
  intro tr
  rw [xrun_bind_snd]
  split
  · rw [hf _ _]; exact hx tr
  · exact hx tr

theorem xmix_messageDecryptSkipped (me : Participant) (si mi k pq : Nat) (sp : UInt32) :
    XMix (XEvTR isReceivedEv) (TripleRatchet.messageDecryptSkipped me si mi k pq sp) := by
  have hA := xevTR_anti isReceivedEv
  have hM := xevTR_mono isReceivedEv
  unfold TripleRatchet.messageDecryptSkipped
  refine xmix_bind_quiet hA (xquiet_of_fix (xfix_getLocalState _ _)) fun st => ?_
  refine xmix_bind_quiet hA (xquiet_receiveSignalMsg _) fun msg => ?_
  refine xmix_bind_quiet hA (xquiet_of_fix (xfix_getEntry _)) fun e => ?_
  split
  · refine xmix_bind_quiet hA (xquiet_of_fix (xfix_guard _)) fun _ => ?_
    refine xmix_bind_quiet hA (xquiet_of_fix (xfix_guardTrace _)) fun _ => ?_
    split
    · refine xmix_bind_quiet hA (xquiet_sendMessage _) fun _ => ?_
      refine xmix_bind_quiet hA (xquiet_of_fix (xfix_receiveMessage _)) fun _ => ?_
      refine xmix_bind_quiet hA (xquiet_verifyMacAndDecrypt _ _ _ _) fun _ => ?_
      refine xmix_of_est ?_
      refine xest_bind_total hA (xtotal_logEvent_tr _) fun _ => ?_
      exact xest_bind_left hM (xest_logEvent_tr _ rfl)
    · exact xmix_of_quiet (xquiet_of_fix xfix_failure)
  · exact xmix_of_quiet (xquiet_of_fix xfix_failure)

theorem xmix_bobStart (b a : Participant) (kh : PQXDH.BobKeyHandles) (r : Nat)
    (mh : PQXDH.PreKeyMsgHandles) (pq : Nat) (sp : UInt32) :
    XMix (XEvPQ isBobDone) (Composed.bobStart b a kh r mh pq sp) := by
  have hA := xevPQ_anti isBobDone
  have hM := xevPQ_mono isBobDone
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine xmix_bind_quiet hA (xquiet_bobHandshake _ _ _ _ _ _) fun o => ?_
  refine xmix_bind_quiet hA (xquiet_receiveSignalMsg _) fun msg => ?_
  refine xmix_bind_quiet hA (xquiet_ensureReceiverChain _ _) fun x => ?_
  rcases x with ⟨st, c, rat⟩
  dsimp only
  split
  · split
    · refine xmix_bind_quiet hA (xquiet_sendMessage _) fun _ => ?_
      refine xmix_bind_quiet hA (xquiet_of_fix (xfix_receiveMessage _)) fun _ => ?_
      refine xmix_bind_quiet hA (xquiet_verifyMacAndDecrypt _ _ _ _) fun _ => ?_
      try dsimp only
      split
      · refine xmix_bind_quiet hA (xquiet_of_fix (xfix_guardOnTrace _)) fun _ => ?_
        refine xmix_of_est ?_
        refine xest_bind_total hA (xtotal_logEvent_pq _) fun _ => ?_
        refine xest_bind_total hA xtotal_traceLength fun _ => ?_
        exact xest_bind_left hM (xest_logEvent_pq _ rfl)
      · refine xmix_of_est ?_
        refine xest_bind_total hA xtotal_traceLength fun _ => ?_
        exact xest_bind_left hM (xest_logEvent_pq _ rfl)
    · exact xmix_of_quiet (xquiet_of_fix xfix_failure)
  · exact xmix_of_quiet (xquiet_of_fix xfix_failure)

theorem xmix_aliceStart (a b : Participant) (i r : Nat) (h : PQXDH.BundleHandles) :
    XMix (XEvPQ isAliceDone) (Composed.aliceStart a b i r h) := by
  have hA := xevPQ_anti isAliceDone
  have hM := xevPQ_mono isAliceDone
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine xmix_bind_quiet hA (xquiet_aliceHandshake _ _ _ _ _) fun o => ?_
  refine xmix_bind_quiet hA (xquiet_genRand _) fun dhsA => ?_
  try dsimp only
  try split
  refine xmix_bind_quiet hA (xquiet_sendMessage _) fun _ => ?_
  refine xmix_bind_quiet hA (xquiet_sendMessage _) fun _ => ?_
  refine xmix_of_est ?_
  refine xest_bind_total hA xtotal_traceLength fun _ => ?_
  exact xest_bind_left hM (xest_logEvent_pq _ rfl)

/-! ## Move level -/

theorem xmix_move_decrypt (tr : ExecTrace) {me : Participant} {si mi pq : Nat} {sp : UInt32}
    {w : Bool} :
    XQuietFrom tr.length ((Move.decrypt me si mi pq sp w).next tr) ∨
      XEvTR isReceivedEv tr.length ((Move.decrypt me si mi pq sp w).next tr) :=
  xmix_bind_fix (xmix_messageDecrypt me si mi pq sp) (fun _ => xfix_pure _) tr

theorem xmix_move_decryptSkipped (tr : ExecTrace) {me : Participant} {si mi k pq : Nat}
    {sp : UInt32} {w : Bool} :
    XQuietFrom tr.length ((Move.decryptSkipped me si mi k pq sp w).next tr) ∨
      XEvTR isReceivedEv tr.length ((Move.decryptSkipped me si mi k pq sp w).next tr) :=
  xmix_bind_fix (xmix_messageDecryptSkipped me si mi k pq sp) (fun _ => xfix_pure _) tr

theorem xmix_move_bobStart (tr : ExecTrace) {b a : Participant}
    {kh : PQXDH.BobKeyHandles} {r : Nat} {mh : PQXDH.PreKeyMsgHandles} {pq : Nat}
    {sp : UInt32} {shown : Nat} :
    XQuietFrom tr.length ((Move.bobStart b a kh r mh pq sp shown).next tr) ∨
      XEvPQ isBobDone tr.length ((Move.bobStart b a kh r mh pq sp shown).next tr) :=
  xmix_bind_fix (xmix_bobStart b a kh r mh pq sp) (fun _ => xfix_pure _) tr

theorem xmix_move_aliceStart (tr : ExecTrace) {a b : Participant} {i r : Nat}
    {h : PQXDH.BundleHandles} {shown : Nat} :
    XQuietFrom tr.length ((Move.aliceStart a b i r h shown).next tr) ∨
      XEvPQ isAliceDone tr.length ((Move.aliceStart a b i r h shown).next tr) :=
  xmix_bind_fix (xmix_aliceStart a b i r h) (fun _ => xfix_pure _) tr

theorem xpl_noEff_of_quietFrom {m : Move} {tr : ExecTrace}
    (h : XQuietFrom tr.length (m.next tr)) : NoSessionEffect tr m := by
  intro i hi
  simp only [newIndices, List.mem_range'] at hi
  obtain ⟨k, _, rfl⟩ := hi
  obtain ⟨h1, h2, h3, h4⟩ := h _ (Nat.le_add_right _ _)
  exact ⟨h1, Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.nonSessionPQAt_of_eq_none h2, h3, h4⟩

theorem xpl_mem_newIndices {tr t : ExecTrace} {i : Nat} (h1 : tr.length ≤ i)
    (h2 : i < t.length) : i ∈ newIndices tr t := by
  simp only [newIndices, List.mem_range']
  exact ⟨i - tr.length, by omega, by omega⟩

theorem xpl_receivedPlaintext_ne_none {tr t : ExecTrace}
    (h : XEvTR isReceivedEv tr.length t) : receivedPlaintext tr t ≠ none := by
  obtain ⟨i, ev, hi, he, hp⟩ := h
  have hmem := xpl_mem_newIndices hi (xlt_of_getEventAt he)
  intro hnone
  unfold receivedPlaintext at hnone
  rw [List.findSome?_eq_none_iff] at hnone
  have h0 := hnone i hmem
  rw [he] at h0
  cases ev <;> first | (simp at h0; done) | cases hp

theorem xpl_eventIdx_ne_none {p : PQXDHEvent → Bool} {tr t : ExecTrace}
    (h : XEvPQ p tr.length t) : eventIdx p tr t ≠ none := by
  obtain ⟨i, ev, hi, he, hp⟩ := h
  have hmem := xpl_mem_newIndices hi (xlt_of_getEventAt he)
  intro hnone
  unfold eventIdx at hnone
  rw [List.find?_eq_none] at hnone
  have h0 := hnone i hmem
  rw [he] at h0
  simp [hp] at h0

theorem xpl_bobVis_anchor_kind {tr t : ExecTrace} {mh : PQXDH.PreKeyMsgHandles}
    {opk : Option DY.Bytes} {v : VisEntry} (hv : v ∈ bobVis tr t mh opk) (ha : v.anchor ≠ none) :
    v.kind = .accept := by
  unfold bobVis at hv
  rcases List.mem_cons.1 hv with rfl | hv
  · exact (ha rfl).elim
  rcases List.mem_append.1 hv with hv | hv
  · obtain ⟨r, _, rfl⟩ := List.mem_map.1 hv
    exact (ha rfl).elim
  · rcases hp : receivedPlaintext tr t with _ | m
    · rw [hp] at hv; simp at hv
    · rw [hp] at hv
      simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hv
      subst hv; rfl

theorem xpl_take_append_anchor {X Y : List VisEntry} {n : Nat} {v : VisEntry}
    (hX : ∀ w ∈ X, w.anchor = none) (hv : v ∈ (X ++ Y).take n) (ha : v.anchor ≠ none) :
    X.length + 1 ≤ ((X ++ Y).take n).length := by
  rw [List.take_append] at hv
  rcases List.mem_append.1 hv with hv | hv
  · exact (ha (hX v (List.mem_of_mem_take hv))).elim
  · have hpos := List.length_pos_of_mem hv
    simp only [List.length_take, List.length_append] at hpos ⊢
    omega

theorem xpl_kyberCoinEntries_anchor {e : DY.Bytes} :
    ∀ w ∈ kyberCoinEntries e, w.anchor = none := by
  intro w hw
  unfold kyberCoinEntries at hw
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hw
  rfl

theorem xpl_aliceVis_take_anchor {tr t : ExecTrace} {h : PQXDH.BundleHandles}
    {n : Nat} {v : VisEntry} (hv : v ∈ (aliceVis tr t h).take n) (ha : v.anchor ≠ none) :
    35 ≤ ((aliceVis tr t h).take n).length := by
  unfold aliceVis at hv ⊢
  generalize eventIdx isAliceDone tr t = d at hv ⊢
  generalize (newRandoms tr t).map (·.1) = rs at hv ⊢
  generalize hr0 : (⟨.recv, received tr ([h.spk, h.spkSig, h.pqpk, h.pqpkSig] ++ h.opk.toList),
    .bundle, none⟩ : VisEntry) = r0 at hv ⊢
  have hr0a : r0.anchor = none := by rw [← hr0]
  rcases rs with _ | ⟨ek, _ | ⟨e, rest⟩⟩
  · have := List.mem_of_mem_take hv
    simp only [aliceDraws, List.mem_singleton] at this
    subst this; exact (ha hr0a).elim
  · have := List.mem_of_mem_take hv
    simp only [aliceDraws, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl
    · exact (ha hr0a).elim
    · exact (ha rfl).elim
  · have hX : ∀ w ∈ r0 :: rngEntry ek :: kyberCoinEntries e, w.anchor = none := by
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact hr0a
      rcases List.mem_cons.1 hw with rfl | hw
      · rfl
      · exact xpl_kyberCoinEntries_anchor w hw
    have hlen : (r0 :: rngEntry ek :: kyberCoinEntries e).length = 34 := by
      simp [kyberCoinEntries]
    have := xpl_take_append_anchor (Y := (rest.take 1).map fun dhsA =>
      ({ rngEntry dhsA with anchor := d } : VisEntry)) hX hv ha
    rw [hlen] at this
    exact this

theorem noSessionEffect_of_no_accept' {m : Move} {tr : ExecTrace} (hk : RpkKind m)
    (ha : m.LogsSessionCompletion tr) (hacc : ∀ v ∈ m.vis tr, v.kind ≠ .accept) : NoSessionEffect tr m := by
  cases m
  case decrypt me si mi pq sp w =>
    rcases xmix_move_decrypt tr (me := me) (si := si) (mi := mi) (pq := pq) (sp := sp) (w := w)
      with h | h
    · exact xpl_noEff_of_quietFrom h
    · obtain ⟨pt, hpt⟩ := Option.ne_none_iff_exists'.1 (xpl_receivedPlaintext_ne_none h)
      refine absurd rfl (hacc ⟨.accept, [pt], .single, none⟩ ?_)
      rw [xpl_vis_eq]
      refine List.mem_append_left _ ?_
      change _ ∈ decVis tr ((Move.decrypt me si mi pq sp w).next tr) si mi w
      unfold decVis
      rw [hpt]
      simp
  case decryptSkipped me si mi k pq sp w =>
    rcases xmix_move_decryptSkipped tr (me := me) (si := si) (mi := mi) (k := k) (pq := pq)
      (sp := sp) (w := w) with h | h
    · exact xpl_noEff_of_quietFrom h
    · obtain ⟨pt, hpt⟩ := Option.ne_none_iff_exists'.1 (xpl_receivedPlaintext_ne_none h)
      refine absurd rfl (hacc ⟨.accept, [pt], .single, none⟩ ?_)
      rw [xpl_vis_eq]
      refine List.mem_append_left _ ?_
      change _ ∈ decVis tr ((Move.decryptSkipped me si mi k pq sp w).next tr) si mi w
      unfold decVis
      rw [hpt]
      simp
  case bobStart b a kh r mh pq sp shown =>
    rcases xmix_move_bobStart tr (b := b) (a := a) (kh := kh) (r := r) (mh := mh) (pq := pq)
      (sp := sp) (shown := shown) with h | h
    · exact xpl_noEff_of_quietFrom h
    · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (xpl_eventIdx_ne_none h)
      obtain ⟨-, hanc⟩ := ha
      obtain ⟨v, hv, hva⟩ := hanc j hj
      have hv' := hv
      have hex := exposures_nil_of_not_leakKind' (tr := tr)
        (m := .bobStart b a kh r mh pq sp shown) rfl (fun h => nomatch h)
      rw [xpl_vis_eq, hex, List.append_nil] at hv'
      dsimp only [xpl_ownVis] at hv'
      exact absurd (xpl_bobVis_anchor_kind (List.mem_of_mem_take hv') (by rw [hva]; simp))
        (hacc v hv)
  case reject draws =>
    exact xpl_noEff_of_next_eq (by unfold Move.next Move.act; simp only [DY.Traceful.run_pure])
  all_goals cases hk

theorem noSessionEffect_aliceStart_short' {a b : Participant} {idStateIdx regIdxB : Nat}
    {h : PQXDH.BundleHandles} {shown : Nat} {tr : ExecTrace}
    (ha : (Move.aliceStart a b idStateIdx regIdxB h shown).LogsSessionCompletion tr)
    (hlen : ((Move.aliceStart a b idStateIdx regIdxB h shown).vis tr).length < 35) :
    NoSessionEffect tr (.aliceStart a b idStateIdx regIdxB h shown) := by
  rcases xmix_move_aliceStart tr (a := a) (b := b) (i := idStateIdx) (r := regIdxB) (h := h)
    (shown := shown) with hq | hq
  · exact xpl_noEff_of_quietFrom hq
  · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (xpl_eventIdx_ne_none hq)
    obtain ⟨-, hanc⟩ := ha
    obtain ⟨v, hv, hva⟩ := hanc j hj
    have hex := exposures_nil_of_not_leakKind' (tr := tr)
      (m := .aliceStart a b idStateIdx regIdxB h shown) rfl (fun h => nomatch h)
    rw [xpl_vis_eq, hex, List.append_nil] at hv hlen
    dsimp only [xpl_ownVis] at hv hlen
    have := xpl_aliceVis_take_anchor hv (by rw [hva]; simp)
    omega

end XplSteps

/-! ## Public transition lemmas -/

/-- A non-setup move emitting no visible entries has `NoSessionEffect`. -/
theorem noSessionEffect_of_vis_nil {m : Move} {tr : ExecTrace} (hs : m.isSetup = false)
    (ha : m.LogsSessionCompletion tr) (hv : m.vis tr = []) : NoSessionEffect tr m :=
  XplSteps.noSessionEffect_of_vis_nil' hs ha hv

/-- An `aliceStart` move emitting fewer than 35 visible entries has `NoSessionEffect`, since
`AliceDone` is anchored at the 35th entry (`dhsA`) of `aliceVis`. -/
theorem noSessionEffect_aliceStart_short {a b : Participant} {idStateIdx regIdxB : Nat}
    {h : PQXDH.BundleHandles} {shown : Nat} {tr : ExecTrace}
    (ha : (Move.aliceStart a b idStateIdx regIdxB h shown).LogsSessionCompletion tr)
    (hlen : ((Move.aliceStart a b idStateIdx regIdxB h shown).vis tr).length < 35) :
    NoSessionEffect tr (.aliceStart a b idStateIdx regIdxB h shown) :=
  XplSteps.noSessionEffect_aliceStart_short' ha hlen

/-- An `RpkKind` move whose visible entries contain no `.accept` entry has `NoSessionEffect`. -/
theorem noSessionEffect_of_no_accept {m : Move} {tr : ExecTrace} (hk : RpkKind m)
    (ha : m.LogsSessionCompletion tr) (hacc : ∀ v ∈ m.vis tr, v.kind ≠ .accept) : NoSessionEffect tr m :=
  XplSteps.noSessionEffect_of_no_accept' hk ha hacc

/-- A non-setup move outside `LeakKind` emits no exposure entries. -/
theorem exposures_nil_of_not_leakKind {m : Move} {tr : ExecTrace} (hs : m.isSetup = false)
    (hk : ¬ LeakKind m) : exposures tr (m.next tr) = [] :=
  XplSteps.exposures_nil_of_not_leakKind' hs hk

/-- The head visible entry of a non-setup move has kind `.recv`, `.pt`, or `.leak`. -/
theorem xpl_vis_head_kind {m : Move} {tr : ExecTrace} (hs : m.isSetup = false)
    (ha : m.LogsSessionCompletion tr) :
    ∀ v ∈ (m.vis tr).head?, v.kind = .recv ∨ v.kind = .pt ∨ v.kind = .leak :=
  XplSteps.xpl_vis_head_kind' hs ha

end Symbolic.Swarm.CREF
