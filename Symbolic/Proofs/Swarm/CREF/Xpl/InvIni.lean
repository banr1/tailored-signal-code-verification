/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Xpl.Faithful
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Trace.Basic
import DY.Actions.ProtocolEvent
import DY.Trace.Monad
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.PersistentGlobalState
import DY.Actions.Random
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Session-Initiation Block Inversion

Defines `IniBlockShape` and `IniStep` and proves `xplStep_ini`: any anchored non-setup move acting
for `p` (or nobody) whose visible entries match a `session_initiate` block (`recv` followed only by
`rng` events) either satisfies `IniKind` or has `NoSessionEffect`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY
open DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.TripleRatchet (TREvent TRState)
open DY.Libsignal.PQXDH (PQXDHEvent)
open CryptoProofLib.Refinement (ExternInterpretation)

/-! ## Transition and Quiet-Walk Helpers -/

namespace XplIniPrivate

def ownVis (m : Move) (tr : ExecTrace) : List VisEntry :=
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

theorem vis_eq (m : Move) (tr : ExecTrace) :
    m.vis tr = ownVis m tr ++ exposures tr (m.next tr) := by
  cases m <;> rfl

theorem pqExposureAt_kind {tr' : ExecTrace} {j : Nat} {v : VisEntry}
    (h : pqExposureAt tr' j = some v) : v.kind = .leak := by
  simp only [pqExposureAt] at h
  split at h <;> (try simp only [Option.some.injEq] at h) <;> (try subst h) <;>
    first | rfl | cases h

theorem trExposureAt_kind {tr' : ExecTrace} {j : Nat} {v : VisEntry}
    (h : trExposureAt tr' j = some v) : v.kind = .leak := by
  simp only [trExposureAt] at h
  split at h <;> (try simp only [Option.some.injEq] at h) <;> (try subst h) <;>
    first | rfl | cases h

theorem exposures_kind {tr tr' : ExecTrace} {v : VisEntry} (h : v ∈ exposures tr tr') :
    v.kind = .leak := by
  simp only [exposures, List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨j, _, hj⟩ | ⟨j, _, hj⟩
  · exact pqExposureAt_kind hj
  · exact trExposureAt_kind hj

theorem encVis_kind {tr tr' : ExecTrace} {w : Option (Nat × Nat)} {b : Bool} {v : VisEntry}
    (hv : v ∈ encVis tr tr' w b) :
    v.kind = .pt ∨ v.kind = .rng ∨ (b = true ∧ v.kind = .send) := by
  unfold encVis at hv
  rcases List.mem_append.1 hv with hv | hv
  · unfold encDraws at hv
    rcases hrs : newRandoms tr tr' with _ | ⟨_, rest⟩
    · rw [hrs] at hv; cases hv
    · rw [hrs] at hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inl rfl
      · obtain ⟨_, _, rfl⟩ := List.mem_map.1 hv; exact Or.inr (Or.inl rfl)
  · cases b with
    | false => simp at hv
    | true =>
      unfold encSend at hv
      rcases hls : lastSent tr tr' with _ | w1
      · rw [hls] at hv; simp at hv
      · rw [hls] at hv
        cases w with
        | none => rcases List.mem_singleton.1 hv with rfl; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        | some p => rcases List.mem_singleton.1 hv with rfl; exact Or.inr (Or.inr ⟨rfl, rfl⟩)

def RecvHeadKind : Move → Prop
  | .aliceStart .. | .bobStart .. | .decrypt .. | .decryptSkipped .. | .reject _ => True
  | _ => False

theorem recvHeadKind_of_mem_vis (m : Move) (tr : ExecTrace) {v : VisEntry} (hv : v ∈ m.vis tr)
    (hk : v.kind = .recv) : RecvHeadKind m := by
  rw [vis_eq] at hv
  rcases List.mem_append.1 hv with hv | hv
  · cases m <;> dsimp only [ownVis] at hv
    case aliceStart => trivial
    case bobStart => trivial
    case decrypt => trivial
    case decryptSkipped => trivial
    case reject => trivial
    case encrypt =>
      rcases encVis_kind hv with h | h | ⟨_, h⟩ <;> rw [hk] at h <;> cases h
    case encryptAbort =>
      rcases encVis_kind hv with h | h | ⟨_, h⟩ <;> rw [hk] at h <;> cases h
    case encryptFail =>
      rcases encVis_kind hv with h | h | ⟨_, h⟩ <;> rw [hk] at h <;> cases h
    all_goals simp at hv
  · have := exposures_kind hv
    rw [hk] at this; cases this

theorem kind_of_matches {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {e : MachineEvent} {v : VisEntry}
    (h : EventMatchesEntry interpretation r S g e v) : v.kind = eventKind e :=
  h.1.symm

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, [], _, b, hb => by simp at hb
  | _ :: _, _ :: _, .cons hab h, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, hr⟩ := forall₂_mem_right h b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

theorem head_entry {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {blk : List MachineEvent} {l : List VisEntry} {e : MachineEvent}
    (hm : List.Forall₂ (EventMatchesEntry interpretation r S g) blk l) (he : blk.head? = some e) :
    ∃ v ∈ l, v.kind = eventKind e ∧ l.head? = some v := by
  cases blk with
  | nil => simp at he
  | cons e' t =>
    simp only [List.head?_cons, Option.some.injEq] at he
    subst he
    cases hm with
    | cons hv _ => exact ⟨_, List.mem_cons_self, kind_of_matches hv, rfl⟩

theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩
    rfl

theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩
    rfl

theorem run_le {α : Type} (x : Traceful α) (tr : ExecTrace) : tr ≤ (x.run tr).2.val :=
  (x.run tr).2.property

theorem lt_of_at?_some {E : Type} [ExecTraceTypes.Has E] {t : ExecTrace} {i : Nat} {x : E}
    (h : (t.at? i : Option E) = some x) : i < t.length := by
  unfold DY.Trace.at? at h
  split at h
  · assumption
  · cases h

theorem at?_le_some {E : Type} [ExecTraceTypes.Has E] {tr tr' : ExecTrace} (hle : tr ≤ tr')
    {i : Nat} {x : E} (h : (tr.at? i : Option E) = some x) :
    (tr'.at? i : Option E) = some x := by
  have hi := lt_of_at?_some h
  have hi' : i < tr'.length := Nat.lt_of_lt_of_le hi (DY.Trace.length_le _ _ hle)
  rw [← h]
  simp only [DY.Trace.at?, hi, hi', ↓reduceDIte]
  rw [← DY.Trace.at_le tr tr' i hi hle]

theorem at?_le_eq {E : Type} [ExecTraceTypes.Has E] {t t' : ExecTrace} (hle : t ≤ t')
    {i : Nat} (hi : i < t.length) : (t'.at? i : Option E) = (t.at? i : Option E) := by
  have hi' : i < t'.length := Nat.lt_of_lt_of_le hi (DY.Trace.length_le _ _ hle)
  simp only [DY.Trace.at?, hi, hi', ↓reduceDIte]
  rw [← DY.Trace.at_le t t' i hi hle]

theorem trace_append_at_length {Entry E1 : Type} [DY.TraceEntryHas E1 Entry]
    (tr : DY.Trace Entry) (e : E1) (h : tr.length < (tr.append e).length) :
    (tr.append e).at tr.length h = DY.TraceEntryHas.inj e := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

def XFix {α : Type} (x : Traceful α) : Prop := ∀ tr, (x.run tr).2.val = tr

theorem xfix_bind {α β : Type} {x : Traceful α} {f : α → Traceful β} (hx : XFix x)
    (hf : ∀ a, XFix (f a)) : XFix (x >>= f) := by
  intro tr; rw [run_bind_snd]; split
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
theorem xfix_receiveMessage (i : Nat) : XFix (Network.receiveMessage i : Traceful DY.Bytes) := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact xfix_bind (xfix_getEntry _) fun _ => xfix_pure _
theorem xfix_traceLength : XFix TripleRatchet.traceLength :=
  fun _ => by simp only [TripleRatchet.traceLength, DY.Traceful.run_mk]
theorem xfix_guardOnTrace (p : ExecTrace → Bool) : XFix (PQXDH.guardTrace p) :=
  fun _ => by simp only [PQXDH.guardTrace, DY.Traceful.run_mk]
theorem xfix_guardTrace (p : ExecTrace → Bool) : XFix (TripleRatchet.guardTrace p) :=
  fun _ => by simp only [TripleRatchet.guardTrace, DY.Traceful.run_mk]

theorem xfix_getLocalState {StateT : Type}
    [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT StateT)]
    (me : Participant) (i : Nat) :
    XFix (PersistentLocalState.getLocalState me i : Traceful StateT) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact xfix_bind (xfix_bind (xfix_getEntry _) fun _ => xfix_pure _) fun s =>
    xfix_bind (xfix_guard _) fun _ => xfix_pure _

theorem xfix_getKey (p : Participant) (i : Nat) (k : PQXDH.KeyKind) :
    XFix (PQXDH.getKey p i k) := by
  unfold PQXDH.getKey
  exact xfix_bind (xfix_getLocalState (StateT := PQXDH.PQXDHState) _ _) fun st => by
    cases st; exact xfix_bind (xfix_guard _) fun _ => xfix_pure _

def XNone (t : ExecTrace) (i : Nat) : Prop :=
  (t.at? i : Option (PersistentGlobalState.State.ExecEntryT
      (PersistentLocalState.LocalState TRState))) = none ∧
    (t.at? i : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none ∧
    (t.at? i : Option (ProtocolEvent.ExecEntryT TREvent)) = none ∧
    (t.at? i : Option (ProtocolEvent.ExecEntryT ComposedEvent)) = none

def XQuietFrom (n : Nat) (t : ExecTrace) : Prop := ∀ i, n ≤ i → XNone t i
def XQuiet {α : Type} (x : Traceful α) : Prop := ∀ tr, XQuietFrom tr.length (x.run tr).2.val

theorem xnone_le {t t' : ExecTrace} (hle : t ≤ t') {i : Nat} (hi : i < t.length)
    (h : XNone t i) : XNone t' i :=
  ⟨(at?_le_eq hle hi).trans h.1, (at?_le_eq hle hi).trans h.2.1,
    (at?_le_eq hle hi).trans h.2.2.1, (at?_le_eq hle hi).trans h.2.2.2⟩

theorem xnone_of_ge {t : ExecTrace} {i : Nat} (hi : t.length ≤ i) : XNone t i := by
  have hn : ∀ {E : Type} [ExecTraceTypes.Has E], (t.at? i : Option E) = none := by
    intro E _; unfold DY.Trace.at?; split
    · omega
    · rfl
  exact ⟨hn, hn, hn, hn⟩

theorem xquietFrom_trans {n : Nat} {t t' : ExecTrace} (hle : t ≤ t')
    (h1 : XQuietFrom n t) (h2 : XQuietFrom t.length t') : XQuietFrom n t' := by
  intro i hi
  rcases Nat.lt_or_ge i t.length with hlt | hge
  · exact xnone_le hle hlt (h1 i hi)
  · exact h2 i hge

theorem xquietFrom_self (t : ExecTrace) : XQuietFrom t.length t := fun _ hi => xnone_of_ge hi
theorem xquiet_of_fix {α : Type} {x : Traceful α} (hx : XFix x) : XQuiet x := by
  intro tr; rw [hx tr]; exact xquietFrom_self tr

theorem xquiet_bind {α β : Type} {x : Traceful α} {f : α → Traceful β} (hx : XQuiet x)
    (hf : ∀ a, XQuiet (f a)) : XQuiet (x >>= f) := by
  intro tr; rw [run_bind_snd]; split
  · exact xquietFrom_trans (run_le _ _) (hx tr) (hf _ _)
  · exact hx tr

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
    simp only [XNone, DY.Trace.at?, hlt, ↓reduceDIte, trace_append_at_length]
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
    | with_reducible exact xquiet_of_fix xfix_traceLength
    | with_reducible exact xquiet_of_fix (xfix_guardOnTrace _)
    | with_reducible exact xquiet_of_fix (xfix_guardTrace _)
    | with_reducible exact xquiet_of_fix (xfix_pure _)
    | with_reducible exact xquiet_of_fix xfix_failure
    | split)

theorem xquiet_receiveSignalMsg (i : Nat) : XQuiet (TripleRatchet.receiveSignalMsg i) := by
  unfold TripleRatchet.receiveSignalMsg; repeat' xquiet_step

theorem xquiet_dhRatchetStep (st : TRState) (pk : DY.Bytes) :
    XQuiet (TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]; repeat' xquiet_step

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

theorem xquiet_lookupIdentity (p : Participant) (i : Nat) :
    XQuiet (PQXDH.lookupIdentity p i) := by
  unfold PQXDH.lookupIdentity; repeat' xquiet_step

theorem xquiet_bobHandshake (b a : Participant) (h : PQXDH.BobKeyHandles) (r e c : Nat) :
    XQuiet (PQXDH.bobHandshake b a h r e c) := by
  unfold PQXDH.bobHandshake
  repeat' (first | with_reducible exact xquiet_lookupIdentity _ _ | xquiet_step)

def XMix {α : Type} (Q : Nat → ExecTrace → Prop) (x : Traceful α) : Prop :=
  ∀ tr, XQuietFrom tr.length (x.run tr).2.val ∨ Q tr.length (x.run tr).2.val
def QAnti (Q : Nat → ExecTrace → Prop) : Prop := ∀ n n' t, n ≤ n' → Q n' t → Q n t
def QMono (Q : Nat → ExecTrace → Prop) : Prop := ∀ n t t', t ≤ t' → Q n t → Q n t'
def XEst {α : Type} (Q : Nat → ExecTrace → Prop) (x : Traceful α) : Prop :=
  ∀ tr, Q tr.length (x.run tr).2.val
def XTotal {α : Type} (x : Traceful α) : Prop := ∀ tr, ∃ a, (x.run tr).1 = some a

theorem xmix_of_quiet {α : Type} {Q : Nat → ExecTrace → Prop} {x : Traceful α}
    (h : XQuiet x) : XMix Q x := fun tr => Or.inl (h tr)
theorem xmix_of_est {α : Type} {Q : Nat → ExecTrace → Prop} {x : Traceful α}
    (h : XEst Q x) : XMix Q x := fun tr => Or.inr (h tr)

theorem xmix_bind_quiet {α β : Type} {Q : Nat → ExecTrace → Prop} (hQ : QAnti Q)
    {x : Traceful α} {f : α → Traceful β} (hx : XQuiet x) (hf : ∀ a, XMix Q (f a)) :
    XMix Q (x >>= f) := by
  intro tr; rw [run_bind_snd]; split
  · rcases hf _ (x.run tr).2.val with h | h
    · exact Or.inl (xquietFrom_trans (run_le _ _) (hx tr) h)
    · exact Or.inr (hQ _ _ _ (DY.Trace.length_le _ _ (run_le _ _)) h)
  · exact Or.inl (hx tr)

theorem xmix_bind_fix {α β : Type} {Q : Nat → ExecTrace → Prop} {x : Traceful α}
    {f : α → Traceful β} (hx : XMix Q x) (hf : ∀ a, XFix (f a)) : XMix Q (x >>= f) := by
  intro tr; rw [run_bind_snd]; split
  · rw [hf _ _]; exact hx tr
  · exact hx tr

theorem xest_bind_left {α β : Type} {Q : Nat → ExecTrace → Prop} (hQ : QMono Q)
    {x : Traceful α} {f : α → Traceful β} (hx : XEst Q x) : XEst Q (x >>= f) := by
  intro tr; rw [run_bind_snd]; split
  · exact hQ _ _ _ (run_le _ _) (hx tr)
  · exact hx tr

theorem xest_bind_total {α β : Type} {Q : Nat → ExecTrace → Prop} (hQ : QAnti Q)
    {x : Traceful α} {f : α → Traceful β} (hx : XTotal x) (hf : ∀ a, XEst Q (f a)) :
    XEst Q (x >>= f) := by
  intro tr; obtain ⟨a, ha⟩ := hx tr; rw [run_bind_snd, ha]
  exact hQ _ _ _ (DY.Trace.length_le _ _ (run_le x tr)) (hf a _)

theorem xtotal_bind {α β : Type} {x : Traceful α} {f : α → Traceful β} (hx : XTotal x)
    (hf : ∀ a, XTotal (f a)) : XTotal (x >>= f) := by
  intro tr; obtain ⟨a, ha⟩ := hx tr; rw [run_bind_fst, ha]; exact hf a _

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

def XEvTR (p : TREvent → Bool) (n : Nat) (t : ExecTrace) : Prop :=
  ∃ i ev, n ≤ i ∧ t.getEventAt TREvent i = some ev ∧ p ev = true
def XEvPQ (p : PQXDHEvent → Bool) (n : Nat) (t : ExecTrace) : Prop :=
  ∃ i ev, n ≤ i ∧ t.getEventAt PQXDHEvent i = some ev ∧ p ev = true

theorem getEventAt_le {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    {t t' : ExecTrace} (hle : t ≤ t') {i : Nat} {ev : E} (h : t.getEventAt E i = some ev) :
    t'.getEventAt E i = some ev := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h ⊢
  rcases he : (t.at? i : Option (ProtocolEvent.ExecEntryT E)) with _ | e
  · rw [he] at h; cases h
  · rw [he] at h; rw [at?_le_some hle he]; exact h

theorem lt_of_getEventAt {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    {t : ExecTrace} {i : Nat} {ev : E} (h : t.getEventAt E i = some ev) : i < t.length := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h
  rcases he : (t.at? i : Option (ProtocolEvent.ExecEntryT E)) with _ | e
  · rw [he] at h; cases h
  · exact lt_of_at?_some he

theorem xevTR_anti (p : TREvent → Bool) : QAnti (XEvTR p) :=
  fun _ _ _ hle ⟨i, ev, hi, he, hp⟩ => ⟨i, ev, Nat.le_trans hle hi, he, hp⟩
theorem xevTR_mono (p : TREvent → Bool) : QMono (XEvTR p) :=
  fun _ _ _ hle ⟨i, ev, hi, he, hp⟩ => ⟨i, ev, hi, getEventAt_le hle he, hp⟩
theorem xevPQ_anti (p : PQXDHEvent → Bool) : QAnti (XEvPQ p) :=
  fun _ _ _ hle ⟨i, ev, hi, he, hp⟩ => ⟨i, ev, Nat.le_trans hle hi, he, hp⟩
theorem xevPQ_mono (p : PQXDHEvent → Bool) : QMono (XEvPQ p) :=
  fun _ _ _ hle ⟨i, ev, hi, he, hp⟩ => ⟨i, ev, hi, getEventAt_le hle he, hp⟩

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

theorem xmix_messageDecryptSkipped (me : Participant) (si mi k pq : Nat) (sp : UInt32) :
    XMix (XEvTR isReceivedEv) (TripleRatchet.messageDecryptSkipped me si mi k pq sp) := by
  have hA := xevTR_anti isReceivedEv
  have hM := xevTR_mono isReceivedEv
  unfold TripleRatchet.messageDecryptSkipped
  refine xmix_bind_quiet hA (xquiet_of_fix (xfix_getLocalState _ _)) fun st => ?_
  refine xmix_bind_quiet hA (xquiet_receiveSignalMsg _) fun msg => ?_
  refine xmix_bind_quiet hA (xfix_getEntry _ |> xquiet_of_fix) fun e => ?_
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

theorem noEff_of_quietFrom {m : Move} {tr : ExecTrace}
    (h : XQuietFrom tr.length (m.next tr)) : NoSessionEffect tr m := by
  intro i hi
  simp only [newIndices, List.mem_range'] at hi
  obtain ⟨k, _, rfl⟩ := hi
  obtain ⟨h1, h2, h3, h4⟩ := h _ (Nat.le_add_right _ _)
  exact ⟨h1, Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.nonSessionPQAt_of_eq_none h2, h3, h4⟩

theorem mem_newIndices {tr t : ExecTrace} {i : Nat} (h1 : tr.length ≤ i)
    (h2 : i < t.length) : i ∈ newIndices tr t := by
  simp only [newIndices, List.mem_range']
  exact ⟨i - tr.length, by omega, by omega⟩

theorem receivedPlaintext_ne_none {tr t : ExecTrace}
    (h : XEvTR isReceivedEv tr.length t) : receivedPlaintext tr t ≠ none := by
  obtain ⟨i, ev, hi, he, hp⟩ := h
  have hmem := mem_newIndices hi (lt_of_getEventAt he)
  intro hnone
  unfold receivedPlaintext at hnone
  rw [List.findSome?_eq_none_iff] at hnone
  have h0 := hnone i hmem
  rw [he] at h0
  cases ev <;> first | (simp at h0; done) | cases hp

theorem eventIdx_ne_none {p : PQXDHEvent → Bool} {tr t : ExecTrace}
    (h : XEvPQ p tr.length t) : eventIdx p tr t ≠ none := by
  obtain ⟨i, ev, hi, he, hp⟩ := h
  have hmem := mem_newIndices hi (lt_of_getEventAt he)
  intro hnone
  unfold eventIdx at hnone
  rw [List.find?_eq_none] at hnone
  have h0 := hnone i hmem
  rw [he] at h0
  simp [hp] at h0

theorem bobVis_anchor_kind {tr t : ExecTrace} {mh : PQXDH.PreKeyMsgHandles}
    {opk : Option DY.Bytes} {v : VisEntry} (hv : v ∈ bobVis tr t mh opk) (ha : v.anchor ≠ none) :
    v.kind = .accept := by
  unfold bobVis at hv
  rcases List.mem_cons.1 hv with rfl | hv
  · exact (ha rfl).elim
  rcases List.mem_append.1 hv with hv | hv
  · obtain ⟨r, _, rfl⟩ := List.mem_map.1 hv; exact (ha rfl).elim
  · rcases hp : receivedPlaintext tr t with _ | m
    · rw [hp] at hv; simp at hv
    · rw [hp] at hv
      simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hv
      subst hv; rfl

theorem noSessionEffect_of_no_accept_rpk {m : Move} {tr : ExecTrace} (hk : RpkKind m)
    (ha : m.LogsSessionCompletion tr) (hacc : ∀ v ∈ m.vis tr, v.kind ≠ .accept)
    (hnoleak : ∀ v ∈ m.vis tr, v.kind ≠ .leak) : NoSessionEffect tr m := by
  cases m
  case decrypt me si mi pq sp w =>
    rcases xmix_bind_fix (xmix_messageDecrypt me si mi pq sp) (fun _ => xfix_pure _) tr with h | h
    · exact noEff_of_quietFrom h
    · obtain ⟨pt, hpt⟩ := Option.ne_none_iff_exists'.1 (receivedPlaintext_ne_none h)
      change receivedPlaintext tr ((Move.decrypt me si mi pq sp w).next tr) = some pt at hpt
      refine absurd rfl (hacc ⟨.accept, [pt], .single, none⟩ ?_)
      rw [vis_eq]
      refine List.mem_append_left _ ?_
      change _ ∈ decVis tr ((Move.decrypt me si mi pq sp w).next tr) si mi w
      unfold decVis; rw [hpt]; simp
  case decryptSkipped me si mi k pq sp w =>
    rcases xmix_bind_fix (xmix_messageDecryptSkipped me si mi k pq sp) (fun _ => xfix_pure _) tr
      with h | h
    · exact noEff_of_quietFrom h
    · obtain ⟨pt, hpt⟩ := Option.ne_none_iff_exists'.1 (receivedPlaintext_ne_none h)
      change receivedPlaintext tr ((Move.decryptSkipped me si mi k pq sp w).next tr) = some pt at hpt
      refine absurd rfl (hacc ⟨.accept, [pt], .single, none⟩ ?_)
      rw [vis_eq]
      refine List.mem_append_left _ ?_
      change _ ∈ decVis tr ((Move.decryptSkipped me si mi k pq sp w).next tr) si mi w
      unfold decVis; rw [hpt]; simp
  case bobStart b a kh r mh pq sp shown =>
    rcases xmix_bind_fix (xmix_bobStart b a kh r mh pq sp) (fun _ => xfix_pure _) tr with h | h
    · exact noEff_of_quietFrom h
    · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (eventIdx_ne_none h)
      obtain ⟨-, hanc⟩ := ha
      obtain ⟨v, hv, hva⟩ := hanc j hj
      have hv' := hv
      rw [vis_eq] at hv'
      rcases List.mem_append.1 hv' with hv_own | hv_exp
      · dsimp only [ownVis] at hv_own
        exact absurd (bobVis_anchor_kind (List.mem_of_mem_take hv_own) (by rw [hva]; simp))
          (hacc v hv)
      · exact absurd (exposures_kind hv_exp) (hnoleak v hv)
  case reject draws =>
    intro i hi
    have hnext : (Move.reject draws).next tr = tr := by
      unfold Move.next Move.act; simp only [DY.Traceful.run_pure]
    rw [hnext] at hi
    simp [newIndices] at hi
  all_goals cases hk

end XplIniPrivate

/-! ## Session-Initiation Inversion -/

/-- Event shape of a `session_initiate` call: `recv b` followed only by `rng` events. -/
structure IniBlockShape (blk : List MachineEvent) : Prop where
  head : ∃ b, blk.head? = some (.recv b)
  tail : ∀ e ∈ blk.tail, eventKind e = .rng

/-- Step conclusion for a `session_initiate` block: a move acting for `p` (or nobody) that either
satisfies `IniKind` or has `NoSessionEffect`. -/
def IniStep (p : Participant) (_blk : List MachineEvent) (tr : ExecTrace) (m : Move) : Prop :=
  ActorIn p m ∧ (IniKind m ∨ NoSessionEffect tr m)

/-- Single-move inversion for a `session_initiate` block. -/
theorem xplStep_ini {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {p : Participant} {blk : List MachineEvent} {m : Move} {tr : ExecTrace}
    (_hs : m.isSetup = false) (ha : m.LogsSessionCompletion tr)
    (hm : List.Forall₂ (EventMatchesEntry interpretation r S g) blk (m.vis tr))
    (hshape : IniBlockShape blk) (hact : ActorIn p m) : IniStep p blk tr m := by
  obtain ⟨b, hb⟩ := hshape.head
  obtain ⟨v, hv, hvk, _⟩ := XplIniPrivate.head_entry hm hb
  have hrk := XplIniPrivate.recvHeadKind_of_mem_vis m tr hv hvk
  have hno_kind : ∀ (k : VisEventKind), k ≠ .recv → k ≠ .rng → ∀ w ∈ m.vis tr, w.kind ≠ k := by
    intro k hnr hng w hw hwk
    obtain ⟨e, he, hew⟩ := XplIniPrivate.forall₂_mem_right hm w hw
    have hek : eventKind e = k := by rw [← XplIniPrivate.kind_of_matches hew, hwk]
    cases blk with
    | nil => cases he
    | cons e₀ t =>
      simp only [List.head?_cons, Option.some.injEq] at hb
      subst hb
      rcases List.mem_cons.1 he with rfl | he'
      · exact hnr hek.symm
      · exact hng ((hshape.tail e he').symm.trans hek).symm
  have hnoacc : ∀ w ∈ m.vis tr, w.kind ≠ .accept := hno_kind .accept (by decide) (by decide)
  have hnoleak : ∀ w ∈ m.vis tr, w.kind ≠ .leak := hno_kind .leak (by decide) (by decide)
  refine ⟨hact, ?_⟩
  cases m
  case aliceStart => exact Or.inl trivial
  case reject => exact Or.inl trivial
  case bobStart => exact Or.inr (XplIniPrivate.noSessionEffect_of_no_accept_rpk trivial ha hnoacc hnoleak)
  case decrypt => exact Or.inr (XplIniPrivate.noSessionEffect_of_no_accept_rpk trivial ha hnoacc hnoleak)
  case decryptSkipped => exact Or.inr (XplIniPrivate.noSessionEffect_of_no_accept_rpk trivial ha hnoacc hnoleak)
  all_goals exact False.elim hrk

end Symbolic.Swarm.CREF
