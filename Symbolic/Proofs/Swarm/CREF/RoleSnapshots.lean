/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.MatchedPrefix
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# `RoleSnapshots` Invariant and Move Preservation

Defines `RoleSnapshots r tr`, stating that every stored `TRState` snapshot for `p` in `tr` satisfies
`st.initiator = decide (p = r.alice)`, and proves its preservation across `Traceful` operations,
model moves, and `OneMove` blocks.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open

open TripleRatchet (TREvent TRState)
open PQXDH (PQXDHEvent)

/-- Every `TRState` snapshot stored for `p` in `tr` has `st.initiator = decide (p = r.alice)`. -/
def RoleSnapshots (r : ProtocolSetup) (tr : ExecTrace) : Prop :=
  ∀ (p : Participant) (st : TRState) (i : Nat),
    (tr.at? i : Option (PersistentGlobalState.State.ExecEntryT
      (PersistentLocalState.LocalState TRState))) = some ⟨⟨p, st⟩⟩ →
    st.initiator = decide (p = r.alice)

abbrev RoleStE :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)

private theorem role_at?_none_of_ge {EntryT : Type} [TraceEntryHas EntryT ExecTrace.Entry]
    {tr : ExecTrace} {j : Nat} (hj : tr.length ≤ j) : (tr.at? j : Option EntryT) = none := by
  simp only [DY.Trace.at?, show ¬ j < tr.length by omega, dite_false]

private theorem role_run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β)
    (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | none => none
      | some a => ((f a).run (x.run tr).2.val).1 := by
  rw [DY.Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr₁⟩
  · rfl
  · rcases (f a).run tr₁.val with ⟨_, _⟩; rfl

private theorem role_run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β)
    (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | none => (x.run tr).2.val
      | some a => ((f a).run (x.run tr).2.val).2.val := by
  rw [DY.Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr₁⟩
  · rfl
  · rcases (f a).run tr₁.val with ⟨_, _⟩; rfl

/-! ## No-new-state and no-session-effect frames -/

theorem roleSnapshots_of_noNewSt {r : ProtocolSetup} {tr tr' : ExecTrace}
    (hle : tr ≤ tr')
    (hno : ∀ i, tr.length ≤ i → i < tr'.length → (tr'.at? i : Option RoleStE) = none)
    (h : RoleSnapshots r tr) :
    RoleSnapshots r tr' := by
  intro p st i hat
  by_cases hi : i < tr.length
  · rw [XplSteps.xat?_le_eq hle hi] at hat
    exact h p st i hat
  · by_cases hi' : i < tr'.length
    · rw [hno i (Nat.le_of_not_lt hi) hi'] at hat
      cases hat
    · rw [role_at?_none_of_ge (Nat.le_of_not_lt hi')] at hat
      cases hat

theorem roleSnapshots_of_noSessionEffect {r : ProtocolSetup} {tr : ExecTrace} {m : Move}
    (hm : NoSessionEffect tr m) (h : RoleSnapshots r tr) :
    RoleSnapshots r (m.next tr) := by
  refine roleSnapshots_of_noNewSt ((Move.act m).run tr).2.property (fun i hi1 hi2 => ?_) h
  refine (hm i ?_).1
  simp only [newIndices, List.mem_range'_1]
  omega

theorem roleSnapshots_of_movesFrom_noSessionEffect {r : ProtocolSetup} {tr : ExecTrace} {δ : List Move}
    (hδ : MovesFrom (fun tr m => NoSessionEffect tr m) tr δ) (h : RoleSnapshots r tr) :
    RoleSnapshots r (runMoves δ tr).1 := by
  induction δ generalizing tr with
  | nil => exact h
  | cons m δ ih => exact ih hδ.2 (roleSnapshots_of_noSessionEffect hδ.1 h)

theorem roleSnapshots_of_movesFrom_invisibleNoEffect {r : ProtocolSetup} {tr : ExecTrace}
    {δ : List Move} (hδ : MovesFrom InvisibleNoEffect tr δ) (h : RoleSnapshots r tr) :
    RoleSnapshots r (runMoves δ tr).1 := by
  induction δ generalizing tr with
  | nil => exact h
  | cons m δ ih => exact ih hδ.2 (roleSnapshots_of_noSessionEffect hδ.1.2 h)

/-! ## `RoleTraceful` combinators -/

/-- Running `x` from a `RoleSnapshots r` trace preserves `RoleSnapshots r` and establishes `Q`
on any returned value. -/
def RoleTraceful (r : ProtocolSetup) {α : Type} (Q : α → Prop) (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, RoleSnapshots r tr →
    RoleSnapshots r (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q a

theorem roleSnapshots_of_xquietFrom {r : ProtocolSetup} {tr t : ExecTrace}
    (hle : tr ≤ t) (hq : XplSteps.XQuietFrom tr.length t) (h : RoleSnapshots r tr) :
    RoleSnapshots r t :=
  roleSnapshots_of_noNewSt hle (fun i hi _ => (hq i hi).1) h

theorem roleSnapshots_of_xquiet {r : ProtocolSetup} {α : Type} {x : Traceful α}
    (hq : XplSteps.XQuiet x) {tr : ExecTrace} (h : RoleSnapshots r tr) :
    RoleSnapshots r (x.run tr).2.val :=
  roleSnapshots_of_xquietFrom (XplSteps.xrun_le x tr) (hq tr) h

theorem RoleTraceful.of_xquiet {r : ProtocolSetup} {α : Type} {x : Traceful α}
    (hq : XplSteps.XQuiet x) :
    RoleTraceful r (fun _ => True) x :=
  fun _ h => ⟨roleSnapshots_of_xquiet hq h, fun _ _ => trivial⟩

theorem RoleTraceful.pure {r : ProtocolSetup} {α : Type} {Q : α → Prop} {a : α} (ha : Q a) :
    RoleTraceful r Q (Pure.pure a) := by
  intro tr htr
  rw [DY.Traceful.run_pure]
  refine ⟨htr, fun b hb => ?_⟩
  cases hb
  exact ha

theorem RoleTraceful.failure {r : ProtocolSetup} {α : Type} {Q : α → Prop} :
    RoleTraceful r Q (failure : Traceful α) := by
  intro tr htr
  rw [DY.Traceful.run_failure]
  exact ⟨htr, fun _ hb => by cases hb⟩

theorem RoleTraceful.bind {r : ProtocolSetup} {α β : Type} {Q₁ : α → Prop} {Q₂ : β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : RoleTraceful r Q₁ x) (hf : ∀ a, Q₁ a → RoleTraceful r Q₂ (f a)) :
    RoleTraceful r Q₂ (x >>= f) := by
  intro tr htr
  rw [role_run_bind_snd, role_run_bind_fst]
  have h1 := hx tr htr
  cases hres : (x.run tr).1 with
  | none => exact ⟨h1.1, fun _ hb => by cases hb⟩
  | some a => exact hf a (h1.2 a hres) (x.run tr).2.val h1.1

theorem RoleTraceful.bind_true {r : ProtocolSetup} {α β : Type} {Q₂ : β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : RoleTraceful r (fun _ => True) x) (hf : ∀ a, RoleTraceful r Q₂ (f a)) :
    RoleTraceful r Q₂ (x >>= f) :=
  RoleTraceful.bind hx (fun a _ => hf a)

theorem RoleTraceful.run_snd {r : ProtocolSetup} {α : Type} {Q : α → Prop} {x : Traceful α}
    (hx : RoleTraceful r Q x) {tr : ExecTrace} (htr : RoleSnapshots r tr) :
    RoleSnapshots r ((x >>= fun _ => Pure.pure ()).run tr).2.val :=
  (RoleTraceful.bind hx (fun _ _ => RoleTraceful.pure (Q := fun _ => True) trivial) tr htr).1

theorem roleSnapshots_append_non_st {r : ProtocolSetup} {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option RoleStE) = none)
    (htr : RoleSnapshots r tr) :
    RoleSnapshots r (tr.append e) := by
  intro p st i hat
  by_cases hi : i < tr.length
  · rw [XplSteps.xat?_le_eq (DY.Trace.append_le tr e) hi] at hat
    exact htr p st i hat
  · by_cases hi' : i < (tr.append e).length
    · have heq : i = tr.length := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hi'
        omega
      subst heq
      have hat' : ((tr.append e).at? tr.length : Option RoleStE) =
          (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option RoleStE) := by
        simp [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_2]
      rw [hat', hnone] at hat
      cases hat
    · rw [role_at?_none_of_ge (Nat.le_of_not_lt hi')] at hat
      cases hat

theorem roleSnapshots_append_st {r : ProtocolSetup} {tr : ExecTrace} (me : Participant)
    {st0 : TRState} (hst0 : st0.initiator = decide (me = r.alice))
    (htr : RoleSnapshots r tr) :
    RoleSnapshots r (tr.append (⟨⟨me, st0⟩⟩ : RoleStE)) := by
  intro p st i hat
  by_cases hi : i < tr.length
  · rw [XplSteps.xat?_le_eq (DY.Trace.append_le tr _) hi] at hat
    exact htr p st i hat
  · by_cases hi' : i < (tr.append (⟨⟨me, st0⟩⟩ : RoleStE)).length
    · have heq : i = tr.length := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hi'
        omega
      subst heq
      have hat' : ((tr.append (⟨⟨me, st0⟩⟩ : RoleStE)).at? tr.length : Option RoleStE) =
          some ⟨⟨me, st0⟩⟩ :=
        DY.Trace.at?_append tr (⟨⟨me, st0⟩⟩ : RoleStE)
      rw [hat'] at hat
      cases hat
      exact hst0
    · rw [role_at?_none_of_ge (Nat.le_of_not_lt hi')] at hat
      cases hat

theorem RoleTraceful.getEntry_st (r : ProtocolSetup) (j : Nat) :
    RoleTraceful r
      (fun e : RoleStE => e.st.state.initiator = decide (e.st.participant = r.alice))
      (DY.getEntry j : Traceful RoleStE) := by
  intro tr htr
  rw [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]
  refine ⟨htr, fun e he => ?_⟩
  rcases e with ⟨⟨p, st⟩⟩
  exact htr p st j he

theorem RoleTraceful.guardP (r : ProtocolSetup) (p : Prop) [Decidable p] :
    RoleTraceful r (fun _ => p) (_root_.guard p) := by
  unfold _root_.guard
  split
  · next hp => exact RoleTraceful.pure hp
  · exact RoleTraceful.failure

theorem RoleTraceful.getLocalState (r : ProtocolSetup) (me : Participant) (j : Nat) :
    RoleTraceful r (fun st : TRState => st.initiator = decide (me = r.alice))
      (PersistentLocalState.getLocalState me j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine RoleTraceful.bind
    (RoleTraceful.bind (RoleTraceful.getEntry_st r j) fun e he =>
      RoleTraceful.pure
        (Q := fun ls : PersistentLocalState.LocalState TRState =>
          ls.state.initiator = decide (ls.participant = r.alice)) he)
    fun ls hls => ?_
  refine RoleTraceful.bind (RoleTraceful.guardP r (ls.participant = me)) fun _ hme => ?_
  subst hme
  exact RoleTraceful.pure hls

theorem RoleTraceful.storeLocalState (r : ProtocolSetup) (me : Participant) {st : TRState}
    (hst : st.initiator = decide (me = r.alice)) :
    RoleTraceful r (fun _ => True) (PersistentLocalState.storeLocalState me st) := by
  intro tr htr
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact ⟨roleSnapshots_append_st me hst htr, fun _ _ => trivial⟩

theorem RoleTraceful.logEvent_tr (r : ProtocolSetup) (ev : TREvent) :
    RoleTraceful r (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro tr htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact ⟨roleSnapshots_append_non_st (⟨ev⟩ : ProtocolEvent.ExecEntryT TREvent) rfl htr,
    fun _ _ => trivial⟩

theorem RoleTraceful.logEvent_pq (r : ProtocolSetup) (ev : PQXDHEvent) :
    RoleTraceful r (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro tr htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact ⟨roleSnapshots_append_non_st (⟨ev⟩ : ProtocolEvent.ExecEntryT PQXDHEvent) rfl htr,
    fun _ _ => trivial⟩

theorem RoleTraceful.logEvent_c (r : ProtocolSetup) (ev : ComposedEvent) :
    RoleTraceful r (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro tr htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
  exact ⟨roleSnapshots_append_non_st (⟨ev⟩ : ProtocolEvent.ExecEntryT ComposedEvent) rfl htr,
    fun _ _ => trivial⟩

theorem RoleTraceful.logSkippedKeys (r : ProtocolSetup) (s : TripleRatchet.SessionInfo)
    (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32),
      RoleTraceful r (fun _ => True) (TripleRatchet.logSkippedKeys s pk rIdx src ck n k)
  | 0, _, _ => RoleTraceful.pure trivial
  | k + 1, ck, n => by
    rw [TripleRatchet.logSkippedKeys]
    exact RoleTraceful.bind (RoleTraceful.logEvent_tr r _) fun _ _ =>
      RoleTraceful.logSkippedKeys r s pk rIdx src k _ _

theorem RoleTraceful.logMessageKeyAndStore (r : ProtocolSetup) (me : Participant)
    {s : TripleRatchet.SessionInfo} {dir : TripleRatchet.KeyDir} {seed pqSalt : DY.Bytes}
    {n : UInt32} {rIdx par : Nat} {st : TRState}
    (hst : st.initiator = decide (me = r.alice)) :
    RoleTraceful r (fun _ => True)
      (TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold TripleRatchet.logMessageKeyAndStore
  exact RoleTraceful.bind (RoleTraceful.logEvent_tr r _) fun _ _ =>
      RoleTraceful.storeLocalState r me hst

theorem RoleTraceful.dhRatchetStep (r : ProtocolSetup) (st : TRState) (pk : DY.Bytes) :
    RoleTraceful r
      (fun x : TRState × TripleRatchet.RecvChain => x.1.initiator = st.initiator)
      (TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine RoleTraceful.bind
    (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_guard _))) fun _ _ => ?_
  refine RoleTraceful.bind (RoleTraceful.of_xquiet (XplSteps.xquiet_genRand 32)) fun _ _ => ?_
  exact RoleTraceful.pure rfl

theorem RoleTraceful.ensureReceiverChain (r : ProtocolSetup) (st : TRState) (pk : DY.Bytes) :
    RoleTraceful r
      (fun x : TRState × TripleRatchet.RecvChain × Bool => x.1.initiator = st.initiator)
      (TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact RoleTraceful.pure rfl
  · refine RoleTraceful.bind (RoleTraceful.dhRatchetStep r st pk) fun x hx => ?_
    rcases x with ⟨st', c⟩
    exact RoleTraceful.pure hx
  · exact RoleTraceful.failure

/-! ## Protocol operations -/

theorem RoleTraceful.messageEncrypt (r : ProtocolSetup) (me : Participant)
    (stateIdx coinsLen pqIdx : Nat) :
    RoleTraceful r (fun _ => True)
      (TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold TripleRatchet.messageEncrypt
  refine RoleTraceful.bind (RoleTraceful.getLocalState r me stateIdx) fun st hst =>
    RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_guard _))) fun _ =>
    RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_genRand 32)) fun _ =>
    RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_genRand coinsLen)) fun _ =>
    RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)) fun _ =>
    RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_receiveMessage pqIdx))) fun _ =>
    RoleTraceful.bind_true (RoleTraceful.logEvent_tr r _) fun _ =>
    RoleTraceful.bind_true (RoleTraceful.logMessageKeyAndStore r me hst) fun _ =>
    RoleTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)

theorem RoleTraceful.messageEncryptAbort (r : ProtocolSetup) (me : Participant) (stateIdx : Nat) :
    RoleTraceful r (fun _ => True) (TripleRatchet.messageEncryptAbort me stateIdx) := by
  unfold TripleRatchet.messageEncryptAbort
  exact RoleTraceful.bind (RoleTraceful.getLocalState r me stateIdx) fun _ _ =>
    RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_genRand 32)) fun _ =>
    RoleTraceful.failure

theorem RoleTraceful.messageDecrypt (r : ProtocolSetup) (me : Participant)
    (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    RoleTraceful r (fun _ => True)
      (TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine RoleTraceful.bind (RoleTraceful.getLocalState r me stateIdx) fun st hst => ?_
  refine RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_receiveSignalMsg msgIdx)) fun msg => ?_
  refine RoleTraceful.bind (RoleTraceful.ensureReceiverChain r st msg.ratchetKey) fun x hx => ?_
  rcases x with ⟨st', c, rat⟩
  dsimp only at hx ⊢
  have hst' : st'.initiator = decide (me = r.alice) := hx.trans hst
  split
  · split
    · refine RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)) fun _ =>
        RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_receiveMessage _))) fun _ =>
        RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_verifyMacAndDecrypt _ _ _ _)) fun _ => ?_
      split
      · exact RoleTraceful.bind_true (RoleTraceful.logEvent_tr r _) fun _ =>
          RoleTraceful.bind_true (RoleTraceful.logEvent_tr r _) fun _ =>
          RoleTraceful.bind_true (RoleTraceful.logSkippedKeys r _ _ _ _ _ _ _) fun _ =>
          RoleTraceful.bind_true (RoleTraceful.logEvent_tr r _) fun _ =>
          RoleTraceful.logMessageKeyAndStore r me hst'
      · exact RoleTraceful.bind_true (RoleTraceful.logSkippedKeys r _ _ _ _ _ _ _) fun _ =>
          RoleTraceful.bind_true (RoleTraceful.logEvent_tr r _) fun _ =>
          RoleTraceful.logMessageKeyAndStore r me hst'
    · exact RoleTraceful.failure
  · exact RoleTraceful.failure

theorem RoleTraceful.messageDecryptSkipped (r : ProtocolSetup) (me : Participant)
    (stateIdx msgIdx k pqIdx : Nat) (spqrMsgIdx : UInt32) :
    RoleTraceful r (fun _ => True)
      (TripleRatchet.messageDecryptSkipped me stateIdx msgIdx k pqIdx spqrMsgIdx) := by
  unfold TripleRatchet.messageDecryptSkipped
  refine RoleTraceful.bind (RoleTraceful.getLocalState r me stateIdx) fun st hst =>
    RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_receiveSignalMsg msgIdx)) fun msg =>
    RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xfix_getEntry k |> XplSteps.xquiet_of_fix)) fun e => ?_
  split
  · refine RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_guard _))) fun _ =>
      RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_guardTrace _))) fun _ => ?_
    split
    · exact RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)) fun _ =>
        RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_receiveMessage _))) fun _ =>
        RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_verifyMacAndDecrypt _ _ _ _)) fun _ =>
        RoleTraceful.bind_true (RoleTraceful.logEvent_tr r _) fun _ =>
        RoleTraceful.bind_true (RoleTraceful.logEvent_tr r _) fun _ =>
        RoleTraceful.logMessageKeyAndStore r me hst
    · exact RoleTraceful.failure
  · exact RoleTraceful.failure

theorem RoleTraceful.aliceStart (r : ProtocolSetup) {a : Participant} (ha : a = r.alice)
    (b : Participant) (ikIdxA regIdxB : Nat) (h : PQXDH.BundleHandles) :
    RoleTraceful r (fun _ => True)
      (Composed.aliceStart a b ikIdxA regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_aliceHandshake _ _ _ _ _)) fun _ =>
    RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_genRand 32)) fun _ =>
    RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)) fun _ =>
    RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)) fun _ =>
    RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix XplSteps.xfix_traceLength)) fun _ =>
    RoleTraceful.bind_true (RoleTraceful.logEvent_pq r _) fun _ =>
    RoleTraceful.bind_true (RoleTraceful.logEvent_tr r _) fun _ =>
    RoleTraceful.bind_true (RoleTraceful.logEvent_c r _) fun _ =>
    RoleTraceful.storeLocalState r a (by simp [ha])

theorem RoleTraceful.bobStart (r : ProtocolSetup) {b : Participant} (hb : b ≠ r.alice)
    (a : Participant) (kh : PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    RoleTraceful r (fun _ => True)
      (Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_bobHandshake b a kh regIdxA mh.ek mh.ct)) fun o => ?_
  refine RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_receiveSignalMsg mh.msg)) fun msg => ?_
  refine RoleTraceful.bind
    (RoleTraceful.ensureReceiverChain r _ msg.ratchetKey)
    fun x hx => ?_
  rcases x with ⟨st, c, rat⟩
  dsimp only at hx ⊢
  have hst : st.initiator = decide (b = r.alice) := by
    rw [hx]
    simp [hb]
  split
  · split
    · refine RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)) fun _ =>
        RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_receiveMessage _))) fun _ =>
        RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_verifyMacAndDecrypt _ _ _ _)) fun _ => ?_
      split
      · refine RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_guardOnTrace _))) fun _ =>
          RoleTraceful.bind_true (RoleTraceful.logEvent_pq r _) fun _ =>
          RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix XplSteps.xfix_traceLength)) fun _ =>
          RoleTraceful.bind_true (RoleTraceful.logEvent_pq r _) fun _ => ?_
        split
        · exact RoleTraceful.bind_true (RoleTraceful.logEvent_tr r _) fun _ =>
            RoleTraceful.bind_true (RoleTraceful.logEvent_tr r _) fun _ =>
            RoleTraceful.bind_true (RoleTraceful.logEvent_c r _) fun _ =>
            RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix XplSteps.xfix_traceLength)) fun _ =>
            RoleTraceful.bind_true (RoleTraceful.logSkippedKeys r _ _ _ _ _ _ _) fun _ =>
            RoleTraceful.bind_true (RoleTraceful.logEvent_tr r _) fun _ =>
            RoleTraceful.logMessageKeyAndStore r b hst
        · exact RoleTraceful.bind_true (RoleTraceful.logEvent_c r _) fun _ =>
            RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix XplSteps.xfix_traceLength)) fun _ =>
            RoleTraceful.bind_true (RoleTraceful.logSkippedKeys r _ _ _ _ _ _ _) fun _ =>
            RoleTraceful.bind_true (RoleTraceful.logEvent_tr r _) fun _ =>
            RoleTraceful.logMessageKeyAndStore r b hst
      · refine RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix XplSteps.xfix_traceLength)) fun _ =>
          RoleTraceful.bind_true (RoleTraceful.logEvent_pq r _) fun _ => ?_
        split
        · exact RoleTraceful.bind_true (RoleTraceful.logEvent_tr r _) fun _ =>
            RoleTraceful.bind_true (RoleTraceful.logEvent_tr r _) fun _ =>
            RoleTraceful.bind_true (RoleTraceful.logEvent_c r _) fun _ =>
            RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix XplSteps.xfix_traceLength)) fun _ =>
            RoleTraceful.bind_true (RoleTraceful.logSkippedKeys r _ _ _ _ _ _ _) fun _ =>
            RoleTraceful.bind_true (RoleTraceful.logEvent_tr r _) fun _ =>
            RoleTraceful.logMessageKeyAndStore r b hst
        · exact RoleTraceful.bind_true (RoleTraceful.logEvent_c r _) fun _ =>
            RoleTraceful.bind_true (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix XplSteps.xfix_traceLength)) fun _ =>
            RoleTraceful.bind_true (RoleTraceful.logSkippedKeys r _ _ _ _ _ _ _) fun _ =>
            RoleTraceful.bind_true (RoleTraceful.logEvent_tr r _) fun _ =>
            RoleTraceful.logMessageKeyAndStore r b hst
    · exact RoleTraceful.failure
  · exact RoleTraceful.failure

/-! ## Per-move preservation -/

theorem roleSnapshots_aliceStart {r : ProtocolSetup} {a : Participant} (ha : a = r.alice)
    (b : Participant) (ikIdxA regIdxB : Nat) (bh : PQXDH.BundleHandles) (shown : Nat)
    {tr : ExecTrace} (h : RoleSnapshots r tr) :
    RoleSnapshots r ((Move.aliceStart a b ikIdxA regIdxB bh shown).next tr) :=
  RoleTraceful.run_snd (RoleTraceful.aliceStart r ha b ikIdxA regIdxB bh) h

theorem roleSnapshots_bobStart {r : ProtocolSetup} {b : Participant} (hb : b ≠ r.alice)
    (a : Participant) (kh : PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (shown : Nat)
    {tr : ExecTrace} (h : RoleSnapshots r tr) :
    RoleSnapshots r ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).next tr) :=
  RoleTraceful.run_snd (RoleTraceful.bobStart r hb a kh regIdxA mh pqIdx spqrMsgIdx) h

theorem roleSnapshots_encrypt {r : ProtocolSetup} (me : Participant)
    (stateIdx coinsLen pqIdx : Nat) (wrap : Option (Nat × Nat))
    {tr : ExecTrace} (h : RoleSnapshots r tr) :
    RoleSnapshots r ((Move.encrypt me stateIdx coinsLen pqIdx wrap).next tr) :=
  RoleTraceful.run_snd (RoleTraceful.messageEncrypt r me stateIdx coinsLen pqIdx) h

theorem roleSnapshots_encryptAbort {r : ProtocolSetup} (me : Participant) (stateIdx : Nat)
    {tr : ExecTrace} (h : RoleSnapshots r tr) :
    RoleSnapshots r ((Move.encryptAbort me stateIdx).next tr) :=
  RoleTraceful.run_snd (RoleTraceful.messageEncryptAbort r me stateIdx) h

theorem roleSnapshots_encryptFail {r : ProtocolSetup} (me : Participant)
    (stateIdx coinsLen : Nat) {tr : ExecTrace} (h : RoleSnapshots r tr) :
    RoleSnapshots r ((Move.encryptFail me stateIdx coinsLen).next tr) :=
  (RoleTraceful.bind (RoleTraceful.of_xquiet (XplSteps.xquiet_of_fix XplSteps.xfix_traceLength))
    (fun n _ => RoleTraceful.bind (RoleTraceful.messageEncrypt r me stateIdx coinsLen (n + 3))
      fun _ _ => RoleTraceful.pure (Q := fun _ => True) trivial) tr h).1

theorem roleSnapshots_decrypt {r : ProtocolSetup} (me : Participant)
    (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    {tr : ExecTrace} (h : RoleSnapshots r tr) :
    RoleSnapshots r ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) :=
  RoleTraceful.run_snd (RoleTraceful.messageDecrypt r me stateIdx msgIdx pqIdx spqrMsgIdx) h

theorem roleSnapshots_decryptSkipped {r : ProtocolSetup} (me : Participant)
    (stateIdx msgIdx k pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    {tr : ExecTrace} (h : RoleSnapshots r tr) :
    RoleSnapshots r ((Move.decryptSkipped me stateIdx msgIdx k pqIdx spqrMsgIdx wrapped).next tr) :=
  RoleTraceful.run_snd (RoleTraceful.messageDecryptSkipped r me stateIdx msgIdx k pqIdx spqrMsgIdx) h

theorem roleSnapshots_reject {r : ProtocolSetup} (draws : List Nat) {tr : ExecTrace}
    (h : RoleSnapshots r tr) :
    RoleSnapshots r ((Move.reject draws).next tr) := by
  unfold Move.next Move.act
  rw [DY.Traceful.run_pure]
  exact h

/-! ## Per-block preservation -/

theorem roleSnapshots_of_oneMove {r : ProtocolSetup} {Q : ExecTrace → Move → Prop}
    (hQ : ∀ tr m, Q tr m → RoleSnapshots r tr → RoleSnapshots r (m.next tr))
    {tr : ExecTrace} {δ : List Move} (hone : OneMove Q tr δ) (h : RoleSnapshots r tr) :
    RoleSnapshots r (runMoves δ tr).1 := by
  obtain ⟨pre, m, post, rfl, hpre, hm, hpost⟩ := hone
  rw [runMoves_append, runMoves]
  exact roleSnapshots_of_movesFrom_invisibleNoEffect hpost
    (hQ (runMoves pre tr).1 m hm (roleSnapshots_of_movesFrom_invisibleNoEffect hpre h))

theorem roleSnapshots_of_rpkMove {r : ProtocolSetup} (hab : r.alice ≠ r.bob)
    {tr : ExecTrace} {m : Move}
    (hact : ActorIn r.bob m) (hkind : RpkKind m ∨ NoSessionEffect tr m)
    (h : RoleSnapshots r tr) :
    RoleSnapshots r (m.next tr) := by
  rcases hkind with hrpk | hno
  · cases m <;> try exact False.elim hrpk
    case bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown =>
      have hb : b = r.bob := by
        rcases hact with h0 | h0 <;> simp [moveActor] at h0
        exact h0
      exact roleSnapshots_bobStart (hb ▸ hab.symm) a kh regIdxA mh pqIdx spqrMsgIdx shown h
    case decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
      exact roleSnapshots_decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped h
    case decryptSkipped me stateIdx msgIdx k pqIdx spqrMsgIdx wrapped =>
      exact roleSnapshots_decryptSkipped me stateIdx msgIdx k pqIdx spqrMsgIdx wrapped h
    case reject draws => exact roleSnapshots_reject draws h
  · exact roleSnapshots_of_noSessionEffect hno h

theorem roleSnapshots_of_bobStartBy_or_decryptBy {r : ProtocolSetup} (hab : r.alice ≠ r.bob)
    {p : Participant} {tr : ExecTrace} {m : Move}
    (hm : BobStartBy r.bob m ∨ DecryptBy p m) (h : RoleSnapshots r tr) :
    RoleSnapshots r (m.next tr) := by
  rcases hm with hbs | hdec
  · cases m <;> try exact False.elim hbs
    case bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown =>
      have hb : b = r.bob := hbs
      exact roleSnapshots_bobStart (hb ▸ hab.symm) a kh regIdxA mh pqIdx spqrMsgIdx shown h
  · cases m <;> try exact False.elim hdec
    case decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
      exact roleSnapshots_decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped h
    case decryptSkipped me stateIdx msgIdx k pqIdx spqrMsgIdx wrapped =>
      exact roleSnapshots_decryptSkipped me stateIdx msgIdx k pqIdx spqrMsgIdx wrapped h

theorem roleSnapshots_of_recvMove {r : ProtocolSetup} {tr : ExecTrace} {m : Move}
    (hkind : RecvKind m ∨ NoSessionEffect tr m) (h : RoleSnapshots r tr) :
    RoleSnapshots r (m.next tr) := by
  rcases hkind with hrcv | hno
  · cases m <;> try exact False.elim hrcv
    case decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
      exact roleSnapshots_decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped h
    case decryptSkipped me stateIdx msgIdx k pqIdx spqrMsgIdx wrapped =>
      exact roleSnapshots_decryptSkipped me stateIdx msgIdx k pqIdx spqrMsgIdx wrapped h
    case reject draws => exact roleSnapshots_reject draws h
  · exact roleSnapshots_of_noSessionEffect hno h

end Symbolic.Swarm.CREF
