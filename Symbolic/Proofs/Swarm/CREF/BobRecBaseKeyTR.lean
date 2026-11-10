/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Xpl.InvRecv
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvSend
public import Symbolic.Proofs.Swarm.CREF.TR.MessageKeyCurrentInv
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
public import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.MatchedPrefix
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyFrame
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvHistStepTR2
import VCVio.Prelude.Core
public import Symbolic.Proofs.Swarm.CREF.RoleSnapshots -- shake: keep
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Bob's Session Base-Key Invariant Across Ratchet and Non-Start Moves

Proves `NewBobSinfo` and `BobRecordBaseKeyInSession` preservation (`bks_movesFrom`, `bks_oneMove`,
`bks_xplBlock_recv`, `bks_xplBlock_send`) across Triple Ratchet steps and all moves that do not
start a Bob session, using `TR.MessageKeyCurrentInv` to show that parent snapshots remain current.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.COMPOSED.CompTrace (TRStEntry)
open DY.Libsignal.TripleRatchet (TRState TREvent)
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir)

private theorem bksTR_at?_none_of_ge {EntryT : Type} [DY.TraceEntryHas EntryT ExecTrace.Entry]
    {tr : ExecTrace} {j : Nat} (hj : tr.length ≤ j) : (tr.at? j : Option EntryT) = none := by
  simp only [DY.Trace.at?, show ¬ j < tr.length by omega, dite_false]

/-! ## Parent-Snapshot Linkage via `MessageKey` Events -/

/-- Every Bob snapshot stored at index `≥ tr₀.length` in `t` shares `sessionInfo` with some Bob
snapshot `k₀` in `tr₀` referenced as parent by a `MessageKey` event logged at index `≥ tr₀.length`. -/
def BkNew (bob : Participant) (tr₀ t : ExecTrace) : Prop :=
  ∀ (j : Nat) (st : TRState), tr₀.length ≤ j →
    (t.at? j : Option TRStEntry) = some ⟨⟨bob, st⟩⟩ →
    ∃ (k₀ : Nat) (st₀ : TRState), (tr₀.at? k₀ : Option TRStEntry) = some ⟨⟨bob, st₀⟩⟩ ∧
      st₀.sessionInfo bob = st.sessionInfo bob ∧
      ∃ (i : Nat) (s : SessionInfo) (dir : KeyDir) (seed salt : DY.Bytes) (n : UInt32)
        (rIdx : Nat), tr₀.length ≤ i ∧
        t.EventLoggedAt (TREvent.MessageKey s dir seed salt n rIdx k₀) i

theorem bkNew_refl (bob : Participant) (tr₀ : ExecTrace) : BkNew bob tr₀ tr₀ := by
  intro j st hj hat
  rw [bksTR_at?_none_of_ge hj] at hat
  cases hat

theorem newBobSinfo_of_bkNew {bob : Participant} {tr₀ t : ExecTrace} (hle : tr₀ ≤ t)
    (hinv : TR.MessageKeyCurrentInv t) (h : BkNew bob tr₀ t) : NewBobSinfo bob tr₀ t := by
  intro j st hj hat
  obtain ⟨k₀, st₀, hat₀, hs, i, s, dir, seed, salt, n, rIdx, hi, hlog⟩ :=
    h j st hj hat
  have hk₀ : k₀ < tr₀.length := bks_lt_length_of_at? hat₀
  have hcur := TR.isCurrentSnapshot_of_isCurrentSnapshotBefore hle hi hk₀
    (hinv s dir seed salt n rIdx k₀ i hlog (by omega))
  exact ⟨k₀, st₀, hat₀, hcur, hs⟩

theorem BkNew.ext {bob : Participant} {tr₀ t t' : ExecTrace} (h : BkNew bob tr₀ t) (hle : t ≤ t')
    (hst : ∀ j, t.length ≤ j → (t'.at? j : Option TRStEntry) = none) : BkNew bob tr₀ t' := by
  intro j st hj hat
  by_cases hjt : j < t.length
  · rw [XplSteps.xat?_le_eq hle hjt] at hat
    obtain ⟨k₀, st₀, hat₀, hs, i, s, dir, seed, salt, n, rIdx, hi, hlog⟩ :=
      h j st hj hat
    exact ⟨k₀, st₀, hat₀, hs, i, s, dir, seed, salt, n, rIdx, hi,
      COMPOSED.CompTrace.eventLoggedAt_mono hle hlog⟩
  · rw [hst j (Nat.le_of_not_lt hjt)] at hat
    cases hat

/-! ## `BkTraceful` Combinators -/

/-- `Traceful` Hoare predicate preserving `BkNew bob tr₀` and establishing postcondition `Q`. -/
def BkTraceful (bob : Participant) (tr₀ : ExecTrace) {α : Type} (Q : α → Prop)
    (x : Traceful α) : Prop :=
  ∀ t : ExecTrace, tr₀ ≤ t → BkNew bob tr₀ t →
    BkNew bob tr₀ (x.run t).2.val ∧ ∀ a, (x.run t).1 = some a → Q a

theorem BkTraceful.pure {bob : Participant} {tr₀ : ExecTrace} {α : Type} {Q : α → Prop} {a : α}
    (ha : Q a) : BkTraceful bob tr₀ Q (Pure.pure a) := by
  intro t _ ht
  rw [DY.Traceful.run_pure]
  refine ⟨ht, fun b hb => ?_⟩
  cases hb
  exact ha

theorem BkTraceful.failure {bob : Participant} {tr₀ : ExecTrace} {α : Type} {Q : α → Prop} :
    BkTraceful bob tr₀ Q (failure : Traceful α) := by
  intro t _ ht
  rw [DY.Traceful.run_failure]
  exact ⟨ht, fun _ hb => by cases hb⟩

theorem BkTraceful.bind {bob : Participant} {tr₀ : ExecTrace} {α β : Type} {Q₁ : α → Prop}
    {Q₂ : β → Prop} {x : Traceful α} {f : α → Traceful β}
    (hx : BkTraceful bob tr₀ Q₁ x) (hf : ∀ a, Q₁ a → BkTraceful bob tr₀ Q₂ (f a)) :
    BkTraceful bob tr₀ Q₂ (x >>= f) := by
  intro t hle ht
  rw [TR.RecvHistStep2.run_bind_snd, TR.RecvHistStep2.run_bind_fst]
  have h1 := hx t hle ht
  have hle1 : tr₀ ≤ (x.run t).2.val := DY.Trace.le_trans _ _ _ hle (XplSteps.xrun_le x t)
  cases hres : (x.run t).1 with
  | none => exact ⟨h1.1, fun _ hb => by cases hb⟩
  | some a => exact hf a (h1.2 a hres) (x.run t).2.val hle1 h1.1

theorem BkTraceful.bind_true {bob : Participant} {tr₀ : ExecTrace} {α β : Type} {Q₂ : β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : BkTraceful bob tr₀ (fun _ => True) x) (hf : ∀ a, BkTraceful bob tr₀ Q₂ (f a)) :
    BkTraceful bob tr₀ Q₂ (x >>= f) :=
  BkTraceful.bind hx (fun a _ => hf a)

theorem BkTraceful.of_xquiet {bob : Participant} {tr₀ : ExecTrace} {α : Type} {x : Traceful α}
    (hq : XplSteps.XQuiet x) : BkTraceful bob tr₀ (fun _ => True) x :=
  fun t _ ht => ⟨ht.ext (XplSteps.xrun_le x t) fun j hj => (hq t j hj).1, fun _ _ => trivial⟩

theorem bkNew_append_non_st {bob : Participant} {tr₀ t : ExecTrace} {E : Type}
    [ExecTraceTypes.Has E] (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option TRStEntry) = none)
    (h : BkNew bob tr₀ t) : BkNew bob tr₀ (t.append e) := by
  refine h.ext (DY.Trace.append_le t e) fun j hj => ?_
  by_cases hj' : j < (t.append e).length
  · have heq : j = t.length := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hj'
      omega
    subst heq
    have hat' : ((t.append e).at? t.length : Option TRStEntry) =
        (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) := by
      simp [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_2]
    rw [hat', hnone]
  · exact bksTR_at?_none_of_ge (Nat.le_of_not_lt hj')

theorem BkTraceful.logEvent_tr {bob : Participant} {tr₀ : ExecTrace} (ev : TREvent) :
    BkTraceful bob tr₀ (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro t _ ht
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
    DY.Traceful.run_pure]
  exact ⟨bkNew_append_non_st (⟨ev⟩ : ProtocolEvent.ExecEntryT TREvent) rfl ht,
    fun _ _ => trivial⟩

theorem BkTraceful.logEvent_pq {bob : Participant} {tr₀ : ExecTrace} (ev : PQXDH.PQXDHEvent) :
    BkTraceful bob tr₀ (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro t _ ht
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
    DY.Traceful.run_pure]
  exact ⟨bkNew_append_non_st
    (⟨ev⟩ : ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent) rfl ht, fun _ _ => trivial⟩

theorem BkTraceful.logEvent_c {bob : Participant} {tr₀ : ExecTrace} (ev : ComposedEvent) :
    BkTraceful bob tr₀ (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro t _ ht
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
    DY.Traceful.run_pure]
  exact ⟨bkNew_append_non_st (⟨ev⟩ : ProtocolEvent.ExecEntryT ComposedEvent) rfl ht,
    fun _ _ => trivial⟩

theorem BkTraceful.logSkippedKeys {bob : Participant} {tr₀ : ExecTrace} (s : SessionInfo)
    (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32),
      BkTraceful bob tr₀ (fun _ => True) (TripleRatchet.logSkippedKeys s pk rIdx src ck n k)
  | 0, _, _ => BkTraceful.pure trivial
  | k + 1, ck, n => by
    rw [TripleRatchet.logSkippedKeys]
    exact BkTraceful.bind (BkTraceful.logEvent_tr _) fun _ _ =>
      BkTraceful.logSkippedKeys s pk rIdx src k _ _

theorem bkNew_append_st_ne {bob me : Participant} {tr₀ t : ExecTrace} {st : TRState}
    (hne : me ≠ bob) (h : BkNew bob tr₀ t) :
    BkNew bob tr₀ (t.append (⟨⟨me, st⟩⟩ : RoleStE)) := by
  intro j st' hj hat
  by_cases hjt : j < t.length
  · rw [XplSteps.xat?_le_eq (DY.Trace.append_le t _) hjt] at hat
    obtain ⟨k₀, st₀, hat₀, hs, i, s, dir, seed, salt, n, rIdx, hi, hlog⟩ :=
      h j st' hj hat
    exact ⟨k₀, st₀, hat₀, hs, i, s, dir, seed, salt, n, rIdx, hi,
      COMPOSED.CompTrace.eventLoggedAt_mono (DY.Trace.append_le t _) hlog⟩
  · by_cases hj' : j < (t.append (⟨⟨me, st⟩⟩ : RoleStE)).length
    · have heq : j = t.length := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hj'
        omega
      subst heq
      rw [DY.Trace.at?_append t (⟨⟨me, st⟩⟩ : RoleStE)] at hat
      cases hat
      exact absurd rfl hne
    · rw [bksTR_at?_none_of_ge (Nat.le_of_not_lt hj')] at hat
      cases hat

theorem BkTraceful.storeLocalState_ne {bob : Participant} {tr₀ : ExecTrace} {me : Participant}
    {st : TRState} (hne : me ≠ bob) :
    BkTraceful bob tr₀ (fun _ => True) (PersistentLocalState.storeLocalState me st) := by
  intro t _ ht
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact ⟨bkNew_append_st_ne hne ht, fun _ _ => trivial⟩

theorem bkNew_append_mk_st {bob : Participant} {tr₀ t : ExecTrace} {par : Nat} {st₀ st : TRState}
    {s : SessionInfo} {dir : KeyDir} {seed salt : DY.Bytes} {n : UInt32} {rIdx : Nat}
    (hle : tr₀ ≤ t) (hpar : (tr₀.at? par : Option TRStEntry) = some ⟨⟨bob, st₀⟩⟩)
    (hs : st₀.sessionInfo bob = st.sessionInfo bob) (h : BkNew bob tr₀ t) :
    BkNew bob tr₀
      ((t.append (⟨TREvent.MessageKey s dir seed salt n rIdx par⟩ :
          ProtocolEvent.ExecEntryT TREvent)).append (⟨⟨bob, st⟩⟩ : RoleStE)) := by
  have h1 := bkNew_append_non_st
    (⟨TREvent.MessageKey s dir seed salt n rIdx par⟩ :
      ProtocolEvent.ExecEntryT TREvent) rfl h
  set t₁ := t.append (⟨TREvent.MessageKey s dir seed salt n rIdx par⟩ :
      ProtocolEvent.ExecEntryT TREvent) with ht₁
  have hlog : t₁.EventLoggedAt (TREvent.MessageKey s dir seed salt n rIdx par) t.length :=
    COMPOSED.CompTrace.eventLoggedAt_here t _
  have htr₀ : tr₀.length ≤ t.length := DY.Trace.length_le _ _ hle
  have hlen₁ : t₁.length = t.length + 1 := by
    simp only [ht₁, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2]
  intro j st' hj hat
  by_cases hjt : j < t₁.length
  · rw [XplSteps.xat?_le_eq (DY.Trace.append_le t₁ _) hjt] at hat
    obtain ⟨k₀, st₀', hat₀, hs', i, s', dir', seed', salt', n', rIdx', hi,
      hlog'⟩ := h1 j st' hj hat
    exact ⟨k₀, st₀', hat₀, hs', i, s', dir', seed', salt', n', rIdx', hi,
      COMPOSED.CompTrace.eventLoggedAt_mono (DY.Trace.append_le t₁ _) hlog'⟩
  · by_cases hj' : j < (t₁.append (⟨⟨bob, st⟩⟩ : RoleStE)).length
    · have heq : j = t₁.length := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hj'
        omega
      subst heq
      rw [DY.Trace.at?_append t₁ (⟨⟨bob, st⟩⟩ : RoleStE)] at hat
      cases hat
      exact ⟨par, st₀, hpar, hs, t.length, s, dir, seed, salt, n, rIdx,
        htr₀, COMPOSED.CompTrace.eventLoggedAt_mono (DY.Trace.append_le t₁ _) hlog⟩
    · rw [bksTR_at?_none_of_ge (Nat.le_of_not_lt hj')] at hat
      cases hat

theorem BkTraceful.logMessageKeyAndStore {bob : Participant} {tr₀ : ExecTrace} (me : Participant)
    {s : SessionInfo} {dir : KeyDir} {seed pqSalt : DY.Bytes} {n : UInt32}
    {rIdx par : Nat} {st : TRState}
    (hpar : me = bob → ∃ st₀ : TRState,
      (tr₀.at? par : Option TRStEntry) = some ⟨⟨bob, st₀⟩⟩ ∧ st₀.sessionInfo bob = st.sessionInfo bob) :
    BkTraceful bob tr₀ (fun _ => True)
      (TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  intro t hle ht
  unfold TripleRatchet.logMessageKeyAndStore
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
    DY.Traceful.run_pure]
  refine ⟨?_, fun _ _ => trivial⟩
  by_cases hme : me = bob
  · subst hme
    obtain ⟨st₀, hpar', hs⟩ := hpar rfl
    exact bkNew_append_mk_st hle hpar' hs ht
  · exact bkNew_append_st_ne hme
      (bkNew_append_non_st (⟨TREvent.MessageKey s dir seed pqSalt n rIdx par⟩ : ProtocolEvent.ExecEntryT TREvent) rfl ht)

theorem BkTraceful.dhRatchetStep {bob : Participant} {tr₀ : ExecTrace} (st : TRState)
    (pk : DY.Bytes) :
    BkTraceful bob tr₀
      (fun x : TRState × TripleRatchet.RecvChain => ∀ p : Participant, x.1.sessionInfo p = st.sessionInfo p)
      (TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine BkTraceful.bind
    (BkTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_guard _))) fun _ _ => ?_
  refine BkTraceful.bind (BkTraceful.of_xquiet (XplSteps.xquiet_genRand 32)) fun _ _ => ?_
  exact BkTraceful.pure
    (Q := fun x : TRState × TripleRatchet.RecvChain => ∀ p : Participant, x.1.sessionInfo p = st.sessionInfo p)
    fun _ => rfl

theorem BkTraceful.ensureReceiverChain {bob : Participant} {tr₀ : ExecTrace} (st : TRState)
    (pk : DY.Bytes) :
    BkTraceful bob tr₀
      (fun x : TRState × TripleRatchet.RecvChain × Bool =>
        ∀ p : Participant, x.1.sessionInfo p = st.sessionInfo p)
      (TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact BkTraceful.pure
      (Q := fun x : TRState × TripleRatchet.RecvChain × Bool =>
        ∀ p : Participant, x.1.sessionInfo p = st.sessionInfo p)
      fun _ => rfl
  · refine BkTraceful.bind (BkTraceful.dhRatchetStep st pk) fun x hx => ?_
    rcases x with ⟨st', c⟩
    exact BkTraceful.pure
      (Q := fun x : TRState × TripleRatchet.RecvChain × Bool =>
        ∀ p : Participant, x.1.sessionInfo p = st.sessionInfo p)
      hx
  · exact BkTraceful.failure

/-! ## Protocol Steps and Move Classification -/

theorem BkTraceful.run_start {bob : Participant} {tr₀ : ExecTrace} {α : Type} {Q : α → Prop}
    {x : Traceful α} (hx : BkTraceful bob tr₀ Q x) : BkNew bob tr₀ (x.run tr₀).2.val :=
  (hx tr₀ (DY.Trace.le_refl tr₀) (bkNew_refl bob tr₀)).1

theorem bkNew_xfix_bind {bob : Participant} {tr₀ : ExecTrace} {α β : Type} {x : Traceful α}
    {f : α → Traceful β} (hx : XplSteps.XFix x)
    (hf : ∀ a, (x.run tr₀).1 = some a → BkNew bob tr₀ ((f a).run tr₀).2.val) :
    BkNew bob tr₀ ((x >>= f).run tr₀).2.val := by
  rw [TR.RecvHistStep2.run_bind_snd]
  cases hres : (x.run tr₀).1 with
  | none => rw [hx tr₀]; exact bkNew_refl bob tr₀
  | some a => rw [hx tr₀]; exact hf a hres

theorem bkNew_getLocalState_bind {bob : Participant} {tr₀ : ExecTrace} {β : Type}
    {me : Participant} {stateIdx : Nat} {f : TRState → Traceful β}
    (hf : ∀ st, (tr₀.at? stateIdx : Option TRStEntry) = some ⟨⟨me, st⟩⟩ →
      BkNew bob tr₀ ((f st).run tr₀).2.val) :
    BkNew bob tr₀
      (((PersistentLocalState.getLocalState me stateIdx : Traceful TRState) >>= f).run tr₀).2.val :=
  bkNew_xfix_bind (XplSteps.xfix_getLocalState me stateIdx) fun st hst =>
    hf st (bks_stored_of_getLocalState hst)

theorem bkNew_bind_unit {bob : Participant} {tr₀ : ExecTrace} {α : Type} {x : Traceful α}
    (h : BkNew bob tr₀ (x.run tr₀).2.val) :
    BkNew bob tr₀ ((x >>= fun _ => (pure () : Traceful Unit)).run tr₀).2.val := by
  rw [XplSteps.xrun_bind_unit]; exact h

theorem bk_par_of_stored {bob me : Participant} {tr₀ : ExecTrace} {par : Nat} {st st' : TRState}
    (hst : (tr₀.at? par : Option TRStEntry) = some ⟨⟨me, st⟩⟩)
    (hs : st.sessionInfo me = st'.sessionInfo me) :
    me = bob → ∃ st₀ : TRState,
      (tr₀.at? par : Option TRStEntry) = some ⟨⟨bob, st₀⟩⟩ ∧ st₀.sessionInfo bob = st'.sessionInfo bob := by
  intro hme
  subst hme
  exact ⟨st, hst, hs⟩

theorem bkNew_messageEncrypt {bob : Participant} {tr₀ : ExecTrace} (me : Participant)
    (stateIdx coinsLen pqIdx : Nat) :
    BkNew bob tr₀ ((TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx).run tr₀).2.val := by
  unfold TripleRatchet.messageEncrypt
  refine bkNew_getLocalState_bind fun st hst => BkTraceful.run_start (Q := fun _ => True) ?_
  exact BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_guard _))) fun _ =>
    BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_genRand 32)) fun _ =>
    BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_genRand coinsLen)) fun _ =>
    BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)) fun _ =>
    BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_receiveMessage pqIdx))) fun _ =>
    BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ =>
    BkTraceful.bind_true (BkTraceful.logMessageKeyAndStore me (bk_par_of_stored hst rfl)) fun _ =>
    BkTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)

theorem bkNew_messageEncryptAbort {bob : Participant} {tr₀ : ExecTrace} (me : Participant)
    (stateIdx : Nat) :
    BkNew bob tr₀ ((TripleRatchet.messageEncryptAbort me stateIdx).run tr₀).2.val := by
  unfold TripleRatchet.messageEncryptAbort
  exact bkNew_getLocalState_bind fun _ _ => BkTraceful.run_start
    (BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_genRand 32)) fun _ =>
      (BkTraceful.failure : BkTraceful bob tr₀ (fun _ => True) _))

theorem bkNew_messageDecrypt {bob : Participant} {tr₀ : ExecTrace} (me : Participant)
    (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    BkNew bob tr₀
      ((TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr₀).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine bkNew_getLocalState_bind fun st hst => BkTraceful.run_start (Q := fun _ => True) ?_
  refine BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_receiveSignalMsg msgIdx)) fun msg => ?_
  refine BkTraceful.bind (BkTraceful.ensureReceiverChain st msg.ratchetKey) fun x hx => ?_
  rcases x with ⟨st', c, rat⟩
  dsimp only at hx ⊢
  split
  · split
    · refine BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)) fun _ =>
        BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_receiveMessage _))) fun _ =>
        BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_verifyMacAndDecrypt _ _ _ _)) fun _ => ?_
      split
      · exact BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ =>
          BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ =>
          BkTraceful.bind_true (BkTraceful.logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ =>
          BkTraceful.logMessageKeyAndStore me (bk_par_of_stored hst (hx me).symm)
      · exact BkTraceful.bind_true (BkTraceful.logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ =>
          BkTraceful.logMessageKeyAndStore me (bk_par_of_stored hst (hx me).symm)
    · exact BkTraceful.failure
  · exact BkTraceful.failure

theorem bkNew_messageDecryptSkipped {bob : Participant} {tr₀ : ExecTrace} (me : Participant)
    (stateIdx msgIdx k pqIdx : Nat) (spqrMsgIdx : UInt32) :
    BkNew bob tr₀
      ((TripleRatchet.messageDecryptSkipped me stateIdx msgIdx k pqIdx spqrMsgIdx).run tr₀).2.val := by
  unfold TripleRatchet.messageDecryptSkipped
  refine bkNew_getLocalState_bind fun st hst => BkTraceful.run_start (Q := fun _ => True) ?_
  refine BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_receiveSignalMsg msgIdx)) fun msg =>
    BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xfix_getEntry k |> XplSteps.xquiet_of_fix)) fun e => ?_
  split
  · refine BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_guard _))) fun _ =>
      BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_guardTrace _))) fun _ => ?_
    split
    · exact BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)) fun _ =>
        BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_receiveMessage _))) fun _ =>
        BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_verifyMacAndDecrypt _ _ _ _)) fun _ =>
        BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ =>
        BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ =>
        BkTraceful.logMessageKeyAndStore me (bk_par_of_stored hst rfl)
    · exact BkTraceful.failure
  · exact BkTraceful.failure

theorem BkTraceful.aliceStart {bob : Participant} {tr₀ : ExecTrace} {a : Participant}
    (ha : a ≠ bob) (b : Participant) (ikIdxA regIdxB : Nat) (h : PQXDH.BundleHandles) :
    BkTraceful bob tr₀ (fun _ => True)
      (Composed.aliceStart a b ikIdxA regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  exact BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_aliceHandshake _ _ _ _ _)) fun _ =>
    BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_genRand 32)) fun _ =>
    BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)) fun _ =>
    BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)) fun _ =>
    BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_of_fix XplSteps.xfix_traceLength)) fun _ =>
    BkTraceful.bind_true (BkTraceful.logEvent_pq _) fun _ =>
    BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ =>
    BkTraceful.bind_true (BkTraceful.logEvent_c _) fun _ =>
    BkTraceful.storeLocalState_ne ha

/-- Moves that cannot create a fresh Bob session: all moves except `setup`, `bobStart`, and
`aliceStart` initiated by `bob`. -/
def BkMoveKind (bob : Participant) : Move → Prop
  | .setup .. | .bobStart .. => False
  | .aliceStart a .. => a ≠ bob
  | _ => True

theorem bkNew_next {bob : Participant} {tr : ExecTrace} {m : Move} (hm : BkMoveKind bob m) :
    BkNew bob tr (m.next tr) := by
  cases m
  case setup => exact hm.elim
  case bobStart => exact hm.elim
  case aliceStart a b ikIdxA regIdxB bh _ =>
    exact bkNew_bind_unit (BkTraceful.run_start (BkTraceful.aliceStart hm b ikIdxA regIdxB bh))
  case encrypt me stateIdx coinsLen pqIdx _ =>
    exact bkNew_bind_unit (bkNew_messageEncrypt me stateIdx coinsLen pqIdx)
  case encryptAbort me stateIdx =>
    exact bkNew_bind_unit (bkNew_messageEncryptAbort me stateIdx)
  case encryptFail me stateIdx coinsLen =>
    exact bkNew_xfix_bind XplSteps.xfix_traceLength fun n _ =>
      bkNew_bind_unit (bkNew_messageEncrypt me stateIdx coinsLen (n + 3))
  case decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ =>
    exact bkNew_bind_unit (bkNew_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx)
  case decryptSkipped me stateIdx msgIdx k pqIdx spqrMsgIdx _ =>
    exact bkNew_bind_unit (bkNew_messageDecryptSkipped me stateIdx msgIdx k pqIdx spqrMsgIdx)
  case reject =>
    unfold Move.next Move.act
    rw [DY.Traceful.run_pure]
    exact bkNew_refl bob tr
  case compromiseIK p idx =>
    unfold Move.next Move.act PQXDH.compromiseIK
    exact bkNew_bind_unit (BkTraceful.run_start
      (BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_getKey _ _ _))) fun _ =>
        BkTraceful.bind_true (BkTraceful.logEvent_pq _) fun _ =>
        BkTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)))
  case compromiseSPK b idx =>
    unfold Move.next Move.act PQXDH.compromiseSPK
    exact bkNew_bind_unit (BkTraceful.run_start
      (BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_getKey _ _ _))) fun _ =>
        BkTraceful.bind_true (BkTraceful.logEvent_pq _) fun _ =>
        BkTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)))
  case compromisePQSPK b idx =>
    unfold Move.next Move.act PQXDH.compromisePQSPK
    exact bkNew_bind_unit (BkTraceful.run_start
      (BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_getKey _ _ _))) fun _ =>
        BkTraceful.bind_true (BkTraceful.logEvent_pq _) fun _ =>
        BkTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)))
  case compromiseOPK b idx =>
    unfold Move.next Move.act PQXDH.compromiseOPK
    exact bkNew_bind_unit (BkTraceful.run_start
      (BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_getKey _ _ _))) fun _ =>
        BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_guardOnTrace _))) fun _ =>
        BkTraceful.bind_true (BkTraceful.logEvent_pq _) fun _ =>
        BkTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)))
  case exposeKey me stateIdx comp =>
    unfold Move.next Move.act TripleRatchet.exposeKey
    refine bkNew_bind_unit (BkTraceful.run_start (Q := fun _ => True)
      (BkTraceful.bind_true (BkTraceful.of_xquiet
        (XplSteps.xquiet_of_fix (XplSteps.xfix_getLocalState me stateIdx))) fun st => ?_))
    cases comp with
    | rk | dhs | cks =>
      exact BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ =>
        BkTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)
    | ckr pk =>
      dsimp only
      split
      · exact BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ =>
          BkTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)
      · exact BkTraceful.failure
  case exposeSpqr me stateIdx =>
    unfold Move.next Move.act TripleRatchet.exposeSpqr
    exact bkNew_bind_unit (BkTraceful.run_start
      (BkTraceful.bind_true (BkTraceful.of_xquiet
        (XplSteps.xquiet_of_fix (XplSteps.xfix_getLocalState me stateIdx))) fun _ =>
        BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ =>
        BkTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)))
  case exposeSkipped skIdx =>
    unfold Move.next Move.act TripleRatchet.exposeSkipped
    refine bkNew_bind_unit (BkTraceful.run_start (Q := fun _ => True)
      (BkTraceful.bind_true (BkTraceful.of_xquiet
        (XplSteps.xquiet_of_fix (XplSteps.xfix_getEntry skIdx))) fun e => ?_))
    split
    · exact BkTraceful.bind_true (BkTraceful.of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_guardTrace _))) fun _ =>
        BkTraceful.bind_true (BkTraceful.logEvent_tr _) fun _ =>
        BkTraceful.of_xquiet (XplSteps.xquiet_sendMessage _)
    · exact BkTraceful.failure
  case attackerSend t =>
    exact bkNew_bind_unit (BkTraceful.run_start (BkTraceful.of_xquiet (XplSteps.xquiet_sendMessage t)))
  case brkDH =>
    exact BkTraceful.run_start (BkTraceful.logEvent_pq .BrokenDH)
  case brkKEM =>
    exact BkTraceful.run_start (BkTraceful.logEvent_pq .BrokenKEM)

/-! ## Move Runs and Block Transport -/

theorem newBobSinfo_refl (bob : Participant) (tr : ExecTrace) : NewBobSinfo bob tr tr :=
  newBobSinfo_of_noNewSt fun _ hj => bksTR_at?_none_of_ge hj

theorem newBobSinfo_trans {bob : Participant} {tr₁ tr₂ tr₃ : ExecTrace} (h₁₂ : tr₁ ≤ tr₂)
    (h₂₃ : tr₂ ≤ tr₃) (h₁ : NewBobSinfo bob tr₁ tr₂) (h₂ : NewBobSinfo bob tr₂ tr₃) :
    NewBobSinfo bob tr₁ tr₃ := by
  intro j st hj hat
  by_cases hj₂ : j < tr₂.length
  · rw [XplSteps.xat?_le_eq h₂₃ hj₂] at hat
    exact h₁ j st hj hat
  · obtain ⟨k₁, st₁, hat₁, hcur₁, hs₁⟩ := h₂ j st (Nat.le_of_not_lt hj₂) hat
    by_cases hk₁ : k₁ < tr₁.length
    · rw [XplSteps.xat?_le_eq h₁₂ hk₁] at hat₁
      exact ⟨k₁, st₁, hat₁, isCurrentSnapshot_of_le_of_lt h₁₂ hk₁ hcur₁, hs₁⟩
    · obtain ⟨k₀, st₀, hat₀, hcur₀, hs₀⟩ := h₁ k₁ st₁ (Nat.le_of_not_lt hk₁) hat₁
      exact ⟨k₀, st₀, hat₀, hcur₀, hs₀.trans hs₁⟩

theorem newBobSinfo_step {bob : Participant} {tr : ExecTrace} {m : Move}
    (hinv : TR.MessageKeyCurrentInv (m.next tr))
    (h : NoSessionEffect tr m ∨ BkMoveKind bob m) : NewBobSinfo bob tr (m.next tr) := by
  rcases h with hno | hk
  · exact newBobSinfo_of_noSessionEffect hno
  · exact newBobSinfo_of_bkNew (XplSteps.xrun_le m.act tr) hinv (bkNew_next hk)

theorem newBobSinfo_runMoves {bob : Participant} :
    ∀ (δ : List Move) (tr : ExecTrace),
      (∀ k, TR.MessageKeyCurrentInv (runMoves (δ.take k) tr).1) →
      MovesFrom (fun tr m => NoSessionEffect tr m ∨ BkMoveKind bob m) tr δ →
      NewBobSinfo bob tr (runMoves δ tr).1
  | [], tr, _, _ => newBobSinfo_refl bob tr
  | m :: δ, tr, hinv, ⟨hm, hδ⟩ => by
    have h₁ : NewBobSinfo bob tr (m.next tr) := newBobSinfo_step (hinv 1) hm
    have h₂ : NewBobSinfo bob (m.next tr) (runMoves δ (m.next tr)).1 :=
      newBobSinfo_runMoves δ (m.next tr) (fun k => hinv (k + 1)) hδ
    exact newBobSinfo_trans (XplSteps.xrun_le m.act tr)
      (TR.RecvHistStep2.le_runMoves_fst δ (m.next tr)) h₁ h₂

theorem newBobSinfo_runTrace {r : ProtocolSetup} {ms₀ δ : List Move} (hrun : ModelRun r (ms₀ ++ δ))
    (hδ : MovesFrom (fun tr m => NoSessionEffect tr m ∨ BkMoveKind r.bob m) (runTraceMoves r ms₀) δ) :
    NewBobSinfo r.bob (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ δ)) := by
  rw [DY.Libsignal.Composed.Refinement.runTrace_append]
  refine newBobSinfo_runMoves δ (runTraceMoves r ms₀) (fun k => ?_) hδ
  have h := TR.messageKeyCurrentInv_reachable (hrun.2.2.1.2.2 (ms₀.length + k))
  rwa [List.take_length_add_append, DY.Libsignal.Composed.Refinement.runTrace_append] at h

/-- Preserves `BobRecordBaseKeyInSession` across a `ModelRun` block `δ` of `NoSessionEffect` or
`BkMoveKind r.bob` moves when Bob's held record preserves `current.aliceBaseKey`. -/
theorem bks_movesFrom {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms₀ δ : List Move} {records records' : Participant → Option HwBytes}
    (hrun : ModelRun r (ms₀ ++ δ))
    (hδ : MovesFrom (fun tr m => NoSessionEffect tr m ∨ BkMoveKind r.bob m) (runTraceMoves r ms₀) δ)
    (hrec : ∀ rr', records' r.bob = some (recordBytes rr') →
      ∃ rr, records r.bob = some (recordBytes rr) ∧
        rr'.current.aliceBaseKey = rr.current.aliceBaseKey)
    (h : BobRecordBaseKeyInSession interpretation r S g ms₀ records) :
    BobRecordBaseKeyInSession interpretation r S g (ms₀ ++ δ) records' :=
  bks_of_ext (newBobSinfo_runTrace hrun hδ) hrec h

theorem bk_movesFrom_of_oneMove {bob : Participant} {Q : ExecTrace → Move → Prop}
    (hQ : ∀ tr m, Q tr m → NoSessionEffect tr m ∨ BkMoveKind bob m) {tr : ExecTrace}
    {δ : List Move} (hone : OneMove Q tr δ) :
    MovesFrom (fun tr m => NoSessionEffect tr m ∨ BkMoveKind bob m) tr δ := by
  obtain ⟨pre, m, post, rfl, hpre, hm, hpost⟩ := hone
  have hinv : ∀ tr m, InvisibleNoEffect tr m → NoSessionEffect tr m ∨ BkMoveKind bob m :=
    fun _ _ h => Or.inl h.2
  refine (movesFrom_append _ pre (m :: post) tr).2 ⟨movesFrom_mono hinv tr pre hpre, ?_⟩
  exact ⟨hQ _ m hm, movesFrom_mono hinv _ post hpost⟩

theorem bk_of_recvStep {bob p : Participant} {blk : List MachineEvent} {tr : ExecTrace}
    {m : Move} (hm : RecvStep p blk tr m) : NoSessionEffect tr m ∨ BkMoveKind bob m := by
  rcases hm with ⟨-, hrcv | hno, -⟩
  · right
    cases m <;> first | exact False.elim hrcv | trivial
  · exact Or.inl hno

theorem bk_of_sendStep {bob p : Participant} {blk : List MachineEvent} {tr : ExecTrace}
    {m : Move} (hm : SendStep p blk tr m) : NoSessionEffect tr m ∨ BkMoveKind bob m := by
  rcases hm with ⟨hsnd, -⟩
  right
  cases m <;> first | exact False.elim hsnd | trivial

theorem bks_oneMove {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms₀ δ : List Move} {records records' : Participant → Option HwBytes}
    {Q : ExecTrace → Move → Prop}
    (hQ : ∀ tr m, Q tr m → NoSessionEffect tr m ∨ BkMoveKind r.bob m)
    (hrun : ModelRun r (ms₀ ++ δ)) (hone : OneMove Q (runTraceMoves r ms₀) δ)
    (hrec : ∀ rr', records' r.bob = some (recordBytes rr') →
      ∃ rr, records r.bob = some (recordBytes rr) ∧
        rr'.current.aliceBaseKey = rr.current.aliceBaseKey)
    (h : BobRecordBaseKeyInSession interpretation r S g ms₀ records) :
    BobRecordBaseKeyInSession interpretation r S g (ms₀ ++ δ) records' :=
  bks_movesFrom hrun (bk_movesFrom_of_oneMove hQ hone) hrec h

theorem bks_xplBlock_recv {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g gB : Ghost} {ms₀ δ : List Move} {acc blk : List MachineEvent}
    {p : Participant} {records records' : Participant → Option HwBytes}
    (hB : XplBlock interpretation r S who gB ms₀ δ acc blk)
    (hf : DeltaFaithful p (runTraceMoves r ms₀) δ) (hshape : RecvBlockShape blk)
    (hrec : ∀ rr', records' r.bob = some (recordBytes rr') →
      ∃ rr, records r.bob = some (recordBytes rr) ∧
        rr'.current.aliceBaseKey = rr.current.aliceBaseKey)
    (h : BobRecordBaseKeyInSession interpretation r S g ms₀ records) :
    BobRecordBaseKeyInSession interpretation r S g (ms₀ ++ δ) records' :=
  bks_oneMove (fun _ _ hm => bk_of_recvStep hm) hB.run (xplInv_recv hB hf hshape) hrec h

theorem bks_xplBlock_send {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g gB : Ghost} {ms₀ δ : List Move} {acc blk : List MachineEvent}
    {p : Participant} {records records' : Participant → Option HwBytes}
    (hB : XplBlock interpretation r S who gB ms₀ δ acc blk)
    (hf : DeltaFaithful p (runTraceMoves r ms₀) δ) (hshape : SendBlockShape blk)
    (hrec : ∀ rr', records' r.bob = some (recordBytes rr') →
      ∃ rr, records r.bob = some (recordBytes rr) ∧
        rr'.current.aliceBaseKey = rr.current.aliceBaseKey)
    (h : BobRecordBaseKeyInSession interpretation r S g ms₀ records) :
    BobRecordBaseKeyInSession interpretation r S g (ms₀ ++ δ) records' :=
  bks_oneMove (fun _ _ hm => bk_of_sendStep hm) hB.run (xplInv_send hB hf hshape) hrec h

end Symbolic.Swarm.CREF
