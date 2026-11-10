/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Actions.Network
import DY.Actions.PersistentGlobalState
import DY.Actions.PersistentLocalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Trace.Basic
import DY.Trace.Manipulation
import DY.Trace.Monad
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.CREF.Cli.World.XplTransferPure
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvRecv
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.Monad

/-!
# Accepting `session_recv_wire` Trace Frame and Bookkeeping Preservation

Defines the trace-extension predicate `rcvFrame` for a `session_recv_wire` step of `p` and proves
other-participant `PureCRecRel` preservation (`rcv_frame_other`) and `CBook` preservation
(`rcv_book`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet (TREvent TRState)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv

open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)

section Frame

open Symbolic.Swarm.COMPOSED
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir)
open DY.Libsignal.TripleRatchet (TRState TREvent
  dhRatchetStep ensureReceiverChain logSkippedKeys logMessageKeyAndStore
  receiveSignalMsg verifyMacAndDecrypt traceLength guardTrace)

/-- Protocol events that a `session_recv_wire` move of `p` from `tr₀` can log: `MessageKey` and
`SkippedKeyStored` belong to `p`, and `SkippedKeyUsed s k` belongs to `p` with a matching
`SkippedKeyStored` at index `k` in `tr₀`. -/
def rcvEv (p : Participant) (tr₀ : ExecTrace) : TREvent → Prop
  | .SkippedKeyUsed s k =>
    s.me = p ∧ ∃ pk n seed rIdx srcIdx,
      (tr₀.at? k : Option CompTrace.TREntry) =
        some ⟨.SkippedKeyStored s pk n seed rIdx srcIdx⟩
  | .MessageKey s _ _ _ _ _ _ => s.me = p
  | .SkippedKeyStored s _ _ _ _ _ => s.me = p
  | _ => True

/-- `tr` extends `tr₀` by entries whose TR states are `p`'s, whose TR events satisfy `rcvEv p tr₀`,
and with no new PQXDH events. -/
def rcvFrame (p : Participant) (tr₀ tr : ExecTrace) : Prop :=
  tr₀ ≤ tr ∧ ∀ i, tr₀.length ≤ i →
    (∀ e : CompTrace.TRStEntry, (tr.at? i : Option CompTrace.TRStEntry) = some e →
      e.st.participant = p) ∧
    (∀ e : CompTrace.TREntry, (tr.at? i : Option CompTrace.TREntry) = some e →
      rcvEv p tr₀ e.ev) ∧
    Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.NonSessionPQAt tr i

theorem rcvFrame_refl (p : Participant) (tr : ExecTrace) : rcvFrame p tr tr := by
  refine ⟨Trace.le_refl tr, fun _ hi => ⟨fun _ he => ?_, fun _ he => ?_, ?_⟩⟩
  · rw [PureXplQuiet.at?_none_of_ge hi] at he; cases he
  · rw [PureXplQuiet.at?_none_of_ge hi] at he; cases he
  · exact Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.nonSessionPQAt_of_eq_none (PureXplQuiet.at?_none_of_ge hi)

theorem rcvFrame_of_quietExt (p : Participant) {tr₀ tr : ExecTrace}
    (hq : PureXplQuiet.QuietExt tr₀ tr) : rcvFrame p tr₀ tr := by
  refine ⟨hq.1, fun i hi => ?_⟩
  by_cases hlt : i < tr.length
  · obtain ⟨hst, hpq, htr, _⟩ := hq.2 i hi hlt
    exact ⟨fun _ he => (by rw [hst] at he; cases he),
      fun _ he => (by rw [htr] at he; cases he), hpq⟩
  · have hge : tr.length ≤ i := by omega
    exact ⟨fun _ he => (by rw [PureXplQuiet.at?_none_of_ge hge] at he; cases he),
      fun _ he => (by rw [PureXplQuiet.at?_none_of_ge hge] at he; cases he),
      Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.nonSessionPQAt_of_eq_none (PureXplQuiet.at?_none_of_ge hge)⟩

theorem rcvFrame_append {E : Type} [DY.ExecTraceTypes.Has E] {p : Participant}
    {tr₀ tr : ExecTrace} {x : E}
    (hst : ∀ e : CompTrace.TRStEntry,
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
        Option CompTrace.TRStEntry) = some e → e.st.participant = p)
    (hev : ∀ e : CompTrace.TREntry,
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
        Option CompTrace.TREntry) = some e → rcvEv p tr₀ e.ev)
    (hpq : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option PureXplQuiet.QPqE) = none)
    (h : rcvFrame p tr₀ tr) : rcvFrame p tr₀ (tr.append x) := by
  refine ⟨Trace.le_trans _ _ _ h.1 (Trace.append_le tr x), fun i hi =>
    ⟨fun e he => ?_, fun e he => ?_, fun e he => ?_⟩⟩
  · rcases CompTrace.at?_append_cases he with ⟨_, he'⟩ | ⟨_, hp⟩
    · exact (h.2 i hi).1 e he'
    · exact hst e hp
  · rcases CompTrace.at?_append_cases he with ⟨_, he'⟩ | ⟨_, hp⟩
    · exact (h.2 i hi).2.1 e he'
    · exact hev e hp
  · rcases CompTrace.at?_append_cases he with ⟨_, he'⟩ | ⟨_, hp⟩
    · exact (h.2 i hi).2.2 e he'
    · rw [hpq] at hp; cases hp

theorem rcvFrame_append_other {E : Type} [DY.ExecTraceTypes.Has E] {p : Participant}
    {tr₀ tr : ExecTrace} {x : E}
    (h1 : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option CompTrace.TRStEntry) = none)
    (h2 : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option CompTrace.TREntry) = none)
    (h3 : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option PureXplQuiet.QPqE) = none)
    (h : rcvFrame p tr₀ tr) : rcvFrame p tr₀ (tr.append x) :=
  rcvFrame_append (fun _ hp => by rw [h1] at hp; cases hp)
    (fun _ hp => by rw [h2] at hp; cases hp) h3 h

/-- Trace effects of a `session_recv_wire` move of `p` from `tr₀`, expressed as preservation
obligations on an invariant `Inv`. -/
structure rcvFx (Inv : ExecTrace → Prop) (p : Participant) (tr₀ : ExecTrace) : Prop where
  send : ∀ m : DY.Bytes, CompTrace.Preserves Inv (DY.Network.sendMessage m)
  rand : ∀ k : Nat, CompTrace.Preserves Inv (DY.Random.genRand k)
  tr : ∀ ev : TREvent, rcvEv p tr₀ ev → CompTrace.Preserves Inv (DY.ProtocolEvent.logEvent ev)
  store : ∀ st : TRState, CompTrace.Preserves Inv (DY.PersistentLocalState.storeLocalState p st)

theorem rcvFrameFx (p : Participant) (tr₀ : ExecTrace) : rcvFx (rcvFrame p tr₀) p tr₀ where
  send _ := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
    exact rcvFrame_append_other rfl rfl rfl h
  rand _ := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact rcvFrame_append_other rfl rfl rfl h
  tr _ hev := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact rcvFrame_append (fun _ hp => by cases hp)
      (fun _ hp => by rw [CompTrace.proj_inj_eq] at hp; cases hp; exact hev) rfl h
  store _ := by
    intro _ h
    simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
    exact rcvFrame_append
      (fun _ hp => by rw [CompTrace.proj_inj_eq] at hp; cases hp; rfl) (fun _ hp => by cases hp) rfl h

theorem rcv_logSkippedKeys {Inv : ExecTrace → Prop} {p : Participant} {tr₀ : ExecTrace}
    (fx : rcvFx Inv p tr₀) (s : SessionInfo) (hs : s.me = p) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (idx : UInt32) (k : Nat),
      CompTrace.Preserves Inv (logSkippedKeys s pk rIdx src ck idx k)
  | _, _, 0 => CompTrace.Preserves.pure ()
  | ck, idx, k + 1 => by
    unfold logSkippedKeys
    exact CompTrace.Preserves.bind (fx.tr _ (by exact hs)) fun _ =>
      rcv_logSkippedKeys fx s hs pk rIdx src _ _ k

theorem rcv_logMKStore {Inv : ExecTrace → Prop} {p : Participant} {tr₀ : ExecTrace}
    (fx : rcvFx Inv p tr₀) (s : SessionInfo) (hs : s.me = p) (dir : KeyDir)
    (seed pqSalt : DY.Bytes) (k : UInt32) (rIdx par : Nat) (st : TRState) :
    CompTrace.Preserves Inv (logMessageKeyAndStore p s dir seed pqSalt k rIdx par st) := by
  unfold logMessageKeyAndStore
  exact CompTrace.Preserves.bind (fx.tr _ (by exact hs)) fun _ => fx.store st

theorem rcv_dhRatchetStep {Inv : ExecTrace → Prop} {p : Participant} {tr₀ : ExecTrace}
    (fx : rcvFx Inv p tr₀) (st : TRState) (pk : DY.Bytes) :
    CompTrace.Preserves Inv (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ =>
    CompTrace.Preserves.bind (fx.rand 32) fun _ => CompTrace.Preserves.pure _

theorem rcv_ensureReceiverChain {Inv : ExecTrace → Prop} {p : Participant} {tr₀ : ExecTrace}
    (fx : rcvFx Inv p tr₀) (st₀ : TRState) (pk : DY.Bytes) :
    CompTrace.Preserves Inv (ensureReceiverChain st₀ pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.bind (rcv_dhRatchetStep fx st₀ pk) fun _ =>
      CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.failure

theorem rcv_messageDecrypt {Inv : ExecTrace → Prop} {p : Participant} {tr₀ : ExecTrace}
    (fx : rcvFx Inv p tr₀) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    CompTrace.Preserves Inv
      (DY.Libsignal.TripleRatchet.messageDecrypt p stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr p stateIdx) fun st =>
    CompTrace.Preserves.bind (CompTrace.Preserves.receiveSignalMsg msgIdx) fun msg =>
    CompTrace.Preserves.bind (rcv_ensureReceiverChain fx st msg.ratchetKey) fun r => ?_
  rcases r with ⟨st', _, _⟩
  dsimp only
  split
  · next seed _ _ =>
    split
    · next _ key _ =>
      refine CompTrace.Preserves.bind (fx.send key) fun _ =>
        CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun pqSalt =>
        CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt st' msg pqSalt seed)
          fun _ => ?_
      try dsimp only
      split
      · exact CompTrace.Preserves.bind (fx.tr _ trivial) fun _ =>
          CompTrace.Preserves.bind (fx.tr _ trivial) fun _ =>
          CompTrace.Preserves.bind (rcv_logSkippedKeys fx (st'.sessionInfo p) rfl _ _ _ _ _ _) fun _ =>
          CompTrace.Preserves.bind (fx.tr _ trivial) fun _ =>
          rcv_logMKStore fx (st'.sessionInfo p) rfl _ _ _ _ _ _ _
      · exact CompTrace.Preserves.bind (rcv_logSkippedKeys fx (st'.sessionInfo p) rfl _ _ _ _ _ _) fun _ =>
          CompTrace.Preserves.bind (fx.tr _ trivial) fun _ =>
          rcv_logMKStore fx (st'.sessionInfo p) rfl _ _ _ _ _ _ _
    · exact CompTrace.Preserves.failure
  · exact CompTrace.Preserves.failure

theorem rcv_getEntry_tr_at {Inv : ExecTrace → Prop} {α : Type}
    (skIdx : Nat) {f : CompTrace.TREntry → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ e : CompTrace.TREntry,
      (tr.at? skIdx : Option CompTrace.TREntry) = some e → Inv ((f e).run tr).2.val) :
    Inv (((DY.getEntry skIdx >>= f).run tr).2.val) := by
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [CompTrace.run_bind_snd, Traceful.run_mk]
  dsimp only
  rcases he : (tr.at? skIdx : Option CompTrace.TREntry) with _ | e
  · exact hInv
  · exact hf e he

theorem rcv_messageDecryptSkipped {p : Participant} (stateIdx msgIdx skIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) (tr₀ : ExecTrace) :
    rcvFrame p tr₀
      ((DY.Libsignal.TripleRatchet.messageDecryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx).run
        tr₀).2.val := by
  have hInv : rcvFrame p tr₀ tr₀ := rcvFrame_refl p tr₀
  have fx : rcvFx (rcvFrame p tr₀) p tr₀ := rcvFrameFx p tr₀
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine CompTrace.bind_getLocalState_tr_at p stateIdx tr₀ hInv fun st _ => ?_
  rw [CompTrace.run_bind_snd]
  have hrcv_snd : ((receiveSignalMsg msgIdx).run tr₀).2.val = tr₀ :=
    CompTrace.Preserves.receiveSignalMsg (Inv := fun t => t = tr₀) msgIdx tr₀ rfl
  rcases hmsg : ((receiveSignalMsg msgIdx).run tr₀).1 with _ | msg
  · rw [hrcv_snd]; exact hInv
  · rw [hrcv_snd]
    refine rcv_getEntry_tr_at skIdx tr₀ hInv fun e he => ?_
    rcases e with ⟨ev⟩
    cases ev with
    | SkippedKeyStored s pk n seed rIdx srcIdx =>
      dsimp only
      refine CompTrace.bind_guardP_at _ tr₀ hInv fun hguard => ?_
      obtain ⟨rfl, _, _⟩ := hguard
      have hsk_ev : rcvEv p tr₀ (.SkippedKeyUsed (st.sessionInfo p) skIdx) :=
        ⟨rfl, pk, n, seed, rIdx, srcIdx, he⟩
      refine (CompTrace.Preserves.bind (CompTrace.Preserves.guardTrace _) fun _ => ?_) tr₀ hInv
      split
      · next _ key _ =>
        exact CompTrace.Preserves.bind (fx.send key) fun _ =>
          CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun pqSalt =>
          CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt st msg pqSalt seed)
            fun _ =>
          CompTrace.Preserves.bind (fx.tr _ hsk_ev) fun _ =>
          CompTrace.Preserves.bind (fx.tr _ trivial) fun _ =>
          rcv_logMKStore fx (st.sessionInfo p) rfl _ _ _ _ _ _ _
      · exact CompTrace.Preserves.failure
    | _ =>
      dsimp only
      rw [DY.Traceful.run_failure]
      exact hInv

theorem rcv_next_move {p : Participant} {tr₀ : ExecTrace} {m : Move}
    (hact : ActorIn p m) (hrk : RecvKind m ∨ NoSessionEffect tr₀ m) :
    rcvFrame p tr₀ (m.next tr₀) := by
  rcases hrk with hrk | hno
  · cases m with
    | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ =>
      have hme : me = p := by
        rcases hact with h | h <;> simp only [moveActor, Option.some.injEq, reduceCtorEq] at h
        exact h
      subst me
      dsimp only [Move.next, Move.act]
      rw [b5_run_bind_pure_val]
      exact rcv_messageDecrypt (rcvFrameFx p tr₀) stateIdx msgIdx pqIdx spqrMsgIdx tr₀
        (rcvFrame_refl p tr₀)
    | decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx _ =>
      have hme : me = p := by
        rcases hact with h | h <;> simp only [moveActor, Option.some.injEq, reduceCtorEq] at h
        exact h
      subst me
      dsimp only [Move.next, Move.act]
      rw [b5_run_bind_pure_val]
      exact rcv_messageDecryptSkipped stateIdx msgIdx skIdx pqIdx spqrMsgIdx tr₀
    | reject _ =>
      rw [b5_reject_next]
      exact rcvFrame_refl p tr₀
    | _ => cases hrk
  · exact rcvFrame_of_quietExt p (PureXplQuiet.quietExt_of_noSessionEffect hno)

theorem rcv_at?_lt {EntryT : Type} [DY.TraceEntryHas EntryT ExecTrace.Entry] {tr₀ tr : ExecTrace}
    (hle : tr₀ ≤ tr) {j : Nat} (hj : j < tr₀.length) :
    (tr.at? j : Option EntryT) = tr₀.at? j := by
  have hj' : j < tr.length := Nat.lt_of_lt_of_le hj (Trace.length_le tr₀ tr hle)
  simp only [Trace.at?, hj, hj', dite_true, Trace.at_le tr₀ tr j hj hle]

theorem rcvFrame_getLocalState {p : Participant} {tr₀ tr : ExecTrace} (h : rcvFrame p tr₀ tr)
    {q : Participant} {i : Nat} {st : TRState}
    (hget : ((DY.PersistentLocalState.getLocalState q i : Traceful TRState).run tr₀).1 = some st) :
    ((DY.PersistentLocalState.getLocalState q i : Traceful TRState).run tr).1 = some st := by
  rw [CompTrace.getLocalState_tr_fst] at hget ⊢
  rcases he : (tr₀.at? i : Option CompTrace.TRStEntry) with _ | e
  · rw [he] at hget; cases hget
  · rw [he] at hget
    rw [CompTrace.at?_le_some h.1 he]
    exact hget

theorem rcvFrame_isCurrentSnapshot {p : Participant} {tr₀ tr : ExecTrace} (h : rcvFrame p tr₀ tr)
    {q : Participant} (hq : q ≠ p) {i : Nat} {st : TRState}
    (hget : ((DY.PersistentLocalState.getLocalState q i : Traceful TRState).run tr₀).1 = some st)
    (hcur : TripleRatchet.isCurrentSnapshot tr₀ i = true) :
    TripleRatchet.isCurrentSnapshot tr i = true := by
  rw [CompTrace.getLocalState_tr_fst] at hget
  rcases he : (tr₀.at? i : Option CompTrace.TRStEntry) with _ | ⟨⟨r, _⟩⟩
  · rw [he] at hget; cases hget
  rw [he] at hget
  have hr : r = q := by
    dsimp only at hget
    split_ifs at hget with hr
    exact hr
  have hlt : i < tr₀.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := CompTrace.TRStEntry) tr₀ i
    rw [he] at this; exact this
  have hlen := Trace.length_le tr₀ tr h.1
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur ⊢
  rw [CompTrace.at?_le_some h.1 he]
  rw [he] at hcur
  dsimp only at hcur ⊢
  rw [show tr.length - (i + 1) = (tr₀.length - (i + 1)) + (tr.length - tr₀.length) by omega,
    ← List.range'_append_1, List.all_append, Bool.and_eq_true]
  simp only [show i + 1 + (tr₀.length - (i + 1)) = tr₀.length by omega]
  refine ⟨Eq.trans (PureXplQuiet.q_all_congr_mem fun j hj => ?_) hcur, ?_⟩
  · rw [List.mem_range'_1] at hj
    rw [rcv_at?_lt h.1 (by omega : j < tr₀.length)]
  · rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range'_1] at hj
    try dsimp only
    rcases hj' : (tr.at? j : Option CompTrace.TRStEntry) with _ | e'
    · rfl
    · have hp := (h.2 j (by omega)).1 e' hj'
      simp only [hp, Bool.or_eq_true, bne_iff_ne, ne_eq]
      exact Or.inl fun h' => hq (h'.trans hr).symm

theorem rcvFrame_eventLoggedAt {p : Participant} {tr₀ tr : ExecTrace} (h : rcvFrame p tr₀ tr)
    {ev : TREvent} {i : Nat} (hl : tr₀.EventLoggedAt ev i) : tr.EventLoggedAt ev i := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hl ⊢
  exact CompTrace.at?_le_some h.1 hl

theorem rcvFrame_someEventOnTraceB {p : Participant} {tr₀ tr : ExecTrace} (h : rcvFrame p tr₀ tr)
    (P : TREvent → Bool) (hP : ∀ ev, rcvEv p tr₀ ev → P ev = false)
    (h0 : (TripleRatchet.anyEventOnTrace TripleRatchet.TREvent) tr₀ P = false) :
    (TripleRatchet.anyEventOnTrace TripleRatchet.TREvent) tr P = false := by
  simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h0 ⊢
  rw [List.any_eq_false] at h0 ⊢
  intro j hj hfj
  rw [List.mem_range] at hj
  try dsimp only at hfj
  by_cases hlt : j < tr₀.length
  · rw [rcv_at?_lt h.1 hlt] at hfj
    exact h0 j (List.mem_range.mpr hlt) hfj
  · rcases he : (tr.at? j : Option CompTrace.TREntry) with _ | e
    · rw [he] at hfj; dsimp only at hfj; cases hfj
    · rw [he] at hfj
      dsimp only at hfj
      rw [hP e.ev ((h.2 j (by omega)).2.1 e he)] at hfj
      cases hfj

theorem rcvFrame_skippedKeyUsedB {p : Participant} {tr₀ tr : ExecTrace} (h : rcvFrame p tr₀ tr)
    {q : Participant} (hq : q ≠ p) {st_q : TRState}
    {pk_q : DY.Bytes} {n_q : UInt32} {seed_q : DY.Bytes} {rIdx_q srcIdx_q k : Nat}
    (hlog : tr₀.EventLoggedAt (TREvent.SkippedKeyStored (st_q.sessionInfo q) pk_q n_q seed_q rIdx_q srcIdx_q) k)
    (hsu : (!TripleRatchet.skippedKeyUsedB tr₀ k) = true) :
    (!TripleRatchet.skippedKeyUsedB tr k) = true := by
  have h0 : TripleRatchet.skippedKeyUsedB tr₀ k = false := by simpa using hsu
  have h1 : TripleRatchet.skippedKeyUsedB tr k = false := by
    unfold TripleRatchet.skippedKeyUsedB at h0 ⊢
    refine rcvFrame_someEventOnTraceB h _ (fun ev hev => ?_) h0
    cases ev with
    | SkippedKeyUsed s k' =>
      obtain ⟨hsme, _, _, _, _, _, hk'⟩ := hev
      refine beq_false_of_ne fun heq => ?_
      subst heq
      have hlog' : (tr₀.at? k' : Option CompTrace.TREntry) =
          some ⟨.SkippedKeyStored (st_q.sessionInfo q) pk_q n_q seed_q rIdx_q srcIdx_q⟩ := by
        rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog
      rw [hk'] at hlog'
      injection hlog' with hE
      injection hE with hEv
      injection hEv with hs _ _ _ _ _
      exact hq ((congrArg SessionInfo.me hs).symm.trans hsme)
    | _ => rfl
  simp [h1]

theorem rcvFrame_receiverKeyUsedB {p : Participant} {tr₀ tr : ExecTrace} (h : rcvFrame p tr₀ tr)
    {q : Participant} (hq : q ≠ p) {st : TRState} {seed : DY.Bytes} {n : UInt32} {rIdx : Nat}
    (hru : (!TripleRatchet.receiverKeyUsedB tr₀ (st.sessionInfo q) seed n rIdx) = true) :
    (!TripleRatchet.receiverKeyUsedB tr (st.sessionInfo q) seed n rIdx) = true := by
  have h0 : TripleRatchet.receiverKeyUsedB tr₀ (st.sessionInfo q) seed n rIdx = false := by
    simpa using hru
  have h1 : TripleRatchet.receiverKeyUsedB tr (st.sessionInfo q) seed n rIdx = false := by
    unfold TripleRatchet.receiverKeyUsedB at h0 ⊢
    refine rcvFrame_someEventOnTraceB h _ (fun ev hev => ?_) h0
    cases ev
    case MessageKey s' dir _ _ _ _ _ =>
      cases dir
      · rfl
      · exact decide_eq_false fun hc => hq ((congrArg SessionInfo.me hc.1).symm.trans hev)
    all_goals rfl
  simp [h1]

theorem rcvFrame_getMessageSentAt {p : Participant} {tr₀ tr : ExecTrace} (h : rcvFrame p tr₀ tr)
    {i : Nat} {x : DY.Bytes} (hi : tr₀.getMessageSentAt i = some x) :
    tr.getMessageSentAt i = some x := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at hi ⊢
  have hlt : i < tr₀.length := by
    by_contra hge
    rw [PureXplQuiet.at?_none_of_ge (EntryT := DY.Network.ExecEntryT) (by omega : tr₀.length ≤ i)] at hi
    cases hi
  rw [rcv_at?_lt (EntryT := DY.Network.ExecEntryT) h.1 hlt]; exact hi

theorem rcvFrame_trRecordStateInv {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {Z : TR.PureTRSlots} {g : Ghost} {ms ms' : List Move} {records : Participant → Option HwBytes}
    {p : Participant} (h : rcvFrame p (runTraceMoves r ms) (runTraceMoves r ms'))
    (hrec : ∀ q bs, records q = some bs → q ≠ p)
    (hrsi : TR.PureTRRecordStateInv interpretation r S Z g ms records) :
    TR.PureTRRecordStateInv interpretation r S Z g ms' records := by
  intro q bs hqb
  have hqp := hrec q bs hqb
  obtain ⟨hq_mem, rec, st, stateIdx, hb, hget, hcur, hrel, hsk, hcanon, hks, hnd⟩ := hrsi q bs hqb
  refine ⟨hq_mem, rec, st, stateIdx, hb, rcvFrame_getLocalState h hget,
    rcvFrame_isCurrentSnapshot h hqp hget hcur, hrel, ?_, hcanon, hks, hnd⟩
  intro c hc k hk
  obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, hsu, hru, hgam, hsrk, hfind⟩ := hsk c hc k hk
  exact ⟨pk, rIdx, srcIdx, skIdx, seed, rcvFrame_eventLoggedAt h hlog,
    rcvFrame_skippedKeyUsedB h hqp hlog hsu, rcvFrame_receiverKeyUsedB h hqp hru, hgam, hsrk, hfind⟩

theorem rcvFrame_purePureAliceInitPending {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms ms' : List Move} {bs : HwBytes} {p : Participant}
    (h : rcvFrame p (runTraceMoves r ms) (runTraceMoves r ms')) (hap : r.alice ≠ p)
    (hp : PureAliceInitPending interpretation r S g ms bs) :
    PureAliceInitPending interpretation r S g ms' bs := by
  obtain ⟨sess, sc, remote, items, kpk, st, stateIdx, ekIdx, ctIdx, ek, ct,
    h1, h2, h3, hget, hcur, h6, h7, hek, hct, rest⟩ := hp
  exact ⟨sess, sc, remote, items, kpk, st, stateIdx, ekIdx, ctIdx, ek, ct,
    h1, h2, h3, rcvFrame_getLocalState h hget, rcvFrame_isCurrentSnapshot h hap hget hcur, h6, h7,
    rcvFrame_getMessageSentAt h hek, rcvFrame_getMessageSentAt h hct, rest⟩

theorem rcvFrame_pureCRecRel {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms ms' : List Move} {p q : Participant} {bs : HwBytes}
    (h : rcvFrame p (runTraceMoves r ms) (runTraceMoves r ms')) (hpq : q ≠ p)
    (hc : PureCRecRel interpretation r S g ms q bs) : PureCRecRel interpretation r S g ms' q bs := by
  rcases hc with hc | ⟨hqa, hc⟩
  · refine Or.inl (rcvFrame_trRecordStateInv h (fun q' bs' hq' => ?_) hc)
    by_cases hqq' : q' = q
    · subst hqq'; exact hpq
    · simp [hqq'] at hq'
  · exact Or.inr ⟨hqa, rcvFrame_purePureAliceInitPending h (fun h' => hpq (hqa.trans h')) hc⟩

theorem rcvFrame_bobDoneBaseKeys {p : Participant} {tr₀ tr : ExecTrace} (h : rcvFrame p tr₀ tr) :
    bobDoneBaseKeys tr = bobDoneBaseKeys tr₀ := by
  exact Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.bobDoneBaseKeys_eq_of_nonSessionPQExt h.1
    fun i h1 _ => (h.2 i h1).2.2

end Frame

/-- For `q ≠ p`, `PureCRecRel` for `q` is preserved across any `OneMove (RecvStep p blk)`. -/
theorem rcv_frame_other {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {blk : List MachineEvent} {g : Ghost} {ms₀ δ : List Move}
    {p q : Participant} {bs : HwBytes}
    (hδ : OneMove (RecvStep p blk) (runTraceMoves r ms₀) δ)
    (hpq : q ≠ p) (hc : PureCRecRel interpretation r S g ms₀ q bs) :
    PureCRecRel interpretation r S g (ms₀ ++ δ) q bs := by
  obtain ⟨pre, m, post, rfl, hpre, ⟨hact, hrk, _⟩, hpost⟩ := hδ
  have hq1 : PureXplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := by
    rw [TR.runTrace_append]
    exact PureXplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)
  have c1 := PureXplQuiet.quiet_pureCRecRel hq1 hc
  have hf : rcvFrame p (runTraceMoves r (ms₀ ++ pre)) (runTraceMoves r (ms₀ ++ pre ++ [m])) := by
    rw [TR.runTrace_snoc]
    rw [← TR.runTrace_append] at hrk
    exact rcv_next_move hact hrk
  have c2 := rcvFrame_pureCRecRel hf hpq c1
  have hq2 : PureXplQuiet.QuietExt (runTraceMoves r (ms₀ ++ pre ++ [m]))
      (runTraceMoves r (ms₀ ++ pre ++ [m] ++ post)) := by
    rw [TR.runTrace_append (ms₁ := ms₀ ++ pre ++ [m]), TR.runTrace_snoc, TR.runTrace_append]
    exact PureXplQuiet.quietExt_of_movesFrom _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost)
  have c3 := PureXplQuiet.quiet_pureCRecRel hq2 c2
  rwa [show ms₀ ++ pre ++ [m] ++ post = ms₀ ++ (pre ++ m :: post) by simp] at c3

private theorem rcv_sentBodies_cons_non_send (e : MachineEvent) (acc : List MachineEvent)
    (he : ∀ m, e ≠ .send m) : TR.sentBodies (e :: acc) = TR.sentBodies acc := by
  unfold TR.sentBodies
  rw [List.filterMap_cons]
  cases e with
  | send m => exact False.elim (he m rfl)
  | _ => rfl

private theorem rcv_sentBodies_mid :
    ∀ (mid : List MachineEvent),
      (∀ e ∈ mid, eventKind e = .rng ∨ eventKind e = .accept) →
      TR.sentBodies mid = []
  | [], _ => rfl
  | e :: mid, hmid => by
    have he : ∀ m, e ≠ .send m := by
      intro m hm
      subst hm
      rcases hmid (.send m) (List.mem_cons_self ..) with h | h <;> cases h
    rw [rcv_sentBodies_cons_non_send _ _ he]
    exact rcv_sentBodies_mid mid fun e' he' => hmid e' (List.mem_cons_of_mem _ he')

/-- `CBook` is preserved across any `OneMove (RecvStep p blk)` when the block emits no
`.send` events and `TRNsBound` holds on the extended move list. -/
theorem rcv_book {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {acc mid : List MachineEvent} {body : HwBytes} {g : Ghost} {ms₀ δ : List Move}
    {p : Participant} {sent accepted : List HwBytes}
    (hδ : OneMove (RecvStep p (.recv (wireWhisperTag :: body) :: mid)) (runTraceMoves r ms₀) δ)
    (hmid : ∀ e ∈ mid, eventKind e = .rng ∨ eventKind e = .accept)
    (hb : CBook interpretation r S g ms₀ sent accepted acc)
    (hns' : TR.TRNsBound r (ms₀ ++ δ) sent) :
    CBook interpretation r S g (ms₀ ++ δ) sent accepted
      (acc ++ .recv (wireWhisperTag :: body) :: mid) := by
  obtain ⟨pre, m, post, rfl, hpre, ⟨hact, hrk, _⟩, hpost⟩ := hδ
  have hq1 : PureXplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := by
    rw [TR.runTrace_append]
    exact PureXplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)
  have hf : rcvFrame p (runTraceMoves r (ms₀ ++ pre)) (runTraceMoves r (ms₀ ++ pre ++ [m])) := by
    rw [TR.runTrace_snoc]
    rw [← TR.runTrace_append] at hrk
    exact rcv_next_move hact hrk
  have hq2 : PureXplQuiet.QuietExt (runTraceMoves r (ms₀ ++ pre ++ [m]))
      (runTraceMoves r (ms₀ ++ pre ++ [m] ++ post)) := by
    rw [TR.runTrace_append (ms₁ := ms₀ ++ pre ++ [m]), TR.runTrace_snoc, TR.runTrace_append]
    exact PureXplQuiet.quietExt_of_movesFrom _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost)
  have hbd : bobDoneBaseKeys (runTraceMoves r (ms₀ ++ (pre ++ m :: post))) =
      bobDoneBaseKeys (runTraceMoves r ms₀) := by
    rw [show ms₀ ++ (pre ++ m :: post) = ms₀ ++ pre ++ [m] ++ post by simp,
      PureXplQuiet.quiet_bobDoneBaseKeys hq2, rcvFrame_bobDoneBaseKeys hf,
      PureXplQuiet.quiet_bobDoneBaseKeys hq1]
  have hsent_blk : TR.sentBodies (.recv (wireWhisperTag :: body) :: mid) = [] := by
    rw [rcv_sentBodies_cons_non_send _ _ (fun _ h => by cases h)]
    exact rcv_sentBodies_mid mid hmid
  obtain ⟨hsent, _, hacc1, hacc2⟩ := hb
  refine ⟨?_, hns', ?_, ?_⟩
  · rw [TR.sentBodies_append, hsent_blk, List.append_nil]; exact hsent
  · rw [hbd]; exact hacc1
  · rw [hbd]; exact hacc2

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
