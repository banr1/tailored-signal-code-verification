/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TRView
public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
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
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Stage1Wire
import VCVio.Prelude.Core
import Symbolic.Proofs.Swarm.CREF.TR.RecvCol -- shake: keep
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
# Whisper Receive Decrypt Step Algebra

Proves `ModelRun`, `MatchedPrefix`, and visibility step lemmas for `Move.attackerSend`,
`Move.decryptSkipped`, and `Move.decrypt` over the composed Triple Ratchet model.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR.RecvDec

cref_open

open DY.Libsignal.TripleRatchet (SessionInfo RecvChain findRecvChain setRecvChain recvChainFor
  consumeMessageKey kdfCk chainKeyAt computeMac messageVersion x25519LowOrder createChain
  maxReceiverChains)
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg parseTrSignalMsg isCurrentSnapshot
  skippedKeyUsedB trMsgKeys logSkippedKeys receiveSignalMsg verifyMacAndDecrypt ensureReceiverChain
  dhRatchetStep messageDecrypt messageDecryptSkipped logMessageKeyAndStore guardTrace)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.PQXDH (PQXDHEvent)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF
open Symbolic.Swarm.CREF.TR

/-! ## `Traceful` and `ExecTrace` Lookup Helpers -/
abbrev StEntry := PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
abbrev TREntry := DY.ProtocolEvent.ExecEntryT TREvent
abbrev PQEntry := DY.ProtocolEvent.ExecEntryT PQXDHEvent
private theorem append_length {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with | some a => ((f a).run (x.run tr).2.val).1 | none => none := by
  rw [Traceful.run_bind]; rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl
theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with | some a => ((f a).run (x.run tr).2.val).2.val | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]; rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl
theorem getLocalState_fst (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 =
      match (tr.at? stH : Option StEntry) with
      | some ⟨⟨p, st⟩⟩ => if p = me then some st else none | none => none := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [run_bind_fst, run_bind_fst, run_bind_snd, Traceful.run_mk]
  rcases (tr.at? stH : Option StEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · dsimp only; rw [Traceful.run_pure]; dsimp only; unfold _root_.guard
    by_cases hp : p = me
    · rw [ite_eq_left_iff.mpr fun h => absurd hp h, ite_eq_left_iff.mpr fun h => absurd hp h,
        run_bind_fst, Traceful.run_pure]; dsimp only; rw [Traceful.run_pure]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hp, ite_eq_right_iff.mpr fun h => absurd h hp,
        run_bind_fst, Traceful.run_failure]
export Symbolic.Swarm.CREF.TR.RecvCol (TRRecvAllCollide)
theorem run_bind_pure_val {α : Type} (m : Traceful α) (tr : ExecTrace) :
    (((m >>= fun _ => (pure () : Traceful Unit))).run tr).2.val = (m.run tr).2.val := by
  rw [Traceful.run_bind]; rcases m.run tr with ⟨_ | _, _⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)
private theorem attackerSend_next_eq (tr : ExecTrace) (t : DY.Bytes) :
    (Move.attackerSend t).next tr = tr.append (⟨t⟩ : Network.ExecEntryT) := by
  unfold Move.next Move.act
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
theorem getLocalState_snd (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [run_bind_snd, run_bind_fst, run_bind_snd, Traceful.run_mk]
  rcases (tr.at? stH : Option StEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · dsimp only; rw [Traceful.run_pure]; dsimp only; unfold _root_.guard
    by_cases hp : p = me
    · rw [ite_eq_left_iff.mpr fun h => absurd hp h, run_bind_snd, Traceful.run_pure]
      dsimp only; rw [Traceful.run_pure]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hp, run_bind_snd, Traceful.run_failure]
theorem forall₂_append {α β : Type} {R : α → β → Prop} {l₁ l₁' : List α} {l₂ l₂' : List β}
    (h1 : List.Forall₂ R l₁ l₂) (h2 : List.Forall₂ R l₁' l₂') :
    List.Forall₂ R (l₁ ++ l₁') (l₂ ++ l₂') := by
  induction h1 with | nil => exact h2 | cons h _ ih => exact .cons h ih
theorem at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by simp only [append_length]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]
theorem at?_eq_none_of_le {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) {i : Nat}
    (hi : tr.length ≤ i) : (tr.at? i : Option E) = none := by
  have h : ¬ i < tr.length := by omega
  simp only [Trace.at?, h, ↓reduceDIte]
theorem trace_snoc_at_length {Entry : Type} (tr : DY.Trace Entry) (x : Entry)
    (h : tr.length < (tr.snoc x).length) : (tr.snoc x).at tr.length h = x := by
  simp only [Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]
theorem trace_append_at_length {Entry E1 : Type} [DY.TraceEntryHas E1 Entry]
    (tr : DY.Trace Entry) (e : E1) (h : tr.length < (tr.append e).length) :
    (tr.append e).at tr.length h = DY.TraceEntryHas.inj e := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1] at h ⊢
  exact trace_snoc_at_length tr (DY.TraceEntryHas.inj e) h
theorem at?_append_non_entry {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = none)
    (i : Nat) : ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  by_cases hlt : i < tr.length
  · exact at?_append_of_lt tr e hlt
  · by_cases heq : i = tr.length
    · subst heq
      have h1 : tr.length < (tr.append e).length := by simp only [append_length]; omega
      have h2 : ¬ tr.length < tr.length := Nat.lt_irrefl _
      simp only [Trace.at?, h1, h2, ↓reduceDIte, trace_append_at_length, hnone]
    · rw [at?_eq_none_of_le (tr.append e) (by simp only [append_length]; omega),
          at?_eq_none_of_le tr (by omega)]
theorem isCurrentSnapshot_append_non_st {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option StEntry) = none)
    (stateIdx : Nat) : isCurrentSnapshot (tr.append e) stateIdx = isCurrentSnapshot tr stateIdx := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]; rw [at?_append_non_entry tr e hnone]
  rcases h : (tr.at? stateIdx : Option StEntry) with _ | s
  · rfl
  · dsimp only
    have hlt : stateIdx < tr.length := by
      have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr stateIdx; rw [h] at this; exact this
    have hlen : (tr.append e).length - (stateIdx + 1) = (tr.length - (stateIdx + 1)) + 1 := by
      simp only [append_length]; omega
    have hsum : (stateIdx + 1) + 1 * (tr.length - (stateIdx + 1)) = tr.length := by omega
    have hlast : (tr.at? tr.length : Option StEntry) = none := at?_eq_none_of_le tr (Nat.le_refl _)
    rw [hlen, List.range'_concat, hsum]
    simp only [List.all_append, List.all_cons, List.all_nil,
      at?_append_non_entry tr e hnone, hlast, Bool.and_true]
theorem getMessageSentAt_attackerSend (tr : ExecTrace) (t : DY.Bytes) :
    ((Move.attackerSend t).next tr).getMessageSentAt tr.length = some t := by
  rw [attackerSend_next_eq, ← Trace.MessageSentAt_eq_getMessageSentAt,
    Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1]
  exact Trace.at?_append tr (⟨t⟩ : Network.ExecEntryT)
theorem getLocalState_attackerSend (me : Participant) (stH : Nat) (tr : ExecTrace) (t : DY.Bytes) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run ((Move.attackerSend t).next tr)).1 =
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 := by
  rw [attackerSend_next_eq, getLocalState_fst, getLocalState_fst,
    at?_append_non_entry tr (⟨t⟩ : Network.ExecEntryT) rfl stH]
/-! ## `ModelRun` and `MatchedPrefix` Step Algebra -/
theorem compromisesCurrentFrom_append (tr : ExecTrace) (ms₁ ms₂ : List Move) :
    compromisesCurrentFrom tr (ms₁ ++ ms₂) =
      (compromisesCurrentFrom tr ms₁ && compromisesCurrentFrom (runMoves ms₁ tr).1 ms₂) := by
  induction ms₁ generalizing tr with
  | nil => simp [compromisesCurrentFrom, runMoves]
  | cons m ms₁ ih => simp only [List.cons_append, compromisesCurrentFrom, ih, Bool.and_assoc, runMoves]
theorem ownSaltsFrom_append (tr : ExecTrace) (ms₁ ms₂ : List Move) :
    ownSaltsFrom tr (ms₁ ++ ms₂) = (ownSaltsFrom tr ms₁ && ownSaltsFrom (runMoves ms₁ tr).1 ms₂) := by
  induction ms₁ generalizing tr with
  | nil => simp [ownSaltsFrom, runMoves]
  | cons m ms₁ ih => simp only [List.cons_append, ownSaltsFrom, ih, Bool.and_assoc, runMoves]
theorem movesAnchored_append_singleton {ms₁ : List Move} {m : Move} {tr : ExecTrace}
    (ha : MovesAnchored ms₁ tr) (hm : m.LogsSessionCompletion (runMoves ms₁ tr).1) :
    MovesAnchored (ms₁ ++ [m]) tr := by
  induction ms₁ generalizing tr with | nil => exact ⟨hm, trivial⟩ | cons m₀ ms₁ ih => exact ⟨ha.1, ih ha.2 hm⟩
theorem modelRun_attackerSend {r₀ : ProtocolSetup} {ms₁ : List Move} {msg : DY.Bytes}
    (hmov : ModelRun r₀ ms₁) (hknows : msg.AttackerKnows (runTraceMoves r₀ ms₁)) :
    ModelRun r₀ (ms₁ ++ [Move.attackerSend msg]) := by
  refine modelRun_snoc_of_old hmov ?_ trivial
    (Stage1Wire.stateFaithful_snoc_of_isCurrentSnapshot hmov.2.2.2.2.2.2 (fun _ _ _ hm => nomatch hm))
  rcases hmov with ⟨hlen, hnoSetup, ⟨hreach, hanch, -⟩, hcomp, hsalts, -, -⟩
  refine ⟨hlen, fun m hm => ?_, ⟨?_, movesAnchored_append_singleton (m := .attackerSend msg) hanch trivial⟩,
    by rw [compromisesCurrentFrom_append, hcomp]; rfl, by rw [ownSaltsFrom_append, hsalts]; rfl⟩
  · rcases List.mem_append.mp hm with h1 | h2
    · exact hnoSetup m h1
    · simp only [List.mem_singleton] at h2; subst h2; rfl
  · rw [runTrace_snoc, Move.next, Move.act, run_bind_pure_val]
    exact (Traceful.PreservesReachability_base Network.reachability reachability msg (runTraceMoves r₀ ms₁) hreach hknows).1
theorem getEventAt_append_non_entry (EventT : Type) [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)]
    {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT EventT)) = none) (i : Nat) :
    (tr.append e).getEventAt EventT i = tr.getEventAt EventT i := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_non_entry (E2 := ProtocolEvent.ExecEntryT EventT) tr e hnone i]
theorem getEventAt_eq_none_of_le (EventT : Type) [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)]
    (tr : ExecTrace) {i : Nat} (hi : tr.length ≤ i) : tr.getEventAt EventT i = none := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_eq_none_of_le (E := ProtocolEvent.ExecEntryT EventT) tr hi]
theorem exposures_attackerSend (tr : ExecTrace) (msg : DY.Bytes) :
    exposures tr ((Move.attackerSend msg).next tr) = [] := by
  rw [attackerSend_next_eq]
  refine exposures_eq_nil fun j hj => ?_
  have hj_eq : j = tr.length := by
    have ⟨h1, h2⟩ := (mem_newIndices (tr0 := tr) (tr := tr.append (⟨msg⟩ : Network.ExecEntryT))).mp hj
    simp only [append_length] at h2; omega
  subst hj_eq; refine ⟨pqExposureAt_of_getEventAt_none ?_, trExposureAt_of_getEventAt_none ?_⟩
  · rw [getEventAt_append_non_entry PQXDHEvent tr (⟨msg⟩ : Network.ExecEntryT) rfl,
        getEventAt_eq_none_of_le PQXDHEvent tr (Nat.le_refl _)]
  · rw [getEventAt_append_non_entry TREvent tr (⟨msg⟩ : Network.ExecEntryT) rfl,
        getEventAt_eq_none_of_le TREvent tr (Nat.le_refl _)]
theorem matchedPrefix_attackerSend {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms₁ : List Move} {τ : List MachineEvent}
    {msg : DY.Bytes} (hmp : MatchedPrefix interpretation r₀ S who g ms₁ τ)
    (hm : msg.AttackerKnows (runTraceMoves r₀ ms₁)) :
    MatchedPrefix interpretation r₀ S who g (ms₁ ++ [.attackerSend msg]) τ := by
  have hstep := matchedPrefix_snoc_env (evs := []) hmp (modelRun_attackerSend hmp.2.1 hm) rfl rfl
    (fun _ h => nomatch h)
    (fun v hv => by rw [vis_attackerSend rfl, exposures_attackerSend] at hv; cases hv)
    (by rw [vis_attackerSend rfl, exposures_attackerSend]; exact List.Forall₂.nil)
  rwa [List.append_nil] at hstep
theorem modelRun_snoc_decrypt {r₀ : ProtocolSetup} {ms₁ : List Move}
    (p : Participant) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool := false)
    (hrun : ModelRun r₀ ms₁) (hcur : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx = true) :
    ModelRun r₀ (ms₁ ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) := by
  refine modelRun_snoc_of_old hrun ?_ trivial
    (Stage1Wire.stateFaithful_snoc_of_isCurrentSnapshot hrun.2.2.2.2.2.2 (fun _ k _ hm => by
      simp only [Move.stateLoad?, Option.some.injEq, Prod.mk.injEq] at hm
      rcases hm with ⟨_, rfl, _⟩; exact hcur))
  rcases hrun with ⟨hlen, hnoSetup, ⟨hreach, hanch, -⟩, hcomp, hsalts, -, -⟩
  refine ⟨hlen, fun m hm => ?_, ⟨?_,
      movesAnchored_append_singleton (m := .decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped) hanch trivial⟩,
    by rw [compromisesCurrentFrom_append, hcomp]; rfl, by rw [ownSaltsFrom_append, hsalts]; rfl⟩
  · rcases List.mem_append.mp hm with h1 | h2
    · exact hnoSetup m h1
    · simp only [List.mem_singleton] at h2; subst h2; rfl
  · rw [runTrace_snoc, Move.next, Move.act, run_bind_pure_val]
    exact (Traceful.PreservesReachability_base DY.Libsignal.TripleRatchet.messageDecrypt.reachability
      reachability (p, stateIdx, msgIdx, pqIdx, spqrMsgIdx) (runTraceMoves r₀ ms₁) hreach hcur).1
theorem modelRun_snoc_decryptSkipped {r₀ : ProtocolSetup} {ms₁ : List Move}
    (p : Participant) (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool := false)
    (hrun : ModelRun r₀ ms₁) (hcur : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx = true) :
    ModelRun r₀ (ms₁ ++ [.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped]) := by
  refine modelRun_snoc_of_old hrun ?_ trivial
    (Stage1Wire.stateFaithful_snoc_of_isCurrentSnapshot hrun.2.2.2.2.2.2 (fun _ k _ hm => by
      simp only [Move.stateLoad?, Option.some.injEq, Prod.mk.injEq] at hm
      rcases hm with ⟨_, rfl, _⟩; exact hcur))
  rcases hrun with ⟨hlen, hnoSetup, ⟨hreach, hanch, -⟩, hcomp, hsalts, -, -⟩
  refine ⟨hlen, fun m hm => ?_, ⟨?_,
      movesAnchored_append_singleton (m := .decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped) hanch trivial⟩,
    by rw [compromisesCurrentFrom_append, hcomp]; rfl, by rw [ownSaltsFrom_append, hsalts]; rfl⟩
  · rcases List.mem_append.mp hm with h1 | h2
    · exact hnoSetup m h1
    · simp only [List.mem_singleton] at h2; subst h2; rfl
  · rw [runTrace_snoc, Move.next, Move.act, run_bind_pure_val]
    exact (Traceful.PreservesReachability_base DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
      reachability (p, stateIdx, msgIdx, skIdx, pqIdx, spqrMsgIdx) (runTraceMoves r₀ ms₁) hreach hcur).1
/-! ## `Move.decryptSkipped` and `Move.decrypt` Trace and Visibility Lemmas -/
private theorem logEvent_tr_run (ev : TREvent) (tr : ExecTrace) :
    ((DY.ProtocolEvent.logEvent ev).run tr).1 = some () ∧
      ((DY.ProtocolEvent.logEvent ev).run tr).2.val = tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT TREvent) := by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure, and_self]
private theorem sendMessage_run (msg : DY.Bytes) (tr : ExecTrace) :
    ((DY.Network.sendMessage msg).run tr).1 = some tr.length ∧
      ((DY.Network.sendMessage msg).run tr).2.val = tr.append (⟨msg⟩ : Network.ExecEntryT) := by
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_mk, and_self]
private theorem logMessageKeyAndStore_run_snd (me : Participant) (s : SessionInfo)
    (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32)
    (rIdx parentStateIdx : Nat) (st : TRState) (tr : ExecTrace) :
    ((logMessageKeyAndStore me s dir seed pqSalt n rIdx parentStateIdx st).run tr).2.val =
      (tr.append (⟨TREvent.MessageKey s dir seed pqSalt n rIdx parentStateIdx⟩ : ProtocolEvent.ExecEntryT TREvent)).append (⟨⟨me, st⟩⟩ : StEntry) := by
  unfold logMessageKeyAndStore
  obtain ⟨hl1, hl2⟩ := logEvent_tr_run
    (TREvent.MessageKey s dir seed pqSalt n rIdx parentStateIdx) tr
  rw [run_bind_snd, hl1, hl2]; dsimp only
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
def logSkippedKeysTr (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat) :
    DY.Bytes → UInt32 → Nat → ExecTrace → ExecTrace
  | _, _, 0, tr => tr
  | ck, n, k + 1, tr =>
    logSkippedKeysTr s pk rIdx sourceStateIdx (kdfCk ck).1 (n + 1) k
      (tr.append (⟨TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx⟩ : TREntry))
theorem logSkippedKeys_run (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) :
    ((logSkippedKeys s pk rIdx sourceStateIdx ck n k).run tr).1 = some () ∧
      ((logSkippedKeys s pk rIdx sourceStateIdx ck n k).run tr).2.val =
        logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr := by
  induction k generalizing ck n tr with
  | zero => unfold logSkippedKeys logSkippedKeysTr; rw [Traceful.run_pure]; exact ⟨rfl, rfl⟩
  | succ k ih =>
    unfold logSkippedKeys logSkippedKeysTr; rw [run_bind_fst, run_bind_snd]
    obtain ⟨hlog1, hlog2⟩ := logEvent_tr_run (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx) tr
    rw [hlog1, hlog2]; exact ih (kdfCk ck).1 (n + 1) _
theorem logSkippedKeysTr_length (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) :
    (logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).length = tr.length + k := by
  induction k generalizing ck n tr with
  | zero => exact (Nat.add_zero _).symm
  | succ k ih => unfold logSkippedKeysTr; rw [ih, append_length]; omega
theorem logSkippedKeysTr_le (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) :
    tr ≤ logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr := by
  induction k generalizing ck n tr with
  | zero => exact Trace.le_refl tr
  | succ k ih =>
    unfold logSkippedKeysTr
    exact Trace.le_trans _ _ _ (Trace.append_le tr _) (ih (kdfCk ck).1 (n + 1) _)
theorem at?_stEntry_logSkippedKeysTr (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) (i : Nat) :
    ((logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).at? i : Option StEntry) =
      (tr.at? i : Option StEntry) := by
  induction k generalizing ck n tr with
  | zero => rfl
  | succ k ih => unfold logSkippedKeysTr; rw [ih, at?_append_non_entry _ _ rfl]
theorem at?_random_logSkippedKeysTr (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) (i : Nat) :
    ((logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).at? i : Option DY.Random.ExecEntryT) =
      (tr.at? i : Option DY.Random.ExecEntryT) := by
  induction k generalizing ck n tr with
  | zero => rfl
  | succ k ih => unfold logSkippedKeysTr; rw [ih, at?_append_non_entry _ _ rfl]
theorem at?_pqEntry_logSkippedKeysTr (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) (i : Nat) :
    ((logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).at? i : Option PQEntry) =
      (tr.at? i : Option PQEntry) := by
  induction k generalizing ck n tr with
  | zero => rfl
  | succ k ih => unfold logSkippedKeysTr; rw [ih, at?_append_non_entry _ _ rfl]
theorem at?_trEntry_logSkippedKeysTr_lt (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) {i : Nat} (hi : i < tr.length) :
    ((logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).at? i : Option TREntry) =
      (tr.at? i : Option TREntry) := by
  have hle := logSkippedKeysTr_le s pk rIdx sourceStateIdx ck n k tr
  have hi' : i < (logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).length :=
    Nat.lt_of_lt_of_le hi (Trace.length_le _ _ hle)
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le _ _ i hi hle]
theorem at?_trEntry_logSkippedKeysTr_add (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) {j : Nat} (hj : j < k) :
    ((logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).at? (tr.length + j) : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored s pk (n + UInt32.ofNat j) (kdfCk (chainKeyAt ck j)).2 rIdx sourceStateIdx⟩ := by
  induction k generalizing ck n tr j with
  | zero => omega
  | succ k ih =>
    unfold logSkippedKeysTr
    cases j with
    | zero =>
      rw [Nat.add_zero]
      rw [at?_trEntry_logSkippedKeysTr_lt _ _ _ _ _ _ _ _ (by simp only [append_length]; omega)]
      rw [Trace.at?_append]
      have hn : n + UInt32.ofNat 0 = n := UInt32.add_zero n
      rw [hn]; rfl
    | succ j' =>
      have hj' : j' < k := by omega
      have hlen : tr.length + (j' + 1) =
          (tr.append (⟨TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx⟩ :
            ProtocolEvent.ExecEntryT TREvent)).length + j' := by simp only [append_length]; omega
      rw [hlen, ih (kdfCk ck).1 (n + 1) _ hj']
      have hn : (n + 1) + UInt32.ofNat j' = n + UInt32.ofNat (j' + 1) := by
        apply UInt32.eq_of_toBitVec_eq
        change n.toBitVec + 1#32 + BitVec.ofNat 32 j' = n.toBitVec + BitVec.ofNat 32 (j' + 1)
        rw [BitVec.ofNat_add]; ac_rfl
      rw [hn]; rfl
theorem at?_trEntry_logSkippedKeysTr_exists (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) {i : Nat}
    (hlo : tr.length ≤ i) (hhi : i < tr.length + k) :
    ∃ n' seed',
      ((logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).at? i : Option TREntry) =
        some ⟨TREvent.SkippedKeyStored s pk n' seed' rIdx sourceStateIdx⟩ := by
  have hj : i - tr.length < k := by omega
  have hi_eq : i = tr.length + (i - tr.length) := by omega
  rw [hi_eq]; exact ⟨_, _, at?_trEntry_logSkippedKeysTr_add s pk rIdx sourceStateIdx ck n k tr hj⟩
theorem receiveMessage_run {idx : Nat} {tr : ExecTrace} {t : DY.Bytes}
    (hat : (tr.at? idx : Option Network.ExecEntryT) = some ⟨t⟩) :
    ((DY.Network.receiveMessage idx).run tr).1 = some t ∧
      ((DY.Network.receiveMessage idx).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1]
  simp only [Traceful.run_bind, Traceful.run_mk, Traceful.run_pure, hat, and_self]
theorem receiveSignalMsg_run {msgIdx : Nat} {tr : ExecTrace} {t : DY.Bytes} {msg : TRSignalMsg}
    (hmsg : tr.getMessageSentAt msgIdx = some t)
    (hparse : parseTrSignalMsg t = some msg)
    (hver : msg.version = messageVersion) :
    ((receiveSignalMsg msgIdx).run tr).1 = some msg ∧
      ((receiveSignalMsg msgIdx).run tr).2.val = tr := by
  have hms := (Trace.MessageSentAt_eq_getMessageSentAt t msgIdx tr).mpr hmsg
  rw [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1] at hms
  obtain ⟨hrm1, hrm2⟩ := receiveMessage_run hms
  unfold receiveSignalMsg; rw [run_bind_fst, run_bind_snd, hrm1, hrm2]; dsimp only
  rw [hparse]; dsimp only
  simp only [_root_.guard, hver, ↓reduceIte, Traceful.run_bind, Traceful.run_pure, and_self]
theorem verifyMacAndDecrypt_run {st : TRState} {msg : TRSignalMsg} {pqSalt seed ptTerm : DY.Bytes}
    (tr : ExecTrace)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm) :
    ((verifyMacAndDecrypt st msg pqSalt seed).run tr).1 = some ptTerm ∧
      ((verifyMacAndDecrypt st msg pqSalt seed).run tr).2.val = tr := by
  unfold verifyMacAndDecrypt
  simp only [_root_.guard, hmac_eq, ↓reduceIte, hdec, Traceful.run_bind, Traceful.run_pure]
  dsimp [liftM, monadLift, MonadLift.monadLift]; simp only [Traceful.run_mk, Traceful.run_pure, and_self]
/-- Pure trace of `Move.decryptSkipped` on `tr`. -/
def decSkippedTr (tr : ExecTrace) (me : Participant) (stateIdx skIdx rIdx _srcIdx : Nat)
    (st : TRState) (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) : ExecTrace :=
  let tr2 := ((tr.append (⟨key⟩ : Network.ExecEntryT)).append
    (⟨TREvent.SkippedKeyUsed (st.sessionInfo me) skIdx⟩ : TREntry)).append
    (⟨TREvent.Received me st.peer pk n ptTerm⟩ : TREntry)
  (tr2.append
    (⟨TREvent.MessageKey (st.sessionInfo me) .receiver seed pqSalt n rIdx stateIdx⟩ : TREntry)).append
    (⟨⟨me, { st with spqr := spqr' }⟩⟩ : StEntry)
theorem decSkippedTr_length (tr : ExecTrace) (me : Participant) (stateIdx skIdx rIdx srcIdx : Nat)
    (st : TRState) (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    (decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n).length =
      tr.length + 5 := by
  unfold decSkippedTr; dsimp only; simp only [append_length]
theorem decryptSkipped_next_eq {me : Participant} {stateIdx msgIdx skIdx pqIdx rIdx srcIdx : Nat}
    {spqrMsgIdx : UInt32} {wrapped : Bool} {tr : ExecTrace} {st : TRState}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hmsg : tr.getMessageSentAt msgIdx = some t)
    (hparse : parseTrSignalMsg t = some msg)
    (hver : msg.version = messageVersion)
    (hsk : (tr.at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo me) msg.ratchetKey msg.counter seed rIdx srcIdx⟩)
    (hunused : skippedKeyUsedB tr skIdx = false)
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : ((tr.append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx : Option Network.ExecEntryT) =
      some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm)
    (hfind : (findRecvChain st.toDRState.recv msg.ratchetKey).isSome = true) :
    (Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).next tr =
      decSkippedTr tr me stateIdx skIdx rIdx srcIdx st msg.ratchetKey seed key pqSalt ptTerm
        spqr' msg.counter := by
  obtain ⟨hrcv1, hrcv2⟩ := receiveSignalMsg_run hmsg hparse hver
  have hge1 : ((DY.getEntry skIdx : Traceful (ProtocolEvent.ExecEntryT TREvent)).run tr).1 =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo me) msg.ratchetKey msg.counter seed rIdx srcIdx⟩ := by
    simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk, hsk]
  have hge2 : ((DY.getEntry skIdx : Traceful (ProtocolEvent.ExecEntryT TREvent)).run tr).2.val = tr := by
    simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  have hgt1 : ((guardTrace fun tr => !skippedKeyUsedB tr skIdx).run tr).1 = some () := by
    unfold guardTrace; simp only [Traceful.run_mk, hunused, Bool.not_false, ↓reduceIte]
  have hgt2 : ((guardTrace fun tr => !skippedKeyUsedB tr skIdx).run tr).2.val = tr := by
    unfold guardTrace; simp only [Traceful.run_mk]
  let tr_k := tr.append (⟨key⟩ : Network.ExecEntryT)
  obtain ⟨hsm1, hsm2⟩ := sendMessage_run key tr
  obtain ⟨hrm1, hrm2⟩ := receiveMessage_run hpqSalt
  obtain ⟨hv1, hv2⟩ := verifyMacAndDecrypt_run tr_k hmac_eq hdec
  obtain ⟨hu1, hu2⟩ := logEvent_tr_run (TREvent.SkippedKeyUsed (st.sessionInfo me) skIdx) tr_k
  obtain ⟨hr1, hr2⟩ := logEvent_tr_run (TREvent.Received me st.peer msg.ratchetKey msg.counter ptTerm)
    (tr_k.append (⟨TREvent.SkippedKeyUsed (st.sessionInfo me) skIdx⟩ : ProtocolEvent.ExecEntryT TREvent))
  unfold Move.next Move.act; rw [run_bind_pure_val]; unfold messageDecryptSkipped
  rw [run_bind_snd, hst, getLocalState_snd]; dsimp only
  rw [run_bind_snd, hrcv1, hrcv2]; dsimp only; rw [run_bind_snd, hge1, hge2]; dsimp only
  simp only [_root_.guard, hfind, true_and, ↓reduceIte]; rw [run_bind_snd, Traceful.run_pure]; dsimp only
  rw [run_bind_snd, hgt1, hgt2]; dsimp only; rw [hspqr]; dsimp only
  rw [run_bind_snd, hsm1, hsm2]; dsimp only; rw [run_bind_snd, hrm1, hrm2]; dsimp only
  rw [run_bind_snd, hv1, hv2]; dsimp only; rw [run_bind_snd, hu1, hu2]; dsimp only
  rw [run_bind_snd, hr1, hr2]; dsimp only
  exact logMessageKeyAndStore_run_snd ..
theorem at?_random_decSkippedTr (tr : ExecTrace) (me : Participant)
    (stateIdx skIdx rIdx srcIdx : Nat) (st : TRState)
    (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) (i : Nat) :
    ((decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n).at? i :
      Option DY.Random.ExecEntryT) = (tr.at? i : Option DY.Random.ExecEntryT) := by
  unfold decSkippedTr; dsimp only
  rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
      at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl]
theorem newRandoms_eq_nil_of_at?_eq (tr tr' : ExecTrace)
    (h : ∀ i, tr.length ≤ i → (tr'.at? i : Option DY.Random.ExecEntryT) = (tr.at? i : Option DY.Random.ExecEntryT)) :
    newRandoms tr tr' = [] := by
  unfold newRandoms; refine List.filterMap_eq_nil_iff.mpr fun i hi => ?_
  have ⟨hlo, _⟩ := mem_newIndices.mp hi
  rw [h i hlo, at?_eq_none_of_le tr hlo]; rfl
theorem newRandoms_decSkippedTr (tr : ExecTrace) (me : Participant)
    (stateIdx skIdx rIdx srcIdx : Nat) (st : TRState)
    (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    newRandoms tr (decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n) = [] :=
  newRandoms_eq_nil_of_at?_eq tr _ fun _ _ => at?_random_decSkippedTr ..
theorem receivedPlaintext_decSkippedTr (tr : ExecTrace) (me : Participant)
    (stateIdx skIdx rIdx srcIdx : Nat) (st : TRState)
    (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    receivedPlaintext tr (decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n) =
      some ptTerm := by
  unfold decSkippedTr; dsimp only
  let tr1 := tr.append (⟨key⟩ : Network.ExecEntryT)
  let tr2 := tr1.append (⟨TREvent.SkippedKeyUsed (st.sessionInfo me) skIdx⟩ : ProtocolEvent.ExecEntryT TREvent)
  let tr3 := tr2.append (⟨TREvent.Received me st.peer pk n ptTerm⟩ : ProtocolEvent.ExecEntryT TREvent)
  rw [receivedPlaintext_append_of_proj (by simp only [append_length]; omega) _ rfl]
  rw [receivedPlaintext_append (by simp only [append_length]; omega)]
  have h3 : receivedAt
      (tr3.append (⟨TREvent.MessageKey (st.sessionInfo me) .receiver seed pqSalt n rIdx stateIdx⟩ : ProtocolEvent.ExecEntryT TREvent))
      tr3.length = none := by simp only [receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self']
  dsimp only [tr3, tr2, tr1] at h3; rw [h3, Option.or_none]
  rw [receivedPlaintext_append (by simp only [append_length]; omega)]
  have h2 : receivedAt tr3 tr2.length = some ptTerm := by
    dsimp only [tr3]; simp only [receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self']
  have h1 : receivedPlaintext tr tr2 = none := by
    dsimp only [tr2, tr1]
    rw [receivedPlaintext_append (by simp only [append_length]; omega),
        receivedPlaintext_append_of_proj (Nat.le_refl _) _ rfl, receivedPlaintext_self]
    simp only [receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self', Option.none_or]
  dsimp only [tr3, tr2, tr1] at h1 h2; simp only [h1, h2, Option.none_or]
theorem exposures_decSkippedTr (tr : ExecTrace) (me : Participant)
    (stateIdx skIdx rIdx srcIdx : Nat) (st : TRState)
    (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    exposures tr (decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n) = [] := by
  let tr' := decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n
  refine exposures_eq_nil fun j hj => ?_
  have ⟨hlo, hhi⟩ := mem_newIndices.mp hj; rw [decSkippedTr_length] at hhi
  have hpq : pqExposureAt tr' j = none := by
    apply pqExposureAt_of_getEventAt_none; simp only [tr', decSkippedTr, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
        at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl, at?_eq_none_of_le tr hlo]
  refine ⟨hpq, ?_⟩
  let tr2 := ((tr.append (⟨key⟩ : Network.ExecEntryT)).append
    (⟨TREvent.SkippedKeyUsed (st.sessionInfo me) skIdx⟩ : ProtocolEvent.ExecEntryT TREvent)).append
    (⟨TREvent.Received me st.peer pk n ptTerm⟩ : ProtocolEvent.ExecEntryT TREvent)
  rcases (show j = tr.length ∨ j = tr.length + 1 ∨ j = tr.length + 2 ∨ j = tr.length + 3 ∨ j = tr.length + 4 by omega) with
    rfl | rfl | rfl | rfl | rfl
  · apply trExposureAt_of_getEventAt_none; simp only [decSkippedTr, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    rw [at?_append_non_entry _ _ rfl, at?_append_of_lt _ _ (by simp only [append_length]; omega),
        at?_append_of_lt _ _ (by simp only [append_length]; omega),
        at?_append_of_lt _ _ (by simp only [append_length]; omega),
        at?_append_non_entry _ _ rfl, at?_eq_none_of_le tr (Nat.le_refl _)]
  · unfold trExposureAt
    have hev : tr'.getEventAt TREvent (tr.length + 1) = some (TREvent.SkippedKeyUsed (st.sessionInfo me) skIdx) := by
      simp only [tr', decSkippedTr, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
      rw [at?_append_non_entry _ _ rfl, at?_append_of_lt _ _ (by simp only [append_length]; omega),
          at?_append_of_lt _ _ (by simp only [append_length]; omega),
          show tr.length + 1 = (tr.append (⟨key⟩ : Network.ExecEntryT)).length from by simp only [append_length],
          Trace.at?_append]
    rw [hev]
  · unfold trExposureAt
    have hev : tr'.getEventAt TREvent (tr.length + 2) = some (TREvent.Received me st.peer pk n ptTerm) := by
      simp only [tr', decSkippedTr, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
      rw [at?_append_non_entry _ _ rfl, at?_append_of_lt _ _ (by simp only [append_length]; omega),
          show tr.length + 2 = ((tr.append (⟨key⟩ : Network.ExecEntryT)).append
            (⟨TREvent.SkippedKeyUsed (st.sessionInfo me) skIdx⟩ : ProtocolEvent.ExecEntryT TREvent)).length from
            by simp only [append_length], Trace.at?_append]
    rw [hev]
  · unfold trExposureAt
    have hev : tr'.getEventAt TREvent (tr.length + 3) =
        some (TREvent.MessageKey (st.sessionInfo me) .receiver seed pqSalt n rIdx stateIdx) := by
      simp only [tr', decSkippedTr, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
      rw [at?_append_non_entry _ _ rfl,
          show tr.length + 3 = tr2.length from by dsimp only [tr2]; simp only [append_length],
          Trace.at?_append]
    rw [hev]
  · apply trExposureAt_of_getEventAt_none; simp only [decSkippedTr, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    rw [at?_append_non_entry _ _ rfl, at?_eq_none_of_le _ (by simp only [append_length]; omega)]
theorem visOf_decryptSkipped {me : Participant} {stateIdx msgIdx skIdx pqIdx rIdx srcIdx : Nat}
    {spqrMsgIdx : UInt32} {tr : ExecTrace} {st : TRState}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hmsg : tr.getMessageSentAt msgIdx = some t) (hparse : parseTrSignalMsg t = some msg)
    (hver : msg.version = messageVersion)
    (hsk : (tr.at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo me) msg.ratchetKey msg.counter seed rIdx srcIdx⟩)
    (hunused : skippedKeyUsedB tr skIdx = false)
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : ((tr.append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx : Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg.ciphertext = some ptTerm)
    (hfind : (findRecvChain st.toDRState.recv msg.ratchetKey).isSome = true) :
    (Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx false).vis tr =
      [trEntry .recv t, trEntry .accept ptTerm] := by
  have hnext := decryptSkipped_next_eq (wrapped := false) hst hmsg hparse hver hsk hunused hspqr hpqSalt hmac_eq hdec hfind
  rw [vis_decryptSkipped_false hnext, hmsg, newRandoms_decSkippedTr,
      receivedPlaintext_decSkippedTr, exposures_decSkippedTr]; rfl
/-- Shared tail trace of `TripleRatchet.messageDecrypt` after `tr_pre`. -/
def decTailTr (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes)
    (n : UInt32) : ExecTrace :=
  let tr_sk := logSkippedKeysTr (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index
    (n.toNat - c.index.toNat) tr_pre
  let tr_rcv := tr_sk.append (⟨TREvent.Received me st1.peer pk n ptTerm⟩ : TREntry)
  (tr_rcv.append
    (⟨TREvent.MessageKey (st1.sessionInfo me) .receiver seed pqSalt n c.rIdx stateIdx⟩ : TREntry)).append
    (⟨⟨me, { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }⟩⟩ : StEntry)
theorem decTailTr_length (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).length =
      tr_pre.length + (n.toNat - c.index.toNat) + 3 := by
  unfold decTailTr; dsimp only; simp only [append_length, logSkippedKeysTr_length]
theorem at?_random_decTailTr (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes)
    (n : UInt32) (i : Nat) :
    ((decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).at? i :
      Option DY.Random.ExecEntryT) = (tr_pre.at? i : Option DY.Random.ExecEntryT) := by
  unfold decTailTr; dsimp only
  rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
      at?_append_non_entry _ _ rfl, at?_random_logSkippedKeysTr]
theorem at?_pqEntry_decTailTr (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes)
    (n : UInt32) (i : Nat) :
    ((decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).at? i :
      Option PQEntry) = (tr_pre.at? i : Option PQEntry) := by
  unfold decTailTr; dsimp only
  rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
      at?_append_non_entry _ _ rfl, at?_pqEntry_logSkippedKeysTr]
theorem at?_trEntry_decTailTr_lt (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes)
    (n : UInt32) {i : Nat} (hi : i < tr_pre.length) :
    ((decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).at? i : Option TREntry) =
      (tr_pre.at? i : Option TREntry) := by
  unfold decTailTr; dsimp only
  rw [at?_append_non_entry _ _ rfl,
      at?_append_of_lt _ _ (by simp only [append_length, logSkippedKeysTr_length]; omega),
      at?_append_of_lt _ _ (by simp only [logSkippedKeysTr_length]; omega),
      at?_trEntry_logSkippedKeysTr_lt _ _ _ _ _ _ _ _ hi]
theorem receivedPlaintext_logSkippedKeysTr {tr0 tr : ExecTrace} (hle : tr0.length ≤ tr.length)
    (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    receivedPlaintext tr0 (logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr) =
      receivedPlaintext tr0 tr := by
  induction k generalizing ck n tr with
  | zero => rfl
  | succ k ih =>
    unfold logSkippedKeysTr
    rw [ih (by simp only [append_length]; omega), receivedPlaintext_append hle]
    have hnone : receivedAt
        (tr.append (⟨TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx⟩ : TREntry))
        tr.length = none := by simp [receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self']
    rw [hnone, Option.or_none]
theorem receivedPlaintext_decTailTr {tr0 tr_pre : ExecTrace} (hle : tr0.length ≤ tr_pre.length)
    (hpre : receivedPlaintext tr0 tr_pre = none)
    (me : Participant) (stateIdx : Nat) (st1 : TRState) (c c' : RecvChain)
    (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    receivedPlaintext tr0 (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n) =
      some ptTerm := by
  unfold decTailTr; dsimp only
  let tr_sk := logSkippedKeysTr (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index
    (n.toNat - c.index.toNat) tr_pre
  rw [receivedPlaintext_append_of_proj (by simp only [append_length, logSkippedKeysTr_length]; omega) _ rfl]
  rw [receivedPlaintext_append (by simp only [append_length, logSkippedKeysTr_length]; omega)]
  have hmk : receivedAt
      ((tr_sk.append (⟨TREvent.Received me st1.peer pk n ptTerm⟩ : TREntry)).append
        (⟨TREvent.MessageKey (st1.sessionInfo me) .receiver seed pqSalt n c.rIdx stateIdx⟩ : TREntry))
      (tr_sk.append (⟨TREvent.Received me st1.peer pk n ptTerm⟩ : TREntry)).length = none := by
    simp only [receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self']
  rw [hmk, Option.or_none, receivedPlaintext_append (by simp only [logSkippedKeysTr_length]; omega)]
  have hsk : receivedPlaintext tr0 tr_sk = none := by rw [receivedPlaintext_logSkippedKeysTr hle, hpre]
  have hrcv : receivedAt (tr_sk.append (⟨TREvent.Received me st1.peer pk n ptTerm⟩ : TREntry))
      tr_sk.length = some ptTerm := by simp only [receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self']
  dsimp only [tr_sk] at hsk hrcv; simp only [hsk, hrcv, Option.none_or]
theorem trExposureAt_decTailTr_ge (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32)
    {j : Nat} (hlo : tr_pre.length ≤ j) :
    trExposureAt (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n) j = none := by
  let k := n.toNat - c.index.toNat
  let tr_sk := logSkippedKeysTr (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index k tr_pre
  have hlen_sk : tr_sk.length = tr_pre.length + k := logSkippedKeysTr_length ..
  by_cases h1 : j < tr_pre.length + k
  · obtain ⟨n', seed', hat⟩ := at?_trEntry_logSkippedKeysTr_exists
      (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index k tr_pre hlo h1
    unfold trExposureAt decTailTr; dsimp only
    have hev : (((tr_sk.append (⟨TREvent.Received me st1.peer pk n ptTerm⟩ : TREntry)).append
        (⟨TREvent.MessageKey (st1.sessionInfo me) .receiver seed pqSalt n c.rIdx stateIdx⟩ : TREntry)).append
        (⟨⟨me, { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }⟩⟩ : StEntry)).getEventAt TREvent j =
        some (TREvent.SkippedKeyStored (st1.sessionInfo me) pk n' seed' c.rIdx stateIdx) := by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
      rw [at?_append_non_entry _ _ rfl, at?_append_of_lt _ _ (by simp only [append_length]; omega),
          at?_append_of_lt _ _ (by omega), hat]
    rw [hev]
  · by_cases h2 : j = tr_pre.length + k
    · subst h2; unfold trExposureAt decTailTr; dsimp only
      have hev : (((tr_sk.append (⟨TREvent.Received me st1.peer pk n ptTerm⟩ : TREntry)).append
          (⟨TREvent.MessageKey (st1.sessionInfo me) .receiver seed pqSalt n c.rIdx stateIdx⟩ : TREntry)).append
          (⟨⟨me, { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }⟩⟩ : StEntry)).getEventAt TREvent (tr_pre.length + k) =
          some (TREvent.Received me st1.peer pk n ptTerm) := by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
        rw [at?_append_non_entry _ _ rfl,
            at?_append_of_lt _ _ (by simp only [append_length]; omega),
            ← hlen_sk, Trace.at?_append]
      rw [hev]
    · by_cases h3 : j = tr_pre.length + k + 1
      · subst h3; unfold trExposureAt decTailTr; dsimp only
        have hev : (((tr_sk.append (⟨TREvent.Received me st1.peer pk n ptTerm⟩ : TREntry)).append
            (⟨TREvent.MessageKey (st1.sessionInfo me) .receiver seed pqSalt n c.rIdx stateIdx⟩ : TREntry)).append
            (⟨⟨me, { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }⟩⟩ : StEntry)).getEventAt TREvent (tr_pre.length + k + 1) =
            some (TREvent.MessageKey (st1.sessionInfo me) .receiver seed pqSalt n c.rIdx stateIdx) := by
          simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
          have hlen1 : tr_pre.length + k + 1 =
              (tr_sk.append (⟨TREvent.Received me st1.peer pk n ptTerm⟩ : ProtocolEvent.ExecEntryT TREvent)).length := by
            simp only [append_length]; omega
          rw [at?_append_non_entry _ _ rfl, hlen1, Trace.at?_append]
        rw [hev]
      · apply trExposureAt_of_getEventAt_none; unfold decTailTr; simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
        rw [at?_append_non_entry _ _ rfl, at?_eq_none_of_le _ (by simp only [append_length, logSkippedKeysTr_length]; omega)]
theorem ensureReceiverChain_run_noRatchet {st : TRState} {pk : DY.Bytes} {c : RecvChain}
    (tr : ExecTrace) (hfind : findRecvChain st.recv pk = some c) :
    ((ensureReceiverChain st pk).run tr).1 = some (st, c, false) ∧
      ((ensureReceiverChain st pk).run tr).2.val = tr := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor TRState.toDRState; dsimp only; rw [hfind]; dsimp only
  rw [Traceful.run_pure]; exact ⟨rfl, rfl⟩
/-- Pure state/chain output of `TripleRatchet.dhRatchetStep st theirPk` at trace length `rngIdx`. -/
def trDhRatchetState (st : TRState) (theirPk : DY.Bytes) (rngIdx : Nat) : TRState × RecvChain :=
  let (rk1, ckr) := createChain st.rk theirPk st.dhs
  let dhs := randTerm rngIdx 32
  let (rk2, cks) := createChain rk1 theirPk dhs
  let c : RecvChain := { ratchetKey := theirPk, chainKey := ckr, index := 0, rIdx := st.rIdx + 2 }
  let recv := (st.recv ++ [c]).drop ((st.recv.length + 1) - maxReceiverChains)
  let pn := if st.ns = 0 then 0 else st.ns - 1
  ({ st with rk := rk2, dhs, cks, ns := 0, pn, rIdx := st.rIdx + 2, recv }, c)
theorem dhRatchetStep_run {st : TRState} {pk : DY.Bytes}
    (tr : ExecTrace) (hlow : x25519LowOrder pk = false) :
    ((dhRatchetStep st pk).run tr).1 = some (trDhRatchetState st pk tr.length) ∧
      ((dhRatchetStep st pk).run tr).2.val = tr.append (⟨32⟩ : DY.Random.ExecEntryT) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]; unfold trDhRatchetState
  have hg1 : ((_root_.guard (!x25519LowOrder pk) : Traceful Unit).run tr).1 = some () := by
    simp only [_root_.guard, hlow, Bool.not_false, ↓reduceIte, Traceful.run_pure]
  have hg2 : ((_root_.guard (!x25519LowOrder pk) : Traceful Unit).run tr).2.val = tr := by
    simp only [_root_.guard, hlow, Bool.not_false, ↓reduceIte, Traceful.run_pure]
  rw [run_bind_fst, run_bind_snd, hg1, hg2]; dsimp only
  have hr : ((DY.Random.genRand 32).run tr).1 = some (randTerm tr.length 32) ∧
      ((DY.Random.genRand 32).run tr).2.val = tr.append (⟨32⟩ : DY.Random.ExecEntryT) := by
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]; exact ⟨rfl, trivial⟩
  rw [run_bind_fst, run_bind_snd, hr.1, hr.2]; dsimp only; rw [Traceful.run_pure]; exact ⟨rfl, rfl⟩
theorem ensureReceiverChain_run_ratchet {st : TRState} {pk : DY.Bytes}
    (tr : ExecTrace) (hfind : findRecvChain st.recv pk = none)
    (hlow : x25519LowOrder pk = false) :
    ((ensureReceiverChain st pk).run tr).1 =
      some ((trDhRatchetState st pk tr.length).1, (trDhRatchetState st pk tr.length).2, true) ∧
      ((ensureReceiverChain st pk).run tr).2.val = tr.append (⟨32⟩ : DY.Random.ExecEntryT) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor TRState.toDRState; dsimp only; rw [hfind]
  simp only [hlow, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨hd1, hd2⟩ := dhRatchetStep_run tr hlow
  rw [run_bind_fst, run_bind_snd, hd1, hd2]; dsimp only; rw [Traceful.run_pure]; exact ⟨rfl, rfl⟩
theorem decrypt_next_noRatchet_eq {me : Participant} {stateIdx msgIdx pqIdx : Nat}
    {spqrMsgIdx : UInt32} {wrapped : Bool} {tr : ExecTrace} {st : TRState}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {c c' : RecvChain}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hmsg : tr.getMessageSentAt msgIdx = some t) (hparse : parseTrSignalMsg t = some msg)
    (hver : msg.version = messageVersion) (hfind : findRecvChain st.recv msg.ratchetKey = some c)
    (hcons : consumeMessageKey c msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : ((tr.append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx : Option Network.ExecEntryT) =
      some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm) :
    (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr =
      decTailTr (tr.append (⟨key⟩ : Network.ExecEntryT)) me stateIdx st c c'
        msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter := by
  obtain ⟨hrcv1, hrcv2⟩ := receiveSignalMsg_run hmsg hparse hver
  obtain ⟨hens1, hens2⟩ := ensureReceiverChain_run_noRatchet tr hfind
  let tr_k := tr.append (⟨key⟩ : Network.ExecEntryT)
  obtain ⟨hsm1, hsm2⟩ := sendMessage_run key tr
  obtain ⟨hrm1, hrm2⟩ := receiveMessage_run hpqSalt
  obtain ⟨hv1, hv2⟩ := verifyMacAndDecrypt_run tr_k hmac_eq hdec
  obtain ⟨hsk1, hsk2⟩ := logSkippedKeys_run (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
    c.chainKey c.index (msg.counter.toNat - c.index.toNat) tr_k
  obtain ⟨hr1, hr2⟩ := logEvent_tr_run (TREvent.Received me st.peer msg.ratchetKey msg.counter ptTerm)
    (logSkippedKeysTr (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
      (msg.counter.toNat - c.index.toNat) tr_k)
  unfold Move.next Move.act; rw [run_bind_pure_val]; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  rw [run_bind_snd, hst, getLocalState_snd]; dsimp only
  rw [run_bind_snd, hrcv1, hrcv2]; dsimp only; rw [run_bind_snd, hens1, hens2]; dsimp only
  rw [hcons]; dsimp only; rw [hspqr]; dsimp only; rw [run_bind_snd, hsm1, hsm2]; dsimp only
  rw [run_bind_snd, hrm1, hrm2]; dsimp only; rw [run_bind_snd, hv1, hv2]; dsimp only
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [run_bind_snd, hsk1, hsk2]; dsimp only; rw [run_bind_snd, hr1, hr2]; dsimp only
  exact logMessageKeyAndStore_run_snd ..
theorem newRandoms_decNoRatchet (tr : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st : TRState) (c c' : RecvChain) (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    newRandoms tr (decTailTr (tr.append (⟨key⟩ : Network.ExecEntryT)) me stateIdx st c c'
      pk seed pqSalt ptTerm spqr' n) = [] := by
  refine newRandoms_eq_nil_of_at?_eq tr _ fun i _ => ?_
  rw [at?_random_decTailTr, at?_append_non_entry _ _ rfl]
theorem exposures_decNoRatchet (tr : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st : TRState) (c c' : RecvChain) (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    exposures tr (decTailTr (tr.append (⟨key⟩ : Network.ExecEntryT)) me stateIdx st c c'
      pk seed pqSalt ptTerm spqr' n) = [] := by
  let tr_pre := tr.append (⟨key⟩ : Network.ExecEntryT)
  let tr' := decTailTr tr_pre me stateIdx st c c' pk seed pqSalt ptTerm spqr' n
  refine exposures_eq_nil fun j hj => ?_
  have ⟨hlo, _⟩ := mem_newIndices.mp hj
  have hpq : pqExposureAt tr' j = none := by
    apply pqExposureAt_of_getEventAt_none; simp only [tr', tr_pre, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    rw [at?_pqEntry_decTailTr, at?_append_non_entry _ _ rfl, at?_eq_none_of_le tr hlo]
  refine ⟨hpq, ?_⟩
  by_cases hjeq : j = tr.length
  · subst hjeq; apply trExposureAt_of_getEventAt_none; simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    rw [at?_trEntry_decTailTr_lt _ _ _ _ _ _ _ _ _ _ _ _ (by simp only [append_length]; omega),
        at?_append_non_entry _ _ rfl, at?_eq_none_of_le tr (Nat.le_refl _)]
  · exact trExposureAt_decTailTr_ge tr_pre me stateIdx st c c' pk seed pqSalt ptTerm spqr' n
      (by simp only [tr_pre, append_length]; omega)
theorem visOf_decrypt_noRatchet {me : Participant} {stateIdx msgIdx pqIdx : Nat}
    {spqrMsgIdx : UInt32} {tr : ExecTrace} {st : TRState}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {c c' : RecvChain}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hmsg : tr.getMessageSentAt msgIdx = some t) (hparse : parseTrSignalMsg t = some msg)
    (hver : msg.version = messageVersion) (hfind : findRecvChain st.recv msg.ratchetKey = some c)
    (hcons : consumeMessageKey c msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : ((tr.append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx : Option Network.ExecEntryT) =
      some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm) :
    (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx false).vis tr =
      [trEntry .recv t, trEntry .accept ptTerm] := by
  have hnext := decrypt_next_noRatchet_eq (wrapped := false) hst hmsg hparse hver hfind hcons hspqr hpqSalt hmac_eq hdec
  have hpre : receivedPlaintext tr (tr.append (⟨key⟩ : Network.ExecEntryT)) = none := by
    rw [receivedPlaintext_append_of_proj (Nat.le_refl _) _ rfl, receivedPlaintext_self]
  rw [vis_decrypt_false hnext, hmsg, newRandoms_decNoRatchet,
      receivedPlaintext_decTailTr (by simp only [append_length]; omega) hpre, exposures_decNoRatchet]; rfl
/-- Prefix trace of `TripleRatchet.messageDecrypt` in the DH-ratchet case. -/
def decRatchetPreTr (tr : ExecTrace) (me : Participant) (st1 : TRState)
    (pk key : DY.Bytes) : ExecTrace :=
  (((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append
    (⟨key⟩ : Network.ExecEntryT)).append
    (⟨TREvent.DHRatchet me st1.peer pk (DY.DiffieHellman.dhPk st1.dhs)⟩ : TREntry)).append
    (⟨TREvent.HonestDH (st1.sessionInfo me) st1.dhs (st1.rIdx - 2)⟩ : TREntry)
theorem decRatchetPreTr_length (tr : ExecTrace) (me : Participant) (st1 : TRState)
    (pk key : DY.Bytes) : (decRatchetPreTr tr me st1 pk key).length = tr.length + 4 := by
  unfold decRatchetPreTr; simp only [append_length]
theorem decrypt_next_ratchet_eq {me : Participant} {stateIdx msgIdx pqIdx : Nat}
    {spqrMsgIdx : UInt32} {wrapped : Bool} {tr : ExecTrace} {st : TRState}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {c' : RecvChain}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hmsg : tr.getMessageSentAt msgIdx = some t) (hparse : parseTrSignalMsg t = some msg)
    (hver : msg.version = messageVersion) (hfind : findRecvChain st.recv msg.ratchetKey = none)
    (hlow : x25519LowOrder msg.ratchetKey = false)
    (hcons : consumeMessageKey (trDhRatchetState st msg.ratchetKey tr.length).2 msg.counter =
      some (seed, c'))
    (hspqr : Spqr.spqrRecv (trDhRatchetState st msg.ratchetKey tr.length).1.spqr
      msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : (((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append
      (⟨key⟩ : Network.ExecEntryT)).at? pqIdx : Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey
      (trDhRatchetState st msg.ratchetKey tr.length).1.peerIk
      (trDhRatchetState st msg.ratchetKey tr.length).1.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm) :
    let st1 := (trDhRatchetState st msg.ratchetKey tr.length).1
    let c := (trDhRatchetState st msg.ratchetKey tr.length).2
    (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr =
      decTailTr (decRatchetPreTr tr me st1 msg.ratchetKey key) me stateIdx st1 c c'
        msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter := by
  dsimp only
  let st1 := (trDhRatchetState st msg.ratchetKey tr.length).1
  let c := (trDhRatchetState st msg.ratchetKey tr.length).2
  obtain ⟨hrcv1, hrcv2⟩ := receiveSignalMsg_run hmsg hparse hver
  obtain ⟨hens1, hens2⟩ := ensureReceiverChain_run_ratchet tr hfind hlow
  let tr_r := tr.append (⟨32⟩ : DY.Random.ExecEntryT)
  let tr_k := tr_r.append (⟨key⟩ : Network.ExecEntryT)
  obtain ⟨hsm1, hsm2⟩ := sendMessage_run key tr_r
  obtain ⟨hrm1, hrm2⟩ := receiveMessage_run hpqSalt
  obtain ⟨hv1, hv2⟩ := verifyMacAndDecrypt_run tr_k hmac_eq hdec
  obtain ⟨hdh1, hdh2⟩ := logEvent_tr_run
    (TREvent.DHRatchet me st1.peer msg.ratchetKey (DY.DiffieHellman.dhPk st1.dhs)) tr_k
  obtain ⟨hhd1, hhd2⟩ := logEvent_tr_run (TREvent.HonestDH (st1.sessionInfo me) st1.dhs (st1.rIdx - 2))
    (tr_k.append (⟨TREvent.DHRatchet me st1.peer msg.ratchetKey (DY.DiffieHellman.dhPk st1.dhs)⟩ :
      ProtocolEvent.ExecEntryT TREvent))
  obtain ⟨hsk1, hsk2⟩ := logSkippedKeys_run (st1.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
    c.chainKey c.index (msg.counter.toNat - c.index.toNat) (decRatchetPreTr tr me st1 msg.ratchetKey key)
  obtain ⟨hr1, hr2⟩ := logEvent_tr_run (TREvent.Received me st1.peer msg.ratchetKey msg.counter ptTerm)
    (logSkippedKeysTr (st1.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
      (msg.counter.toNat - c.index.toNat) (decRatchetPreTr tr me st1 msg.ratchetKey key))
  unfold Move.next Move.act; rw [run_bind_pure_val]; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  rw [run_bind_snd, hst, getLocalState_snd]; dsimp only
  rw [run_bind_snd, hrcv1, hrcv2]; dsimp only; rw [run_bind_snd, hens1, hens2]; dsimp only
  rw [hcons]; dsimp only; rw [hspqr]; dsimp only; rw [run_bind_snd, hsm1, hsm2]; dsimp only
  rw [run_bind_snd, hrm1, hrm2]; dsimp only; rw [run_bind_snd, hv1, hv2]; dsimp only; simp only [↓reduceIte]
  dsimp only [st1, c, decRatchetPreTr, tr_k, tr_r] at hdh1 hdh2 hhd1 hhd2 hsk1 hsk2 hr1 hr2 ⊢
  rw [run_bind_snd, hdh1, hdh2]; dsimp only; rw [run_bind_snd, hhd1, hhd2]; dsimp only
  rw [run_bind_snd, hsk1, hsk2]; dsimp only; rw [run_bind_snd, hr1, hr2]; dsimp only
  exact logMessageKeyAndStore_run_snd ..
theorem newRandoms_decRatchet (tr : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    newRandoms tr (decTailTr (decRatchetPreTr tr me st1 pk key) me stateIdx st1 c c'
      pk seed pqSalt ptTerm spqr' n) = [(randTerm tr.length 32, 32)] := by
  let tr_pre := decRatchetPreTr tr me st1 pk key
  let tr' := decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n
  have hlen : tr'.length - tr.length = 1 + (3 + ((n.toNat - c.index.toNat) + 3)) := by
    dsimp only [tr', tr_pre]; rw [decTailTr_length, decRatchetPreTr_length]; omega
  unfold newRandoms newIndices
  rw [hlen, ← List.range'_append (s := tr.length) (m := 1) (n := 3 + ((n.toNat - c.index.toNat) + 3)) (step := 1),
      Nat.one_mul, List.filterMap_append]
  have h0 : (tr'.at? tr.length : Option DY.Random.ExecEntryT) = some ⟨32⟩ := by
    dsimp only [tr', tr_pre]; rw [at?_random_decTailTr]; unfold decRatchetPreTr
    rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl, Trace.at?_append]
  have hrest : (List.range' (tr.length + 1) (3 + ((n.toNat - c.index.toNat) + 3))).filterMap
      (fun i => (tr'.at? i : Option DY.Random.ExecEntryT).map fun r => (randTerm i r.length, r.length)) = [] := by
    refine List.filterMap_eq_nil_iff.mpr fun i hi => ?_
    rw [List.mem_range'_1] at hi; dsimp only [tr', tr_pre]; rw [at?_random_decTailTr]; unfold decRatchetPreTr
    rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
        at?_eq_none_of_le (tr.append (⟨32⟩ : DY.Random.ExecEntryT)) (by simp only [append_length]; omega)]; rfl
  rw [hrest, List.append_nil]
  change [tr.length].filterMap
    (fun i => (tr'.at? i : Option DY.Random.ExecEntryT).map fun r => (randTerm i r.length, r.length)) = _
  simp only [List.filterMap_cons, List.filterMap_nil, h0, Option.map_some]
theorem receivedPlaintext_decRatchetPreTr (tr : ExecTrace) (me : Participant)
    (st1 : TRState) (pk key : DY.Bytes) :
    receivedPlaintext tr (decRatchetPreTr tr me st1 pk key) = none := by
  unfold decRatchetPreTr
  rw [receivedPlaintext_append (by simp only [append_length]; omega)]
  have h3 : receivedAt
      ((((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨key⟩ : Network.ExecEntryT)).append
        (⟨TREvent.DHRatchet me st1.peer pk (DY.DiffieHellman.dhPk st1.dhs)⟩ : TREntry)).append
        (⟨TREvent.HonestDH (st1.sessionInfo me) st1.dhs (st1.rIdx - 2)⟩ : TREntry))
      (((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨key⟩ : Network.ExecEntryT)).append
        (⟨TREvent.DHRatchet me st1.peer pk (DY.DiffieHellman.dhPk st1.dhs)⟩ : TREntry)).length = none := by
    simp only [receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self']
  rw [h3, Option.or_none, receivedPlaintext_append (by simp only [append_length]; omega)]
  have h2 : receivedAt
      (((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨key⟩ : Network.ExecEntryT)).append
        (⟨TREvent.DHRatchet me st1.peer pk (DY.DiffieHellman.dhPk st1.dhs)⟩ : TREntry))
      ((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append
        (⟨key⟩ : Network.ExecEntryT)).length = none := by
    simp only [receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self']
  rw [h2, Option.or_none, receivedPlaintext_append_of_proj (by simp only [append_length]; omega) _ rfl,
      receivedPlaintext_append_of_proj (Nat.le_refl _) _ rfl, receivedPlaintext_self]
theorem exposures_decRatchet (tr : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    exposures tr (decTailTr (decRatchetPreTr tr me st1 pk key) me stateIdx st1 c c'
      pk seed pqSalt ptTerm spqr' n) = [] := by
  let tr_pre := decRatchetPreTr tr me st1 pk key
  let tr' := decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n
  refine exposures_eq_nil fun j hj => ?_
  have ⟨hlo, _⟩ := mem_newIndices.mp hj
  have hpq : pqExposureAt tr' j = none := by
    apply pqExposureAt_of_getEventAt_none; simp only [tr', tr_pre, decRatchetPreTr, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    rw [at?_pqEntry_decTailTr, at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
        at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl, at?_eq_none_of_le tr hlo]
  refine ⟨hpq, ?_⟩
  by_cases hlt4 : j < tr.length + 4
  · rcases (show j = tr.length ∨ j = tr.length + 1 ∨ j = tr.length + 2 ∨ j = tr.length + 3 by omega) with
      rfl | rfl | rfl | rfl
    · apply trExposureAt_of_getEventAt_none; simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
      rw [at?_trEntry_decTailTr_lt _ _ _ _ _ _ _ _ _ _ _ _ (by rw [decRatchetPreTr_length]; omega)]
      unfold decRatchetPreTr
      rw [at?_append_of_lt _ _ (by simp only [append_length]; omega),
          at?_append_of_lt _ _ (by simp only [append_length]; omega),
          at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl, at?_eq_none_of_le tr (Nat.le_refl _)]
    · apply trExposureAt_of_getEventAt_none; simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
      rw [at?_trEntry_decTailTr_lt _ _ _ _ _ _ _ _ _ _ _ _ (by rw [decRatchetPreTr_length]; omega)]
      unfold decRatchetPreTr
      rw [at?_append_of_lt _ _ (by simp only [append_length]; omega),
          at?_append_of_lt _ _ (by simp only [append_length]; omega),
          at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl, at?_eq_none_of_le tr (by omega)]
    · unfold trExposureAt
      have hev : tr'.getEventAt TREvent (tr.length + 2) =
          some (TREvent.DHRatchet me st1.peer pk (DY.DiffieHellman.dhPk st1.dhs)) := by
        simp only [tr', tr_pre, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
        rw [at?_trEntry_decTailTr_lt _ _ _ _ _ _ _ _ _ _ _ _ (by rw [decRatchetPreTr_length]; omega)]
        unfold decRatchetPreTr
        rw [at?_append_of_lt _ _ (by simp only [append_length]; omega),
            show tr.length + 2 = ((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨key⟩ : Network.ExecEntryT)).length from
              by simp only [append_length], Trace.at?_append]
      rw [hev]
    · unfold trExposureAt
      have hev : tr'.getEventAt TREvent (tr.length + 3) =
          some (TREvent.HonestDH (st1.sessionInfo me) st1.dhs (st1.rIdx - 2)) := by
        simp only [tr', tr_pre, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
        rw [at?_trEntry_decTailTr_lt _ _ _ _ _ _ _ _ _ _ _ _ (by rw [decRatchetPreTr_length]; omega)]
        unfold decRatchetPreTr
        rw [show tr.length + 3 = (((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨key⟩ : Network.ExecEntryT)).append
              (⟨TREvent.DHRatchet me st1.peer pk (DY.DiffieHellman.dhPk st1.dhs)⟩ : ProtocolEvent.ExecEntryT TREvent)).length
              from by simp only [append_length], Trace.at?_append]
      rw [hev]
  · exact trExposureAt_decTailTr_ge tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n
      (by dsimp only [tr_pre]; rw [decRatchetPreTr_length]; omega)
theorem visOf_decrypt_ratchet {me : Participant} {stateIdx msgIdx pqIdx : Nat}
    {spqrMsgIdx : UInt32} {tr : ExecTrace} {st : TRState}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {c' : RecvChain}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hmsg : tr.getMessageSentAt msgIdx = some t) (hparse : parseTrSignalMsg t = some msg)
    (hver : msg.version = messageVersion) (hfind : findRecvChain st.recv msg.ratchetKey = none)
    (hlow : x25519LowOrder msg.ratchetKey = false)
    (hcons : consumeMessageKey (trDhRatchetState st msg.ratchetKey tr.length).2 msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv (trDhRatchetState st msg.ratchetKey tr.length).1.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : (((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx :
      Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey
      (trDhRatchetState st msg.ratchetKey tr.length).1.peerIk
      (trDhRatchetState st msg.ratchetKey tr.length).1.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg.ciphertext = some ptTerm) :
    (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx false).vis tr =
      [trEntry .recv t, trEntry .rng (randTerm tr.length 32), trEntry .accept ptTerm] := by
  have hnext := decrypt_next_ratchet_eq (wrapped := false) hst hmsg hparse hver hfind hlow hcons hspqr hpqSalt hmac_eq hdec
  dsimp only at hnext
  rw [vis_decrypt_false hnext, hmsg, newRandoms_decRatchet,
      receivedPlaintext_decTailTr (by rw [decRatchetPreTr_length]; omega) (receivedPlaintext_decRatchetPreTr ..),
      exposures_decRatchet]; rfl
/-! ## `MatchedPrefix`, Snapshot, and `TRNsBound` Step Lemmas -/
private theorem matchedPrefix_step_whisper {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms₁ : List Move} {m : Move}
    {τ rest : List MachineEvent} {vrest : List VisEntry} {me : Participant}
    {t : DY.Bytes} {body : HwBytes}
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ τ)
    (hrun' : ModelRun r₀ (ms₁ ++ [m])) (hparty : m.party? = some me) (hpath : m.prekeyPath? = none)
    (hwho : who[callCount (runVis r₀ ms₁)]? = some me)
    (ht_rep : t ∈ recvRepresentations interpretation r₀ S g ms₁ body)
    (hvis : m.vis (runTraceMoves r₀ ms₁) = trEntry .recv t :: vrest)
    (hcs_rest : callStarts rest = []) (hnorecv : ∀ v ∈ vrest, v.kind ≠ .recv)
    (hfor_rest : List.Forall₂ (EventMatchesEntry interpretation r₀ S g) rest vrest) :
    MatchedPrefix interpretation r₀ S who g (ms₁ ++ [m])
      (τ ++ (.recv (wireWhisperTag :: body) :: rest)) := by
  have hrole := Stage1Wire.roleFaithful_snoc hmp.2.2.1
    (fun p hp => by rw [hparty, Option.some.injEq] at hp; subst hp; exact hwho)
  have hp1 := Stage1Wire.pathFaithful_snoc_of_prekeyPath_none hmp.2.2.2.1 hpath
  have hpf' : PathFaithful interpretation r₀ S g (ms₁ ++ [m]) (τ ++ (.recv (wireWhisperTag :: body) :: rest)) := by
    intro i m' promote b pf hi hpr hcs hp
    have hcs_app : callStarts (τ ++ (.recv (wireWhisperTag :: body) :: rest)) =
        callStarts τ ++ [.recv (wireWhisperTag :: body)] := by
      unfold callStarts at hcs_rest ⊢; rw [List.filter_append, List.filter_cons, hcs_rest]; rfl
    rw [hcs_app] at hcs
    by_cases hk : callCount (runVis r₀ ((ms₁ ++ [m]).take i)) < (callStarts τ).length
    · rw [List.getElem?_append_left hk] at hcs; exact hp1 i m' promote b pf hi hpr hcs hp
    · have hk_lt := (List.getElem?_eq_some_iff.mp hcs).1
      simp only [List.length_append, List.length_singleton] at hk_lt
      have hk_eq : callCount (runVis r₀ ((ms₁ ++ [m]).take i)) = (callStarts τ).length := by omega
      rw [hk_eq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq, MachineEvent.recv.injEq] at hcs; subst hcs; cases hp
  have hrf' : ReadFaithful interpretation r₀ S g (ms₁ ++ [m]) (τ ++ (.recv (wireWhisperTag :: body) :: rest)) := by
    intro ev hev hkind
    rw [runVis_snoc, hvis, List.zip_append hmp.2.2.2.2.2.length_eq] at hev
    rcases List.mem_append.mp hev with hold | hnew
    · have ho := hmp.2.2.2.2.1 ev hold hkind
      split at ho
      · exact Stage1Wire.recvRepresentations_mono_append ho
      · intro p hp; exact Stage1Wire.recvRepresentations_mono_append (ho p hp)
      · exact Stage1Wire.preKeyRepresentations_mono_append ho
      · exact trivial
    · rcases List.mem_cons.mp hnew with rfl | htail
      · exact Stage1Wire.recvRepresentations_mono_append ht_rep
      · exact absurd hkind (hnorecv ev.2 (List.of_mem_zip htail).2)
  have hhead : EventMatchesEntry interpretation r₀ S g (.recv (wireWhisperTag :: body)) (trEntry .recv t) :=
    ⟨rfl, t, rfl, by rw [eventBytes, ht_rep.2.1]⟩
  exact matchedPrefix_snoc hmp hrun' hrole hpf' hrf' (hvis ▸ .cons hhead hfor_rest)
theorem matchedPrefix_step_decryptSkipped {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms₁ : List Move} {τ : List MachineEvent}
    {me : Participant} {stateIdx msgIdx skIdx pqIdx rIdx srcIdx : Nat}
    {spqrMsgIdx : UInt32} {st : TRState}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {body outPt : HwBytes}
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ τ)
    (hcur : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx = true)
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms₁)).1 = some st)
    (hmsg : (runTraceMoves r₀ ms₁).getMessageSentAt msgIdx = some t)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hsk : ((runTraceMoves r₀ ms₁).at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo me) msg.ratchetKey msg.counter seed rIdx srcIdx⟩)
    (hunused : skippedKeyUsedB (runTraceMoves r₀ ms₁) skIdx = false)
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : (((runTraceMoves r₀ ms₁).append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx :
      Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm)
    (_ht_gam : gamma interpretation S g t = body) (hpt_gam : gamma interpretation S g ptTerm = outPt)
    (hwho : who[callCount (runVis r₀ ms₁)]? = some me)
    (ht_rep : t ∈ recvRepresentations interpretation r₀ S g ms₁ body)
    (hfind : (findRecvChain st.toDRState.recv msg.ratchetKey).isSome = true) :
    MatchedPrefix interpretation r₀ S who g
      (ms₁ ++ [.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx false])
      (τ ++ [.recv (wireWhisperTag :: body), .accept outPt]) :=
  matchedPrefix_step_whisper hmp
    (modelRun_snoc_decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx false hmp.2.1 hcur)
    rfl rfl hwho ht_rep (visOf_decryptSkipped hst hmsg hparse hver hsk hunused hspqr hpqSalt hmac_eq hdec hfind)
    rfl (by simp [trEntry]) (.cons ⟨rfl, by simp [trEntry, eventBytes, hpt_gam]⟩ .nil)
theorem matchedPrefix_step_decrypt_noRatchet {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms₁ : List Move} {τ : List MachineEvent}
    {me : Participant} {stateIdx msgIdx pqIdx : Nat}
    {spqrMsgIdx : UInt32} {st : TRState} {c c' : RecvChain}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {body outPt : HwBytes}
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ τ)
    (hcur : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx = true)
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms₁)).1 = some st)
    (hmsg : (runTraceMoves r₀ ms₁).getMessageSentAt msgIdx = some t)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hfind : findRecvChain st.recv msg.ratchetKey = some c)
    (hcons : consumeMessageKey c msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : (((runTraceMoves r₀ ms₁).append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx :
      Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm)
    (_ht_gam : gamma interpretation S g t = body) (hpt_gam : gamma interpretation S g ptTerm = outPt)
    (hwho : who[callCount (runVis r₀ ms₁)]? = some me)
    (ht_rep : t ∈ recvRepresentations interpretation r₀ S g ms₁ body) :
    MatchedPrefix interpretation r₀ S who g
      (ms₁ ++ [.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx false])
      (τ ++ [.recv (wireWhisperTag :: body), .accept outPt]) :=
  matchedPrefix_step_whisper hmp
    (modelRun_snoc_decrypt me stateIdx msgIdx pqIdx spqrMsgIdx false hmp.2.1 hcur)
    rfl rfl hwho ht_rep (visOf_decrypt_noRatchet hst hmsg hparse hver hfind hcons hspqr hpqSalt hmac_eq hdec)
    rfl (by simp [trEntry]) (.cons ⟨rfl, by simp [trEntry, eventBytes, hpt_gam]⟩ .nil)
theorem matchedPrefix_step_decrypt_ratchet {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms₁ : List Move} {τ : List MachineEvent}
    {me : Participant} {stateIdx msgIdx pqIdx : Nat}
    {spqrMsgIdx : UInt32} {st : TRState} {c' : RecvChain}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {body rngBytes outPt : HwBytes}
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ τ)
    (hcur : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx = true)
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms₁)).1 = some st)
    (hmsg : (runTraceMoves r₀ ms₁).getMessageSentAt msgIdx = some t)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hfind : findRecvChain st.recv msg.ratchetKey = none)
    (hlow : x25519LowOrder msg.ratchetKey = false)
    (hcons : consumeMessageKey (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms₁).length).2
      msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms₁).length).1.spqr
      msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : ((((runTraceMoves r₀ ms₁).append (⟨32⟩ : DY.Random.ExecEntryT)).append
      (⟨key⟩ : Network.ExecEntryT)).at? pqIdx : Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey
      (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms₁).length).1.peerIk
      (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms₁).length).1.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm)
    (_ht_gam : gamma interpretation S g t = body)
    (hrng_gam : gamma interpretation S g (randTerm (runTraceMoves r₀ ms₁).length 32) = rngBytes)
    (hpt_gam : gamma interpretation S g ptTerm = outPt)
    (hwho : who[callCount (runVis r₀ ms₁)]? = some me)
    (ht_rep : t ∈ recvRepresentations interpretation r₀ S g ms₁ body) :
    MatchedPrefix interpretation r₀ S who g
      (ms₁ ++ [.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx false])
      (τ ++ [.recv (wireWhisperTag :: body), .rng rngBytes, .accept outPt]) :=
  matchedPrefix_step_whisper hmp
    (modelRun_snoc_decrypt me stateIdx msgIdx pqIdx spqrMsgIdx false hmp.2.1 hcur)
    rfl rfl hwho ht_rep (visOf_decrypt_ratchet hst hmsg hparse hver hfind hlow hcons hspqr hpqSalt hmac_eq hdec)
    rfl (by simp [trEntry])
    (.cons ⟨rfl, by simp [trEntry, eventBytes, hrng_gam]⟩ (.cons ⟨rfl, by simp [trEntry, eventBytes, hpt_gam]⟩ .nil))
theorem getLocalState_append_stEntry_at_length (tr₀ : ExecTrace) (me : Participant) (st' : TRState) :
    ((PersistentLocalState.getLocalState me tr₀.length : Traceful TRState).run
      (tr₀.append (⟨⟨me, st'⟩⟩ : StEntry))).1 = some st' := by
  rw [getLocalState_fst, Trace.at?_append]; simp only [↓reduceIte]
theorem isCurrentSnapshot_append_stEntry_at_length (tr₀ : ExecTrace) (me : Participant) (st' : TRState) :
    isCurrentSnapshot (tr₀.append (⟨⟨me, st'⟩⟩ : StEntry)) tr₀.length = true := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]; rw [Trace.at?_append]; dsimp only
  have hlen : (tr₀.append (⟨⟨me, st'⟩⟩ : StEntry)).length - (tr₀.length + 1) = 0 := by
    simp only [append_length]; omega
  rw [hlen]; rfl
theorem getLocalState_append_stEntry_ne_or_old {tr tr₀ : ExecTrace}
    (hpreserved : ∀ i, (tr₀.at? i : Option StEntry) = (tr.at? i : Option StEntry))
    (me : Participant) (st' : TRState) (q : Participant) (idx : Nat) (st_q : TRState)
    (hget : ((PersistentLocalState.getLocalState q idx : Traceful TRState).run
      (tr₀.append (⟨⟨me, st'⟩⟩ : StEntry))).1 = some st_q) :
    (q = me ∧ idx = tr₀.length ∧ st_q = st') ∨
      ((PersistentLocalState.getLocalState q idx : Traceful TRState).run tr).1 = some st_q := by
  by_cases hlt : idx < tr₀.length
  · right; rw [getLocalState_fst] at hget ⊢; rw [at?_append_of_lt tr₀ _ hlt, hpreserved idx] at hget
    exact hget
  · by_cases heq : idx = tr₀.length
    · left; subst heq; rw [getLocalState_fst, Trace.at?_append] at hget
      by_cases hq : me = q
      · subst hq; simp only [↓reduceIte, Option.some.injEq] at hget; exact ⟨rfl, rfl, hget.symm⟩
      · simp only [hq, ↓reduceIte] at hget; cases hget
    · rw [getLocalState_fst,
          at?_eq_none_of_le (tr₀.append (⟨⟨me, st'⟩⟩ : StEntry)) (by simp only [append_length]; omega)] at hget
      cases hget
theorem trNsBound_of_append_stEntry {r₀ : ProtocolSetup} {ms₁ ms₂ : List Move} {sent : List HwBytes}
    {tr₀ : ExecTrace} {me : Participant} {st' : TRState}
    (htr : runTraceMoves r₀ ms₂ = tr₀.append (⟨⟨me, st'⟩⟩ : StEntry))
    (hpreserved : ∀ i, (tr₀.at? i : Option StEntry) = ((runTraceMoves r₀ ms₁).at? i : Option StEntry))
    (hns_new : st'.ns.toNat ≤ sent.length) (hns : TRNsBound r₀ ms₁ sent) :
    TRNsBound r₀ ms₂ sent := by
  intro q idx st_q hget; rw [htr] at hget
  rcases getLocalState_append_stEntry_ne_or_old hpreserved me st' q idx st_q hget with ⟨_, _, rfl⟩ | hold
  · exact hns_new
  · exact hns q idx st_q hold
end Symbolic.Swarm.CREF.TR.RecvDec
