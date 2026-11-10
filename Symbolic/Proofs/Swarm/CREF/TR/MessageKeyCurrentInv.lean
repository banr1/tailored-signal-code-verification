/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.Xpl.Faithful
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.COMPOSED.CompLineage
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Current-Snapshot Invariant for Message-Key Events

Defines `MessageKeyCurrentInv` (every `TREvent.MessageKey` logged at index `j` with
`parent ≠ j + 1` reads a snapshot `parent` that remained current up to `j`), proves reachability
preservation (`messageKeyCurrentInv_reachable`), and derives `isCurrentSnapshot_of_decrypt_accept`,
`isCurrentSnapshot_of_decryptSkipped_accept`, and `rcvCurrentSnapshot_of_xplBlock`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR

cref_open

open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir RecvChain KeyComponent kdfCk findRecvChain
  setRecvChain consumeMessageKey)
open DY.Libsignal.PQXDH (BundleHandles BobKeyHandles PreKeyMsgHandles guardTrace)
open DY.Libsignal.TripleRatchet (TRState TREvent receiveSignalMsg ensureReceiverChain dhRatchetStep
  verifyMacAndDecrypt logSkippedKeys logMessageKeyAndStore isCurrentSnapshot messageEncrypt
  messageEncryptAbort messageDecrypt messageDecryptSkipped exposeKey exposeSpqr exposeSkipped
  traceLength guardTrace)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Swarm.COMPOSED.CompRatchet (InertOnPQXDH)

/-! ## `IsCurrentSnapshotBefore` and `MessageKeyCurrentInv` -/

/-- Snapshot `parent` is stored on `tr` before `j` and no index `k` with `parent < k < j` stores a
`TRState` with the same `(participant, initiator)`. -/
def IsCurrentSnapshotBefore (tr : ExecTrace) (parent j : Nat) : Prop :=
  ∃ e : TRStEntry,
    (tr.at? parent : Option TRStEntry) = some e ∧
    parent < j ∧
    ∀ k (e' : TRStEntry), parent < k → k < j →
      (tr.at? k : Option TRStEntry) = some e' →
      (e'.st.participant != e.st.participant ||
        e'.st.state.initiator != e.st.state.initiator) = true

/-- Every `TREvent.MessageKey` logged at index `j` with `parent ≠ j + 1`
reads a snapshot `parent` that was current up to `j`. -/
def MessageKeyCurrentInv (tr : ExecTrace) : Prop :=
  ∀ s dir seed salt n rIdx parent j,
    tr.EventLoggedAt (TREvent.MessageKey s dir seed salt n rIdx parent) j →
    parent ≠ j + 1 →
    IsCurrentSnapshotBefore tr parent j

private theorem mkInv_append_length {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem at?_eq_of_le_of_lt {E : Type} [ExecTraceTypes.Has E]
    {tr tr' : ExecTrace} (hle : tr ≤ tr') {i : Nat} (hi : i < tr.length) :
    (tr'.at? i : Option E) = (tr.at? i : Option E) := by
  have hi' : i < tr'.length := Nat.lt_of_lt_of_le hi (Trace.length_le _ _ hle)
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr tr' i hi hle]

private theorem at?_eq_none_of_le_local {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) {i : Nat} (hi : tr.length ≤ i) : (tr.at? i : Option E) = none := by
  have h : ¬ i < tr.length := by omega
  simp only [Trace.at?, h, ↓reduceDIte]

private theorem at?_append_non_entry_local {E1 E2 : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = none)
    (i : Nat) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  by_cases hlt : i < tr.length
  · exact at?_append_of_lt tr e hlt
  · by_cases heq : i = tr.length
    · subst heq
      have h1 : tr.length < (tr.append e).length := by
        rw [mkInv_append_length]; exact Nat.lt_succ_self _
      have h2 : ¬ tr.length < tr.length := Nat.lt_irrefl _
      simp only [Trace.at?, h1, h2, ↓reduceDIte]
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte, hnone]
    · rw [at?_eq_none_of_le_local (tr.append e) (by rw [mkInv_append_length]; omega),
          at?_eq_none_of_le_local tr (by omega)]

private theorem isCurrentSnapshot_append_non_st_local {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none)
    (stateIdx : Nat) :
    isCurrentSnapshot (tr.append e) stateIdx = isCurrentSnapshot tr stateIdx := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
  rw [at?_append_non_entry_local tr e hnone]
  rcases h : (tr.at? stateIdx : Option TRStEntry) with _ | s
  · rfl
  · dsimp only
    have hlt : stateIdx < tr.length := by
      have := Trace.at?_eq_some_implies_length_le (EntryT := TRStEntry) tr stateIdx
      rw [h] at this; exact this
    have hlen : (tr.append e).length - (stateIdx + 1) = (tr.length - (stateIdx + 1)) + 1 := by
      rw [mkInv_append_length]; omega
    have hsum : (stateIdx + 1) + 1 * (tr.length - (stateIdx + 1)) = tr.length := by omega
    have hlast : (tr.at? tr.length : Option TRStEntry) = none :=
      at?_eq_none_of_le_local tr (Nat.le_refl _)
    rw [hlen, List.range'_concat, hsum]
    simp only [List.all_append, List.all_cons, List.all_nil,
      at?_append_non_entry_local tr e hnone, hlast, Bool.and_true]

theorem IsCurrentSnapshotBefore.mono {tr tr' : ExecTrace} (hle : tr ≤ tr')
    {parent j : Nat} (hj : j ≤ tr.length) (h : IsCurrentSnapshotBefore tr parent j) :
    IsCurrentSnapshotBefore tr' parent j := by
  obtain ⟨e, he, hplt, hno⟩ := h
  refine ⟨e, at?_le_some hle he, hplt, fun k e' hpk hkj hk' => ?_⟩
  rw [at?_eq_of_le_of_lt hle (by omega)] at hk'
  exact hno k e' hpk hkj hk'

theorem isCurrentSnapshotBefore_of_isCurrentSnapshot {tr : ExecTrace} {parent : Nat}
    (hc : isCurrentSnapshot tr parent = true) :
    IsCurrentSnapshotBefore tr parent tr.length := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hc
  rcases he : (tr.at? parent : Option TRStEntry) with _ | e
  · rw [he] at hc; cases hc
  · rw [he] at hc
    have hplt : parent < tr.length := by
      have := Trace.at?_eq_some_implies_length_le (EntryT := TRStEntry) tr parent
      rw [he] at this; exact this
    refine ⟨e, he, hplt, fun k e' hpk hkj hk => ?_⟩
    have hmem : k ∈ List.range' (parent + 1) (tr.length - (parent + 1)) :=
      List.mem_range'_1.mpr ⟨by omega, by omega⟩
    have hall := List.all_eq_true.mp hc k hmem
    rw [hk] at hall
    exact hall

theorem isCurrentSnapshot_of_isCurrentSnapshotBefore {tr₀ tr : ExecTrace}
    (hle : tr₀ ≤ tr) {parent j : Nat} (hj : tr₀.length ≤ j) (hplt : parent < tr₀.length)
    (h : IsCurrentSnapshotBefore tr parent j) :
    isCurrentSnapshot tr₀ parent = true := by
  obtain ⟨e, he, _, hno⟩ := h
  have he₀ : (tr₀.at? parent : Option TRStEntry) = some e := by
    rw [← at?_eq_of_le_of_lt hle hplt]; exact he
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
  rw [he₀]; dsimp only
  rw [List.all_eq_true]
  intro k hk
  obtain ⟨hk1, hk2⟩ := List.mem_range'_1.mp hk
  rcases hk_at : (tr₀.at? k : Option TRStEntry) with _ | e'
  · rfl
  · exact hno k e' (by omega) (by omega) (at?_le_some hle hk_at)

/-! ## Step Preservation Helpers for `MessageKeyCurrentInv` -/

private theorem messageKeyCurrentInv_nil : MessageKeyCurrentInv Trace.nil := by
  intro _ _ _ _ _ _ _ _ h _
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, Trace.at?,
    Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at h

private theorem messageKeyCurrentInv_append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {x : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) : Option TREntry) = none)
    (h : MessageKeyCurrentInv tr) : MessageKeyCurrentInv (tr.append x) := by
  intro s dir seed salt n rIdx parent j hlog hne
  have hlog0 := eventLoggedAt_append_other hnone hlog
  have hj : j ≤ tr.length := Nat.le_of_lt (Trace.EventLoggedAt_implies_i_le_length _ j tr hlog0)
  exact (h s dir seed salt n rIdx parent j hlog0 hne).mono (Trace.append_le tr x) hj

private theorem messageKeyCurrentInv_append_tr_nonMK {tr : ExecTrace} {ev : TREvent}
    (hev : ∀ s dir seed salt n rIdx parent,
      ev ≠ TREvent.MessageKey s dir seed salt n rIdx parent)
    (h : MessageKeyCurrentInv tr) : MessageKeyCurrentInv (tr.append (TREvE ev)) := by
  intro s dir seed salt n rIdx parent j hlog hne
  rcases eventLoggedAt_append_same hlog with ⟨hj, hlog0⟩ | ⟨_, heq⟩
  · exact (h s dir seed salt n rIdx parent j hlog0 hne).mono
      (Trace.append_le tr _) (Nat.le_of_lt hj)
  · exact absurd heq (hev s dir seed salt n rIdx parent)

private theorem messageKeyCurrentInv_append_mk_eq {tr : ExecTrace}
    {s : SessionInfo} {dir : KeyDir} {seed salt : Bytes} {n : UInt32}
    {rIdx : Nat} (h : MessageKeyCurrentInv tr) :
    MessageKeyCurrentInv
      (tr.append (TREvE (TREvent.MessageKey s dir seed salt n rIdx (tr.length + 1)))) := by
  intro s' dir' seed' salt' n' rIdx' parent' j hlog hne
  rcases eventLoggedAt_append_same hlog with ⟨hj, hlog0⟩ | ⟨rfl, heq⟩
  · exact (h s' dir' seed' salt' n' rIdx' parent' j hlog0 hne).mono
      (Trace.append_le tr _) (Nat.le_of_lt hj)
  · cases heq; exact absurd rfl hne

private theorem messageKeyCurrentInv_append_mk_current {tr : ExecTrace}
    {s : SessionInfo} {dir : KeyDir} {seed salt : Bytes} {n : UInt32}
    {rIdx parent : Nat}
    (hc : isCurrentSnapshot tr parent = true) (h : MessageKeyCurrentInv tr) :
    MessageKeyCurrentInv
      (tr.append (TREvE (TREvent.MessageKey s dir seed salt n rIdx parent))) := by
  intro s' dir' seed' salt' n' rIdx' parent' j hlog hne
  rcases eventLoggedAt_append_same hlog with ⟨hj, hlog0⟩ | ⟨rfl, heq⟩
  · exact (h s' dir' seed' salt' n' rIdx' parent' j hlog0 hne).mono
      (Trace.append_le tr _) (Nat.le_of_lt hj)
  · cases heq
    exact (isCurrentSnapshotBefore_of_isCurrentSnapshot hc).mono
      (Trace.append_le tr _) (Nat.le_refl tr.length)

private theorem messageKeyCurrentInv_inertOnPQXDH : InertOnPQXDH MessageKeyCurrentInv where
  append_net _ _ h := messageKeyCurrentInv_append_other rfl h
  append_rnd _ _ h := messageKeyCurrentInv_append_other rfl h
  append_pqxSt _ _ _ h := messageKeyCurrentInv_append_other rfl h
  append_pqxEv_nonDone _ _ _ h := messageKeyCurrentInv_append_other rfl h

private def InvAndCurrent (stateIdx : Nat) (tr : ExecTrace) : Prop :=
  MessageKeyCurrentInv tr ∧ isCurrentSnapshot tr stateIdx = true

private theorem invAndCurrent_append_other {E : Type} [ExecTraceTypes.Has E]
    {stateIdx : Nat} {tr : ExecTrace} {x : E}
    (hnone_tr : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) : Option TREntry) = none)
    (hnone_st : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) : Option TRStEntry) = none)
    (h : InvAndCurrent stateIdx tr) : InvAndCurrent stateIdx (tr.append x) :=
  ⟨messageKeyCurrentInv_append_other hnone_tr h.1,
   by rw [isCurrentSnapshot_append_non_st_local tr x hnone_st]; exact h.2⟩

private theorem invAndCurrent_append_tr_nonMK {stateIdx : Nat} {tr : ExecTrace} {ev : TREvent}
    (hev : ∀ s dir seed salt n rIdx parent,
      ev ≠ TREvent.MessageKey s dir seed salt n rIdx parent)
    (h : InvAndCurrent stateIdx tr) : InvAndCurrent stateIdx (tr.append (TREvE ev)) :=
  ⟨messageKeyCurrentInv_append_tr_nonMK hev h.1,
   by rw [isCurrentSnapshot_append_non_st_local tr (TREvE ev) rfl]; exact h.2⟩

private theorem mkInv_sendMessage_snd (msg : Bytes) (tr : ExecTrace) :
    ((Network.sendMessage msg).run tr).2.val = tr.append (NetE msg) := by
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]

private theorem mkInv_genRand_snd (k : Nat) (tr : ExecTrace) :
    ((Random.genRand k).run tr).2.val = tr.append (RndE k) := by
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]

private theorem mkInv_logEvent_run {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    (ev : E) (tr : ExecTrace) :
    ((ProtocolEvent.logEvent ev).run tr).1 = some () ∧
      ((ProtocolEvent.logEvent ev).run tr).2.val =
        tr.append ({ ev := ev } : ProtocolEvent.ExecEntryT E) := by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure,
    and_self]

private theorem mkInv_storeLocalState_tr_snd (p : Participant) (st : TRState) (tr : ExecTrace) :
    ((PersistentLocalState.storeLocalState p st).run tr).2.val = tr.append (TRStE p st) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]

private theorem mkInv_logMessageKeyAndStore_snd
    (me : Participant) (s : SessionInfo) (dir : KeyDir) (seed pqSalt : Bytes)
    (n : UInt32) (rIdx parent : Nat) (st : TRState) (tr : ExecTrace) :
    ((logMessageKeyAndStore me s dir seed pqSalt n rIdx parent st).run tr).2.val =
      (tr.append (TREvE (TREvent.MessageKey s dir seed pqSalt n rIdx parent))).append
        (TRStE me st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  rw [run_bind_snd, (mkInv_logEvent_run _ _).1, (mkInv_logEvent_run _ _).2]; dsimp only
  exact mkInv_storeLocalState_tr_snd me st _

private theorem mkInv_preserves_sendMessage (msg : Bytes) :
    Preserves MessageKeyCurrentInv (Network.sendMessage msg) := by
  intro tr h; rw [mkInv_sendMessage_snd]; exact messageKeyCurrentInv_append_other rfl h

private theorem mkInv_preserves_genRand (k : Nat) :
    Preserves MessageKeyCurrentInv (Random.genRand k) := by
  intro tr h; rw [mkInv_genRand_snd]; exact messageKeyCurrentInv_append_other rfl h

private theorem mkInv_preserves_logEvent_other {E : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)] (ev : E)
    (hnone : (TraceEntryHas.proj
      (TraceEntryHas.inj ({ ev := ev } : ProtocolEvent.ExecEntryT E) : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT TREvent)) = none) :
    Preserves MessageKeyCurrentInv (ProtocolEvent.logEvent ev) := by
  intro tr h; rw [(mkInv_logEvent_run ev tr).2]
  exact messageKeyCurrentInv_append_other hnone h

private theorem mkInv_preserves_logEvent_tr (ev : TREvent)
    (hev : ∀ s dir seed salt n rIdx parent,
      ev ≠ TREvent.MessageKey s dir seed salt n rIdx parent) :
    Preserves MessageKeyCurrentInv (ProtocolEvent.logEvent ev) := by
  intro tr h; rw [(mkInv_logEvent_run ev tr).2]
  exact messageKeyCurrentInv_append_tr_nonMK hev h

private theorem mkInv_preserves_store_tr (p : Participant) (st : TRState) :
    Preserves MessageKeyCurrentInv (PersistentLocalState.storeLocalState p st) := by
  intro tr h; rw [mkInv_storeLocalState_tr_snd]; exact messageKeyCurrentInv_append_other rfl h

private theorem invCur_preserves_sendMessage (stateIdx : Nat) (msg : Bytes) :
    Preserves (InvAndCurrent stateIdx) (Network.sendMessage msg) := by
  intro tr h; rw [mkInv_sendMessage_snd]; exact invAndCurrent_append_other rfl rfl h

private theorem invCur_preserves_genRand (stateIdx : Nat) (k : Nat) :
    Preserves (InvAndCurrent stateIdx) (Random.genRand k) := by
  intro tr h; rw [mkInv_genRand_snd]; exact invAndCurrent_append_other rfl rfl h

private theorem invCur_preserves_logEvent_tr (stateIdx : Nat) (ev : TREvent)
    (hev : ∀ s dir seed salt n rIdx parent,
      ev ≠ TREvent.MessageKey s dir seed salt n rIdx parent) :
    Preserves (InvAndCurrent stateIdx) (ProtocolEvent.logEvent ev) := by
  intro tr h; rw [(mkInv_logEvent_run ev tr).2]
  exact invAndCurrent_append_tr_nonMK hev h

private theorem preserves_invAndCurrent_logSkippedKeys (stateIdx : Nat)
    (s : SessionInfo) (pk : Bytes) (rIdx src : Nat) :
    ∀ (ck : Bytes) (n : UInt32) (k : Nat),
      Preserves (InvAndCurrent stateIdx) (logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0 => Preserves.pure _
  | ck, n, k + 1 =>
    Preserves.bind (invCur_preserves_logEvent_tr stateIdx _ (by rintro _ _ _ _ _ _ _ ⟨⟩))
      fun _ => preserves_invAndCurrent_logSkippedKeys stateIdx s pk rIdx src (kdfCk ck).1 (n + 1) k

private theorem preserves_mkInv_logSkippedKeys (s : SessionInfo) (pk : Bytes) (rIdx src : Nat) :
    ∀ (ck : Bytes) (n : UInt32) (k : Nat),
      Preserves MessageKeyCurrentInv (logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0 => Preserves.pure _
  | ck, n, k + 1 =>
    Preserves.bind (mkInv_preserves_logEvent_tr _ (by rintro _ _ _ _ _ _ _ ⟨⟩))
      fun _ => preserves_mkInv_logSkippedKeys s pk rIdx src (kdfCk ck).1 (n + 1) k

private theorem logSkippedKeys_run_total (s : SessionInfo) (pk : Bytes) (rIdx src : Nat) :
    ∀ (ck : Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace),
      ((logSkippedKeys s pk rIdx src ck n k).run tr).1 = some () ∧
      ((logSkippedKeys s pk rIdx src ck n k).run tr).2.val.length = tr.length + k
  | _, _, 0, tr => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [Traceful.run_pure]
    exact ⟨rfl, (Nat.add_zero _).symm⟩
  | ck, n, k + 1, tr => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [run_bind_fst, run_bind_snd, (mkInv_logEvent_run _ tr).1, (mkInv_logEvent_run _ tr).2]
    dsimp only
    obtain ⟨h1, h2⟩ := logSkippedKeys_run_total s pk rIdx src (kdfCk ck).1 (n + 1) k
      (tr.append (TREvE (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx src)))
    refine ⟨h1, ?_⟩
    rw [h2, mkInv_append_length]
    omega

private theorem preserves_invAndCurrent_ensureReceiverChain (stateIdx : Nat)
    (st : TRState) (pk : Bytes) :
    Preserves (InvAndCurrent stateIdx) (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  split
  · exact Preserves.pure _
  · exact Preserves.bind
      (Preserves.bind (Preserves.guardP _) fun _ =>
        Preserves.bind (invCur_preserves_genRand stateIdx 32) fun _ => Preserves.pure _)
      fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_mkInv_ensureReceiverChain (st : TRState) (pk : Bytes) :
    Preserves MessageKeyCurrentInv (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  split
  · exact Preserves.pure _
  · exact Preserves.bind
      (Preserves.bind (Preserves.guardP _) fun _ =>
        Preserves.bind (mkInv_preserves_genRand 32) fun _ => Preserves.pure _)
      fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_of_invAndCurrent {stateIdx : Nat} {α β : Type}
    {x : Traceful α} {f : α → Traceful β}
    (hx : Preserves (InvAndCurrent stateIdx) x)
    (hf : ∀ a tr, InvAndCurrent stateIdx tr → MessageKeyCurrentInv ((f a).run tr).2.val)
    (tr : ExecTrace) (h : InvAndCurrent stateIdx tr) :
    MessageKeyCurrentInv (((x >>= f).run tr).2.val) := by
  rw [run_bind_snd]
  have h1 : InvAndCurrent stateIdx (x.run tr).2.val := hx tr h
  cases (x.run tr).1 with
  | none => exact h1.1
  | some a => exact hf a _ h1

private theorem mkInv_logMessageKeyAndStore_of_invAndCurrent
    (me : Participant) (s : SessionInfo) (dir : KeyDir) (mk pqSalt : Bytes)
    (n : UInt32) (rIdx stateIdx : Nat) (st : TRState)
    (tr : ExecTrace) (h : InvAndCurrent stateIdx tr) :
    MessageKeyCurrentInv
      ((logMessageKeyAndStore me s dir mk pqSalt n rIdx stateIdx st).run tr).2.val := by
  rw [mkInv_logMessageKeyAndStore_snd]
  exact messageKeyCurrentInv_append_other rfl (messageKeyCurrentInv_append_mk_current h.2 h.1)

/-! ## Transition Preservation Proofs for `MessageKeyCurrentInv` -/

private theorem mkInv_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) :
    Preserves MessageKeyCurrentInv (aliceStart a b idStateIdx regIdxB bh) := by
  intro tr₀ hInv₀; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine bind_aliceHandshake_at a b idStateIdx regIdxB bh tr₀ hInv₀
    (messageKeyCurrentInv_append_other rfl hInv₀)
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  have hInv₂ : MessageKeyCurrentInv ((tr₀.append (RndE 32)).append (RndE 32)) :=
    messageKeyCurrentInv_append_other rfl (messageKeyCurrentInv_append_other rfl hInv₀)
  refine (Preserves.bind (mkInv_preserves_genRand 32) fun dhsA => ?_) _ hInv₂
  dsimp only
  refine Preserves.bind (mkInv_preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind (mkInv_preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind Preserves.traceLength fun doneIdx => ?_
  refine Preserves.bind (mkInv_preserves_logEvent_other _ rfl) fun _ => ?_
  refine Preserves.bind (mkInv_preserves_logEvent_tr _ (by rintro _ _ _ _ _ _ _ ⟨⟩)) fun _ => ?_
  refine Preserves.bind (mkInv_preserves_logEvent_other _ rfl) fun _ => ?_
  exact mkInv_preserves_store_tr a _

private theorem mkInv_bobStart_tail (b : Participant) (st : TRState) (c : RecvChain)
    (pk seed pqSalt m : Bytes) (n : UInt32) (st' : TRState)
    (t0 : ExecTrace) (hInv0 : MessageKeyCurrentInv t0) :
    MessageKeyCurrentInv ((do
      let skipped := n.toNat - c.index.toNat
      let childIdx := (← traceLength) + skipped + 2
      logSkippedKeys (st.sessionInfo b) pk c.rIdx childIdx c.chainKey c.index skipped
      ProtocolEvent.logEvent (TREvent.Received b st.peer pk n m)
      logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt n c.rIdx childIdx
        st').run t0).2.val := by
  let skipped := n.toNat - c.index.toNat
  let childIdx := t0.length + skipped + 2
  obtain ⟨hsk1, hsk2⟩ :=
    logSkippedKeys_run_total (st.sessionInfo b) pk c.rIdx childIdx c.chainKey c.index skipped t0
  have hInvSk : MessageKeyCurrentInv
      ((logSkippedKeys (st.sessionInfo b) pk c.rIdx childIdx c.chainKey c.index skipped).run t0).2.val :=
    preserves_mkInv_logSkippedKeys (st.sessionInfo b) pk c.rIdx childIdx c.chainKey c.index skipped t0 hInv0
  unfold DY.Libsignal.TripleRatchet.traceLength
  dsimp only
  rw [run_bind_snd, Traceful.run_mk]; dsimp only
  rw [run_bind_snd, hsk1]; dsimp only
  let t1 := ((logSkippedKeys (st.sessionInfo b) pk c.rIdx childIdx c.chainKey c.index skipped).run t0).2.val
  have ht1 : t1.length = t0.length + skipped := hsk2
  let t2 := t1.append (TREvE (TREvent.Received b st.peer pk n m))
  have hInv2 : MessageKeyCurrentInv t2 :=
    messageKeyCurrentInv_append_tr_nonMK (by rintro _ _ _ _ _ _ _ ⟨⟩) hInvSk
  have hlen : t2.length + 1 = t0.length + (n.toNat - c.index.toNat) + 2 := by
    dsimp only [t2]
    rw [mkInv_append_length, ht1]
  rw [run_bind_snd, (mkInv_logEvent_run _ t1).1, (mkInv_logEvent_run _ t1).2]; dsimp only
  rw [mkInv_logMessageKeyAndStore_snd, ← hlen]
  exact messageKeyCurrentInv_append_other rfl (messageKeyCurrentInv_append_mk_eq hInv2)

private theorem mkInv_bobStart (b a : Participant) (kh : BobKeyHandles)
    (regIdxA : Nat) (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves MessageKeyCurrentInv (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  intro tr₀ hInv₀
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr₀ hInv₀
    fun _ _ _ opkB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  refine (Preserves.bind (Preserves.receiveSignalMsg _) fun msg => ?_) tr₀ hInv₀
  refine Preserves.bind (preserves_mkInv_ensureReceiverChain _ _) fun ⟨st, c, ratcheted⟩ => ?_
  dsimp only
  rcases consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · exact Preserves.failure
  · dsimp only
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · exact Preserves.failure
    · dsimp only
      refine Preserves.bind (mkInv_preserves_sendMessage key) fun _ => ?_
      refine Preserves.bind (Preserves.receiveMessage pqIdx) fun pqSalt => ?_
      refine Preserves.bind (Preserves.verifyMacAndDecrypt _ _ _ _) fun m => ?_
      cases o : Option.map dhPk opkB with
      | none =>
        refine Preserves.bind Preserves.traceLength fun doneIdx => ?_
        refine Preserves.bind (mkInv_preserves_logEvent_other _ rfl) fun _ => ?_
        cases ratcheted
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine Preserves.bind (mkInv_preserves_logEvent_other _ rfl) fun _ => ?_
          exact mkInv_bobStart_tail b st c msg.ratchetKey seed pqSalt m msg.counter
            { st with recv := setRecvChain st.recv c', spqr := spqr' }
        · simp only [↓reduceIte]
          refine Preserves.bind
            (mkInv_preserves_logEvent_tr _ (by rintro _ _ _ _ _ _ _ ⟨⟩))
            fun _ => ?_
          refine Preserves.bind
            (mkInv_preserves_logEvent_tr _ (by rintro _ _ _ _ _ _ _ ⟨⟩))
            fun _ => ?_
          refine Preserves.bind (mkInv_preserves_logEvent_other _ rfl) fun _ => ?_
          exact mkInv_bobStart_tail b st c msg.ratchetKey seed pqSalt m msg.counter
            { st with recv := setRecvChain st.recv c', spqr := spqr' }
      | some opk =>
        dsimp only
        refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
        refine Preserves.bind (mkInv_preserves_logEvent_other _ rfl) fun _ => ?_
        refine Preserves.bind Preserves.traceLength fun doneIdx => ?_
        refine Preserves.bind (mkInv_preserves_logEvent_other _ rfl) fun _ => ?_
        cases ratcheted
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine Preserves.bind (mkInv_preserves_logEvent_other _ rfl) fun _ => ?_
          exact mkInv_bobStart_tail b st c msg.ratchetKey seed pqSalt m msg.counter
            { st with recv := setRecvChain st.recv c', spqr := spqr' }
        · simp only [↓reduceIte]
          refine Preserves.bind
            (mkInv_preserves_logEvent_tr _ (by rintro _ _ _ _ _ _ _ ⟨⟩))
            fun _ => ?_
          refine Preserves.bind
            (mkInv_preserves_logEvent_tr _ (by rintro _ _ _ _ _ _ _ ⟨⟩))
            fun _ => ?_
          refine Preserves.bind (mkInv_preserves_logEvent_other _ rfl) fun _ => ?_
          exact mkInv_bobStart_tail b st c msg.ratchetKey seed pqSalt m msg.counter
            { st with recv := setRecvChain st.recv c', spqr := spqr' }

private theorem mkInv_messageEncrypt (me : Participant) (stH coinsLen pqIdx : Nat)
    (tr : ExecTrace) (hPre : isCurrentSnapshot tr stH = true) (hInv : MessageKeyCurrentInv tr) :
    MessageKeyCurrentInv ((messageEncrypt me stH coinsLen pqIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine preserves_of_invAndCurrent (Preserves.getLocalState_tr me stH) (fun st => ?_) tr ⟨hInv, hPre⟩
  refine preserves_of_invAndCurrent (Preserves.guardP _) (fun _ => ?_)
  refine preserves_of_invAndCurrent (invCur_preserves_genRand stH 32) (fun m => ?_)
  refine preserves_of_invAndCurrent (invCur_preserves_genRand stH coinsLen) (fun coins => ?_)
  dsimp only
  rcases Spqr.spqrSend st.spqr coins with ⟨spqr', key, pqMsg⟩
  dsimp only
  refine preserves_of_invAndCurrent (invCur_preserves_sendMessage stH key) (fun _ => ?_)
  rcases kdfCk st.cks with ⟨ck', seed⟩
  dsimp only
  refine preserves_of_invAndCurrent (Preserves.receiveMessage pqIdx) (fun pqSalt => ?_)
  refine preserves_of_invAndCurrent
    (invCur_preserves_logEvent_tr stH _ (by rintro _ _ _ _ _ _ _ ⟨⟩)) (fun _ => ?_)
  intro tr' h'
  rw [run_bind_snd]
  have h1 : MessageKeyCurrentInv ((logMessageKeyAndStore me (st.sessionInfo me) .sender seed pqSalt st.ns st.rIdx stH
      { st with cks := ck', ns := st.ns + 1, spqr := spqr' }).run tr').2.val :=
    mkInv_logMessageKeyAndStore_of_invAndCurrent me (st.sessionInfo me) .sender
      seed pqSalt st.ns st.rIdx stH
      { st with cks := ck', ns := st.ns + 1, spqr := spqr' } tr' h'
  cases ((logMessageKeyAndStore me (st.sessionInfo me) .sender seed pqSalt
      st.ns st.rIdx stH { st with cks := ck', ns := st.ns + 1, spqr := spqr' }).run tr').1 with
  | none => exact h1
  | some _ => exact mkInv_preserves_sendMessage _ _ h1

private theorem mkInv_messageEncryptAbort (me : Participant) (stH : Nat) :
    Preserves MessageKeyCurrentInv (messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  exact Preserves.bind (Preserves.getLocalState_tr me stH) fun _ =>
    Preserves.bind (mkInv_preserves_genRand 32) fun _ => Preserves.failure

private theorem mkInv_messageDecrypt (me : Participant) (stH msgH pqIdx : Nat)
    (spqrMsgIdx : UInt32) (tr : ExecTrace) (hPre : isCurrentSnapshot tr stH = true)
    (hInv : MessageKeyCurrentInv tr) :
    MessageKeyCurrentInv ((messageDecrypt me stH msgH pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine preserves_of_invAndCurrent (Preserves.getLocalState_tr me stH) (fun st₀ => ?_) tr ⟨hInv, hPre⟩
  refine preserves_of_invAndCurrent (Preserves.receiveSignalMsg msgH) (fun msg => ?_)
  refine preserves_of_invAndCurrent (preserves_invAndCurrent_ensureReceiverChain stH st₀ msg.ratchetKey)
    (fun ⟨st, c, ratcheted⟩ => ?_)
  dsimp only
  rcases consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · dsimp only; intro tr' h'; rw [Traceful.run_failure]; exact h'.1
  · dsimp only
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · dsimp only; intro tr' h'; rw [Traceful.run_failure]; exact h'.1
    · dsimp only
      refine preserves_of_invAndCurrent
        (invCur_preserves_sendMessage stH key) (fun _ => ?_)
      refine preserves_of_invAndCurrent (Preserves.receiveMessage pqIdx) (fun pqSalt => ?_)
      refine preserves_of_invAndCurrent (Preserves.verifyMacAndDecrypt _ _ _ _) (fun m => ?_)
      cases ratcheted
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine preserves_of_invAndCurrent
          (preserves_invAndCurrent_logSkippedKeys stH (st.sessionInfo me) msg.ratchetKey c.rIdx stH
            c.chainKey c.index (msg.counter.toNat - c.index.toNat)) (fun _ => ?_)
        refine preserves_of_invAndCurrent
          (invCur_preserves_logEvent_tr stH _ (by rintro _ _ _ _ _ _ _ ⟨⟩)) (fun _ => ?_)
        exact mkInv_logMessageKeyAndStore_of_invAndCurrent me (st.sessionInfo me) .receiver
          seed pqSalt msg.counter c.rIdx stH { st with recv := setRecvChain st.recv c', spqr := spqr' }
      · simp only [↓reduceIte]
        refine preserves_of_invAndCurrent
          (invCur_preserves_logEvent_tr stH _ (by rintro _ _ _ _ _ _ _ ⟨⟩)) (fun _ => ?_)
        refine preserves_of_invAndCurrent
          (invCur_preserves_logEvent_tr stH _ (by rintro _ _ _ _ _ _ _ ⟨⟩)) (fun _ => ?_)
        refine preserves_of_invAndCurrent
          (preserves_invAndCurrent_logSkippedKeys stH (st.sessionInfo me) msg.ratchetKey c.rIdx stH
            c.chainKey c.index (msg.counter.toNat - c.index.toNat)) (fun _ => ?_)
        refine preserves_of_invAndCurrent
          (invCur_preserves_logEvent_tr stH _ (by rintro _ _ _ _ _ _ _ ⟨⟩)) (fun _ => ?_)
        exact mkInv_logMessageKeyAndStore_of_invAndCurrent me (st.sessionInfo me) .receiver
          seed pqSalt msg.counter c.rIdx stH { st with recv := setRecvChain st.recv c', spqr := spqr' }

private theorem mkInv_messageDecryptSkipped (me : Participant)
    (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace)
    (hPre : isCurrentSnapshot tr stH = true) (hInv : MessageKeyCurrentInv tr) :
    MessageKeyCurrentInv
      ((messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine preserves_of_invAndCurrent (Preserves.getLocalState_tr me stH) (fun st => ?_) tr ⟨hInv, hPre⟩
  refine preserves_of_invAndCurrent (Preserves.receiveSignalMsg msgH) (fun msg => ?_)
  refine preserves_of_invAndCurrent (Preserves.getEntry (E := TREntry) evH) (fun ⟨ev⟩ => ?_)
  cases ev with
  | SkippedKeyStored s pk n seed rIdx _sourceStateIdx =>
    dsimp only
    refine preserves_of_invAndCurrent (Preserves.guardP _) (fun _ => ?_)
    refine preserves_of_invAndCurrent (Preserves.guardTrace _) (fun _ => ?_)
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · dsimp only; intro tr' h'; rw [Traceful.run_failure]; exact h'.1
    · dsimp only
      refine preserves_of_invAndCurrent
        (invCur_preserves_sendMessage stH key) (fun _ => ?_)
      refine preserves_of_invAndCurrent (Preserves.receiveMessage pqIdx) (fun pqSalt => ?_)
      refine preserves_of_invAndCurrent (Preserves.verifyMacAndDecrypt _ _ _ _) (fun m => ?_)
      refine preserves_of_invAndCurrent
        (invCur_preserves_logEvent_tr stH _ (by rintro _ _ _ _ _ _ _ ⟨⟩)) (fun _ => ?_)
      refine preserves_of_invAndCurrent
        (invCur_preserves_logEvent_tr stH _ (by rintro _ _ _ _ _ _ _ ⟨⟩)) (fun _ => ?_)
      exact mkInv_logMessageKeyAndStore_of_invAndCurrent me s .receiver seed pqSalt n rIdx
        stH { st with spqr := spqr' }
  | _ => dsimp only; intro tr' h'; rw [Traceful.run_failure]; exact h'.1

private theorem mkInv_exposeKey (me : Participant) (stH : Nat) (k : KeyComponent) :
    Preserves MessageKeyCurrentInv (exposeKey me stH k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine Preserves.bind (Preserves.getLocalState_tr me stH) fun st => ?_
  cases k with
  | rk | dhs | cks =>
    exact Preserves.bind
      (mkInv_preserves_logEvent_tr _ (by rintro _ _ _ _ _ _ _ ⟨⟩))
      fun _ => mkInv_preserves_sendMessage _
  | ckr pk =>
    dsimp only
    rcases findRecvChain st.recv pk with _ | c
    · exact Preserves.failure
    · exact Preserves.bind
        (mkInv_preserves_logEvent_tr _ (by rintro _ _ _ _ _ _ _ ⟨⟩))
        fun _ => mkInv_preserves_sendMessage _

private theorem mkInv_exposeSpqr (me : Participant) (stH : Nat) :
    Preserves MessageKeyCurrentInv (exposeSpqr me stH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  exact Preserves.bind (Preserves.getLocalState_tr me stH) fun _ =>
    Preserves.bind
      (mkInv_preserves_logEvent_tr _ (by rintro _ _ _ _ _ _ _ ⟨⟩))
      fun _ => mkInv_preserves_sendMessage _

private theorem mkInv_exposeSkipped (evH : Nat) :
    Preserves MessageKeyCurrentInv (exposeSkipped evH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine Preserves.bind (Preserves.getEntry (E := TREntry) evH) fun ⟨ev⟩ => ?_
  cases ev with
  | SkippedKeyStored _ _ _ _ _ _ =>
    exact Preserves.bind (Preserves.guardTrace _) fun _ =>
      Preserves.bind
        (mkInv_preserves_logEvent_tr _ (by rintro _ _ _ _ _ _ _ ⟨⟩))
        fun _ => mkInv_preserves_sendMessage _
  | _ => exact Preserves.failure

/-- Every reachable trace satisfies `MessageKeyCurrentInv`. -/
theorem messageKeyCurrentInv_reachable {tr : ExecTrace}
    (hReach : tr.Reachable reachability) : MessageKeyCurrentInv tr := by
  have hI := messageKeyCurrentInv_inertOnPQXDH
  induction hReach with
  | Base => exact messageKeyCurrentInv_nil
  | Step input hPre _ ih =>
    rcases input with ⟨⟨i, hi⟩, inp⟩
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · let msg : Bytes := inp
      change MessageKeyCurrentInv (((Network.sendMessage msg).run _).2.val)
      rw [mkInv_sendMessage_snd]
      exact hI.append_net _ inp ih
    · exact hI.preserves_registerIdentity inp _ ih
    · rcases inp with ⟨p, skIdx⟩; exact hI.preserves_registerCorruptIdentity p skIdx _ ih
    · rcases inp with ⟨b, idStateIdx⟩; exact hI.preserves_genSignedPrekey b idStateIdx _ ih
    · rcases inp with ⟨b, idStateIdx⟩; exact hI.preserves_genPQPrekey b idStateIdx _ ih
    · exact hI.preserves_genOneTimePrekey inp _ ih
    · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩
      exact mkInv_aliceStart a b idStateIdx regIdxB bh _ ih
    · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩
      exact mkInv_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ ih
    · rcases inp with ⟨me, stH, coinsLen, pqIdx⟩
      exact mkInv_messageEncrypt me stH coinsLen pqIdx _ hPre ih
    · rcases inp with ⟨me, stH⟩; exact mkInv_messageEncryptAbort me stH _ ih
    · rcases inp with ⟨me, stH, msgH, pqIdx, spqrMsgIdx⟩
      exact mkInv_messageDecrypt me stH msgH pqIdx spqrMsgIdx _ hPre ih
    · rcases inp with ⟨me, stH, msgH, evH, pqIdx, spqrMsgIdx⟩
      exact mkInv_messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx _ hPre ih
    · rcases inp with ⟨me, stH, k⟩; exact mkInv_exposeKey me stH k _ ih
    · rcases inp with ⟨me, stH⟩; exact mkInv_exposeSpqr me stH _ ih
    · exact mkInv_exposeSkipped inp _ ih
    · rcases inp with ⟨p, stateIdx⟩; exact hI.preserves_compromiseIK p stateIdx _ ih
    · rcases inp with ⟨b, stateIdx⟩; exact hI.preserves_compromiseSPK b stateIdx _ ih
    · rcases inp with ⟨b, stateIdx⟩; exact hI.preserves_compromisePQSPK b stateIdx _ ih
    · rcases inp with ⟨b, stateIdx⟩; exact hI.preserves_compromiseOPK b stateIdx _ ih
    · exact hI.preserves_breakDH _ ih
    · exact hI.preserves_breakKEM _ ih
    · exact hI.preserves_invertDH inp _ ih
    · exact hI.preserves_invertKEM inp _ ih
    · omega

/-! ## Extraction Corollaries for `decrypt` and `decryptSkipped` Moves -/

private def NoNewTREvent (tr t : ExecTrace) : Prop :=
  ∀ i, tr.length ≤ i → (t.at? i : Option TREntry) = none

private def HasLoggedMessageKeyFrom (tr t : ExecTrace) (stateIdx : Nat) : Prop :=
  stateIdx < tr.length ∧
  ∃ s dir seed pqSalt n rIdx j,
    tr.length ≤ j ∧
    t.EventLoggedAt (TREvent.MessageKey s dir seed pqSalt n rIdx stateIdx) j

private theorem noNewTREvent_refl (tr : ExecTrace) : NoNewTREvent tr tr :=
  fun _ hi => at?_eq_none_of_le_local tr hi

private theorem noNewTREvent_trans {tr t₁ t₂ : ExecTrace} (hle : t₁ ≤ t₂)
    (h1 : NoNewTREvent tr t₁) (h2 : NoNewTREvent t₁ t₂) : NoNewTREvent tr t₂ := by
  intro i hi
  by_cases hlt : i < t₁.length
  · rw [at?_eq_of_le_of_lt hle hlt]; exact h1 i hi
  · exact h2 i (by omega)

private theorem noNewTREvent_append_other {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none) :
    NoNewTREvent tr (tr.append e) := by
  intro i hi
  rw [at?_append_non_entry_local tr e hnone]
  exact at?_eq_none_of_le_local tr hi

private theorem noNewTREvent_of_xquiet {α : Type} {x : Traceful α}
    (hx : XplSteps.XQuiet x) (tr : ExecTrace) :
    NoNewTREvent tr (x.run tr).2.val :=
  fun i hi => (hx tr i hi).2.2.1

private theorem receiveSignalMsg_trace_eq (msgH : Nat) (tr : ExecTrace) :
    ((receiveSignalMsg msgH).run tr).2.val = tr :=
  Preserves.receiveSignalMsg (Inv := fun t => t = tr) msgH tr rfl

private theorem bind_noNewTREvent_or {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr₀ tr : ExecTrace} {stateIdx : Nat}
    (hx : NoNewTREvent tr (x.run tr).2.val)
    (hf : ∀ a, NoNewTREvent (x.run tr).2.val ((f a).run (x.run tr).2.val).2.val ∨
      HasLoggedMessageKeyFrom tr₀ ((f a).run (x.run tr).2.val).2.val stateIdx) :
    NoNewTREvent tr ((x >>= f).run tr).2.val ∨
      HasLoggedMessageKeyFrom tr₀ ((x >>= f).run tr).2.val stateIdx := by
  rw [run_bind_snd]
  cases (x.run tr).1 with
  | none => exact .inl hx
  | some a =>
    rcases hf a with h2 | hmk
    · exact .inl (noNewTREvent_trans ((f a).run (x.run tr).2.val).2.property hx h2)
    · exact .inr hmk

private theorem hasLoggedMessageKeyFrom_logMessageKeyAndStore
    {tr₀ tr : ExecTrace} (hle : tr₀ ≤ tr) {stateIdx : Nat} (hst : stateIdx < tr₀.length)
    (me : Participant) (s : SessionInfo) (dir : KeyDir) (seed pqSalt : Bytes)
    (n : UInt32) (rIdx : Nat) (st : TRState) :
    HasLoggedMessageKeyFrom tr₀
      ((logMessageKeyAndStore me s dir seed pqSalt n rIdx stateIdx st).run tr).2.val
      stateIdx := by
  refine ⟨hst, s, dir, seed, pqSalt, n, rIdx, tr.length, Trace.length_le _ _ hle, ?_⟩
  rw [mkInv_logMessageKeyAndStore_snd]
  exact eventLoggedAt_mono (Trace.append_le _ _) (eventLoggedAt_here tr _)

private theorem messageDecrypt_dichotomy (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) (tr : ExecTrace) :
    NoNewTREvent tr ((messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val ∨
      HasLoggedMessageKeyFrom tr
        ((messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val stateIdx := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  rw [run_bind_snd, getLocalState_tr_fst, getLocalState_tr_snd]
  rcases he : (tr.at? stateIdx : Option TRStEntry) with _ | ⟨⟨p, st₀⟩⟩
  · exact .inl (noNewTREvent_refl tr)
  · dsimp only
    by_cases hp : p = me
    · subst p; simp only [↓reduceIte]
      have hst_lt : stateIdx < tr.length := by
        have := Trace.at?_eq_some_implies_length_le (EntryT := TRStEntry) tr stateIdx
        rw [he] at this; exact this
      refine bind_noNewTREvent_or (noNewTREvent_of_xquiet (XplSteps.xquiet_receiveSignalMsg msgIdx) tr)
        fun msg => ?_
      rw [receiveSignalMsg_trace_eq]
      refine bind_noNewTREvent_or
        (noNewTREvent_of_xquiet (XplSteps.xquiet_ensureReceiverChain st₀ msg.ratchetKey) tr)
        fun ⟨st, c, ratcheted⟩ => ?_
      dsimp only
      let tr₁ := ((ensureReceiverChain st₀ msg.ratchetKey).run tr).2.val
      have hle₁ : tr ≤ tr₁ := ((ensureReceiverChain st₀ msg.ratchetKey).run tr).2.property
      rcases consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
      · dsimp only; rw [Traceful.run_failure]; exact .inl (noNewTREvent_refl tr₁)
      · dsimp only
        rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
        · dsimp only; rw [Traceful.run_failure]; exact .inl (noNewTREvent_refl tr₁)
        · dsimp only
          refine bind_noNewTREvent_or
            (by rw [mkInv_sendMessage_snd]; exact noNewTREvent_append_other tr₁ (NetE key) rfl)
            fun _ => ?_
          rw [mkInv_sendMessage_snd]
          let tr₂ := tr₁.append (NetE key)
          have hle₂ : tr ≤ tr₂ := Trace.le_trans _ _ _ hle₁ (Trace.append_le tr₁ _)
          refine bind_noNewTREvent_or
            (by rw [receiveMessage_snd]; exact noNewTREvent_refl tr₂) fun pqSalt => ?_
          rw [receiveMessage_snd]
          refine bind_noNewTREvent_or
            (by rw [verifyMacAndDecrypt_trace]; exact noNewTREvent_refl tr₂) fun m => ?_
          rw [verifyMacAndDecrypt_trace]
          have hTail : ∀ t₃, tr ≤ t₃ → HasLoggedMessageKeyFrom tr ((do
              let _ ← logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
                (msg.counter.toNat - c.index.toNat)
              let _ ← ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
              logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter
                c.rIdx stateIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }).run t₃).2.val
              stateIdx := by
            intro t₃ hle₃
            let skipped := msg.counter.toNat - c.index.toNat
            obtain ⟨hsk1, _⟩ :=
              logSkippedKeys_run_total (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
                skipped t₃
            have hle_sk : tr ≤ ((logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
                c.chainKey c.index skipped).run t₃).2.val :=
              Trace.le_trans _ _ _ hle₃ ((logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
                c.chainKey c.index skipped).run t₃).2.property
            change HasLoggedMessageKeyFrom tr (((logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx
              stateIdx c.chainKey c.index skipped >>= fun _ => do
                let _ ← ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
                logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt
                  msg.counter c.rIdx stateIdx
                  { st with recv := setRecvChain st.recv c', spqr := spqr' }).run t₃).2.val) stateIdx
            rw [run_bind_snd, hsk1]; dsimp only
            rw [run_bind_snd, (mkInv_logEvent_run _ _).1, (mkInv_logEvent_run _ _).2]; dsimp only
            have hle_rcv : tr ≤ (((logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
                c.chainKey c.index skipped).run t₃).2.val).append
                (TREvE (TREvent.Received me st.peer msg.ratchetKey msg.counter m)) :=
              Trace.le_trans _ _ _ hle_sk (Trace.append_le _ _)
            exact hasLoggedMessageKeyFrom_logMessageKeyAndStore hle_rcv hst_lt me (st.sessionInfo me)
              .receiver seed pqSalt msg.counter c.rIdx
              { st with recv := setRecvChain st.recv c', spqr := spqr' }
          cases ratcheted
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact .inr (hTail tr₂ hle₂)
          · simp only [↓reduceIte]
            rw [run_bind_snd, (mkInv_logEvent_run _ tr₂).1, (mkInv_logEvent_run _ tr₂).2]; dsimp only
            rw [run_bind_snd, (mkInv_logEvent_run _ _).1, (mkInv_logEvent_run _ _).2]; dsimp only
            exact .inr (hTail _
              (Trace.le_trans _ _ _ hle₂
                (Trace.le_trans _ _ _ (Trace.append_le tr₂ _) (Trace.append_le _ _))))
    · simp only [hp, ↓reduceIte]; exact .inl (noNewTREvent_refl tr)

private theorem messageDecryptSkipped_dichotomy (me : Participant)
    (stateIdx msgIdx evIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace) :
    NoNewTREvent tr ((messageDecryptSkipped me stateIdx msgIdx evIdx pqIdx spqrMsgIdx).run tr).2.val ∨
      HasLoggedMessageKeyFrom tr
        ((messageDecryptSkipped me stateIdx msgIdx evIdx pqIdx spqrMsgIdx).run tr).2.val stateIdx := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  rw [run_bind_snd, getLocalState_tr_fst, getLocalState_tr_snd]
  rcases he : (tr.at? stateIdx : Option TRStEntry) with _ | ⟨⟨p, st⟩⟩
  · exact .inl (noNewTREvent_refl tr)
  · dsimp only
    by_cases hp : p = me
    · subst p; simp only [↓reduceIte]
      have hst_lt : stateIdx < tr.length := by
        have := Trace.at?_eq_some_implies_length_le (EntryT := TRStEntry) tr stateIdx
        rw [he] at this; exact this
      refine bind_noNewTREvent_or (noNewTREvent_of_xquiet (XplSteps.xquiet_receiveSignalMsg msgIdx) tr)
        fun msg => ?_
      rw [receiveSignalMsg_trace_eq]
      refine bind_noNewTREvent_or
        (noNewTREvent_of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_getEntry evIdx)) tr)
        fun ⟨ev⟩ => ?_
      rw [XplSteps.xfix_getEntry (E := ProtocolEvent.ExecEntryT TREvent) evIdx tr]
      cases ev with
      | SkippedKeyStored s pk n seed rIdx _sourceStateIdx =>
        dsimp only
        refine bind_noNewTREvent_or
          (noNewTREvent_of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_guard _)) tr) fun _ => ?_
        rw [XplSteps.xfix_guard _ tr]
        refine bind_noNewTREvent_or
          (noNewTREvent_of_xquiet (XplSteps.xquiet_of_fix (XplSteps.xfix_guardTrace _)) tr) fun _ => ?_
        rw [XplSteps.xfix_guardTrace _ tr]
        rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
        · dsimp only; rw [Traceful.run_failure]; exact .inl (noNewTREvent_refl tr)
        · dsimp only
          refine bind_noNewTREvent_or
            (by rw [mkInv_sendMessage_snd]; exact noNewTREvent_append_other tr (NetE key) rfl)
            fun _ => ?_
          rw [mkInv_sendMessage_snd]
          let tr₁ := tr.append (NetE key)
          have hle₁ : tr ≤ tr₁ := Trace.append_le tr _
          refine bind_noNewTREvent_or
            (by rw [receiveMessage_snd]; exact noNewTREvent_refl tr₁) fun pqSalt => ?_
          rw [receiveMessage_snd]
          refine bind_noNewTREvent_or
            (by rw [verifyMacAndDecrypt_trace]; exact noNewTREvent_refl tr₁) fun m => ?_
          rw [verifyMacAndDecrypt_trace]
          rw [run_bind_snd, (mkInv_logEvent_run _ tr₁).1, (mkInv_logEvent_run _ tr₁).2]; dsimp only
          rw [run_bind_snd, (mkInv_logEvent_run _ _).1, (mkInv_logEvent_run _ _).2]; dsimp only
          have hle₃ : tr ≤ (tr₁.append (TREvE (TREvent.SkippedKeyUsed s evIdx))).append
              (TREvE (TREvent.Received me st.peer pk n m)) :=
            Trace.le_trans _ _ _ hle₁
              (Trace.le_trans _ _ _ (Trace.append_le tr₁ _) (Trace.append_le _ _))
          exact .inr (hasLoggedMessageKeyFrom_logMessageKeyAndStore hle₃ hst_lt me s .receiver
            seed pqSalt n rIdx { st with spqr := spqr' })
      | _ => dsimp only; rw [Traceful.run_failure]; exact .inl (noNewTREvent_refl tr)
    · simp only [hp, ↓reduceIte]; exact .inl (noNewTREvent_refl tr)

private theorem receivedPlaintext_eq_none_of_noNewTREvent {tr t : ExecTrace}
    (h : NoNewTREvent tr t) : receivedPlaintext tr t = none := by
  unfold receivedPlaintext
  rw [List.findSome?_eq_none_iff]
  intro i hi
  obtain ⟨hlo, _⟩ := List.mem_range'_1.mp hi
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  rw [h i hlo]

private theorem not_accept_of_noNewTREvent {tr t : ExecTrace} (stateIdx msgIdx : Nat)
    (wrapped : Bool) (h : NoNewTREvent tr t) :
    ¬ ∃ v ∈ decVis tr t stateIdx msgIdx wrapped ++ exposures tr t, v.kind = .accept := by
  rintro ⟨v, hv, hk⟩
  rcases List.mem_append.mp hv with hv | hv
  · unfold decVis at hv
    rw [receivedPlaintext_eq_none_of_noNewTREvent h] at hv
    simp only [Option.map_none, Option.toList_none, List.append_nil, List.mem_append,
      List.mem_map] at hv
    rcases hv with hv | ⟨_, _, rfl⟩
    · rcases hm : tr.getMessageSentAt msgIdx with _ | b
      · simp [hm] at hv
      · simp only [hm, Option.map_some, Option.toList_some, List.mem_singleton] at hv
        subst hv; cases hk
    · cases hk
  · have := xpl_exposures_kind hv
    rw [hk] at this; cases this

private theorem isCurrentSnapshot_of_hasLoggedMessageKeyFrom {tr t : ExecTrace} {stateIdx : Nat}
    (hle : tr ≤ t) (hInv : MessageKeyCurrentInv t) (hmk : HasLoggedMessageKeyFrom tr t stateIdx) :
    isCurrentSnapshot tr stateIdx = true := by
  obtain ⟨hst, s, dir, seed, pqSalt, n, rIdx, j, hj, hlog⟩ := hmk
  have hne : stateIdx ≠ j + 1 := by omega
  exact isCurrentSnapshot_of_isCurrentSnapshotBefore hle hj hst
    (hInv s dir seed pqSalt n rIdx stateIdx j hlog hne)

/-- If a `Move.decrypt` from `tr` reaches a reachable trace and emits an `.accept` visible entry,
the snapshot `stateIdx` it reads is current on `tr`. -/
theorem isCurrentSnapshot_of_decrypt_accept {tr : ExecTrace} {me : Participant}
    {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    (hreach : ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr).Reachable
      reachability)
    (hacc : ∃ v ∈ (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr,
      v.kind = .accept) :
    isCurrentSnapshot tr stateIdx = true := by
  let m := Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped
  have hnext : m.next tr = ((messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val :=
    XplSteps.xrun_bind_unit _ tr
  rcases messageDecrypt_dichotomy me stateIdx msgIdx pqIdx spqrMsgIdx tr with hno | hmk
  · rw [← hnext] at hno
    exact False.elim (not_accept_of_noNewTREvent stateIdx msgIdx wrapped hno hacc)
  · rw [← hnext] at hmk
    exact isCurrentSnapshot_of_hasLoggedMessageKeyFrom (m.le_next tr)
      (messageKeyCurrentInv_reachable hreach) hmk

/-- If a `Move.decryptSkipped` from `tr` reaches a reachable trace and emits an `.accept` visible
entry, the snapshot `stateIdx` it reads is current on `tr`. -/
theorem isCurrentSnapshot_of_decryptSkipped_accept {tr : ExecTrace} {me : Participant}
    {stateIdx msgIdx evIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    (hreach : ((Move.decryptSkipped me stateIdx msgIdx evIdx pqIdx spqrMsgIdx wrapped).next
      tr).Reachable reachability)
    (hacc : ∃ v ∈ (Move.decryptSkipped me stateIdx msgIdx evIdx pqIdx spqrMsgIdx wrapped).vis tr,
      v.kind = .accept) :
    isCurrentSnapshot tr stateIdx = true := by
  let m := Move.decryptSkipped me stateIdx msgIdx evIdx pqIdx spqrMsgIdx wrapped
  have hnext : m.next tr =
      ((messageDecryptSkipped me stateIdx msgIdx evIdx pqIdx spqrMsgIdx).run tr).2.val :=
    XplSteps.xrun_bind_unit _ tr
  rcases messageDecryptSkipped_dichotomy me stateIdx msgIdx evIdx pqIdx spqrMsgIdx tr with hno | hmk
  · rw [← hnext] at hno
    exact False.elim (not_accept_of_noNewTREvent stateIdx msgIdx wrapped hno hacc)
  · rw [← hnext] at hmk
    exact isCurrentSnapshot_of_hasLoggedMessageKeyFrom (m.le_next tr)
      (messageKeyCurrentInv_reachable hreach) hmk

private theorem runMoves_vis_eq_nil_of_invisible :
    ∀ (tr : ExecTrace) (δ : List Move),
      MovesFrom InvisibleNoEffect tr δ → (runMoves δ tr).2 = []
  | _, [], _ => rfl
  | tr, m :: δ, ⟨⟨hv, _⟩, hδ⟩ => by
    rw [runMoves_cons_snd, hv, List.nil_append]
    exact runMoves_vis_eq_nil_of_invisible (m.next tr) δ hδ

private theorem runMoves_append_snd :
    ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
      (runMoves (ms₁ ++ ms₂) tr).2 =
        (runMoves ms₁ tr).2 ++ (runMoves ms₂ (runMoves ms₁ tr).1).2
  | [], _, _ => rfl
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, runMoves_cons_snd, runMoves_cons_fst,
      runMoves_append_snd ms₁ ms₂ (m.next tr), List.append_assoc]

/-- In an accepting block `blk` explained by `pre ++ m :: post` with invisible `pre` and `post`, if
`m` is `decrypt` or `decryptSkipped`, then `m` reads a current snapshot on
`runTraceMoves r (ms₀ ++ pre)`. -/
theorem rcvCurrentSnapshot_of_xplBlock {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms₀ pre post : List Move} {m : Move}
    {acc blk : List MachineEvent}
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc blk)
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post)
    (hacc : ∃ e ∈ blk, eventKind e = .accept) :
    match m with
    | .decrypt _ stateIdx .. => isCurrentSnapshot (runTraceMoves r (ms₀ ++ pre)) stateIdx = true
    | .decryptSkipped _ stateIdx .. => isCurrentSnapshot (runTraceMoves r (ms₀ ++ pre)) stateIdx = true
    | _ => True := by
  have htr_pre : (runMoves pre (runTraceMoves r ms₀)).1 = runTraceMoves r (ms₀ ++ pre) :=
    (runTrace_append r ms₀ pre).symm
  have hvis_eq : (runMoves (pre ++ m :: post) (runTraceMoves r ms₀)).2 =
      m.vis (runTraceMoves r (ms₀ ++ pre)) := by
    rw [runMoves_append_snd, runMoves_vis_eq_nil_of_invisible _ _ hpre, List.nil_append,
      runMoves_cons_snd, runMoves_vis_eq_nil_of_invisible _ _ hpost, List.append_nil, htr_pre]
  obtain ⟨e, he, hek⟩ := hacc
  obtain ⟨v, hv, hev⟩ := xpl_forall₂_mem_left hB.matched e he
  rw [hvis_eq] at hv
  have hvk : v.kind = .accept := by rw [xpl_kind_of_matches hev, hek]
  have hreach_m : (m.next (runTraceMoves r (ms₀ ++ pre))).Reachable reachability := by
    have hall := hB.run.2.2.1.2.2 (ms₀ ++ pre ++ [m]).length
    have hsplit : ms₀ ++ (pre ++ m :: post) = (ms₀ ++ pre ++ [m]) ++ post := by simp
    rw [hsplit, List.take_left, runTrace_snoc] at hall
    exact hall
  cases m with
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    exact isCurrentSnapshot_of_decrypt_accept hreach_m ⟨v, hv, hvk⟩
  | decryptSkipped me stateIdx msgIdx evIdx pqIdx spqrMsgIdx wrapped =>
    exact isCurrentSnapshot_of_decryptSkipped_accept hreach_m ⟨v, hv, hvk⟩
  | _ => trivial

end Symbolic.Swarm.CREF.TR
