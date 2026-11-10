/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
public import Symbolic.Proofs.Swarm.CREF.TR.RecvFresh
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.MessageKeyCurrentInv
import Symbolic.Proofs.Swarm.CREF.TR.RecvFreshDecA
import Symbolic.Proofs.Swarm.CREF.TR.RecvFreshDecB1
import Symbolic.Proofs.Swarm.CREF.TR.RecvHistStepTR2
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# `TRRecvFreshAll` Initialization and Single-Move Preservation

Proves `trRecvFreshAll_nil` on the initial setup trace and single-move preservation of
`TRRecvFreshAll` across `decryptSkipped`, `decrypt`, `encrypt`, `encryptAbort`, `encryptFail`,
`exposeKey`, `exposeSpqr`, and `exposeSkipped`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR

cref_open

open DY DY.Libsignal DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg isCurrentSnapshot receiveSignalMsg
  ensureReceiverChain verifyMacAndDecrypt logSkippedKeys logMessageKeyAndStore messageDecrypt
  messageDecryptSkipped messageEncrypt messageEncryptAbort exposeKey exposeSpqr exposeSkipped
  skippedKeyUsedB guardTrace parseTrSignalMsg trMsgKeys trHonestWireMsg)
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir KeyComponent RecvChain findRecvChain setRecvChain
  consumeMessageKey computeMac messageVersion x25519LowOrder kdfCk)
open Symbolic.Swarm.CREF.TR.RecvDec (StEntry TREntry logSkippedKeysTr decSkippedTr decTailTr
  decRatchetPreTr trDhRatchetState at?_append_of_lt at?_eq_none_of_le at?_append_non_entry
  isCurrentSnapshot_append_non_st getLocalState_fst getLocalState_snd run_bind_pure_val
  getLocalState_append_stEntry_ne_or_old logSkippedKeysTr_le decSkippedTr_length decTailTr_length)

/-- `TRRecvFreshAll` holds on the initial setup trace since `setupTrace r₀` stores no `TRState`
snapshots. -/
theorem trRecvFreshAll_nil (r₀ : ProtocolSetup) : TRRecvFreshAll r₀ [] := by
  intro q stateIdx st _hq hst _hcur
  have hat : ((setupTrace r₀).at? stateIdx : Option RecvHistStep2.StEntry) = some ⟨⟨q, st⟩⟩ :=
    at?_of_getLocalState_rfb1 hst
  exact False.elim (RecvHistStep2.traceStatesP_at?_st
    (RecvHistStep2.traceStatesP_setupTrace (P := fun _ => False) r₀) hat)

/-- Trace-indexed form of `TRRecvFreshAll`. -/
def TRRecvFreshAllAt (r₀ : ProtocolSetup) (tr : ExecTrace) : Prop :=
  ∀ q stateIdx st,
    (q = r₀.alice ∨ q = r₀.bob) →
    ((PersistentLocalState.getLocalState q stateIdx : Traceful TRState).run tr).1 = some st →
    isCurrentSnapshot tr stateIdx = true →
    TRRecvCountersFresh tr q st ∧ TRSkippedRIdxChainRel tr q st

theorem trRecvFreshAllAt_append_non {E : Type} [ExecTraceTypes.Has E] {r₀ : ProtocolSetup} {tr : ExecTrace}
    (e : E)
    (hnone_st : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option StEntry) = none)
    (hnone_tr : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (h : TRRecvFreshAllAt r₀ tr) : TRRecvFreshAllAt r₀ (tr.append e) := by
  intro q stateIdx st hq hget hcur
  rw [getLocalState_fst, at?_append_non_entry _ e hnone_st, ← getLocalState_fst] at hget
  rw [isCurrentSnapshot_append_non_st _ e hnone_st] at hcur
  obtain ⟨hcf, hsk⟩ := h q stateIdx st hq hget hcur
  exact ⟨trRecvCountersFresh_of_imp
      (fun _ _ _ _ _ i hev => (eventLoggedAt_append_non_tr_rfb1 tr e hnone_tr _ i).mp hev)
      (fun _ _ _ _ _ i hev => (eventLoggedAt_append_non_tr_rfb1 tr e hnone_tr _ i).mp hev) hcf,
    trSkippedRIdxChainRel_of_imp
      (fun _ _ _ _ _ i hev => (eventLoggedAt_append_non_tr_rfb1 tr e hnone_tr _ i).mp hev) hsk⟩

/-! ## `decSkippedTr` and `decTailTr` Current-Snapshot Helpers -/

theorem isCurrentSnapshot_of_decSkippedTr_reachable
    {tr : ExecTrace} {me : Participant} {stateIdx skIdx rIdx srcIdx : Nat}
    {st : TRState} {pk seed key pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hreach : (decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n).Reachable
      reachability) :
    isCurrentSnapshot tr stateIdx = true := by
  have hat_st : (tr.at? stateIdx : Option StEntry) = some ⟨⟨me, st⟩⟩ := at?_of_getLocalState_rfb1 hst
  have hplt : stateIdx < tr.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr stateIdx
    rw [hat_st] at this; exact this
  let tr2 := ((tr.append (⟨key⟩ : Network.ExecEntryT)).append
    (⟨TREvent.SkippedKeyUsed (st.sessionInfo me) skIdx⟩ : TREntry)).append
    (⟨TREvent.Received me st.peer pk n ptTerm⟩ : TREntry)
  let ev_mk := TREvent.MessageKey (st.sessionInfo me) .receiver seed pqSalt n rIdx stateIdx
  let T := decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n
  have hle_tr2 : tr ≤ tr2 :=
    Trace.le_trans _ _ _
      (Trace.le_trans _ _ _ (Trace.append_le tr _) (Trace.append_le _ _))
      (Trace.append_le _ _)
  have hle_T : tr ≤ T :=
    Trace.le_trans _ _ _ hle_tr2
      (Trace.le_trans _ _ _ (Trace.append_le tr2 _) (Trace.append_le _ _))
  have hlen_tr2 : tr.length ≤ tr2.length := Trace.length_le _ _ hle_tr2
  have hlog : T.EventLoggedAt ev_mk tr2.length := by
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; unfold T decSkippedTr; dsimp only
    rw [at?_append_non_entry _ _ rfl]; exact Trace.at?_append tr2 (⟨ev_mk⟩ : TREntry)
  have hInv : MessageKeyCurrentInv T := messageKeyCurrentInv_reachable hreach
  have hne : stateIdx ≠ tr2.length + 1 := by omega
  exact isCurrentSnapshot_of_isCurrentSnapshotBefore hle_T hlen_tr2 hplt
    (hInv (st.sessionInfo me) .receiver seed pqSalt n rIdx stateIdx tr2.length hlog hne)

theorem isCurrentSnapshot_of_decTailTr_reachable
    {tr tr_pre : ExecTrace} {me : Participant} {stateIdx : Nat}
    {st₀ st1 : TRState} {c c' : RecvChain} {pk seed pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    (hle_pre : tr ≤ tr_pre)
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st₀)
    (hreach : (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).Reachable
      reachability) :
    isCurrentSnapshot tr stateIdx = true := by
  have hat_st : (tr.at? stateIdx : Option StEntry) = some ⟨⟨me, st₀⟩⟩ := at?_of_getLocalState_rfb1 hst
  have hplt : stateIdx < tr.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr stateIdx
    rw [hat_st] at this; exact this
  let tr_sk := logSkippedKeysTr (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index
    (n.toNat - c.index.toNat) tr_pre
  let tr_rcv := tr_sk.append (⟨TREvent.Received me st1.peer pk n ptTerm⟩ : TREntry)
  let ev_mk := TREvent.MessageKey (st1.sessionInfo me) .receiver seed pqSalt n c.rIdx stateIdx
  let T := decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n
  have hle_T : tr ≤ T :=
    Trace.le_trans _ _ _ hle_pre (decTailTr_le_rfb1 tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n)
  have hle_rcv : tr ≤ tr_rcv :=
    Trace.le_trans _ _ _ hle_pre
      (Trace.le_trans _ _ _
        (logSkippedKeysTr_le (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index
          (n.toNat - c.index.toNat) tr_pre)
        (Trace.append_le _ _))
  have hlen_rcv : tr.length ≤ tr_rcv.length := Trace.length_le _ _ hle_rcv
  have hlog : T.EventLoggedAt ev_mk tr_rcv.length := by
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; unfold T decTailTr; dsimp only
    rw [at?_append_non_entry _ _ rfl]; exact Trace.at?_append tr_rcv (⟨ev_mk⟩ : TREntry)
  have hInv : MessageKeyCurrentInv T := messageKeyCurrentInv_reachable hreach
  have hne : stateIdx ≠ tr_rcv.length + 1 := by omega
  exact isCurrentSnapshot_of_isCurrentSnapshotBefore hle_T hlen_rcv hplt
    (hInv (st1.sessionInfo me) .receiver seed pqSalt n c.rIdx stateIdx
      tr_rcv.length hlog hne)

/-! ## `Move.decryptSkipped` Freshness Preservation -/

private theorem trRecvCountersFresh_append_trEntry_other_fsi {tr : ExecTrace} {ev : TREvent}
    {p : Participant} {st : TRState}
    (hNoMK : ∀ seed pqSalt n r pIdx,
      ev ≠ TREvent.MessageKey (st.sessionInfo p) .receiver seed pqSalt n r pIdx)
    (hNoSK : ∀ pk n seed r srcIdx,
      ev ≠ TREvent.SkippedKeyStored (st.sessionInfo p) pk n seed r srcIdx)
    (hFresh : TRRecvCountersFresh tr p st) :
    TRRecvCountersFresh (tr.append (⟨ev⟩ : TREntry)) p st :=
  trRecvCountersFresh_of_imp
    (fun seed pqSalt n r pIdx i hlog =>
      ((eventLoggedAt_append_trEntry_iff_rfb1 tr ⟨ev⟩ _ i).mp hlog).elim id
        fun ⟨_, heq⟩ => False.elim (hNoMK seed pqSalt n r pIdx heq))
    (fun pk n seed r srcIdx i hlog =>
      ((eventLoggedAt_append_trEntry_iff_rfb1 tr ⟨ev⟩ _ i).mp hlog).elim id
        fun ⟨_, heq⟩ => False.elim (hNoSK pk n seed r srcIdx heq))
    hFresh

private theorem eventLoggedAt_decSkippedTr_skippedKeyStored_fsi
    {tr : ExecTrace} {q : Participant} {stateIdx skIdx rIdx srcIdx : Nat}
    {st1 : TRState} {pk seed key pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    {sinfo : SessionInfo} {pk' : DY.Bytes} {n' : UInt32} {seed' : DY.Bytes}
    {r' src' i : Nat} :
    (decSkippedTr tr q stateIdx skIdx rIdx srcIdx st1 pk seed key pqSalt ptTerm spqr' n).EventLoggedAt
      (TREvent.SkippedKeyStored sinfo pk' n' seed' r' src') i ↔
    tr.EventLoggedAt (TREvent.SkippedKeyStored sinfo pk' n' seed' r' src') i := by
  unfold decSkippedTr
  dsimp only
  rw [eventLoggedAt_append_non_tr_rfb1 _ _ rfl,
      eventLoggedAt_append_trEntry_iff_rfb1,
      eventLoggedAt_append_trEntry_iff_rfb1,
      eventLoggedAt_append_trEntry_iff_rfb1,
      eventLoggedAt_append_non_tr_rfb1 _ _ rfl]
  constructor
  · rintro (((h | ⟨_, h⟩) | ⟨_, h⟩) | ⟨_, h⟩)
    · exact h
    · nomatch h
    · nomatch h
    · nomatch h
  · intro h
    exact Or.inl (Or.inl (Or.inl h))

private theorem eventLoggedAt_decSkippedTr_messageKey_fsi
    {tr : ExecTrace} {q : Participant} {stateIdx skIdx rIdx srcIdx : Nat}
    {st1 : TRState} {pk seed key pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    {s : SessionInfo} {dir : KeyDir} {seed' pqSalt' : DY.Bytes} {n' : UInt32}
    {r' pIdx' i : Nat}
    (hlog : (decSkippedTr tr q stateIdx skIdx rIdx srcIdx st1 pk seed key pqSalt ptTerm spqr' n).EventLoggedAt
      (TREvent.MessageKey s dir seed' pqSalt' n' r' pIdx') i) :
    tr.EventLoggedAt (TREvent.MessageKey s dir seed' pqSalt' n' r' pIdx') i ∨
      s = st1.sessionInfo q := by
  unfold decSkippedTr at hlog
  dsimp only at hlog
  rw [eventLoggedAt_append_non_tr_rfb1 _ _ rfl] at hlog
  rcases (eventLoggedAt_append_trEntry_iff_rfb1 _ _ _ i).mp hlog with hlog2 | ⟨_, heq⟩
  · rcases (eventLoggedAt_append_trEntry_iff_rfb1 _ _ _ i).mp hlog2 with hlog1 | ⟨_, heq⟩
    · rcases (eventLoggedAt_append_trEntry_iff_rfb1 _ _ _ i).mp hlog1 with hlog0 | ⟨_, heq⟩
      · exact Or.inl ((eventLoggedAt_append_non_tr_rfb1 _ _ rfl _ _).mp hlog0)
      · nomatch heq
    · nomatch heq
  · injection heq with hs
    exact Or.inr hs.symm

private theorem trRecvCountersFresh_decSkippedTr_spqr_fsi
    {tr : ExecTrace} {p : Participant} {stateIdx skIdx rIdx srcIdx : Nat}
    {st : TRState} {pk seed key pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    (hFresh : TRRecvCountersFresh tr p st)
    (hsk : tr.EventLoggedAt
      (TREvent.SkippedKeyStored (st.sessionInfo p) pk n seed rIdx srcIdx) skIdx) :
    TRRecvCountersFresh
      (decSkippedTr tr p stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n) p
      { st with spqr := spqr' } := by
  change TRRecvCountersFresh
    (decSkippedTr tr p stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n) p st
  unfold decSkippedTr
  dsimp only
  have h1 : TRRecvCountersFresh (tr.append (⟨key⟩ : Network.ExecEntryT)) p st :=
    trRecvCountersFresh_of_imp
      (fun _ _ _ _ _ _ h => (eventLoggedAt_append_non_tr_rfb1 _ _ rfl _ _).mp h)
      (fun _ _ _ _ _ _ h => (eventLoggedAt_append_non_tr_rfb1 _ _ rfl _ _).mp h)
      hFresh
  have h2 : TRRecvCountersFresh
      ((tr.append (⟨key⟩ : Network.ExecEntryT)).append
        (⟨TREvent.SkippedKeyUsed (st.sessionInfo p) skIdx⟩ : TREntry)) p st := by
    apply trRecvCountersFresh_append_trEntry_other_fsi (hFresh := h1)
    · intro _ _ _ _ _ h; nomatch h
    · intro _ _ _ _ _ h; nomatch h
  have h3 : TRRecvCountersFresh
      (((tr.append (⟨key⟩ : Network.ExecEntryT)).append
        (⟨TREvent.SkippedKeyUsed (st.sessionInfo p) skIdx⟩ : TREntry)).append
        (⟨TREvent.Received p st.peer pk n ptTerm⟩ : TREntry)) p st := by
    apply trRecvCountersFresh_append_trEntry_other_fsi (hFresh := h2)
    · intro _ _ _ _ _ h; nomatch h
    · intro _ _ _ _ _ h; nomatch h
  rcases h3 with ⟨hF1, hF2a, hF2b, hF3, hF4⟩
  rcases hFresh with ⟨hF1_0, _, hF2b_0, _, _⟩
  refine trRecvCountersFresh_of_imp
    (fun _ _ _ _ _ _ h => (eventLoggedAt_append_non_tr_rfb1 _ _ rfl _ _).mp h)
    (fun _ _ _ _ _ _ h => (eventLoggedAt_append_non_tr_rfb1 _ _ rfl _ _).mp h)
    ⟨?_, ?_, ?_, hF3, hF4⟩
  · intro c hc
    refine ⟨?_, ?_⟩
    · intro seed' pqSalt' n' pIdx i hlog
      rcases (eventLoggedAt_append_trEntry_iff_rfb1 _ _ _ i).mp hlog with hpre | ⟨_, heq⟩
      · exact (hF1 c hc).1 seed' pqSalt' n' pIdx i hpre
      · injection heq with _ _ hseed hpq hn hr _
        subst hseed hpq hn hr
        exact (hF1_0 c hc).2 pk n seed srcIdx skIdx hsk
    · intro pk' n' seed' src' i hlog
      rcases (eventLoggedAt_append_trEntry_iff_rfb1 _ _ _ i).mp hlog with hpre | ⟨_, heq⟩
      · exact (hF1 c hc).2 pk' n' seed' src' i hpre
      · nomatch heq
  · intro seed' pqSalt' n' r pIdx i hlog
    rcases (eventLoggedAt_append_trEntry_iff_rfb1 _ _ _ i).mp hlog with hpre | ⟨_, heq⟩
    · exact hF2a seed' pqSalt' n' r pIdx i hpre
    · injection heq with _ _ _ _ _ hr _
      subst hr
      exact hF2b_0 pk n seed rIdx srcIdx skIdx hsk
  · intro pk' n' seed' r src' i hlog
    rcases (eventLoggedAt_append_trEntry_iff_rfb1 _ _ _ i).mp hlog with hpre | ⟨_, heq⟩
    · exact hF2b pk' n' seed' r src' i hpre
    · nomatch heq

private theorem trSkippedRIdxChainRel_decSkippedTr_spqr_fsi
    {tr : ExecTrace} {q p : Participant} {stateIdx skIdx rIdx srcIdx : Nat}
    {st1 st : TRState} {pk seed key pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    (hRel : TRSkippedRIdxChainRel tr p st) :
    TRSkippedRIdxChainRel
      (decSkippedTr tr q stateIdx skIdx rIdx srcIdx st1 pk seed key pqSalt ptTerm spqr' n)
      p { st with spqr := spqr' } :=
  trSkippedRIdxChainRel_of_imp
    (fun _ _ _ _ _ _ h => eventLoggedAt_decSkippedTr_skippedKeyStored_fsi.mp h)
    hRel

private theorem at?_stEntry_decSkippedTr_lt_fsi (tr : ExecTrace) (me : Participant)
    (stateIdx skIdx rIdx srcIdx : Nat) (st : TRState) (pk seed key pqSalt ptTerm spqr' : DY.Bytes)
    (n : UInt32) {i : Nat} (hi : i < tr.length + 4) :
    ((decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n).at? i :
      Option StEntry) = (tr.at? i : Option StEntry) := by
  unfold decSkippedTr; dsimp only
  rw [at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
      at?_append_non_entry _ _ rfl,
      at?_append_non_entry _ _ rfl,
      at?_append_non_entry _ _ rfl,
      at?_append_non_entry _ _ rfl]

private theorem at?_stEntry_decSkippedTr_last_fsi (tr : ExecTrace) (me : Participant)
    (stateIdx skIdx rIdx srcIdx : Nat) (st : TRState) (pk seed key pqSalt ptTerm spqr' : DY.Bytes)
    (n : UInt32) :
    ((decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n).at?
      (tr.length + 4) : Option StEntry) =
      some ⟨⟨me, { st with spqr := spqr' }⟩⟩ := by
  unfold decSkippedTr; dsimp only
  let tr2 := ((tr.append (⟨key⟩ : Network.ExecEntryT)).append
    (⟨TREvent.SkippedKeyUsed (st.sessionInfo me) skIdx⟩ : TREntry)).append
    (⟨TREvent.Received me st.peer pk n ptTerm⟩ : TREntry)
  let tr_mid := tr2.append
    (⟨TREvent.MessageKey (st.sessionInfo me) .receiver seed pqSalt n rIdx stateIdx⟩ : TREntry)
  have hmid : tr.length + 4 = tr_mid.length := by
    dsimp only [tr_mid, tr2]; simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rw [hmid]
  exact Trace.at?_append tr_mid (⟨⟨me, { st with spqr := spqr' }⟩⟩ : StEntry)

private theorem decSkippedTr_le_fsi (tr : ExecTrace) (me : Participant)
    (stateIdx skIdx rIdx srcIdx : Nat) (st : TRState) (pk seed key pqSalt ptTerm spqr' : DY.Bytes)
    (n : UInt32) :
    tr ≤ decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n := by
  unfold decSkippedTr
  exact Trace.le_trans _ _ _
    (Trace.le_trans _ _ _
      (Trace.le_trans _ _ _
        (Trace.le_trans _ _ _ (Trace.append_le tr _) (Trace.append_le _ _))
        (Trace.append_le _ _))
      (Trace.append_le _ _))
    (Trace.append_le _ _)

theorem trRecvFreshAllAt_decSkippedTr
    {r₀ : ProtocolSetup} {tr : ExecTrace} {p : Participant}
    {stateIdx skIdx rIdx srcIdx : Nat}
    {st : TRState} {pk seed key pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    (hFreshAll : TRRecvFreshAllAt r₀ tr)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 = some st)
    (hsk : tr.EventLoggedAt
      (TREvent.SkippedKeyStored (st.sessionInfo p) pk n seed rIdx srcIdx) skIdx)
    (hreach : (decSkippedTr tr p stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n).Reachable
      reachability) :
    TRRecvFreshAllAt r₀
      (decSkippedTr tr p stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n) := by
  let st' : TRState := { st with spqr := spqr' }
  let T := decSkippedTr tr p stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n
  let k := tr.length + 4
  have hcur : isCurrentSnapshot tr stateIdx = true :=
    isCurrentSnapshot_of_decSkippedTr_reachable hst hreach
  have hle : tr ≤ T :=
    decSkippedTr_le_fsi tr p stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n
  have hk_at : (T.at? k : Option StEntry) = some ⟨⟨p, st'⟩⟩ :=
    at?_stEntry_decSkippedTr_last_fsi tr p stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n
  intro q j s hq_mem hget hcurj
  have hget' := at?_of_getLocalState_rfb1 hget
  have hjlt : j < T.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) T j
    rw [hget'] at this; exact this
  have hTlen : T.length = k + 1 := by
    dsimp only [T, k]
    rw [decSkippedTr_length]
  by_cases hjk : j = k
  · subst hjk
    rw [hk_at] at hget'
    injection hget' with hst_eq
    injection hst_eq with hinner
    injection hinner with hqp hs_eq
    subst hqp; subst hs_eq
    obtain ⟨hcf₀, hrel₀⟩ := hFreshAll p stateIdx st hq_mem hst hcur
    exact ⟨trRecvCountersFresh_decSkippedTr_spqr_fsi hcf₀ hsk,
           trSkippedRIdxChainRel_decSkippedTr_spqr_fsi hrel₀⟩
  · have hjk_lt : j < k := by omega
    have hold_j : (T.at? j : Option StEntry) = (tr.at? j : Option StEntry) :=
      at?_stEntry_decSkippedTr_lt_fsi tr p stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n hjk_lt
    have hj_tr : (tr.at? j : Option StEntry) = some ⟨⟨q, s⟩⟩ := hold_j.symm.trans hget'
    have hjlt₀ : j < tr.length := by
      have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr j
      rw [hj_tr] at this; exact this
    have hcur₀ : isCurrentSnapshot tr j = true :=
      isCurrentSnapshot_of_le_rfb1 hle hjlt₀ hcurj
    have hget₀ : ((PersistentLocalState.getLocalState q j : Traceful TRState).run tr).1 = some s := by
      rw [getLocalState_fst_rfb1, hj_tr]; simp
    obtain ⟨hcf_q, hrel_q⟩ := hFreshAll q j s hq_mem hget₀ hcur₀
    have hpi : p ≠ q ∨ st'.initiator ≠ s.initiator :=
      part_or_init_ne_of_current_rfb1 hcurj hget' hk_at hjk_lt
    have hsne : s.sessionInfo q ≠ st.sessionInfo p := sinfo_ne_of_part_or_init_ne_rfb1 hpi
    have hmk_imp : ∀ seed' pqSalt' n' r' pIdx' i,
        T.EventLoggedAt (TREvent.MessageKey (s.sessionInfo q) .receiver seed' pqSalt' n' r' pIdx') i →
        tr.EventLoggedAt (TREvent.MessageKey (s.sessionInfo q) .receiver seed' pqSalt' n' r' pIdx') i := by
      intro seed' pqSalt' n' r' pIdx' i hl
      rcases eventLoggedAt_decSkippedTr_messageKey_fsi hl with h0 | hs_eq
      · exact h0
      · exact False.elim (hsne hs_eq)
    have hsk_imp : ∀ pk' n' seed' r' src' i,
        T.EventLoggedAt (TREvent.SkippedKeyStored (s.sessionInfo q) pk' n' seed' r' src') i →
        tr.EventLoggedAt (TREvent.SkippedKeyStored (s.sessionInfo q) pk' n' seed' r' src') i :=
      fun _ _ _ _ _ _ hl => eventLoggedAt_decSkippedTr_skippedKeyStored_fsi.mp hl
    exact ⟨trRecvCountersFresh_of_imp hmk_imp hsk_imp hcf_q,
           trSkippedRIdxChainRel_of_imp hsk_imp hrel_q⟩

private theorem guard_snd_fsi (p : Prop) [Decidable p] (tr : ExecTrace) :
    ((_root_.guard p : Traceful Unit).run tr).2.val = tr := by
  unfold _root_.guard; split <;> simp only [Traceful.run_pure, Traceful.run_failure]

private theorem guardTrace_snd_fsi (p : ExecTrace → Bool) (tr : ExecTrace) :
    ((guardTrace p).run tr).2.val = tr := by
  unfold guardTrace; simp only [Traceful.run_mk]

private theorem receiveMessage_snd_fsi (idx : Nat) (tr : ExecTrace) :
    ((DY.Network.receiveMessage idx).run tr).2.val = tr := by
  rw [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, RecvHistStep2.run_bind_snd]
  have hge : ((DY.getEntry idx : Traceful DY.Network.ExecEntryT).run tr).2.val = tr := by
    rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  rcases ((DY.getEntry idx : Traceful DY.Network.ExecEntryT).run tr).1 <;>
    simp only [Traceful.run_pure, hge]

private theorem receiveSignalMsg_snd_fsi (msgIdx : Nat) (tr : ExecTrace) :
    ((receiveSignalMsg msgIdx).run tr).2.val = tr := by
  unfold receiveSignalMsg
  rw [RecvHistStep2.run_bind_snd, receiveMessage_snd_fsi]
  rcases ((DY.Network.receiveMessage msgIdx).run tr).1 with _ | raw
  · rfl
  · dsimp only
    rcases parseTrSignalMsg raw with _ | msg
    · simp only [Traceful.run_failure]
    · dsimp only; rw [RecvHistStep2.run_bind_snd, guard_snd_fsi]
      rcases ((_root_.guard (msg.version = messageVersion) : Traceful Unit).run tr).1 <;>
        simp only [Traceful.run_pure]

private theorem verifyMacAndDecrypt_snd_fsi (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) (tr : ExecTrace) :
    ((verifyMacAndDecrypt st msg pqSalt seed).run tr).2.val = tr := by
  unfold verifyMacAndDecrypt
  rw [RecvHistStep2.run_bind_snd, guard_snd_fsi]
  rcases ((_root_.guard (msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire) :
      Traceful Unit).run tr).1 with _ | ⟨⟩
  · rfl
  · dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift]; rw [Traceful.run_mk]

theorem trRecvFreshAllAt_decryptSkipped_next
    {r₀ : ProtocolSetup} {tr : ExecTrace} {me : Participant}
    {stateIdx msgIdx skIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    (hreach : ((Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).next tr).Reachable
      reachability)
    (hFreshAll : TRRecvFreshAllAt r₀ tr) :
    TRRecvFreshAllAt r₀ ((Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).next tr) := by
  revert hreach
  unfold Move.next Move.act
  rw [run_bind_pure_val]
  unfold messageDecryptSkipped
  rw [RecvHistStep2.run_bind_snd, getLocalState_snd]
  rcases hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 with _ | st
  · exact fun _ => hFreshAll
  · dsimp only
    rw [RecvHistStep2.run_bind_snd, receiveSignalMsg_snd_fsi]
    rcases ((receiveSignalMsg msgIdx).run tr).1 with _ | msg
    · exact fun _ => hFreshAll
    · dsimp only
      have hge_fst : ((DY.getEntry skIdx : Traceful TREntry).run tr).1 = (tr.at? skIdx : Option TREntry) := by
        rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
      have hge_snd : ((DY.getEntry skIdx : Traceful TREntry).run tr).2.val = tr := by
        rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
      rw [RecvHistStep2.run_bind_snd, hge_fst, hge_snd]
      rcases hsk : (tr.at? skIdx : Option TREntry) with _ | e
      · exact fun _ => hFreshAll
      · rcases e with ⟨ev⟩
        dsimp only
        cases ev with
        | SkippedKeyStored s pk n seed rIdx srcIdx =>
          dsimp only; rw [RecvHistStep2.run_bind_snd, guard_snd_fsi]
          by_cases hg : s = st.sessionInfo me ∧ pk = msg.ratchetKey ∧ n = msg.counter ∧ (TripleRatchet.findRecvChain st.toDRState.recv pk).isSome = true
          · rcases hg with ⟨rfl, rfl, rfl, hfc⟩
            have hg1 : ((_root_.guard (st.sessionInfo me = st.sessionInfo me ∧ msg.ratchetKey = msg.ratchetKey ∧ msg.counter = msg.counter ∧ (TripleRatchet.findRecvChain st.toDRState.recv msg.ratchetKey).isSome = true) : Traceful Unit).run tr).1 = some () := by
              simp only [_root_.guard, hfc, and_self, ↓reduceIte, Traceful.run_pure]
            rw [hg1]; dsimp only
            rw [RecvHistStep2.run_bind_snd, guardTrace_snd_fsi]
            rcases ((guardTrace fun tr => !skippedKeyUsedB tr skIdx).run tr).1 with _ | ⟨⟩
            · exact fun _ => hFreshAll
            · dsimp only
              rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
              · dsimp only; rw [Traceful.run_failure]; exact fun _ => hFreshAll
              · dsimp only
                let tr_k := tr.append (⟨key⟩ : Network.ExecEntryT)
                have hsm1 : ((DY.Network.sendMessage key).run tr).1 = some tr.length := by
                  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
                have hsm2 : ((DY.Network.sendMessage key).run tr).2.val = tr_k := by
                  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
                have hFresh_k : TRRecvFreshAllAt r₀ tr_k :=
                  trRecvFreshAllAt_append_non (⟨key⟩ : Network.ExecEntryT) rfl rfl hFreshAll
                rw [RecvHistStep2.run_bind_snd, hsm1, hsm2]; dsimp only
                rw [RecvHistStep2.run_bind_snd, receiveMessage_snd_fsi]
                rcases ((DY.Network.receiveMessage pqIdx).run tr_k).1 with _ | pqSalt
                · exact fun _ => hFresh_k
                · dsimp only
                  rw [RecvHistStep2.run_bind_snd, verifyMacAndDecrypt_snd_fsi]
                  rcases ((verifyMacAndDecrypt st msg pqSalt seed).run tr_k).1 with _ | ptTerm
                  · exact fun _ => hFresh_k
                  · dsimp only; unfold logMessageKeyAndStore
                    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
                      Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
                      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
                      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
                    exact fun hreach => trRecvFreshAllAt_decSkippedTr hFreshAll hst (by rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]) hreach
          · have hg0 : ((_root_.guard (s = st.sessionInfo me ∧ pk = msg.ratchetKey ∧ n = msg.counter ∧ (TripleRatchet.findRecvChain st.toDRState.recv pk).isSome = true) : Traceful Unit).run tr).1 = none := by
              simp only [_root_.guard, hg, ↓reduceIte, Traceful.run_failure]
            rw [hg0]; exact fun _ => hFreshAll
        | _ => dsimp only; rw [Traceful.run_failure]; exact fun _ => hFreshAll

theorem trRecvFreshAll_snoc_decryptSkipped
    {r₀ : ProtocolSetup} {ms : List Move} {me : Participant}
    {stateIdx msgIdx skIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    (hreach : (runTraceMoves r₀
      (ms ++ [Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped])).Reachable
      reachability)
    (hFreshAll : TRRecvFreshAll r₀ ms) :
    TRRecvFreshAll r₀
      (ms ++ [Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped]) := by
  change TRRecvFreshAllAt r₀
    (runTraceMoves r₀ (ms ++ [Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped]))
  rw [runTrace_snoc] at hreach ⊢
  exact trRecvFreshAllAt_decryptSkipped_next hreach hFreshAll

/-! ## `Move.decrypt` Freshness Preservation -/

theorem trRecvFreshAllAt_decTailTr_noRatchet
    {r₀ : ProtocolSetup} {tr : ExecTrace} {p : Participant} {stateIdx : Nat}
    {st : TRState} {c c' : RecvChain} {pk seed key pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    (hFreshAll : TRRecvFreshAllAt r₀ tr)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 = some st)
    (hNodupRk : (st.recv.map RecvChain.ratchetKey).Nodup)
    (hfind : findRecvChain st.recv pk = some c)
    (hcons : consumeMessageKey c n = some (seed, c'))
    (hreach : (decTailTr (tr.append (⟨key⟩ : Network.ExecEntryT)) p stateIdx st c c'
      pk seed pqSalt ptTerm spqr' n).Reachable reachability) :
    TRRecvFreshAllAt r₀
      (decTailTr (tr.append (⟨key⟩ : Network.ExecEntryT)) p stateIdx st c c'
        pk seed pqSalt ptTerm spqr' n) := by
  let tr_pre := tr.append (⟨key⟩ : Network.ExecEntryT)
  let st' : TRState := { st with recv := setRecvChain st.recv c', spqr := spqr' }
  let T := decTailTr tr_pre p stateIdx st c c' pk seed pqSalt ptTerm spqr' n
  let k := tr_pre.length + (n.toNat - c.index.toNat) + 2
  have hcur : isCurrentSnapshot tr stateIdx = true :=
    isCurrentSnapshot_of_decTailTr_reachable (Trace.append_le tr _) hst hreach
  have hle : tr ≤ T :=
    Trace.le_trans _ _ _ (Trace.append_le tr _)
      (decTailTr_le_rfb1 tr_pre p stateIdx st c c' pk seed pqSalt ptTerm spqr' n)
  have hk_at : (T.at? k : Option StEntry) = some ⟨⟨p, st'⟩⟩ :=
    at?_stEntry_decTailTr_last_rfb1 tr_pre p stateIdx st c c' pk seed pqSalt ptTerm spqr' n
  intro q j s hq_mem hget hcurj
  have hget' := at?_of_getLocalState_rfb1 hget
  have hjlt : j < T.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) T j
    rw [hget'] at this; exact this
  have hTlen : T.length = k + 1 := by
    dsimp only [T, k]
    rw [decTailTr_length]
  by_cases hjk : j = k
  · subst hjk
    rw [hk_at] at hget'
    injection hget' with hst_eq
    injection hst_eq with hinner
    injection hinner with hqp hs_eq
    subst hqp; subst hs_eq
    obtain ⟨hcf₀, hrel₀⟩ := hFreshAll p stateIdx st hq_mem hst hcur
    have hcf_pre : TRRecvCountersFresh tr_pre p st :=
      trRecvCountersFresh_of_imp
        (fun _ _ _ _ _ _ h => (eventLoggedAt_append_non_tr_rfb1 _ _ rfl _ _).mp h)
        (fun _ _ _ _ _ _ h => (eventLoggedAt_append_non_tr_rfb1 _ _ rfl _ _).mp h)
        hcf₀
    have hrel_pre : TRSkippedRIdxChainRel tr_pre p st :=
      trSkippedRIdxChainRel_of_imp
        (fun _ _ _ _ _ _ h => (eventLoggedAt_append_non_tr_rfb1 _ _ rfl _ _).mp h)
        hrel₀
    have hc_mem : c ∈ st.recv := List.mem_of_find?_eq_some hfind
    have hprops := consumeMessageKey_props hcons
    have hrk : c.ratchetKey = pk :=
      beq_iff_eq.mp (List.find?_some (p := fun x : RecvChain => x.ratchetKey == pk) hfind)
    have hrk' : c'.ratchetKey = c.ratchetKey := hprops.2.1
    have hrIdx' : c'.rIdx = c.rIdx := hprops.2.2.1
    have hcf_new : TRRecvCountersFresh T p st' :=
      trRecvCountersFresh_decTailTr_consumeMessageKey hcf_pre hc_mem hNodupRk hcons
        (consumeMessageKey_counter_lt_rfb1 hcons)
    have hrel_new : TRSkippedRIdxChainRel T p st' := by
      change TRSkippedRIdxChainRel
        (decTailTr tr_pre p stateIdx st c c' pk seed pqSalt ptTerm spqr' n) p st'
      rw [← hrk]
      exact trSkippedRIdxChainRel_decTailTr_existing hcf_pre hrel_pre hc_mem hrk' hrIdx'
    exact ⟨hcf_new, hrel_new⟩
  · have hjk_lt : j < k := by omega
    have hold_j : (T.at? j : Option StEntry) = (tr.at? j : Option StEntry) := by
      dsimp only [T, tr_pre]
      rw [at?_stEntry_decTailTr_lt_rfb1 _ _ _ _ _ _ _ _ _ _ _ _ hjk_lt,
          at?_append_non_entry _ _ rfl]
    have hj_tr : (tr.at? j : Option StEntry) = some ⟨⟨q, s⟩⟩ := hold_j.symm.trans hget'
    have hjlt₀ : j < tr.length := by
      have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr j
      rw [hj_tr] at this; exact this
    have hcur₀ : isCurrentSnapshot tr j = true :=
      isCurrentSnapshot_of_le_rfb1 hle hjlt₀ hcurj
    have hget₀ : ((PersistentLocalState.getLocalState q j : Traceful TRState).run tr).1 = some s := by
      rw [getLocalState_fst_rfb1, hj_tr]; simp
    obtain ⟨hcf_q, hrel_q⟩ := hFreshAll q j s hq_mem hget₀ hcur₀
    have hpi : p ≠ q ∨ st'.initiator ≠ s.initiator :=
      part_or_init_ne_of_current_rfb1 hcurj hget' hk_at hjk_lt
    have hsne : s.sessionInfo q ≠ st.sessionInfo p := sinfo_ne_of_part_or_init_ne_rfb1 hpi
    have hmk_imp : ∀ seed' pqSalt' n' r' pIdx' i,
        T.EventLoggedAt (TREvent.MessageKey (s.sessionInfo q) .receiver seed' pqSalt' n' r' pIdx') i →
        tr.EventLoggedAt (TREvent.MessageKey (s.sessionInfo q) .receiver seed' pqSalt' n' r' pIdx') i := by
      intro seed' pqSalt' n' r' pIdx' i hl
      rcases eventLoggedAt_decTailTr_messageKey_rfb1 hl with hPre | ⟨hs_eq, _⟩
      · exact (eventLoggedAt_append_non_tr_rfb1 _ _ rfl _ _).mp hPre
      · exact False.elim (hsne hs_eq)
    have hsk_imp : ∀ pk' n' seed' r' src' i,
        T.EventLoggedAt (TREvent.SkippedKeyStored (s.sessionInfo q) pk' n' seed' r' src') i →
        tr.EventLoggedAt (TREvent.SkippedKeyStored (s.sessionInfo q) pk' n' seed' r' src') i := by
      intro pk' n' seed' r' src' i hl
      rcases eventLoggedAt_decTailTr_skippedKeyStored_rfb1 hl with hPre | ⟨_, _, hs_eq, _⟩
      · exact (eventLoggedAt_append_non_tr_rfb1 _ _ rfl _ _).mp hPre
      · exact False.elim (hsne hs_eq)
    exact ⟨trRecvCountersFresh_of_imp hmk_imp hsk_imp hcf_q,
           trSkippedRIdxChainRel_of_imp hsk_imp hrel_q⟩

theorem trRecvFreshAllAt_decTailTr_ratchet
    {r₀ : ProtocolSetup} {tr : ExecTrace} {p : Participant} {stateIdx : Nat}
    {st : TRState} {c' : RecvChain} {pk seed key pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    (hFreshAll : TRRecvFreshAllAt r₀ tr)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 = some st)
    (hNodupRk : (st.recv.map RecvChain.ratchetKey).Nodup)
    (hfind : findRecvChain st.recv pk = none)
    (hcons : consumeMessageKey (trDhRatchetState st pk tr.length).2 n = some (seed, c'))
    (hreach : (decTailTr (decRatchetPreTr tr p (trDhRatchetState st pk tr.length).1 pk key)
      p stateIdx (trDhRatchetState st pk tr.length).1 (trDhRatchetState st pk tr.length).2 c'
      pk seed pqSalt ptTerm spqr' n).Reachable reachability) :
    TRRecvFreshAllAt r₀
      (decTailTr (decRatchetPreTr tr p (trDhRatchetState st pk tr.length).1 pk key)
        p stateIdx (trDhRatchetState st pk tr.length).1 (trDhRatchetState st pk tr.length).2 c'
        pk seed pqSalt ptTerm spqr' n) := by
  let st1 := (trDhRatchetState st pk tr.length).1
  let c := (trDhRatchetState st pk tr.length).2
  let tr_pre := decRatchetPreTr tr p st1 pk key
  let st' : TRState := { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }
  let T := decTailTr tr_pre p stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n
  let k := tr_pre.length + (n.toNat - c.index.toNat) + 2
  have hcur : isCurrentSnapshot tr stateIdx = true :=
    isCurrentSnapshot_of_decTailTr_reachable (decRatchetPreTr_le_rfb1 tr p st1 pk key) hst hreach
  have hle : tr ≤ T :=
    Trace.le_trans _ _ _ (decRatchetPreTr_le_rfb1 tr p st1 pk key)
      (decTailTr_le_rfb1 tr_pre p stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n)
  have hk_at : (T.at? k : Option StEntry) = some ⟨⟨p, st'⟩⟩ :=
    at?_stEntry_decTailTr_last_rfb1 tr_pre p stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n
  intro q j s hq_mem hget hcurj
  have hget' := at?_of_getLocalState_rfb1 hget
  have hjlt : j < T.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) T j
    rw [hget'] at this; exact this
  have hTlen : T.length = k + 1 := by
    dsimp only [T, k]
    rw [decTailTr_length]
  by_cases hjk : j = k
  · subst hjk
    rw [hk_at] at hget'
    injection hget' with hst_eq
    injection hst_eq with hinner
    injection hinner with hqp hs_eq
    subst hqp; subst hs_eq
    obtain ⟨hcf₀, hrel₀⟩ := hFreshAll p stateIdx st hq_mem hst hcur
    have hrk' : c'.ratchetKey = c.ratchetKey := consumeMessageKey_ratchetKey_rfb1 hcons
    have hrIdx' : c'.rIdx = st.rIdx + 2 := (consumeMessageKey_rIdx_eq_rfb1 hcons).trans rfl
    have hcf_new : TRRecvCountersFresh T p st' :=
      trRecvCountersFresh_decTailTr_ratchet_consumeMessageKey hcf₀ hNodupRk hfind hcons
        (consumeMessageKey_counter_lt_rfb1 hcons)
    have hrel_new : TRSkippedRIdxChainRel T p st' := by
      refine trSkippedRIdxChainRel_ratchet hcf₀ hrel₀ hrk' rfl hrIdx' rfl (fun d hd => ?_)
      rcases mem_setRecvChain_iff_of_nodup_rfb1 hd hrk' with h | ⟨hd1, hdc⟩
      · exact Or.inl h
      · rcases mem_trDhRatchetState_recv hd1 with h | h
        · exact Or.inr h
        · exact absurd h hdc
    exact ⟨hcf_new, hrel_new⟩
  · have hjk_lt : j < k := by omega
    have hold_j : (T.at? j : Option StEntry) = (tr.at? j : Option StEntry) := by
      dsimp only [T, tr_pre]
      rw [at?_stEntry_decTailTr_lt_rfb1 _ _ _ _ _ _ _ _ _ _ _ _ hjk_lt,
          at?_stEntry_decRatchetPreTr_rfb1]
    have hj_tr : (tr.at? j : Option StEntry) = some ⟨⟨q, s⟩⟩ := hold_j.symm.trans hget'
    have hjlt₀ : j < tr.length := by
      have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr j
      rw [hj_tr] at this; exact this
    have hcur₀ : isCurrentSnapshot tr j = true :=
      isCurrentSnapshot_of_le_rfb1 hle hjlt₀ hcurj
    have hget₀ : ((PersistentLocalState.getLocalState q j : Traceful TRState).run tr).1 = some s := by
      rw [getLocalState_fst_rfb1, hj_tr]; simp
    obtain ⟨hcf_q, hrel_q⟩ := hFreshAll q j s hq_mem hget₀ hcur₀
    have hpi : p ≠ q ∨ st'.initiator ≠ s.initiator :=
      part_or_init_ne_of_current_rfb1 hcurj hget' hk_at hjk_lt
    have hsne : s.sessionInfo q ≠ st1.sessionInfo p := sinfo_ne_of_part_or_init_ne_rfb1 hpi
    have hmk_imp : ∀ seed' pqSalt' n' r' pIdx' i,
        T.EventLoggedAt (TREvent.MessageKey (s.sessionInfo q) .receiver seed' pqSalt' n' r' pIdx') i →
        tr.EventLoggedAt (TREvent.MessageKey (s.sessionInfo q) .receiver seed' pqSalt' n' r' pIdx') i := by
      intro seed' pqSalt' n' r' pIdx' i hl
      rcases eventLoggedAt_decTailTr_messageKey_rfb1 hl with hPre | ⟨hs_eq, _⟩
      · exact eventLoggedAt_decRatchetPreTr_messageKey_rfb1 hPre
      · exact False.elim (hsne hs_eq)
    have hsk_imp : ∀ pk' n' seed' r' src' i,
        T.EventLoggedAt (TREvent.SkippedKeyStored (s.sessionInfo q) pk' n' seed' r' src') i →
        tr.EventLoggedAt (TREvent.SkippedKeyStored (s.sessionInfo q) pk' n' seed' r' src') i := by
      intro pk' n' seed' r' src' i hl
      rcases eventLoggedAt_decTailTr_skippedKeyStored_rfb1 hl with hPre | ⟨_, _, hs_eq, _⟩
      · exact eventLoggedAt_decRatchetPreTr_skippedKeyStored_rfb1 hPre
      · exact False.elim (hsne hs_eq)
    exact ⟨trRecvCountersFresh_of_imp hmk_imp hsk_imp hcf_q,
           trSkippedRIdxChainRel_of_imp hsk_imp hrel_q⟩

theorem trRecvFreshAllAt_decrypt_next
    {r₀ : ProtocolSetup} {tr : ExecTrace} {me : Participant}
    {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    (hNodup : ∀ st,
      ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st →
      (st.recv.map RecvChain.ratchetKey).Nodup)
    (hreach : ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr).Reachable
      reachability)
    (hFreshAll : TRRecvFreshAllAt r₀ tr) :
    TRRecvFreshAllAt r₀ ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) := by
  revert hreach
  unfold Move.next Move.act
  rw [run_bind_pure_val]
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  rw [RecvHistStep2.run_bind_snd, getLocalState_snd]
  rcases hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 with _ | st
  · exact fun _ => hFreshAll
  · have hNodupRk : (st.recv.map RecvChain.ratchetKey).Nodup := hNodup st hst
    dsimp only
    rw [RecvHistStep2.run_bind_snd, receiveSignalMsg_snd_fsi]
    rcases ((receiveSignalMsg msgIdx).run tr).1 with _ | msg
    · exact fun _ => hFreshAll
    · dsimp only
      rcases hfind : findRecvChain st.recv msg.ratchetKey with _ | c
      · by_cases hlow : x25519LowOrder msg.ratchetKey = false
        · obtain ⟨hens1, hens2⟩ := RecvDec.ensureReceiverChain_run_ratchet tr hfind hlow
          let st1 := (trDhRatchetState st msg.ratchetKey tr.length).1
          let c := (trDhRatchetState st msg.ratchetKey tr.length).2
          let tr_r := tr.append (⟨32⟩ : DY.Random.ExecEntryT)
          have hFresh_r : TRRecvFreshAllAt r₀ tr_r :=
            trRecvFreshAllAt_append_non (⟨32⟩ : DY.Random.ExecEntryT) rfl rfl hFreshAll
          rw [RecvHistStep2.run_bind_snd, hens1, hens2]
          dsimp only
          rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
          · dsimp only; rw [Traceful.run_failure]; exact fun _ => hFresh_r
          · dsimp only
            rcases Spqr.spqrRecv st1.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
            · dsimp only; rw [Traceful.run_failure]; exact fun _ => hFresh_r
            · dsimp only
              let tr_rk := tr_r.append (⟨key⟩ : Network.ExecEntryT)
              have hsm1 : ((DY.Network.sendMessage key).run tr_r).1 = some tr_r.length := by
                rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
              have hsm2 : ((DY.Network.sendMessage key).run tr_r).2.val = tr_rk := by
                rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
              have hFresh_rk : TRRecvFreshAllAt r₀ tr_rk :=
                trRecvFreshAllAt_append_non (⟨key⟩ : Network.ExecEntryT) rfl rfl hFresh_r
              rw [RecvHistStep2.run_bind_snd, hsm1, hsm2]; dsimp only
              rw [RecvHistStep2.run_bind_snd, receiveMessage_snd_fsi]
              rcases ((DY.Network.receiveMessage pqIdx).run tr_rk).1 with _ | pqSalt
              · exact fun _ => hFresh_rk
              · dsimp only
                rw [RecvHistStep2.run_bind_snd, verifyMacAndDecrypt_snd_fsi]
                rcases ((verifyMacAndDecrypt st1 msg pqSalt seed).run tr_rk).1 with _ | ptTerm
                · exact fun _ => hFresh_rk
                · dsimp only; simp only [↓reduceIte]
                  obtain ⟨hsk1, hsk2⟩ := RecvDec.logSkippedKeys_run (st1.sessionInfo me) msg.ratchetKey
                    c.rIdx stateIdx c.chainKey c.index (msg.counter.toNat - c.index.toNat)
                    (decRatchetPreTr tr me st1 msg.ratchetKey key)
                  have htail : ((do
                      ProtocolEvent.logEvent (TREvent.DHRatchet me st1.peer msg.ratchetKey
                        (DY.DiffieHellman.dhPk st1.dhs))
                      ProtocolEvent.logEvent (TREvent.HonestDH (st1.sessionInfo me) st1.dhs (st1.rIdx - 2))
                      logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
                        (msg.counter.toNat - c.index.toNat)
                      ProtocolEvent.logEvent (TREvent.Received me st1.peer msg.ratchetKey msg.counter ptTerm)
                      logMessageKeyAndStore me (st1.sessionInfo me) .receiver seed pqSalt
                        msg.counter c.rIdx stateIdx
                        { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }).run tr_rk).2.val =
                    decTailTr (decRatchetPreTr tr me st1 msg.ratchetKey key) me stateIdx st1 c c'
                      msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter := by
                    have hle_run : ∀ (ev : TREvent) (t : ExecTrace),
                        ((ProtocolEvent.logEvent ev).run t).1 = some () ∧
                        ((ProtocolEvent.logEvent ev).run t).2.val = t.append (⟨ev⟩ : TREntry) := fun ev t => by
                      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
                        Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure, and_self]
                    rw [RecvHistStep2.run_bind_snd, (hle_run _ _).1, (hle_run _ _).2]; dsimp only
                    rw [RecvHistStep2.run_bind_snd, (hle_run _ _).1, (hle_run _ _).2]; dsimp only
                    change (((logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey
                      c.index (msg.counter.toNat - c.index.toNat) >>= _).run
                        (decRatchetPreTr tr me st1 msg.ratchetKey key)).2.val) = _
                    rw [RecvHistStep2.run_bind_snd, hsk1, hsk2]; dsimp only
                    unfold logMessageKeyAndStore
                    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
                      Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
                      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
                      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]; rfl
                  rw [htail]; intro hreach
                  exact trRecvFreshAllAt_decTailTr_ratchet hFreshAll hst hNodupRk hfind hcons hreach
        · have hlow_true : x25519LowOrder msg.ratchetKey = true := by
            cases h : x25519LowOrder msg.ratchetKey
            · exact absurd h hlow
            · rfl
          have hens_fail : ((ensureReceiverChain st msg.ratchetKey).run tr).1 = none ∧
              ((ensureReceiverChain st msg.ratchetKey).run tr).2.val = tr := by
            simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold DY.Libsignal.TripleRatchet.recvChainFor TRState.toDRState
            dsimp only; rw [hfind]; simp only [hlow_true, ↓reduceIte, Traceful.run_failure, and_self]
          rw [RecvHistStep2.run_bind_snd, hens_fail.1, hens_fail.2]
          exact fun _ => hFreshAll
      · obtain ⟨hens1, hens2⟩ := RecvDec.ensureReceiverChain_run_noRatchet tr hfind
        rw [RecvHistStep2.run_bind_snd, hens1, hens2]; dsimp only
        rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
        · dsimp only; rw [Traceful.run_failure]; exact fun _ => hFreshAll
        · dsimp only
          rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
          · dsimp only; rw [Traceful.run_failure]; exact fun _ => hFreshAll
          · dsimp only
            let tr_k := tr.append (⟨key⟩ : Network.ExecEntryT)
            have hsm1 : ((DY.Network.sendMessage key).run tr).1 = some tr.length := by
              rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
            have hsm2 : ((DY.Network.sendMessage key).run tr).2.val = tr_k := by
              rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
            have hFresh_k : TRRecvFreshAllAt r₀ tr_k :=
              trRecvFreshAllAt_append_non (⟨key⟩ : Network.ExecEntryT) rfl rfl hFreshAll
            rw [RecvHistStep2.run_bind_snd, hsm1, hsm2]; dsimp only
            rw [RecvHistStep2.run_bind_snd, receiveMessage_snd_fsi]
            rcases ((DY.Network.receiveMessage pqIdx).run tr_k).1 with _ | pqSalt
            · exact fun _ => hFresh_k
            · dsimp only
              rw [RecvHistStep2.run_bind_snd, verifyMacAndDecrypt_snd_fsi]
              rcases ((verifyMacAndDecrypt st msg pqSalt seed).run tr_k).1 with _ | ptTerm
              · exact fun _ => hFresh_k
              · dsimp only; simp only [Bool.false_eq_true, ↓reduceIte]
                obtain ⟨hsk1, hsk2⟩ := RecvDec.logSkippedKeys_run (st.sessionInfo me) msg.ratchetKey
                  c.rIdx stateIdx c.chainKey c.index (msg.counter.toNat - c.index.toNat) tr_k
                rw [RecvHistStep2.run_bind_snd, hsk1, hsk2]; dsimp only
                unfold logMessageKeyAndStore
                simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
                  Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
                  Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
                  Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
                exact fun hreach => trRecvFreshAllAt_decTailTr_noRatchet hFreshAll hst hNodupRk hfind hcons hreach

theorem trRecvFreshAll_snoc_decrypt
    {r₀ : ProtocolSetup} {ms : List Move} {me : Participant}
    {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    (hNodup : ∀ st,
      ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run (runTraceMoves r₀ ms)).1 = some st →
      (st.recv.map RecvChain.ratchetKey).Nodup)
    (hreach : (runTraceMoves r₀
      (ms ++ [Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped])).Reachable
      reachability)
    (hFreshAll : TRRecvFreshAll r₀ ms) :
    TRRecvFreshAll r₀
      (ms ++ [Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) := by
  change TRRecvFreshAllAt r₀
    (runTraceMoves r₀ (ms ++ [Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped]))
  rw [runTrace_snoc] at hreach ⊢
  exact trRecvFreshAllAt_decrypt_next hNodup hreach hFreshAll

/-! ## `encrypt`, `encryptAbort`, `encryptFail`, and Exposure Freshness Preservation -/

theorem trRecvFreshAllAt_append_tr_other {r₀ : ProtocolSetup} {tr : ExecTrace} (ev : TREvent)
    (hNoMK : ∀ sinfo seed pqSalt n r pIdx,
      ev ≠ TREvent.MessageKey sinfo .receiver seed pqSalt n r pIdx)
    (hNoSK : ∀ sinfo pk n seed r srcIdx,
      ev ≠ TREvent.SkippedKeyStored sinfo pk n seed r srcIdx)
    (h : TRRecvFreshAllAt r₀ tr) : TRRecvFreshAllAt r₀ (tr.append (⟨ev⟩ : TREntry)) := by
  intro q stateIdx st hq hget hcur
  rw [getLocalState_fst, at?_append_non_entry _ (⟨ev⟩ : TREntry) rfl, ← getLocalState_fst] at hget
  rw [isCurrentSnapshot_append_non_st _ (⟨ev⟩ : TREntry) rfl] at hcur
  obtain ⟨hcf, hsk⟩ := h q stateIdx st hq hget hcur
  exact ⟨trRecvCountersFresh_append_trEntry_other_fsi (hNoMK (st.sessionInfo q)) (hNoSK (st.sessionInfo q)) hcf,
    trSkippedRIdxChainRel_of_imp
      (fun pk n seed r srcIdx i hlog =>
        ((eventLoggedAt_append_trEntry_iff_rfb1 tr ⟨ev⟩ _ i).mp hlog).elim id
          fun ⟨_, heq⟩ => False.elim (hNoSK (st.sessionInfo q) pk n seed r srcIdx heq))
      hsk⟩

theorem trRecvFreshAllAt_append_store {r₀ : ProtocolSetup} {tr : ExecTrace} (p : Participant) (st' : TRState)
    (hcf' : (p = r₀.alice ∨ p = r₀.bob) → TRRecvCountersFresh tr p st')
    (hsk' : (p = r₀.alice ∨ p = r₀.bob) → TRSkippedRIdxChainRel tr p st')
    (h : TRRecvFreshAllAt r₀ tr) : TRRecvFreshAllAt r₀ (tr.append (⟨⟨p, st'⟩⟩ : StEntry)) := by
  intro q idx st_q hq hget hcur
  have hle : tr ≤ tr.append (⟨⟨p, st'⟩⟩ : StEntry) := Trace.append_le tr _
  have hcf_up : ∀ {q' st''}, TRRecvCountersFresh tr q' st'' →
      TRRecvCountersFresh (tr.append (⟨⟨p, st'⟩⟩ : StEntry)) q' st'' := fun hc =>
    trRecvCountersFresh_of_imp
      (fun _ _ _ _ _ i hev => (eventLoggedAt_append_non_tr_rfb1 tr _ rfl _ i).mp hev)
      (fun _ _ _ _ _ i hev => (eventLoggedAt_append_non_tr_rfb1 tr _ rfl _ i).mp hev) hc
  have hsk_up : ∀ {q' st''}, TRSkippedRIdxChainRel tr q' st'' →
      TRSkippedRIdxChainRel (tr.append (⟨⟨p, st'⟩⟩ : StEntry)) q' st'' := fun hs =>
    trSkippedRIdxChainRel_of_imp
      (fun _ _ _ _ _ i hev => (eventLoggedAt_append_non_tr_rfb1 tr _ rfl _ i).mp hev) hs
  rcases getLocalState_append_stEntry_ne_or_old (tr := tr) (fun _ => rfl) p st' q idx st_q hget with
    ⟨rfl, _, rfl⟩ | hold
  · exact ⟨hcf_up (hcf' hq), hsk_up (hsk' hq)⟩
  · have hlt : idx < tr.length := by
      have h_at := at?_of_getLocalState_rfb1 hold
      have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr idx
      rw [h_at] at this; exact this
    have hcur₀ : isCurrentSnapshot tr idx = true :=
      isCurrentSnapshot_of_le_rfb1 hle hlt hcur
    obtain ⟨hcf, hsk⟩ := h q idx st_q hq hold hcur₀
    exact ⟨hcf_up hcf, hsk_up hsk⟩

private theorem isCurrentSnapshot_of_enc7_reachable
    {tr : ExecTrace} {p : Participant} {stateIdx ptLen coinsLen rIdx : Nat}
    {st st' : TRState} {key pqSalt seed ptTerm msgOut pk : DY.Bytes} {n : UInt32}
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 = some st)
    (hreach :
      (let tr4 := (((tr.append (⟨ptLen⟩ : DY.Random.ExecEntryT)).append
        (⟨coinsLen⟩ : DY.Random.ExecEntryT)).append
        (⟨key⟩ : DY.Network.ExecEntryT)).append
        (⟨TREvent.Sent p st.peer pk n ptTerm⟩ : TREntry)
      (((tr4.append
        (⟨TREvent.MessageKey (st.sessionInfo p) .sender seed pqSalt n rIdx stateIdx⟩ : TREntry)).append
        (⟨⟨p, st'⟩⟩ : StEntry)).append
        (⟨msgOut⟩ : DY.Network.ExecEntryT))).Reachable reachability) :
    isCurrentSnapshot tr stateIdx = true := by
  have hat_st : (tr.at? stateIdx : Option StEntry) = some ⟨⟨p, st⟩⟩ := at?_of_getLocalState_rfb1 hst
  have hplt : stateIdx < tr.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr stateIdx
    rw [hat_st] at this; exact this
  let tr4 := (((tr.append (⟨ptLen⟩ : DY.Random.ExecEntryT)).append
    (⟨coinsLen⟩ : DY.Random.ExecEntryT)).append
    (⟨key⟩ : DY.Network.ExecEntryT)).append
    (⟨TREvent.Sent p st.peer pk n ptTerm⟩ : TREntry)
  let ev := TREvent.MessageKey (st.sessionInfo p) .sender seed pqSalt n rIdx stateIdx
  let tr5 := tr4.append (⟨ev⟩ : TREntry)
  let tr6 := tr5.append (⟨⟨p, st'⟩⟩ : StEntry)
  let T := tr6.append (⟨msgOut⟩ : DY.Network.ExecEntryT)
  have hle_tr4 : tr ≤ tr4 :=
    Trace.le_trans _ _ _
      (Trace.le_trans _ _ _
        (Trace.le_trans _ _ _ (Trace.append_le tr _) (Trace.append_le _ _))
        (Trace.append_le _ _))
      (Trace.append_le _ _)
  have hle_T : tr ≤ T :=
    Trace.le_trans _ _ _ hle_tr4
      (Trace.le_trans _ _ _
        (Trace.le_trans _ _ _ (Trace.append_le tr4 _) (Trace.append_le _ _))
        (Trace.append_le _ _))
  have hlen_tr4 : tr.length ≤ tr4.length := Trace.length_le _ _ hle_tr4
  have hlog : T.EventLoggedAt ev tr4.length := by
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; dsimp only [T, tr6, tr5]
    rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl]
    exact Trace.at?_append tr4 (⟨ev⟩ : TREntry)
  have hInv : MessageKeyCurrentInv T := messageKeyCurrentInv_reachable hreach
  have hne : stateIdx ≠ tr4.length + 1 := by omega
  exact isCurrentSnapshot_of_isCurrentSnapshotBefore hle_T hlen_tr4 hplt
    (hInv (st.sessionInfo p) .sender seed pqSalt n rIdx stateIdx tr4.length hlog hne)

theorem trRecvFreshAll_snoc_encrypt_reach
    {r₀ : ProtocolSetup} {ms₁ : List Move}
    (p : Participant) (stateIdx coinsLen pqIdx : Nat)
    (wrap : Option (Nat × Nat) := none)
    (hreach : (runTraceMoves r₀ (ms₁ ++ [Move.encrypt p stateIdx coinsLen pqIdx wrap])).Reachable
      reachability)
    (h : TRRecvFreshAll r₀ ms₁) :
    TRRecvFreshAll r₀ (ms₁ ++ [Move.encrypt p stateIdx coinsLen pqIdx wrap]) := by
  change TRRecvFreshAllAt r₀ (runTraceMoves r₀ (ms₁ ++ [Move.encrypt p stateIdx coinsLen pqIdx wrap]))
  rw [runTrace_snoc] at hreach ⊢
  set tr := runTraceMoves r₀ ms₁
  have hFresh₀ : TRRecvFreshAllAt r₀ tr := h
  revert hreach
  unfold Move.next Move.act; rw [run_bind_pure_val]
  unfold messageEncrypt
  rw [RecvHistStep2.run_bind_snd, getLocalState_snd]
  rcases hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 with _ | st
  · exact fun _ => hFresh₀
  · dsimp only
    rw [RecvHistStep2.run_bind_snd, guard_snd_fsi]
    rcases ((_root_.guard (st.ns ≠ TripleRatchet.u32Max) : Traceful Unit).run tr).1 with _ | ⟨⟩
    · exact fun _ => hFresh₀
    · dsimp only
      let tr1 := tr.append (⟨32⟩ : DY.Random.ExecEntryT)
      let tr2 := tr1.append (⟨coinsLen⟩ : DY.Random.ExecEntryT)
      let key := (Spqr.spqrSend st.spqr (randTerm (tr.length + 1) coinsLen)).2.1
      let tr3 := tr2.append (⟨key⟩ : DY.Network.ExecEntryT)
      have hr1_1 : ((DY.Random.genRand 32).run tr).1 = some (randTerm tr.length 32) := by
        simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure, randTerm]
      have hr1_2 : ((DY.Random.genRand 32).run tr).2.val = tr1 := by
        simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]; rfl
      have hr2_1 : ((DY.Random.genRand coinsLen).run tr1).1 = some (randTerm (tr.length + 1) coinsLen) := by
        simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure, randTerm]
        dsimp only [tr1]; rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      have hr2_2 : ((DY.Random.genRand coinsLen).run tr1).2.val = tr2 := by
        simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]; rfl
      have hsm_1 : ((DY.Network.sendMessage key).run tr2).1 = some tr2.length := by
        rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
      have hsm_2 : ((DY.Network.sendMessage key).run tr2).2.val = tr3 := by
        rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
      have hFresh₃ : TRRecvFreshAllAt r₀ tr3 :=
        trRecvFreshAllAt_append_non (⟨key⟩ : DY.Network.ExecEntryT) rfl rfl
          (trRecvFreshAllAt_append_non (⟨coinsLen⟩ : DY.Random.ExecEntryT) rfl rfl
            (trRecvFreshAllAt_append_non (⟨32⟩ : DY.Random.ExecEntryT) rfl rfl hFresh₀))
      rw [RecvHistStep2.run_bind_snd, hr1_1, hr1_2]; dsimp only
      rw [RecvHistStep2.run_bind_snd, hr2_1, hr2_2]; dsimp only
      rw [RecvHistStep2.run_bind_snd, hsm_1, hsm_2]; dsimp only
      rw [RecvHistStep2.run_bind_snd, receiveMessage_snd_fsi]
      rcases ((DY.Network.receiveMessage pqIdx).run tr3).1 with _ | pqSalt
      · exact fun _ => hFresh₃
      · dsimp only; unfold logMessageKeyAndStore
        simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
        intro hreach
        let m := randTerm tr.length 32
        let coins := randTerm (tr.length + 1) coinsLen
        let spqr' := (Spqr.spqrSend st.spqr coins).1
        let pqMsg := (Spqr.spqrSend st.spqr coins).2.2
        let ck' := (kdfCk st.cks).1
        let seed := (kdfCk st.cks).2
        let keys := trMsgKeys pqSalt seed
        let wire := trHonestWireMsg (DY.DiffieHellman.dhPk st.dhs) st.ns st.pn
          (DY.SymEnc.symEnc keys.cipherKey keys.iv m) pqMsg
        let mac := computeMac keys.macKey st.myIk st.peerIk wire
        let pk := DY.DiffieHellman.dhPk st.dhs
        let tr4 := tr3.append (⟨TREvent.Sent p st.peer pk st.ns m⟩ : TREntry)
        let tr5 := tr4.append
          (⟨TREvent.MessageKey (st.sessionInfo p) .sender seed pqSalt st.ns st.rIdx stateIdx⟩ : TREntry)
        let st' : TRState := { st with cks := ck', ns := st.ns + 1, spqr := spqr' }
        have hcur : isCurrentSnapshot tr stateIdx = true :=
          isCurrentSnapshot_of_enc7_reachable hst hreach
        have hFresh₄ : TRRecvFreshAllAt r₀ tr4 :=
          trRecvFreshAllAt_append_tr_other _
            (fun _ _ _ _ _ _ h => by nomatch h)
            (fun _ _ _ _ _ _ h => by nomatch h) hFresh₃
        have hFresh₅ : TRRecvFreshAllAt r₀ tr5 :=
          trRecvFreshAllAt_append_tr_other _
            (fun _ _ _ _ _ _ h => by nomatch h)
            (fun _ _ _ _ _ _ h => by nomatch h) hFresh₄
        have hget₅ : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr5).1 =
            some st := by
          dsimp only [tr5, tr4, tr3, tr2, tr1]
          rw [getLocalState_fst,
              at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
              at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
              at?_append_non_entry _ _ rfl, ← getLocalState_fst]
          exact hst
        have hcur₅ : isCurrentSnapshot tr5 stateIdx = true := by
          dsimp only [tr5, tr4, tr3, tr2, tr1]
          rw [isCurrentSnapshot_append_non_st _ _ rfl, isCurrentSnapshot_append_non_st _ _ rfl,
              isCurrentSnapshot_append_non_st _ _ rfl, isCurrentSnapshot_append_non_st _ _ rfl,
              isCurrentSnapshot_append_non_st _ _ rfl]
          exact hcur
        have hFresh₆ : TRRecvFreshAllAt r₀ (tr5.append (⟨⟨p, st'⟩⟩ : StEntry)) :=
          trRecvFreshAllAt_append_store p st'
            (fun hp => (hFresh₅ p stateIdx st hp hget₅ hcur₅).1)
            (fun hp => (hFresh₅ p stateIdx st hp hget₅ hcur₅).2)
            hFresh₅
        exact trRecvFreshAllAt_append_non (⟨DY.Concat.concat wire mac⟩ : DY.Network.ExecEntryT) rfl rfl hFresh₆

theorem trRecvFreshAll_snoc_encryptAbort
    {r₀ : ProtocolSetup} {ms₁ : List Move} (p : Participant) (stateIdx : Nat)
    (h : TRRecvFreshAll r₀ ms₁) :
    TRRecvFreshAll r₀ (ms₁ ++ [Move.encryptAbort p stateIdx]) := by
  change TRRecvFreshAllAt r₀ (runTraceMoves r₀ (ms₁ ++ [Move.encryptAbort p stateIdx]))
  rw [runTrace_snoc]; set tr := runTraceMoves r₀ ms₁
  unfold Move.next Move.act; rw [run_bind_pure_val]; unfold messageEncryptAbort
  rw [RecvHistStep2.run_bind_snd, getLocalState_snd]
  rcases ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 with _ | st
  · exact h
  · dsimp only
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk, Traceful.run_pure, Traceful.run_failure]
    exact trRecvFreshAllAt_append_non (⟨32⟩ : DY.Random.ExecEntryT) rfl rfl h

theorem trRecvFreshAll_snoc_encryptFail
    {r₀ : ProtocolSetup} {ms₁ : List Move} (p : Participant) (stateIdx coinsLen : Nat)
    (h : TRRecvFreshAll r₀ ms₁) :
    TRRecvFreshAll r₀ (ms₁ ++ [Move.encryptFail p stateIdx coinsLen]) := by
  change TRRecvFreshAllAt r₀ (runTraceMoves r₀ (ms₁ ++ [Move.encryptFail p stateIdx coinsLen]))
  rw [runTrace_snoc]; set tr := runTraceMoves r₀ ms₁
  have htl1 : (TripleRatchet.traceLength.run tr).1 = some tr.length := by
    unfold TripleRatchet.traceLength; rw [Traceful.run_mk]
  have htl2 : (TripleRatchet.traceLength.run tr).2.val = tr := by
    unfold TripleRatchet.traceLength; rw [Traceful.run_mk]
  unfold Move.next Move.act; dsimp only
  rw [RecvHistStep2.run_bind_snd, htl1, htl2]; dsimp only
  rw [run_bind_pure_val]; unfold messageEncrypt
  rw [RecvHistStep2.run_bind_snd, getLocalState_snd]
  rcases ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 with _ | st
  · exact h
  · dsimp only; rw [RecvHistStep2.run_bind_snd, guard_snd_fsi]
    rcases ((_root_.guard (st.ns ≠ TripleRatchet.u32Max) : Traceful Unit).run tr).1 with _ | ⟨⟩
    · exact h
    · dsimp only
      let tr1 := tr.append (⟨32⟩ : DY.Random.ExecEntryT)
      let tr2 := tr1.append (⟨coinsLen⟩ : DY.Random.ExecEntryT)
      let key := (Spqr.spqrSend st.spqr (randTerm (tr.length + 1) coinsLen)).2.1
      let tr3 := tr2.append (⟨key⟩ : DY.Network.ExecEntryT)
      have hr1_1 : ((DY.Random.genRand 32).run tr).1 = some (randTerm tr.length 32) := by
        simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure, randTerm]
      have hr1_2 : ((DY.Random.genRand 32).run tr).2.val = tr1 := by
        simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]; rfl
      have hr2_1 : ((DY.Random.genRand coinsLen).run tr1).1 = some (randTerm (tr.length + 1) coinsLen) := by
        simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure, randTerm]
        dsimp only [tr1]; rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      have hr2_2 : ((DY.Random.genRand coinsLen).run tr1).2.val = tr2 := by
        simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]; rfl
      have hsm_1 : ((DY.Network.sendMessage key).run tr2).1 = some tr2.length := by
        rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
      have hsm_2 : ((DY.Network.sendMessage key).run tr2).2.val = tr3 := by
        rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
      have hnone : (tr3.at? (tr.length + 3) : Option DY.Network.ExecEntryT) = none :=
        at?_eq_none_of_le tr3 (by dsimp only [tr3, tr2, tr1]; simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)
      have hrm_1 : ((DY.Network.receiveMessage (tr.length + 3)).run tr3).1 = none := by
        simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_bind, Traceful.run_mk, hnone]
      rw [RecvHistStep2.run_bind_snd, hr1_1, hr1_2]; dsimp only
      rw [RecvHistStep2.run_bind_snd, hr2_1, hr2_2]; dsimp only
      rw [RecvHistStep2.run_bind_snd, hsm_1, hsm_2]; dsimp only
      rw [RecvHistStep2.run_bind_snd, hrm_1, receiveMessage_snd_fsi]; dsimp only
      exact trRecvFreshAllAt_append_non (⟨key⟩ : DY.Network.ExecEntryT) rfl rfl
        (trRecvFreshAllAt_append_non (⟨coinsLen⟩ : DY.Random.ExecEntryT) rfl rfl
          (trRecvFreshAllAt_append_non (⟨32⟩ : DY.Random.ExecEntryT) rfl rfl h))

theorem trRecvFreshAll_snoc_exposeKey
    {r₀ : ProtocolSetup} {ms₁ : List Move} (p : Participant) (stateIdx : Nat) (kc : KeyComponent)
    (h : TRRecvFreshAll r₀ ms₁) :
    TRRecvFreshAll r₀ (ms₁ ++ [Move.exposeKey p stateIdx kc]) := by
  change TRRecvFreshAllAt r₀ (runTraceMoves r₀ (ms₁ ++ [Move.exposeKey p stateIdx kc]))
  rw [runTrace_snoc]; set tr := runTraceMoves r₀ ms₁
  unfold Move.next Move.act; rw [run_bind_pure_val]; unfold exposeKey
  rw [RecvHistStep2.run_bind_snd, getLocalState_snd]
  rcases ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 with _ | st
  · exact h
  · dsimp only
    cases kc with
    | rk =>
      dsimp only; simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
      exact trRecvFreshAllAt_append_non (⟨st.rk⟩ : DY.Network.ExecEntryT) rfl rfl
        (trRecvFreshAllAt_append_tr_other _ (fun _ _ _ _ _ _ h => by nomatch h) (fun _ _ _ _ _ _ h => by nomatch h) h)
    | dhs =>
      dsimp only; simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
      exact trRecvFreshAllAt_append_non (⟨st.dhs⟩ : DY.Network.ExecEntryT) rfl rfl
        (trRecvFreshAllAt_append_tr_other _ (fun _ _ _ _ _ _ h => by nomatch h) (fun _ _ _ _ _ _ h => by nomatch h) h)
    | cks =>
      dsimp only; simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
      exact trRecvFreshAllAt_append_non (⟨st.cks⟩ : DY.Network.ExecEntryT) rfl rfl
        (trRecvFreshAllAt_append_tr_other _ (fun _ _ _ _ _ _ h => by nomatch h) (fun _ _ _ _ _ _ h => by nomatch h) h)
    | ckr pk =>
      dsimp only; rcases findRecvChain st.recv pk with _ | c
      · dsimp only; rw [Traceful.run_failure]; exact h
      · dsimp only; simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
        exact trRecvFreshAllAt_append_non (⟨c.chainKey⟩ : DY.Network.ExecEntryT) rfl rfl
          (trRecvFreshAllAt_append_tr_other _ (fun _ _ _ _ _ _ h => by nomatch h) (fun _ _ _ _ _ _ h => by nomatch h) h)

theorem trRecvFreshAll_snoc_exposeSpqr
    {r₀ : ProtocolSetup} {ms₁ : List Move} (p : Participant) (stateIdx : Nat)
    (h : TRRecvFreshAll r₀ ms₁) :
    TRRecvFreshAll r₀ (ms₁ ++ [Move.exposeSpqr p stateIdx]) := by
  change TRRecvFreshAllAt r₀ (runTraceMoves r₀ (ms₁ ++ [Move.exposeSpqr p stateIdx]))
  rw [runTrace_snoc]; set tr := runTraceMoves r₀ ms₁
  unfold Move.next Move.act; rw [run_bind_pure_val]; unfold exposeSpqr
  rw [RecvHistStep2.run_bind_snd, getLocalState_snd]
  rcases ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 with _ | st
  · exact h
  · dsimp only; simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
    exact trRecvFreshAllAt_append_non (⟨st.spqr⟩ : DY.Network.ExecEntryT) rfl rfl
      (trRecvFreshAllAt_append_tr_other _ (fun _ _ _ _ _ _ h => by nomatch h) (fun _ _ _ _ _ _ h => by nomatch h) h)

theorem trRecvFreshAll_snoc_exposeSkipped
    {r₀ : ProtocolSetup} {ms₁ : List Move} (skIdx : Nat)
    (h : TRRecvFreshAll r₀ ms₁) :
    TRRecvFreshAll r₀ (ms₁ ++ [Move.exposeSkipped skIdx]) := by
  change TRRecvFreshAllAt r₀ (runTraceMoves r₀ (ms₁ ++ [Move.exposeSkipped skIdx]))
  rw [runTrace_snoc]; set tr := runTraceMoves r₀ ms₁
  unfold Move.next Move.act; rw [run_bind_pure_val]; unfold exposeSkipped
  simp only [Traceful.run_bind, Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  split
  · simp only; split
    · simp only [Traceful.run_bind, guardTrace, Traceful.run_mk]; split
      · simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
        exact trRecvFreshAllAt_append_non (⟨_⟩ : DY.Network.ExecEntryT) rfl rfl
          (trRecvFreshAllAt_append_tr_other _ (fun _ _ _ _ _ _ h => by nomatch h) (fun _ _ _ _ _ _ h => by nomatch h) h)
      · exact h
    · rw [Traceful.run_failure]; dsimp only; rw [Traceful.run_mk]; exact h
  · dsimp only; exact h

end Symbolic.Swarm.CREF.TR
