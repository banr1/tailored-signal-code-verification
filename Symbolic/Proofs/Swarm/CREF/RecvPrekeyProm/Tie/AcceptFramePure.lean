/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.Tie.AcceptFramePureA
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.ProtocolEvent
import DY.Actions.Network
import DY.Actions.PersistentGlobalState
import DY.Actions.PersistentLocalState
import DY.Actions.Random
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Other-Participant Record Preservation Across Promoted Prekey Receive

Shows that `promRcvFrame` preserves `bobDoneBaseKeys` and `PureCRecRel` for any participant
`q ≠ p`, so `OneMove (RecvStep p blk)` leaves other participants' `PureCRecRel` intact.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.RecvPrekeyProm

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.COMPOSED
open DY.Libsignal.TripleRatchet (SessionInfo)
open DY.Libsignal.TripleRatchet (TRState TREvent)

private theorem prom_rcv_at?_lt {EntryT : Type} [DY.TraceEntryHas EntryT ExecTrace.Entry]
    {tr₀ tr : ExecTrace} (hle : tr₀ ≤ tr) {j : Nat} (hj : j < tr₀.length) :
    (tr.at? j : Option EntryT) = tr₀.at? j := by
  have hj' : j < tr.length := Nat.lt_of_lt_of_le hj (DY.Trace.length_le tr₀ tr hle)
  simp only [DY.Trace.at?, hj, hj', dite_true, DY.Trace.at_le tr₀ tr j hj hle]

private theorem promRcvFrame_getLocalState {p : Participant} {tr₀ tr : ExecTrace}
    (h : promRcvFrame p tr₀ tr) {q : Participant} {i : Nat} {st : TRState}
    (hget : ((DY.PersistentLocalState.getLocalState q i : Traceful TRState).run tr₀).1 = some st) :
    ((DY.PersistentLocalState.getLocalState q i : Traceful TRState).run tr).1 = some st := by
  rw [CompTrace.getLocalState_tr_fst] at hget ⊢
  rcases he : (tr₀.at? i : Option CompTrace.TRStEntry) with _ | e
  · rw [he] at hget; cases hget
  · rw [he] at hget
    rw [CompTrace.at?_le_some h.1 he]
    exact hget

private theorem promRcvFrame_isCurrentSnapshot {p : Participant} {tr₀ tr : ExecTrace}
    (h : promRcvFrame p tr₀ tr) {q : Participant} (hq : q ≠ p) {i : Nat} {st : TRState}
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
    have := DY.Trace.at?_eq_some_implies_length_le (EntryT := CompTrace.TRStEntry) tr₀ i
    rw [he] at this; exact this
  have hlen := DY.Trace.length_le tr₀ tr h.1
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur ⊢
  rw [CompTrace.at?_le_some h.1 he]
  rw [he] at hcur
  dsimp only at hcur ⊢
  rw [show tr.length - (i + 1) = (tr₀.length - (i + 1)) + (tr.length - tr₀.length) by omega,
    ← List.range'_append_1, List.all_append, Bool.and_eq_true]
  simp only [show i + 1 + (tr₀.length - (i + 1)) = tr₀.length by omega]
  refine ⟨Eq.trans (Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.q_all_congr_mem fun j hj => ?_) hcur, ?_⟩
  · rw [List.mem_range'_1] at hj
    rw [prom_rcv_at?_lt h.1 (by omega : j < tr₀.length)]
  · rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range'_1] at hj
    try dsimp only
    rcases hj' : (tr.at? j : Option CompTrace.TRStEntry) with _ | e'
    · rfl
    · have hp := (h.2 j (by omega)).1 e' hj'
      simp only [hp, Bool.or_eq_true, bne_iff_ne, ne_eq]
      exact Or.inl fun h' => hq (h'.trans hr).symm

private theorem promRcvFrame_eventLoggedAt {p : Participant} {tr₀ tr : ExecTrace}
    (h : promRcvFrame p tr₀ tr) {ev : TREvent} {i : Nat} (hl : tr₀.EventLoggedAt ev i) :
    tr.EventLoggedAt ev i := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hl ⊢
  exact CompTrace.at?_le_some h.1 hl

private theorem promRcvFrame_someEventOnTraceB {p : Participant} {tr₀ tr : ExecTrace}
    (h : promRcvFrame p tr₀ tr) (P : TREvent → Bool)
    (hP : ∀ ev, promRcvEv p tr₀ ev → P ev = false)
    (h0 : (TripleRatchet.anyEventOnTrace TripleRatchet.TREvent) tr₀ P = false) :
    (TripleRatchet.anyEventOnTrace TripleRatchet.TREvent) tr P = false := by
  simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h0 ⊢
  rw [List.any_eq_false] at h0 ⊢
  intro j hj hfj
  rw [List.mem_range] at hj
  try dsimp only at hfj
  by_cases hlt : j < tr₀.length
  · rw [prom_rcv_at?_lt h.1 hlt] at hfj
    exact h0 j (List.mem_range.mpr hlt) hfj
  · rcases he : (tr.at? j : Option CompTrace.TREntry) with _ | e
    · rw [he] at hfj; dsimp only at hfj; cases hfj
    · rw [he] at hfj
      dsimp only at hfj
      rw [hP e.ev ((h.2 j (by omega)).2.1 e he)] at hfj
      cases hfj

private theorem promRcvFrame_skippedKeyUsedB {p : Participant} {tr₀ tr : ExecTrace}
    (h : promRcvFrame p tr₀ tr) {q : Participant} (hq : q ≠ p) {st_q : TRState}
    {pk_q : DY.Bytes} {n_q : UInt32} {seed_q : DY.Bytes} {rIdx_q srcIdx_q k : Nat}
    (hlog : tr₀.EventLoggedAt (TREvent.SkippedKeyStored (st_q.sessionInfo q) pk_q n_q seed_q rIdx_q srcIdx_q) k)
    (hsu : (!TripleRatchet.skippedKeyUsedB tr₀ k) = true) :
    (!TripleRatchet.skippedKeyUsedB tr k) = true := by
  have h0 : TripleRatchet.skippedKeyUsedB tr₀ k = false := by simpa using hsu
  have h1 : TripleRatchet.skippedKeyUsedB tr k = false := by
    unfold TripleRatchet.skippedKeyUsedB at h0 ⊢
    refine promRcvFrame_someEventOnTraceB h _ (fun ev hev => ?_) h0
    cases ev with
    | SkippedKeyUsed s k' =>
      obtain ⟨hsme, _, _, _, _, _, hk'⟩ := hev
      refine beq_false_of_ne fun heq => ?_
      subst heq
      have hlog' : (tr₀.at? k' : Option CompTrace.TREntry) =
          some ⟨.SkippedKeyStored (st_q.sessionInfo q) pk_q n_q seed_q rIdx_q srcIdx_q⟩ := by
        rwa [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
      rw [hk'] at hlog'
      injection hlog' with hE
      injection hE with hEv
      injection hEv with hs _ _ _ _ _
      exact hq ((congrArg SessionInfo.me hs).symm.trans hsme)
    | _ => rfl
  simp [h1]

private theorem promRcvFrame_receiverKeyUsedB {p : Participant} {tr₀ tr : ExecTrace}
    (h : promRcvFrame p tr₀ tr) {q : Participant} (hq : q ≠ p) {st : TRState}
    {seed : DY.Bytes} {n : UInt32} {rIdx : Nat}
    (hru : (!TripleRatchet.receiverKeyUsedB tr₀ (st.sessionInfo q) seed n rIdx) = true) :
    (!TripleRatchet.receiverKeyUsedB tr (st.sessionInfo q) seed n rIdx) = true := by
  have h0 : TripleRatchet.receiverKeyUsedB tr₀ (st.sessionInfo q) seed n rIdx = false := by
    simpa using hru
  have h1 : TripleRatchet.receiverKeyUsedB tr (st.sessionInfo q) seed n rIdx = false := by
    unfold TripleRatchet.receiverKeyUsedB at h0 ⊢
    refine promRcvFrame_someEventOnTraceB h _ (fun ev hev => ?_) h0
    cases ev
    case MessageKey s' dir _ _ _ _ _ =>
      cases dir
      · rfl
      · exact decide_eq_false fun hc => hq ((congrArg SessionInfo.me hc.1).symm.trans hev)
    all_goals rfl
  simp [h1]

private theorem promRcvFrame_getMessageSentAt {p : Participant} {tr₀ tr : ExecTrace}
    (h : promRcvFrame p tr₀ tr) {i : Nat} {x : DY.Bytes} (hi : tr₀.getMessageSentAt i = some x) :
    tr.getMessageSentAt i = some x := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at hi ⊢
  have hlt : i < tr₀.length := by
    by_contra hge
    rw [Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.at?_none_of_ge (EntryT := DY.Network.ExecEntryT) (by omega : tr₀.length ≤ i)] at hi
    cases hi
  rw [prom_rcv_at?_lt (EntryT := DY.Network.ExecEntryT) h.1 hlt]; exact hi

private theorem promRcvFrame_trRecordStateInv {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {Z : TR.PureTRSlots} {g : Ghost} {ms ms' : List Move}
    {records : Participant → Option HwBytes} {p : Participant}
    (h : promRcvFrame p (runTraceMoves r ms) (runTraceMoves r ms'))
    (hrec : ∀ q bs, records q = some bs → q ≠ p)
    (hrsi : TR.PureTRRecordStateInv interpretation r S Z g ms records) :
    TR.PureTRRecordStateInv interpretation r S Z g ms' records := by
  intro q bs hqb
  have hqp := hrec q bs hqb
  obtain ⟨hq_mem, rec, st, stateIdx, hb, hget, hcur, hrel, hsk, hcanon, hks, hnd⟩ := hrsi q bs hqb
  refine ⟨hq_mem, rec, st, stateIdx, hb, promRcvFrame_getLocalState h hget,
    promRcvFrame_isCurrentSnapshot h hqp hget hcur, hrel, ?_, hcanon, hks, hnd⟩
  intro c hc k hk
  obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, hsu, hru, hgam, hsrk, hfind⟩ := hsk c hc k hk
  exact ⟨pk, rIdx, srcIdx, skIdx, seed, promRcvFrame_eventLoggedAt h hlog,
    promRcvFrame_skippedKeyUsedB h hqp hlog hsu, promRcvFrame_receiverKeyUsedB h hqp hru, hgam, hsrk, hfind⟩

private theorem promRcvFrame_aliceInitPending {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms ms' : List Move} {bs : HwBytes} {p : Participant}
    (h : promRcvFrame p (runTraceMoves r ms) (runTraceMoves r ms')) (hap : r.alice ≠ p)
    (hp : PureAliceInitPending interpretation r S g ms bs) :
    PureAliceInitPending interpretation r S g ms' bs := by
  obtain ⟨sess, sc, remote, items, kpk, st, stateIdx, ekIdx, ctIdx, ek, ct,
    h1, h2, h3, hget, hcur, h6, h7, hek, hct, rest⟩ := hp
  exact ⟨sess, sc, remote, items, kpk, st, stateIdx, ekIdx, ctIdx, ek, ct,
    h1, h2, h3, promRcvFrame_getLocalState h hget, promRcvFrame_isCurrentSnapshot h hap hget hcur,
    h6, h7, promRcvFrame_getMessageSentAt h hek, promRcvFrame_getMessageSentAt h hct, rest⟩

private theorem promRcvFrame_cRecRel {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms ms' : List Move} {p q : Participant} {bs : HwBytes}
    (h : promRcvFrame p (runTraceMoves r ms) (runTraceMoves r ms')) (hpq : q ≠ p)
    (hc : PureCRecRel interpretation r S g ms q bs) : PureCRecRel interpretation r S g ms' q bs := by
  rcases hc with hc | ⟨hqa, hc⟩
  · refine Or.inl (promRcvFrame_trRecordStateInv h (fun q' bs' hq' => ?_) hc)
    by_cases hqq' : q' = q
    · subst hqq'; exact hpq
    · simp [hqq'] at hq'
  · exact Or.inr ⟨hqa, promRcvFrame_aliceInitPending h (fun h' => hpq (hqa.trans h')) hc⟩

theorem promRcvFrame_bobDoneBaseKeys {p : Participant} {tr₀ tr : ExecTrace}
    (h : promRcvFrame p tr₀ tr) :
    bobDoneBaseKeys tr = bobDoneBaseKeys tr₀ := by
  exact Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.bobDoneBaseKeys_eq_of_nonSessionPQExt h.1
    fun i h1 _ => (h.2 i h1).2.2

/-- For `q ≠ p`, `PureCRecRel` for `q` is preserved across any `OneMove (RecvStep p blk)`. -/
theorem prom_rcv_frame_other {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {blk : List MachineEvent} {g : Ghost} {ms₀ δ : List Move}
    {p q : Participant} {bs : HwBytes}
    (hδ : OneMove (RecvStep p blk) (runTraceMoves r ms₀) δ)
    (hpq : q ≠ p) (hc : PureCRecRel interpretation r S g ms₀ q bs) :
    PureCRecRel interpretation r S g (ms₀ ++ δ) q bs := by
  obtain ⟨pre, m, post, rfl, hpre, ⟨hact, hrk, _⟩, hpost⟩ := hδ
  have hq1 : Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := by
    rw [TR.runTrace_append]
    exact Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)
  have c1 := Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_pureCRecRel hq1 hc
  have hf : promRcvFrame p (runTraceMoves r (ms₀ ++ pre)) (runTraceMoves r (ms₀ ++ pre ++ [m])) := by
    rw [TR.runTrace_snoc]
    rw [← TR.runTrace_append] at hrk
    exact prom_rcv_next_move hact hrk
  have c2 := promRcvFrame_cRecRel hf hpq c1
  have hq2 : Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.QuietExt (runTraceMoves r (ms₀ ++ pre ++ [m]))
      (runTraceMoves r (ms₀ ++ pre ++ [m] ++ post)) := by
    rw [TR.runTrace_append (ms₁ := ms₀ ++ pre ++ [m]), TR.runTrace_snoc, TR.runTrace_append]
    exact Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quietExt_of_movesFrom _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost)
  have c3 := Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_pureCRecRel hq2 c2
  rwa [show ms₀ ++ pre ++ [m] ++ post = ms₀ ++ (pre ++ m :: post) by simp] at c3

end Symbolic.Swarm.CREF.CliPure.RecvPrekeyProm
