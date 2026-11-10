/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvFresh
import DY.Trace.Basic
import DY.Actions.ProtocolEvent
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3StepExistingPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Receiver-Counter Freshness Elimination Lemmas

Eliminates `TRRecvCountersFresh` to show that receiver message keys at counters
at or above a chain's current index are unused and distinct from stored skipped keys.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR

cref_open

open DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Proofs.libsignal.RngG.CliPure.R3 (vec32_toList_of_length_eq)
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain)
open DY.Libsignal.TripleRatchet (TREvent TRState skippedKeyUsedB receiverKeyUsedB anyEventOnTrace)
open Symbolic.Swarm.CREF.TR.RecvDec
  (StEntry TREntry at?_append_of_lt at?_eq_none_of_le at?_append_non_entry
   logSkippedKeysTr logSkippedKeysTr_length at?_trEntry_logSkippedKeysTr_lt
   at?_trEntry_logSkippedKeysTr_add decTailTr decSkippedTr decRatchetPreTr trDhRatchetState)

theorem exists_eventLoggedAt_of_someEventOnTraceB_tr {tr : ExecTrace} {q : TREvent → Bool}
    (h : (DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.TripleRatchet.TREvent) tr q = true) : ∃ ev i, tr.EventLoggedAt ev i ∧ q ev = true := by
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h; rw [List.any_eq_true] at h
  obtain ⟨i, _, hi⟩ := h; revert hi
  cases he : (tr.at? i : Option (ProtocolEvent.ExecEntryT TREvent)) with
  | none => intro hi; cases hi
  | some e => intro hi; refine ⟨e.ev, i, ?_, hi⟩; simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; rw [he]

/-- On a trace satisfying `TRRecvCountersFresh`, no receiver key at chain `c`'s `rIdx`
with counter `c.index ≤ n` has been used. -/
theorem receiverKeyUsedB_false_of_ge_tr {tr : ExecTrace} {p : Participant} {st : TRState}
    (hF : TRRecvCountersFresh tr p st) {c : RecvChain} (hc : c ∈ st.recv)
    (seed : DY.Bytes) {n : UInt32} (hn : c.index ≤ n) :
    receiverKeyUsedB tr (st.sessionInfo p) seed n c.rIdx = false := by
  rcases hb : receiverKeyUsedB tr (st.sessionInfo p) seed n c.rIdx with _ | _
  · rfl
  · exfalso; unfold receiverKeyUsedB at hb
    obtain ⟨ev, i, hev, hq⟩ := exists_eventLoggedAt_of_someEventOnTraceB_tr hb
    cases ev with
    | MessageKey s' dir seed' pqSalt' n' r' pa' =>
      cases dir with
      | receiver =>
        simp only [decide_eq_true_eq] at hq; obtain ⟨hs, _, hn_eq, hr_eq⟩ := hq
        subst hs hn_eq hr_eq; have hlt := (hF.1 c hc).1 seed' pqSalt' n' pa' i hev
        rw [UInt32.le_iff_toNat_le] at hn; rw [UInt32.lt_iff_toNat_lt] at hlt; omega
      | sender => simp at hq
    | _ => simp at hq

/-- Any key at counter `c.index ≤ n` differs from every stored skipped key of chain `c`. -/
theorem not_consumed_of_skippedKeyStored_tr {tr : ExecTrace} {p : Participant} {st : TRState}
    (hF : TRRecvCountersFresh tr p st) {c : RecvChain} (hc : c ∈ st.recv) {n : UInt32} (hn : c.index ≤ n)
    {seed pk_k seed_k : DY.Bytes} {n_k : UInt32} {rIdx_k srcIdx_k skIdx_k : Nat}
    (hlog : tr.EventLoggedAt
      (TREvent.SkippedKeyStored (st.sessionInfo p) pk_k n_k seed_k rIdx_k srcIdx_k) skIdx_k) :
    ¬ (seed = seed_k ∧ n = n_k ∧ c.rIdx = rIdx_k) := by
  rintro ⟨_, rfl, rfl⟩; have hlt := (hF.1 c hc).2 pk_k n seed_k srcIdx_k skIdx_k hlog
  rw [UInt32.le_iff_toNat_le] at hn; rw [UInt32.lt_iff_toNat_lt] at hlt; omega

end Symbolic.Swarm.CREF.CliPure.TR
