/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
public import Symbolic.Proofs.Swarm.CREF.TR.SlotsZ6Pure
import DY.Trace.Basic
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.ProtocolEvent
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Frame Preservation of `SkippedInstallByteFresh`

Defines `SkippedKeySrcLt` and `NoNewSkSnoc`, and proves preservation of
`SkippedInstallByteFresh` across trace extensions with no new `SkippedKeyStored`
events and across existing-chain `decTailTr` decrypt tails.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR

cref_open
open DY
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet (SessionInfo DRState RecvChain findRecvChain recvChainFor
  consumeMessageKey)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.FreshSigma (StEntry TREntry)
open Symbolic.Swarm.CREF.TR.RecvDec
  (at?_append_of_lt at?_append_non_entry
   logSkippedKeysTr logSkippedKeysTr_length
   at?_trEntry_logSkippedKeysTr_lt at?_trEntry_logSkippedKeysTr_add
   at?_stEntry_logSkippedKeysTr decTailTr getLocalState_snd
    decrypt_next_noRatchet_eq)

theorem le_runMoves_fst (ms : List Move) (tr : ExecTrace) :
    tr ≤ (runMoves ms tr).1 :=
  RecvHistStep2.le_runMoves_fst ms tr

/-- Every logged `TREvent.SkippedKeyStored` event on `tr` has `src < tr.length`. -/
def SkippedKeySrcLt (tr : ExecTrace) : Prop :=
  ∀ (s : SessionInfo) (pk : DY.Bytes) (n : UInt32) (seed : DY.Bytes) (rIdx src i : Nat),
    tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i → src < tr.length

/-! ## Preservation across moves without new `SkippedKeyStored` events -/

theorem trStateStoredAt_of_le_of_lt {tr₁ tr₂ : ExecTrace} (hle : tr₁ ≤ tr₂)
    {p : Participant} {st : TRState} {src : Nat} (hlt : src < tr₁.length)
    (h2 : TRStateStoredAt p st src tr₂) :
    TRStateStoredAt p st src tr₁ := by
  have hlt2 : src < tr₂.length := by
    have hlen := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr₂ src
    change (tr₂.at? src : Option StEntry) = some _ at h2
    rwa [h2] at hlen
  change (tr₁.at? src : Option StEntry) = some ⟨⟨p, st⟩⟩
  change (tr₂.at? src : Option StEntry) = some ⟨⟨p, st⟩⟩ at h2
  simp only [Trace.at?, hlt, hlt2, ↓reduceDIte] at h2 ⊢
  rw [← Trace.at_le tr₁ tr₂ src hlt hle] at h2
  exact h2

theorem skippedInstallByteFresh_of_le_of_noNewSk
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (r₀ : ProtocolSetup) (ms₁ ms₂ : List Move)
    (h1 : SkippedInstallByteFresh interpretation S g r₀ ms₁)
    (hsrc_lt : SkippedKeySrcLt (runTraceMoves r₀ ms₁))
    (hle : runTraceMoves r₀ ms₁ ≤ runTraceMoves r₀ ms₂)
    (hno_new : ∀ s pk n seed rIdx src i,
      (runTraceMoves r₀ ms₂).EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i →
      (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i) :
    SkippedInstallByteFresh interpretation S g r₀ ms₂ := by
  intro s pk n seed rIdx src i p₀ st₀ c₀ hlog2 hst2 hrc c hc
  have hlog1 := hno_new s pk n seed rIdx src i hlog2
  have hsrc_lt_len : src < (runTraceMoves r₀ ms₁).length := hsrc_lt s pk n seed rIdx src i hlog1
  have hst1 := trStateStoredAt_of_le_of_lt hle hsrc_lt_len hst2
  exact h1 s pk n seed rIdx src i p₀ st₀ c₀ hlog1 hst1 hrc c hc

/-- Appending `m` logs no new `TREvent.SkippedKeyStored` event on `runTraceMoves r₀ (ms ++ [m])`. -/
def NoNewSkSnoc (r₀ : ProtocolSetup) (ms : List Move) (m : Move) : Prop :=
  ∀ s pk n seed rIdx src i,
    (runTraceMoves r₀ (ms ++ [m])).EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i →
    (runTraceMoves r₀ ms).EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i

/-! ## Existing-chain decrypt preservation of `SkippedInstallByteFresh` -/

theorem recvChainFor_eq_some_false_of_findRecvChain_some
    {st : DRState} {pk : DY.Bytes} {c : RecvChain}
    (hfind : findRecvChain st.recv pk = some c) :
    recvChainFor st pk = some (c, false) := by
  unfold recvChainFor
  rw [hfind]

theorem skippedInstallByteFresh_decTailTr_of_findRecvChain_some
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (r₀ : ProtocolSetup) (ms : List Move)
    {tr : ExecTrace} {me : Participant} {stH : Nat}
    {st : TRState} {c c' : RecvChain} {pk seed pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    (htr_le : runTraceMoves r₀ ms ≤ tr)
    (hno_new_pre : ∀ s' pk' n' seed' rIdx' src' i',
      tr.EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i' →
      (runTraceMoves r₀ ms).EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i')
    (hst_pre : ∀ {p₀ : Participant} {st₀ : TRState} {src : Nat},
      src < (runTraceMoves r₀ ms).length →
      TRStateStoredAt p₀ st₀ src (decTailTr tr me stH st c c' pk seed pqSalt ptTerm spqr' n) →
      TRStateStoredAt p₀ st₀ src (runTraceMoves r₀ ms))
    (hstH : TRStateStoredAt me st stH tr)
    (hfind : findRecvChain st.recv pk = some c)
    (hsrc_lt : SkippedKeySrcLt (runTraceMoves r₀ ms))
    (h1 : SkippedInstallByteFresh interpretation S g r₀ ms) :
    ∀ (s' : SessionInfo) (pk' : DY.Bytes) (n' : UInt32) (seed' : DY.Bytes) (rIdx' src' i' : Nat)
      (p₀ : Participant) (st₀ : TRState) (c₀ : RecvChain),
      (decTailTr tr me stH st c c' pk seed pqSalt ptTerm spqr' n).EventLoggedAt
        (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i' →
      TRStateStoredAt p₀ st₀ src' (decTailTr tr me stH st c c' pk seed pqSalt ptTerm spqr' n) →
      recvChainFor st₀.toDRState pk' = some (c₀, true) →
      ∀ c_m ∈ st₀.recv, gamma interpretation S g c_m.ratchetKey ≠ gamma interpretation S g pk' := by
  intro s' pk' n' seed' rIdx' src' i' p₀ st₀ c₀ hlog hst₀ hrc c_m hc_m
  let k := n.toNat - c.index.toNat
  let tr1 := logSkippedKeysTr (st.sessionInfo me) pk c.rIdx stH c.chainKey c.index k tr
  have hlog_tr1 : tr1.EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i' := by
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
    have hlog' := hlog
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog'
    unfold decTailTr at hlog'
    dsimp only at hlog'
    rw [at?_append_non_entry _ _ rfl] at hlog'
    rcases Nat.lt_or_ge i' (tr1.length + 1) with hlt1 | hge1
    · rw [at?_append_of_lt _ _
        (by dsimp only [tr1, k] at hlt1 ⊢; simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)] at hlog'
      rcases Nat.lt_or_ge i' tr1.length with hlt0 | hge0
      · rw [at?_append_of_lt _ _ hlt0] at hlog'
        exact hlog'
      · have heq0 : i' = tr1.length := by omega
        subst heq0
        rw [Trace.at?_append] at hlog'
        nomatch hlog'
    · rcases Nat.eq_or_lt_of_le hge1 with heq1 | hgt1
      · have hlen_rcv : tr1.length + 1 =
            (tr1.append (⟨TREvent.Received me st.peer pk n ptTerm⟩ : TREntry)).length := by
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
        rw [← heq1, hlen_rcv, Trace.at?_append] at hlog'
        nomatch hlog'
      · rw [Symbolic.Swarm.CREF.TR.RecvDec.at?_eq_none_of_le _
          (by dsimp only [tr1, k] at hgt1 ⊢; simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)] at hlog'
        nomatch hlog'
  rcases Nat.lt_or_ge i' tr.length with hi_lt | hi_ge
  · have hlog_tr : tr.EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i' := by
      rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
      have hlog_tr1' := hlog_tr1
      rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog_tr1'
      rwa [at?_trEntry_logSkippedKeysTr_lt _ _ _ _ _ _ _ _ hi_lt] at hlog_tr1'
    have hlog0 := hno_new_pre s' pk' n' seed' rIdx' src' i' hlog_tr
    have hi0_lt : i' < (runTraceMoves r₀ ms).length := by
      have hlen := Trace.at?_eq_some_implies_length_le (EntryT := TREntry) (runTraceMoves r₀ ms) i'
      have hlog0' := hlog0
      rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog0'
      rwa [hlog0'] at hlen
    have hsrc_lt0 : src' < (runTraceMoves r₀ ms).length :=
      hsrc_lt s' pk' n' seed' rIdx' src' i' hlog0
    exact h1 s' pk' n' seed' rIdx' src' i' p₀ st₀ c₀ hlog0 (hst_pre hsrc_lt0 hst₀) hrc c_m hc_m
  · have hi_lt1 : i' < tr1.length := by
      have hlen := Trace.at?_eq_some_implies_length_le (EntryT := TREntry) tr1 i'
      have hlog_tr1_at := hlog_tr1
      rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog_tr1_at
      rwa [hlog_tr1_at] at hlen
    have htr1_len : tr1.length = tr.length + k :=
      logSkippedKeysTr_length (st.sessionInfo me) pk c.rIdx stH c.chainKey c.index k tr
    have hj_lt : i' - tr.length < k := by omega
    have hi_eq : i' = tr.length + (i' - tr.length) := by omega
    have hat_add := at?_trEntry_logSkippedKeysTr_add
      (st.sessionInfo me) pk c.rIdx stH c.chainKey c.index k tr hj_lt
    have hlog_tr1' := hlog_tr1
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog_tr1'
    rw [hi_eq, hat_add] at hlog_tr1'
    injection hlog_tr1' with hE
    injection hE with hE'
    injection hE' with _ hpk_eq _ _ _ hsrc_eq
    subst hpk_eq hsrc_eq
    have hstH_lt : stH < tr.length := by
      have hlen := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr stH
      change (tr.at? stH : Option StEntry) = some _ at hstH
      rwa [hstH] at hlen
    have hst₀_tr : TRStateStoredAt p₀ st₀ stH tr := by
      change (tr.at? stH : Option StEntry) = some ⟨⟨p₀, st₀⟩⟩
      have hst₀' : ((decTailTr tr me stH st c c' pk seed pqSalt ptTerm spqr' n).at? stH :
          Option StEntry) = some ⟨⟨p₀, st₀⟩⟩ := hst₀
      unfold decTailTr at hst₀'
      dsimp only at hst₀'
      rw [at?_append_of_lt _ _
          (by dsimp only [tr1, k] at htr1_len; simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
          at?_append_non_entry _ _ rfl,
          at?_append_non_entry _ _ rfl, at?_stEntry_logSkippedKeysTr] at hst₀'
      exact hst₀'
    have hst_eq : st₀ = st := by
      change (tr.at? stH : Option StEntry) = some ⟨⟨me, st⟩⟩ at hstH
      change (tr.at? stH : Option StEntry) = some ⟨⟨p₀, st₀⟩⟩ at hst₀_tr
      rw [hstH] at hst₀_tr
      injection hst₀_tr with h1'
      injection h1' with h2'
      injection h2' with _ h3'
      exact h3'.symm
    subst hst_eq
    have hrc_false : recvChainFor st₀.toDRState pk = some (c, false) :=
      recvChainFor_eq_some_false_of_findRecvChain_some hfind
    rw [hrc_false] at hrc
    nomatch hrc

end Symbolic.Swarm.CREF.CliPure.TR
