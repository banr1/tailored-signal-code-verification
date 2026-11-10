/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
public import Symbolic.Proofs.Swarm.CREF.TR.RecvFresh
import DY.Trace.Basic
import DY.Actions.ProtocolEvent
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.EvalDist.ProbabilityNotation
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Existing-Chain Preservation of Receiver Freshness

Proves preservation of `TRRecvCountersFresh` and `TRSkippedRIdxChainRel` across `decTailTr` on
an existing receiver chain.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Symbolic.Swarm.CREF.TR

cref_open

open DY.Libsignal.TripleRatchet (SessionInfo KeyDir RecvChain setRecvChain consumeMessageKey kdfCk chainKeyAt)
open DY.Libsignal.TripleRatchet
open Symbolic.Swarm.CREF.TR.RecvDec (StEntry TREntry logSkippedKeysTr decTailTr at?_append_of_lt
  at?_eq_none_of_le at?_append_non_entry logSkippedKeysTr_length at?_trEntry_logSkippedKeysTr_lt
  at?_trEntry_logSkippedKeysTr_add)

/-! ## Event Classification Helpers for `logSkippedKeysTr` and `decTailTr` -/

theorem eventLoggedAt_append_stEntry (tr : ExecTrace) (e : StEntry) (ev : TREvent) (i : Nat) :
    (tr.append e).EventLoggedAt ev i ↔ tr.EventLoggedAt ev i := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  rw [at?_append_non_entry tr e rfl i]

theorem eventLoggedAt_append_trEntry_iff (tr : ExecTrace) (e : TREntry) (ev : TREvent) (i : Nat) :
    (tr.append e).EventLoggedAt ev i ↔ (tr.EventLoggedAt ev i ∨ (i = tr.length ∧ e.ev = ev)) := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  by_cases hlt : i < tr.length
  · rw [at?_append_of_lt tr e hlt]
    have hne : i ≠ tr.length := Nat.ne_of_lt hlt
    simp [hne]
  · by_cases heq : i = tr.length
    · subst heq
      rw [Trace.at?_append tr e, at?_eq_none_of_le tr (Nat.le_refl _)]
      cases e with
      | mk ev0 =>
        simp [eq_comm]
    · have hgt : (tr.append e).length ≤ i := by
        rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
        omega
      rw [at?_eq_none_of_le (tr.append e) hgt, at?_eq_none_of_le tr (by omega)]
      simp [heq]

theorem eventLoggedAt_logSkippedKeysTr_iff
    (s : SessionInfo) (pk : DY.Bytes) (rIdx stateIdx : Nat)
    (ck : DY.Bytes) (base : UInt32) (count : Nat) (tr : ExecTrace) (ev : TREvent) (i : Nat) :
    (logSkippedKeysTr s pk rIdx stateIdx ck base count tr).EventLoggedAt ev i ↔
      (tr.EventLoggedAt ev i ∨
        ∃ j < count,
          i = tr.length + j ∧
          ev = TREvent.SkippedKeyStored s pk (base + UInt32.ofNat j) (kdfCk (chainKeyAt ck j)).2 rIdx stateIdx) := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  by_cases hlt : i < tr.length
  · rw [at?_trEntry_logSkippedKeysTr_lt s pk rIdx stateIdx ck base count tr hlt]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨j, _, hij, _⟩)
      · exact h
      · omega
  · by_cases hlt2 : i < tr.length + count
    · have hj : i - tr.length < count := by omega
      have hij : i = tr.length + (i - tr.length) := by omega
      rw [hij, at?_trEntry_logSkippedKeysTr_add s pk rIdx stateIdx ck base count tr hj,
          at?_eq_none_of_le tr (by omega)]
      constructor
      · intro h
        injection h with h1
        injection h1 with h2
        exact Or.inr ⟨i - tr.length, hj, rfl, h2.symm⟩
      · rintro (h | ⟨j, _, hij', rfl⟩)
        · nomatch h
        · have hj_eq : i - tr.length = j := by omega
          rw [hj_eq]
    · have hge : (logSkippedKeysTr s pk rIdx stateIdx ck base count tr).length ≤ i := by
        rw [logSkippedKeysTr_length]; omega
      rw [at?_eq_none_of_le _ hge, at?_eq_none_of_le tr (by omega)]
      constructor
      · intro h; nomatch h
      · rintro (h | ⟨j, hj, hij, _⟩)
        · nomatch h
        · omega

theorem eventLoggedAt_decTailTr_messageKey
    {tr_pre : ExecTrace} {q : Participant} {stateIdx : Nat} {st1 : TRState} {c c' : RecvChain}
    {pk seed pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    {s : SessionInfo} {dir : KeyDir} {seed' pqSalt' : DY.Bytes} {n' : UInt32}
    {r' pIdx' i : Nat}
    (hlog : (decTailTr tr_pre q stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).EventLoggedAt
      (TREvent.MessageKey s dir seed' pqSalt' n' r' pIdx') i) :
    tr_pre.EventLoggedAt (TREvent.MessageKey s dir seed' pqSalt' n' r' pIdx') i ∨
      (s = st1.sessionInfo q ∧ dir = .receiver ∧ seed' = seed ∧ pqSalt' = pqSalt ∧ n' = n ∧ r' = c.rIdx) := by
  unfold decTailTr at hlog
  rw [eventLoggedAt_append_stEntry] at hlog
  rcases (eventLoggedAt_append_trEntry_iff _ _ _ i).mp hlog with hlog2 | ⟨_, heq⟩
  · rcases (eventLoggedAt_append_trEntry_iff _ _ _ i).mp hlog2 with hlog1 | ⟨_, heq⟩
    · rcases (eventLoggedAt_logSkippedKeysTr_iff _ _ _ _ _ _ _ _ _ i).mp hlog1 with hlog0 | ⟨j, _, _, heq⟩
      · exact Or.inl hlog0
      · nomatch heq
    · nomatch heq
  · injection heq with hs hdir hseed hpq hn hr _
    exact Or.inr ⟨hs.symm, hdir.symm, hseed.symm, hpq.symm, hn.symm, hr.symm⟩

theorem eventLoggedAt_decTailTr_skippedKeyStored
    {tr_pre : ExecTrace} {q : Participant} {stateIdx : Nat} {st1 : TRState} {c c' : RecvChain}
    {pk seed pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    {s : SessionInfo} {pk' : DY.Bytes} {n' : UInt32} {seed' : DY.Bytes} {r' srcIdx' i : Nat}
    (hlog : (decTailTr tr_pre q stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).EventLoggedAt
      (TREvent.SkippedKeyStored s pk' n' seed' r' srcIdx') i) :
    tr_pre.EventLoggedAt (TREvent.SkippedKeyStored s pk' n' seed' r' srcIdx') i ∨
      (∃ j < n.toNat - c.index.toNat,
        s = st1.sessionInfo q ∧ pk' = pk ∧ n' = c.index + UInt32.ofNat j ∧ r' = c.rIdx) := by
  unfold decTailTr at hlog
  rw [eventLoggedAt_append_stEntry] at hlog
  rcases (eventLoggedAt_append_trEntry_iff _ _ _ i).mp hlog with hlog2 | ⟨_, heq⟩
  · rcases (eventLoggedAt_append_trEntry_iff _ _ _ i).mp hlog2 with hlog1 | ⟨_, heq⟩
    · rcases (eventLoggedAt_logSkippedKeysTr_iff _ _ _ _ _ _ _ _ _ i).mp hlog1 with hlog0 | ⟨j, hj, _, heq⟩
      · exact Or.inl hlog0
      · injection heq with hs hpk hn hseed hr hsrc
        exact Or.inr ⟨j, hj, hs, hpk, hn, hr⟩
    · nomatch heq
  · nomatch heq

/-! ## `setRecvChain`, `consumeMessageKey`, and `UInt32` Helpers -/

theorem eq_of_mem_of_nodup_map {α β : Type} {f : α → β} {l : List α}
    (hNodup : (l.map f).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (heq : f x = f y) :
    x = y := by
  induction l with
  | nil => nomatch hx
  | cons a tl ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hNodup
    rcases hNodup with ⟨hNotMem, hNodupTl⟩
    rcases List.mem_cons.mp hx with rfl | hx_tl <;> rcases List.mem_cons.mp hy with rfl | hy_tl
    · rfl
    · exfalso; exact hNotMem ⟨y, hy_tl, heq.symm⟩
    · exfalso; exact hNotMem ⟨x, hx_tl, heq⟩
    · exact ih hNodupTl hx_tl hy_tl

theorem map_rIdx_setRecvChain {chains : List RecvChain} {c c' : RecvChain}
    (hc : c ∈ chains) (hNodup : (chains.map RecvChain.ratchetKey).Nodup)
    (hrk : c'.ratchetKey = c.ratchetKey) (hrIdx : c'.rIdx = c.rIdx) :
    (setRecvChain chains c').map RecvChain.rIdx = chains.map RecvChain.rIdx := by
  unfold setRecvChain
  rw [List.map_map]
  apply List.map_congr_left
  intro d hd
  dsimp only [Function.comp_def]
  split
  · next hEq =>
    have hd_rk : d.ratchetKey = c.ratchetKey := (beq_iff_eq.mp hEq).trans hrk
    have hdc : d = c := eq_of_mem_of_nodup_map hNodup hd hc hd_rk
    rw [hrIdx, hdc]
  · rfl

theorem mem_setRecvChain_iff_of_nodup {chains : List RecvChain} {c c' d : RecvChain}
    (h : d ∈ setRecvChain chains c')
    (hrk : c'.ratchetKey = c.ratchetKey) :
    d = c' ∨ (d ∈ chains ∧ d ≠ c) := by
  unfold setRecvChain at h
  rw [List.mem_map] at h
  obtain ⟨d0, hd0, rfl⟩ := h
  split
  · exact Or.inl rfl
  · next hNe =>
    refine Or.inr ⟨hd0, fun hEq => ?_⟩
    subst hEq
    exact hNe (beq_iff_eq.mpr hrk.symm)

theorem uint32_add_ofNat_lt {base n : UInt32} {j : Nat}
    (hj : j < n.toNat - base.toNat) :
    base + UInt32.ofNat j < n := by
  have hn_lt : n.toNat < 2 ^ 32 := n.toNat_lt
  have hj_lt : j < 2 ^ 32 := by omega
  have hofNat : (UInt32.ofNat j).toNat = j := Nat.mod_eq_of_lt hj_lt
  have hsum_lt : base.toNat + (UInt32.ofNat j).toNat < 2 ^ 32 := by omega
  have hadd_toNat : (base + UInt32.ofNat j).toNat = base.toNat + j := by
    change (base.toNat + (UInt32.ofNat j).toNat) % (2 ^ 32) = base.toNat + j
    rw [Nat.mod_eq_of_lt hsum_lt, hofNat]
  exact UInt32.lt_iff_toNat_lt.mpr (by omega)

theorem consumeMessageKey_props {c c' : RecvChain} {n : UInt32} {seed : DY.Bytes}
    (hcons : consumeMessageKey c n = some (seed, c')) :
    c.index ≤ n ∧ c'.ratchetKey = c.ratchetKey ∧ c'.rIdx = c.rIdx ∧ c'.index = n + 1 := by
  unfold consumeMessageKey at hcons
  split at hcons
  · nomatch hcons
  · next hnot_lt =>
    split at hcons
    · nomatch hcons
    · split at hcons
      · nomatch hcons
      · injection hcons with hpair
        injection hpair with _ hc'
        subst hc'
        exact ⟨UInt32.not_lt.mp hnot_lt, rfl, rfl, rfl⟩

/-! ## Existing-Chain Preservation of `TRRecvCountersFresh` -/

theorem trRecvCountersFresh_decTailTr_existing
    {tr_pre : ExecTrace} {p : Participant} {stateIdx : Nat} {st1 : TRState} {c c' : RecvChain}
    {pk seed pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    (hFresh : TRRecvCountersFresh tr_pre p st1)
    (hc_mem : c ∈ st1.recv)
    (hNodupRk : (st1.recv.map RecvChain.ratchetKey).Nodup)
    (hrk : c'.ratchetKey = c.ratchetKey)
    (hrIdx : c'.rIdx = c.rIdx)
    (hc_le : c.index ≤ n)
    (hn_lt : n < c'.index) :
    TRRecvCountersFresh
      (decTailTr tr_pre p stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n) p
      { st1 with recv := setRecvChain st1.recv c', spqr := spqr' } := by
  rcases hFresh with ⟨hF1, hF2a, hF2b, hF3, hF4⟩
  have hsinfo : ({ st1 with recv := setRecvChain st1.recv c', spqr := spqr' } : TRState).sessionInfo p = st1.sessionInfo p := rfl
  have hc_rIdx_le : c.rIdx ≤ st1.rIdx := hF3 c hc_mem
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    rw [hsinfo]
    rcases mem_setRecvChain_iff_of_nodup hd hrk with rfl | ⟨hd_mem, hd_ne⟩
    · refine ⟨?_, ?_⟩
      · intro seed' pqSalt' n' pIdx' i hlog
        rw [hrIdx] at hlog
        rcases eventLoggedAt_decTailTr_messageKey hlog with h0 | ⟨_, _, _, _, rfl, _⟩
        · have hlt_c : n' < c.index := (hF1 c hc_mem).1 seed' pqSalt' n' pIdx' i h0
          exact UInt32.lt_of_lt_of_le hlt_c (UInt32.le_of_lt (UInt32.lt_of_le_of_lt hc_le hn_lt))
        · exact hn_lt
      · intro pk' n' seed' srcIdx' i hlog
        rw [hrIdx] at hlog
        rcases eventLoggedAt_decTailTr_skippedKeyStored hlog with h0 | ⟨j, hj, _, _, rfl, _⟩
        · have hlt_c : n' < c.index := (hF1 c hc_mem).2 pk' n' seed' srcIdx' i h0
          exact UInt32.lt_of_lt_of_le hlt_c (UInt32.le_of_lt (UInt32.lt_of_le_of_lt hc_le hn_lt))
        · exact UInt32.lt_trans (uint32_add_ofNat_lt hj) hn_lt
    · have hdrIdx_ne : d.rIdx ≠ c.rIdx := fun hEq =>
        hd_ne (eq_of_mem_of_nodup_map hF4 hd_mem hc_mem hEq)
      refine ⟨?_, ?_⟩
      · intro seed' pqSalt' n' pIdx' i hlog
        rcases eventLoggedAt_decTailTr_messageKey hlog with h0 | ⟨_, _, _, _, _, hr_eq⟩
        · exact (hF1 d hd_mem).1 seed' pqSalt' n' pIdx' i h0
        · exact False.elim (hdrIdx_ne hr_eq)
      · intro pk' n' seed' srcIdx' i hlog
        rcases eventLoggedAt_decTailTr_skippedKeyStored hlog with h0 | ⟨_, _, _, _, _, hr_eq⟩
        · exact (hF1 d hd_mem).2 pk' n' seed' srcIdx' i h0
        · exact False.elim (hdrIdx_ne hr_eq)
  · intro seed' pqSalt' n' r' pIdx' i hlog
    rw [hsinfo] at hlog
    rcases eventLoggedAt_decTailTr_messageKey hlog with h0 | ⟨_, _, _, _, _, rfl⟩
    · exact hF2a seed' pqSalt' n' r' pIdx' i h0
    · exact hc_rIdx_le
  · intro pk' n' seed' r' srcIdx' i hlog
    rw [hsinfo] at hlog
    rcases eventLoggedAt_decTailTr_skippedKeyStored hlog with h0 | ⟨_, _, _, _, _, rfl⟩
    · exact hF2b pk' n' seed' r' srcIdx' i h0
    · exact hc_rIdx_le
  · intro d hd
    rcases mem_setRecvChain_iff_of_nodup hd hrk with rfl | ⟨hd_mem, _⟩
    · rw [hrIdx]; exact hc_rIdx_le
    · exact hF3 d hd_mem
  · dsimp only
    rw [map_rIdx_setRecvChain hc_mem hNodupRk hrk hrIdx]
    exact hF4

theorem trRecvCountersFresh_decTailTr_consumeMessageKey
    {tr_pre : ExecTrace} {p : Participant} {stateIdx : Nat} {st1 : TRState} {c c' : RecvChain}
    {pk seed pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    (hFresh : TRRecvCountersFresh tr_pre p st1)
    (hc_mem : c ∈ st1.recv)
    (hNodupRk : (st1.recv.map RecvChain.ratchetKey).Nodup)
    (hcons : consumeMessageKey c n = some (seed, c'))
    (hn_bound : n.toNat + 1 < 2 ^ 32) :
    TRRecvCountersFresh
      (decTailTr tr_pre p stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n) p
      { st1 with recv := setRecvChain st1.recv c', spqr := spqr' } := by
  obtain ⟨hc_le, hrk, hrIdx, hc'_idx⟩ := consumeMessageKey_props hcons
  have hn_lt : n < c'.index := by
    rw [hc'_idx]
    have hadd_toNat : (n + 1).toNat = n.toNat + 1 := by
      change (n.toNat + 1) % (2 ^ 32) = n.toNat + 1
      exact Nat.mod_eq_of_lt hn_bound
    exact UInt32.lt_iff_toNat_lt.mpr (by omega)
  exact trRecvCountersFresh_decTailTr_existing hFresh hc_mem hNodupRk hrk hrIdx hc_le hn_lt

/-! ## Existing-Chain Preservation of `TRSkippedRIdxChainRel` -/

theorem pk_eq_ratchetKey_of_decTailTr_at_rIdx
    {tr_pre : ExecTrace} {p : Participant} {stateIdx : Nat} {st1 : TRState}
    {c c' : RecvChain} {seed pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    (hRel : TRSkippedRIdxChainRel tr_pre p st1) (hc : c ∈ st1.recv)
    {pk₁ : DY.Bytes} {n₁ : UInt32} {seed₁ : DY.Bytes} {srcIdx₁ i₁ : Nat}
    (hlog : (decTailTr tr_pre p stateIdx st1 c c' c.ratchetKey seed pqSalt ptTerm spqr' n).EventLoggedAt
      (TREvent.SkippedKeyStored (st1.sessionInfo p) pk₁ n₁ seed₁ c.rIdx srcIdx₁) i₁) :
    pk₁ = c.ratchetKey := by
  rcases eventLoggedAt_decTailTr_skippedKeyStored hlog with hOld | ⟨_, _, _, rfl, _, _⟩
  · exact hRel.2 c hc pk₁ n₁ seed₁ srcIdx₁ i₁ hOld
  · rfl

theorem trSkippedRIdxChainRel_existing
    {tr_pre : ExecTrace} {p : Participant} {stateIdx : Nat} {st1 st' : TRState}
    {c c' : RecvChain} {seed pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    (hF : TRRecvCountersFresh tr_pre p st1)
    (hRel : TRSkippedRIdxChainRel tr_pre p st1)
    (hc : c ∈ st1.recv)
    (hrk : c'.ratchetKey = c.ratchetKey)
    (hrIdx : c'.rIdx = c.rIdx)
    (hsinfo : st'.sessionInfo p = st1.sessionInfo p)
    (hrecv : ∀ c_post ∈ st'.recv, c_post = c' ∨ c_post ∈ st1.recv) :
    TRSkippedRIdxChainRel
      (decTailTr tr_pre p stateIdx st1 c c' c.ratchetKey seed pqSalt ptTerm spqr' n) p st' := by
  refine ⟨?_, ?_⟩
  · intro pk₁ n₁ seed₁ srcIdx₁ i₁ pk₂ n₂ seed₂ srcIdx₂ i₂ rIdx h₁ h₂
    rw [hsinfo] at h₁ h₂
    rcases eventLoggedAt_decTailTr_skippedKeyStored h₁ with hOld₁ | ⟨_, _, _, rfl, _, rfl⟩
    · rcases eventLoggedAt_decTailTr_skippedKeyStored h₂ with hOld₂ | ⟨_, _, _, rfl, _, rfl⟩
      · exact hRel.1 pk₁ n₁ seed₁ srcIdx₁ i₁ pk₂ n₂ seed₂ srcIdx₂ i₂ rIdx hOld₁ hOld₂
      · exact hRel.2 c hc pk₁ n₁ seed₁ srcIdx₁ i₁ hOld₁
    · exact (pk_eq_ratchetKey_of_decTailTr_at_rIdx hRel hc h₂).symm
  · intro c_post hc_post pk n_k seed_k srcIdx i hlog
    rw [hsinfo] at hlog
    rcases hrecv c_post hc_post with hc_eq | hc_old
    · rw [hc_eq, hrIdx] at hlog
      rw [hc_eq, hrk]
      exact pk_eq_ratchetKey_of_decTailTr_at_rIdx hRel hc hlog
    · rcases eventLoggedAt_decTailTr_skippedKeyStored hlog with hOld | ⟨_, _, _, rfl, _, hRIdxEq⟩
      · exact hRel.2 c_post hc_old pk n_k seed_k srcIdx i hOld
      · have hEq : c = c_post :=
          eq_of_mem_of_nodup_map hF.2.2.2.2 hc hc_old hRIdxEq.symm
        rw [← hEq]

theorem trSkippedRIdxChainRel_decTailTr_existing
    {tr_pre : ExecTrace} {p : Participant} {stateIdx : Nat} {st1 : TRState}
    {c c' : RecvChain} {seed pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    (hF : TRRecvCountersFresh tr_pre p st1)
    (hRel : TRSkippedRIdxChainRel tr_pre p st1)
    (hc : c ∈ st1.recv)
    (hrk : c'.ratchetKey = c.ratchetKey)
    (hrIdx : c'.rIdx = c.rIdx) :
    TRSkippedRIdxChainRel
      (decTailTr tr_pre p stateIdx st1 c c' c.ratchetKey seed pqSalt ptTerm spqr' n) p
      { st1 with recv := setRecvChain st1.recv c', spqr := spqr' } := by
  refine trSkippedRIdxChainRel_existing hF hRel hc hrk hrIdx rfl (fun d hd => ?_)
  rcases mem_setRecvChain_iff_of_nodup hd hrk with rfl | ⟨hd_mem, _⟩
  · exact Or.inl rfl
  · exact Or.inr hd_mem

end Symbolic.Swarm.CREF.TR
