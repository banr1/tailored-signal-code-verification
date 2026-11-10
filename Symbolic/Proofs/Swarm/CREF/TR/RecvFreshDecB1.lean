/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvFresh
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvFreshDecA
import VCVio.Prelude.Core
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
# DH-Ratchet Preservation of Receiver Freshness

Proves preservation of `TRRecvCountersFresh`, `TRSkippedRIdxChainRel`, and `TRRecvFreshAll`
across `decRatchetPreTr`, `trDhRatchetState`, `decTailTr`, and full DH-ratchet `Move.decrypt`
steps.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR

cref_open

open DY.Comparse DY.Literal DY.DiffieHellman
open DY.Libsignal.TripleRatchet
  (SessionInfo DRState KeyComponent KeyDir RecvChain findRecvChain setRecvChain recvChainFor consumeMessageKey chainKeyAt kdfCk kdfRk maxForwardJumps u32Max computeMac messageVersion createChain x25519LowOrder maxReceiverChains)
open DY.Libsignal.TripleRatchet
open Symbolic.Swarm.CREF.TR.RecvDec
  (StEntry TREntry
   at?_append_of_lt at?_eq_none_of_le at?_append_non_entry
   logSkippedKeysTr logSkippedKeysTr_length logSkippedKeysTr_le
   at?_trEntry_logSkippedKeysTr_lt at?_trEntry_logSkippedKeysTr_add
   decTailTr
   trDhRatchetState at?_stEntry_logSkippedKeysTr
   decTailTr_length at?_trEntry_decTailTr_lt
   decRatchetPreTr decRatchetPreTr_length decrypt_next_ratchet_eq
   getMessageSentAt_attackerSend getLocalState_attackerSend)

private theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

private theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl

private theorem getLocalState_fst (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 =
      match (tr.at? stH : Option StEntry) with
      | some ⟨⟨p, st⟩⟩ => if p = me then some st else none
      | none => none := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1,
    Symbolic.DYBridge.DY.getEntry_eq_1]
  unfold _root_.guard
  rw [run_bind_fst, run_bind_fst, run_bind_snd, Traceful.run_mk]
  rcases (tr.at? stH : Option StEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · dsimp only
    rw [Symbolic.DYBridge.DY.Traceful.run_eq_1 (Pure.pure _)]
    change (((if p = me then pure () else failure : Traceful Unit) >>= fun _ => pure st).run tr).1 =
      if p = me then some st else none
    by_cases hp : p = me
    · rw [ite_eq_left_iff.mpr fun h => absurd hp h, ite_eq_left_iff.mpr fun h => absurd hp h]
      simp only [DY.Traceful.run_bind, DY.Traceful.run_pure]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hp, ite_eq_right_iff.mpr fun h => absurd h hp]
      simp only [DY.Traceful.run_bind, DY.Traceful.run_failure]

private theorem at?_eq_some_of_getLocalState_some {p : Participant} {stateIdx : Nat}
    {tr : ExecTrace} {st : TRState}
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run tr).1 = some st) :
    (tr.at? stateIdx : Option StEntry) = some ⟨⟨p, st⟩⟩ := by
  rw [getLocalState_fst] at hst
  rcases h : (tr.at? stateIdx : Option StEntry) with _ | ⟨⟨me, st'⟩⟩
  · rw [h] at hst; cases hst
  · rw [h] at hst
    by_cases hme : me = p
    · subst hme; simp only [↓reduceIte, Option.some.injEq] at hst; subst hst; rfl
    · simp only [hme, ↓reduceIte] at hst; cases hst

/-! ## `TRRecvCountersFresh` Preservation -/

theorem eventLoggedAt_append_non_tr_rfb1 {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (ev : TREvent) (i : Nat) :
    (tr.append e).EventLoggedAt ev i ↔ tr.EventLoggedAt ev i := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  rw [at?_append_non_entry tr e hnone]

theorem eventLoggedAt_append_trEntry_iff_rfb1
    (tr : ExecTrace) (e : TREntry) (ev : TREvent) (i : Nat) :
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
      | mk ev0 => simp [eq_comm]
    · have hgt : (tr.append e).length ≤ i := by
        rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
      rw [at?_eq_none_of_le (tr.append e) hgt, at?_eq_none_of_le tr (by omega)]
      simp [heq]

theorem eventLoggedAt_logSkippedKeysTr_iff_rfb1
    (s : SessionInfo) (pk : DY.Bytes) (rIdx stateIdx : Nat)
    (ck : DY.Bytes) (base : UInt32) (count : Nat) (tr : ExecTrace) (ev : TREvent) (i : Nat) :
    (logSkippedKeysTr s pk rIdx stateIdx ck base count tr).EventLoggedAt ev i ↔
      (tr.EventLoggedAt ev i ∨
        ∃ j < count,
          i = tr.length + j ∧
          ev = TREvent.SkippedKeyStored s pk (base + UInt32.ofNat j)
            (kdfCk (chainKeyAt ck j)).2 rIdx stateIdx) := by
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

theorem eventLoggedAt_decRatchetPreTr_messageKey_rfb1
    {tr : ExecTrace} {q : Participant} {st1 : TRState} {pk_dh key : DY.Bytes}
    {ses : SessionInfo} {seed pqSalt : DY.Bytes} {n : UInt32}
    {r pIdx i : Nat}
    (hlog : (decRatchetPreTr tr q st1 pk_dh key).EventLoggedAt
      (TREvent.MessageKey ses .receiver seed pqSalt n r pIdx) i) :
    tr.EventLoggedAt (TREvent.MessageKey ses .receiver seed pqSalt n r pIdx) i := by
  unfold decRatchetPreTr at hlog
  rcases (eventLoggedAt_append_trEntry_iff_rfb1 _ _ _ i).mp hlog with hlog1 | ⟨_, heq⟩
  · rcases (eventLoggedAt_append_trEntry_iff_rfb1 _ _ _ i).mp hlog1 with hlog0 | ⟨_, heq⟩
    · rw [eventLoggedAt_append_non_tr_rfb1 _ _ rfl,
          eventLoggedAt_append_non_tr_rfb1 _ _ rfl] at hlog0
      exact hlog0
    · nomatch heq
  · nomatch heq

theorem eventLoggedAt_decRatchetPreTr_skippedKeyStored_rfb1
    {tr : ExecTrace} {q : Participant} {st1 : TRState} {pk_dh key : DY.Bytes}
    {s : SessionInfo} {pk' : DY.Bytes} {n' : UInt32} {seed' : DY.Bytes} {r' srcIdx' i : Nat}
    (hlog : (decRatchetPreTr tr q st1 pk_dh key).EventLoggedAt
      (TREvent.SkippedKeyStored s pk' n' seed' r' srcIdx') i) :
    tr.EventLoggedAt (TREvent.SkippedKeyStored s pk' n' seed' r' srcIdx') i := by
  unfold decRatchetPreTr at hlog
  rcases (eventLoggedAt_append_trEntry_iff_rfb1 _ _ _ i).mp hlog with hlog1 | ⟨_, heq⟩
  · rcases (eventLoggedAt_append_trEntry_iff_rfb1 _ _ _ i).mp hlog1 with hlog0 | ⟨_, heq⟩
    · rw [eventLoggedAt_append_non_tr_rfb1 _ _ rfl,
          eventLoggedAt_append_non_tr_rfb1 _ _ rfl] at hlog0
      exact hlog0
    · nomatch heq
  · nomatch heq

theorem eventLoggedAt_decTailTr_messageKey_rfb1
    {tr_pre : ExecTrace} {q : Participant} {stateIdx : Nat} {st1 : TRState} {c c' : RecvChain}
    {pk seed pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    {s : SessionInfo} {dir : KeyDir} {mk' pqSalt' : DY.Bytes} {n' : UInt32}
    {r' pIdx' i : Nat}
    (hlog : (decTailTr tr_pre q stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).EventLoggedAt
      (TREvent.MessageKey s dir mk' pqSalt' n' r' pIdx') i) :
    tr_pre.EventLoggedAt (TREvent.MessageKey s dir mk' pqSalt' n' r' pIdx') i ∨
      (s = st1.sessionInfo q ∧ dir = .receiver ∧ mk' = seed ∧ pqSalt' = pqSalt ∧
        n' = n ∧ r' = c.rIdx) := by
  unfold decTailTr at hlog
  rw [eventLoggedAt_append_non_tr_rfb1 _ _ rfl] at hlog
  rcases (eventLoggedAt_append_trEntry_iff_rfb1 _ _ _ i).mp hlog with hlog2 | ⟨_, heq⟩
  · rcases (eventLoggedAt_append_trEntry_iff_rfb1 _ _ _ i).mp hlog2 with hlog1 | ⟨_, heq⟩
    · rcases (eventLoggedAt_logSkippedKeysTr_iff_rfb1 _ _ _ _ _ _ _ _ _ i).mp hlog1 with
        hlog0 | ⟨_, _, _, heq⟩
      · exact Or.inl hlog0
      · nomatch heq
    · nomatch heq
  · injection heq with hs hdir hmk hpq hn hr _
    exact Or.inr ⟨hs.symm, hdir.symm, hmk.symm, hpq.symm, hn.symm, hr.symm⟩

theorem eventLoggedAt_decTailTr_skippedKeyStored_rfb1
    {tr_pre : ExecTrace} {q : Participant} {stateIdx : Nat} {st1 : TRState} {c c' : RecvChain}
    {pk seed pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    {s : SessionInfo} {pk' : DY.Bytes} {n' : UInt32} {seed' : DY.Bytes} {r' srcIdx' i : Nat}
    (hlog : (decTailTr tr_pre q stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).EventLoggedAt
      (TREvent.SkippedKeyStored s pk' n' seed' r' srcIdx') i) :
    tr_pre.EventLoggedAt (TREvent.SkippedKeyStored s pk' n' seed' r' srcIdx') i ∨
      (∃ j < n.toNat - c.index.toNat,
        s = st1.sessionInfo q ∧ pk' = pk ∧ n' = c.index + UInt32.ofNat j ∧ r' = c.rIdx) := by
  unfold decTailTr at hlog
  rw [eventLoggedAt_append_non_tr_rfb1 _ _ rfl] at hlog
  rcases (eventLoggedAt_append_trEntry_iff_rfb1 _ _ _ i).mp hlog with hlog2 | ⟨_, heq⟩
  · rcases (eventLoggedAt_append_trEntry_iff_rfb1 _ _ _ i).mp hlog2 with hlog1 | ⟨_, heq⟩
    · rcases (eventLoggedAt_logSkippedKeysTr_iff_rfb1 _ _ _ _ _ _ _ _ _ i).mp hlog1 with
        hlog0 | ⟨j, hj, _, heq⟩
      · exact Or.inl hlog0
      · injection heq with hs hpk hn hseed hr hsrc
        exact Or.inr ⟨j, hj, hs, hpk, hn, hr⟩
    · nomatch heq
  · nomatch heq

theorem trRecvCountersFresh_decRatchetPreTr
    {tr : ExecTrace} {q p : Participant} {st1 st : TRState} {pk key : DY.Bytes}
    (hFresh : TRRecvCountersFresh tr p st) :
    TRRecvCountersFresh (decRatchetPreTr tr q st1 pk key) p st :=
  trRecvCountersFresh_of_imp
    (fun _ _ _ _ _ _ => eventLoggedAt_decRatchetPreTr_messageKey_rfb1)
    (fun _ _ _ _ _ _ => eventLoggedAt_decRatchetPreTr_skippedKeyStored_rfb1)
    hFresh

theorem mem_trDhRatchetState_recv {st : TRState} {pk : DY.Bytes} {rngIdx : Nat} {d : RecvChain}
    (hd : d ∈ (trDhRatchetState st pk rngIdx).1.recv) :
    d ∈ st.recv ∨ d = (trDhRatchetState st pk rngIdx).2 := by
  unfold trDhRatchetState at hd
  dsimp only at hd
  have hmem : d ∈ st.recv ++ [(trDhRatchetState st pk rngIdx).2] := List.mem_of_mem_drop hd
  rcases List.mem_append.mp hmem with h1 | h2
  · exact Or.inl h1
  · simp only [List.mem_singleton] at h2
    exact Or.inr h2

theorem trDhRatchetState_snd_mem_recv (st : TRState) (pk : DY.Bytes) (rngIdx : Nat) :
    (trDhRatchetState st pk rngIdx).2 ∈ (trDhRatchetState st pk rngIdx).1.recv := by
  unfold trDhRatchetState
  dsimp only
  let c := (trDhRatchetState st pk rngIdx).2
  change c ∈ (st.recv ++ [c]).drop (st.recv.length + 1 - maxReceiverChains)
  have hle : st.recv.length + 1 - maxReceiverChains ≤ st.recv.length := by
    unfold maxReceiverChains; omega
  rw [List.drop_append_of_le_length hle]
  exact List.mem_append_right _ (List.mem_singleton_self c)

theorem findRecvChain_eq_none_iff_rfb1 (chains : List RecvChain) (rk : DY.Bytes) :
    findRecvChain chains rk = none ↔ rk ∉ chains.map RecvChain.ratchetKey := by
  unfold findRecvChain
  rw [List.find?_eq_none]
  simp [List.mem_map, beq_iff_eq]

theorem nodup_map_drop_rfb1 {α β : Type} (f : α → β) (l : List α) (k : Nat)
    (hNodup : (l.map f).Nodup) : ((l.drop k).map f).Nodup := by
  rw [List.map_drop]
  exact hNodup.sublist (List.drop_sublist k (l.map f))

theorem nodup_map_ratchetKey_trDhRatchetState {st : TRState} {peerDh : DY.Bytes} {rngIdx : Nat}
    (hNodup : (st.recv.map RecvChain.ratchetKey).Nodup)
    (hFindNone : findRecvChain st.recv peerDh = none) :
    (((trDhRatchetState st peerDh rngIdx).1).recv.map RecvChain.ratchetKey).Nodup := by
  have hNotMem : peerDh ∉ st.recv.map RecvChain.ratchetKey :=
    (findRecvChain_eq_none_iff_rfb1 st.recv peerDh).mp hFindNone
  let newChain : RecvChain :=
    { ratchetKey := peerDh
      chainKey := (createChain st.rk peerDh st.dhs).2
      index := 0
      rIdx := st.rIdx + 2 }
  have hAppNodup : ((st.recv ++ [newChain]).map RecvChain.ratchetKey).Nodup := by
    rw [List.map_append, List.map_singleton, List.nodup_append]
    refine ⟨hNodup, List.nodup_singleton _, ?_⟩
    intro x hx y hy hxy
    rw [List.mem_singleton] at hy
    subst hy
    subst hxy
    exact hNotMem hx
  simpa [trDhRatchetState, newChain] using
    nodup_map_drop_rfb1 RecvChain.ratchetKey (st.recv ++ [newChain])
      (st.recv.length + 1 - maxReceiverChains) hAppNodup

/-- `trDhRatchetState` preserves `TRRecvCountersFresh` on any trace `tr1` where `st` satisfies it. -/
theorem trRecvCountersFresh_trDhRatchetState
    {tr1 : ExecTrace} {p : Participant} {st : TRState} {pk : DY.Bytes} {rngIdx : Nat}
    (hFresh : TRRecvCountersFresh tr1 p st) :
    TRRecvCountersFresh tr1 p (trDhRatchetState st pk rngIdx).1 := by
  rcases hFresh with ⟨hF1, hF2a, hF2b, hF3, hF4⟩
  have hsinfo : ((trDhRatchetState st pk rngIdx).1).sessionInfo p = st.sessionInfo p := rfl
  have hrIdx_st1 : ((trDhRatchetState st pk rngIdx).1).rIdx = st.rIdx + 2 := rfl
  have hrIdx_c : ((trDhRatchetState st pk rngIdx).2).rIdx = st.rIdx + 2 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    rw [hsinfo]
    rcases mem_trDhRatchetState_recv hd with hd_old | rfl
    · exact hF1 d hd_old
    · refine ⟨?_, ?_⟩
      · intro seed' pqSalt' n' pIdx' i hlog
        have hr_le : ((trDhRatchetState st pk rngIdx).2).rIdx ≤ st.rIdx :=
          hF2a seed' pqSalt' n' _ pIdx' i hlog
        omega
      · intro pk' n' seed' srcIdx' i hlog
        have hr_le : ((trDhRatchetState st pk rngIdx).2).rIdx ≤ st.rIdx :=
          hF2b pk' n' seed' _ srcIdx' i hlog
        omega
  · intro seed' pqSalt' n' r' pIdx' i hlog
    rw [hsinfo] at hlog
    have hr_le : r' ≤ st.rIdx := hF2a seed' pqSalt' n' r' pIdx' i hlog
    omega
  · intro pk' n' seed' r' srcIdx' i hlog
    rw [hsinfo] at hlog
    have hr_le : r' ≤ st.rIdx := hF2b pk' n' seed' r' srcIdx' i hlog
    omega
  · intro d hd
    rcases mem_trDhRatchetState_recv hd with hd_old | rfl
    · have := hF3 d hd_old
      omega
    · omega
  · have hAppNodup : (((st.recv ++ [(trDhRatchetState st pk rngIdx).2]).map RecvChain.rIdx)).Nodup := by
      rw [List.map_append, List.map_singleton, List.nodup_append]
      refine ⟨hF4, List.nodup_singleton _, ?_⟩
      intro x hx y hy hxy
      rw [List.mem_singleton] at hy
      rw [List.mem_map] at hx
      obtain ⟨d, hd, rfl⟩ := hx
      have hd_le : d.rIdx ≤ st.rIdx := hF3 d hd
      omega
    exact nodup_map_drop_rfb1 RecvChain.rIdx (st.recv ++ [(trDhRatchetState st pk rngIdx).2])
      (st.recv.length + 1 - maxReceiverChains) hAppNodup

theorem trRecvCountersFresh_decTailTr_ratchet_consumeMessageKey
    {tr : ExecTrace} {p : Participant} {stateIdx rngIdx : Nat} {st : TRState} {c' : RecvChain}
    {pk seed key pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    (hFresh : TRRecvCountersFresh tr p st)
    (hNodupRk : (st.recv.map RecvChain.ratchetKey).Nodup)
    (hFindNone : findRecvChain st.recv pk = none)
    (hcons : consumeMessageKey (trDhRatchetState st pk rngIdx).2 n = some (seed, c'))
    (hn_bound : n.toNat + 1 < 2 ^ 32) :
    let st1 := (trDhRatchetState st pk rngIdx).1
    let c := (trDhRatchetState st pk rngIdx).2
    TRRecvCountersFresh
      (decTailTr (decRatchetPreTr tr p st1 pk key) p stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n) p
      { st1 with recv := setRecvChain st1.recv c', spqr := spqr' } := by
  intro st1 c
  have hFreshPre : TRRecvCountersFresh (decRatchetPreTr tr p st1 pk key) p st :=
    trRecvCountersFresh_decRatchetPreTr hFresh
  have hFreshSt1 : TRRecvCountersFresh (decRatchetPreTr tr p st1 pk key) p st1 :=
    trRecvCountersFresh_trDhRatchetState hFreshPre
  have hc_mem : c ∈ st1.recv := trDhRatchetState_snd_mem_recv st pk rngIdx
  have hNodupRk1 : (st1.recv.map RecvChain.ratchetKey).Nodup :=
    nodup_map_ratchetKey_trDhRatchetState hNodupRk hFindNone
  exact trRecvCountersFresh_decTailTr_consumeMessageKey hFreshSt1 hc_mem hNodupRk1 hcons hn_bound

/-! ## `TRSkippedRIdxChainRel` Preservation -/

theorem trSkippedRIdxChainRel_ratchet
    {tr : ExecTrace} {p : Participant} {stateIdx : Nat} {st st1 st' : TRState}
    {pk_dh key : DY.Bytes} {c_new c' : RecvChain} {seed pqSalt pt spqr' : DY.Bytes} {n : UInt32}
    (hF : TRRecvCountersFresh tr p st)
    (hRel : TRSkippedRIdxChainRel tr p st)
    (hrk : c'.ratchetKey = c_new.ratchetKey)
    (hrIdx_new : c_new.rIdx = st.rIdx + 2)
    (hrIdx' : c'.rIdx = st.rIdx + 2)
    (hsinfo' : st'.sessionInfo p = st.sessionInfo p)
    (hrecv : ∀ c_post ∈ st'.recv, c_post = c' ∨ c_post ∈ st.recv) :
    TRSkippedRIdxChainRel
      (decTailTr (decRatchetPreTr tr p st1 pk_dh key) p stateIdx st1 c_new c'
        c_new.ratchetKey seed pqSalt pt spqr' n)
      p st' := by
  refine ⟨?_, ?_⟩
  · intro pk₁ n₁ seed₁ srcIdx₁ i₁ pk₂ n₂ seed₂ srcIdx₂ i₂ rIdx h₁ h₂
    rw [hsinfo'] at h₁ h₂
    rcases eventLoggedAt_decTailTr_skippedKeyStored_rfb1 h₁ with hPre₁ | ⟨_, _, _, rfl, _, rfl⟩
    · have hOld₁ := eventLoggedAt_decRatchetPreTr_skippedKeyStored_rfb1 hPre₁
      have hle₁ : rIdx ≤ st.rIdx := hF.2.2.1 pk₁ n₁ seed₁ rIdx srcIdx₁ i₁ hOld₁
      rcases eventLoggedAt_decTailTr_skippedKeyStored_rfb1 h₂ with hPre₂ | ⟨_, _, _, rfl, _, hRIdxEq⟩
      · have hOld₂ := eventLoggedAt_decRatchetPreTr_skippedKeyStored_rfb1 hPre₂
        exact hRel.1 pk₁ n₁ seed₁ srcIdx₁ i₁ pk₂ n₂ seed₂ srcIdx₂ i₂ rIdx hOld₁ hOld₂
      · omega
    · rcases eventLoggedAt_decTailTr_skippedKeyStored_rfb1 h₂ with hPre₂ | ⟨_, _, _, rfl, _, _⟩
      · have hOld₂ := eventLoggedAt_decRatchetPreTr_skippedKeyStored_rfb1 hPre₂
        have hle₂ : c_new.rIdx ≤ st.rIdx := hF.2.2.1 pk₂ n₂ seed₂ c_new.rIdx srcIdx₂ i₂ hOld₂
        omega
      · rfl
  · intro c_post hc_post pk n_k seed_k srcIdx i hlog
    rw [hsinfo'] at hlog
    rcases hrecv c_post hc_post with hc_eq | hc_old
    · rw [hc_eq] at hlog
      rw [hc_eq]
      rcases eventLoggedAt_decTailTr_skippedKeyStored_rfb1 hlog with hPre | ⟨_, _, _, rfl, _, _⟩
      · have hOld := eventLoggedAt_decRatchetPreTr_skippedKeyStored_rfb1 hPre
        have hle : c'.rIdx ≤ st.rIdx := hF.2.2.1 pk n_k seed_k c'.rIdx srcIdx i hOld
        omega
      · exact hrk.symm
    · have hle_c : c_post.rIdx ≤ st.rIdx := hF.2.2.2.1 c_post hc_old
      rcases eventLoggedAt_decTailTr_skippedKeyStored_rfb1 hlog with hPre | ⟨_, _, _, rfl, _, hRIdxEq⟩
      · have hOld := eventLoggedAt_decRatchetPreTr_skippedKeyStored_rfb1 hPre
        exact hRel.2 c_post hc_old pk n_k seed_k srcIdx i hOld
      · omega

/-! ## `TRRecvFreshAll` Step Preservation -/

theorem mem_setRecvChain_iff_of_nodup_rfb1 {chains : List RecvChain} {c c' d : RecvChain}
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

theorem consumeMessageKey_eq_some_iff_rfb1 (c : RecvChain) (counter : UInt32) (seed : DY.Bytes)
    (c' : RecvChain) :
    consumeMessageKey c counter = some (seed, c') ↔
      ¬ counter < c.index ∧
      counter.toNat - c.index.toNat ≤ maxForwardJumps ∧
      counter ≠ u32Max ∧
      seed = (kdfCk (chainKeyAt c.chainKey (counter.toNat - c.index.toNat))).2 ∧
      c' = { c with
        chainKey := (kdfCk (chainKeyAt c.chainKey (counter.toNat - c.index.toNat))).1
        index := counter + 1 } := by
  unfold consumeMessageKey
  split
  · next h1 =>
    simp only [reduceCtorEq, false_iff, not_and]
    intro h; exact absurd h1 h
  · next h1 =>
    split
    · next h2 =>
      simp only [reduceCtorEq, false_iff, not_and]
      intro _ h; omega
    · next h2 =>
      split
      · next h3 =>
        simp only [reduceCtorEq, false_iff, not_and]
        intro _ _ h; exact absurd h3 h
      · next h3 =>
        rw [Option.some.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨hs, hc⟩
          exact ⟨h1, by omega, h3, hs.symm, hc.symm⟩
        · rintro ⟨-, -, -, hs, hc⟩
          exact ⟨hs.symm, hc.symm⟩

theorem consumeMessageKey_ratchetKey_rfb1 {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (h : consumeMessageKey c counter = some (seed, c')) : c'.ratchetKey = c.ratchetKey := by
  obtain ⟨-, -, -, -, rfl⟩ := (consumeMessageKey_eq_some_iff_rfb1 c counter seed c').mp h
  rfl

theorem consumeMessageKey_rIdx_eq_rfb1 {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (h : consumeMessageKey c counter = some (seed, c')) : c'.rIdx = c.rIdx := by
  obtain ⟨-, -, -, -, rfl⟩ := (consumeMessageKey_eq_some_iff_rfb1 c counter seed c').mp h
  rfl

theorem consumeMessageKey_counter_lt_rfb1 {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (h : consumeMessageKey c counter = some (seed, c')) : counter.toNat + 1 < 2 ^ 32 := by
  obtain ⟨-, -, hne, -, -⟩ := (consumeMessageKey_eq_some_iff_rfb1 c counter seed c').mp h
  have hlt : counter.toNat < 2 ^ 32 := counter.toNat_lt
  have hne_val : counter.toNat ≠ 2 ^ 32 - 1 := by
    intro hEq
    apply hne
    apply UInt32.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    exact hEq
  omega

theorem getLocalState_fst_rfb1 (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 =
    match (tr.at? stH : Option StEntry) with
    | some ⟨⟨p, st⟩⟩ => if p = me then some st else none
    | none => none :=
  getLocalState_fst me stH tr

theorem at?_of_getLocalState_rfb1 {tr : ExecTrace} {me : Participant} {stH : Nat} {st : TRState}
    (h : ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 = some st) :
    (tr.at? stH : Option StEntry) = some ⟨⟨me, st⟩⟩ :=
  at?_eq_some_of_getLocalState_some h

theorem at?_ext_lt_rfb1 {E : Type} [ExecTraceTypes.Has E] {t T : ExecTrace} (hle : t ≤ T)
    {j : Nat} (hj : j < t.length) :
    (T.at? j : Option E) = (t.at? j : Option E) := by
  have hj' : j < T.length := Nat.lt_of_lt_of_le hj (Trace.length_le t T hle)
  simp only [Trace.at?, hj, hj', ↓reduceDIte]
  rw [← Trace.at_le t T j hj hle]

theorem isCurrentSnapshot_of_le_rfb1 {t T : ExecTrace} (hle : t ≤ T) {j : Nat} (hj : j < t.length)
    (h : isCurrentSnapshot T j = true) : isCurrentSnapshot t j = true := by
  have hL := Trace.length_le t T hle
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at h ⊢
  rw [at?_ext_lt_rfb1 hle hj] at h
  rcases he : (t.at? j : Option StEntry) with _ | e
  · rw [he] at h; exact h
  · rw [he] at h
    dsimp only at h ⊢
    rw [List.all_eq_true] at h ⊢
    intro k hk
    rw [List.mem_range'] at hk
    obtain ⟨m, hm, hkm⟩ := hk
    have hk' := h k (by rw [List.mem_range']; exact ⟨m, by omega, hkm⟩)
    rwa [at?_ext_lt_rfb1 hle (show k < t.length by omega)] at hk'

theorem part_or_init_ne_of_current_rfb1 {T : ExecTrace} {j k : Nat} {q p : Participant} {s st : TRState}
    (hcur : isCurrentSnapshot T j = true)
    (hj : (T.at? j : Option StEntry) = some ⟨⟨q, s⟩⟩)
    (hk : (T.at? k : Option StEntry) = some ⟨⟨p, st⟩⟩) (hjk : j < k) :
    p ≠ q ∨ st.initiator ≠ s.initiator := by
  have hklt : k < T.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) T k
    rw [hk] at this; exact this
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur
  rw [hj] at hcur
  dsimp only at hcur
  rw [List.all_eq_true] at hcur
  have h2 := hcur k (by rw [List.mem_range']; exact ⟨k - (j + 1), by omega, by omega⟩)
  rw [hk] at h2
  dsimp only at h2
  by_cases hpq : p = q
  · subst hpq
    right
    intro hinit
    simp [hinit] at h2
  · exact Or.inl hpq

theorem sinfo_ne_of_part_or_init_ne_rfb1 {p q : Participant} {s st : TRState}
    (h : p ≠ q ∨ st.initiator ≠ s.initiator) : s.sessionInfo q ≠ st.sessionInfo p := by
  intro heq
  rcases h with h | h
  · exact h (congrArg SessionInfo.me heq).symm
  · exact h (congrArg SessionInfo.initiator heq).symm

theorem decRatchetPreTr_le_rfb1 (tr : ExecTrace) (me : Participant) (st1 : TRState)
    (pk key : DY.Bytes) :
    tr ≤ decRatchetPreTr tr me st1 pk key := by
  unfold decRatchetPreTr
  exact Trace.le_trans _ _ _
    (Trace.le_trans _ _ _
      (Trace.le_trans _ _ _ (Trace.append_le _ _) (Trace.append_le _ _))
      (Trace.append_le _ _))
    (Trace.append_le _ _)

theorem decTailTr_le_rfb1 (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    tr_pre ≤ decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n := by
  unfold decTailTr
  exact Trace.le_trans _ _ _
    (Trace.le_trans _ _ _
      (Trace.le_trans _ _ _
        (logSkippedKeysTr_le (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index
          (n.toNat - c.index.toNat) tr_pre)
        (Trace.append_le _ _))
      (Trace.append_le _ _))
    (Trace.append_le _ _)

theorem at?_stEntry_decRatchetPreTr_rfb1 (tr : ExecTrace) (me : Participant) (st1 : TRState)
    (pk key : DY.Bytes) (i : Nat) :
    ((decRatchetPreTr tr me st1 pk key).at? i : Option StEntry) = (tr.at? i : Option StEntry) := by
  unfold decRatchetPreTr
  rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
      at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl]

theorem at?_stEntry_decTailTr_lt_rfb1 (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes)
    (n : UInt32) {i : Nat} (hi : i < tr_pre.length + (n.toNat - c.index.toNat) + 2) :
    ((decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).at? i : Option StEntry) =
      (tr_pre.at? i : Option StEntry) := by
  unfold decTailTr; dsimp only
  have hlen := logSkippedKeysTr_length (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index
    (n.toNat - c.index.toNat) tr_pre
  rw [at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
      at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl, at?_stEntry_logSkippedKeysTr]

theorem at?_stEntry_decTailTr_last_rfb1 (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    ((decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).at?
        (tr_pre.length + (n.toNat - c.index.toNat) + 2) : Option StEntry) =
      some ⟨⟨me, { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }⟩⟩ := by
  unfold decTailTr; dsimp only
  have hlen := logSkippedKeysTr_length (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index
    (n.toNat - c.index.toNat) tr_pre
  let tr_sk := logSkippedKeysTr (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index
    (n.toNat - c.index.toNat) tr_pre
  let tr_rcv := tr_sk.append (⟨TREvent.Received me st1.peer pk n ptTerm⟩ : TREntry)
  let tr_mid := tr_rcv.append (⟨TREvent.MessageKey (st1.sessionInfo me) .receiver seed pqSalt n
    c.rIdx stateIdx⟩ : TREntry)
  have hmid : tr_pre.length + (n.toNat - c.index.toNat) + 2 = tr_mid.length := by
    dsimp only [tr_mid, tr_rcv, tr_sk]
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    omega
  rw [hmid]
  exact Trace.at?_append tr_mid (⟨⟨me, { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }⟩⟩ : StEntry)

end Symbolic.Swarm.CREF.TR
