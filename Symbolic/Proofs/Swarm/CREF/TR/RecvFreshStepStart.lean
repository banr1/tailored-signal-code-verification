/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvFreshStepPQ
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
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
# Receiver Freshness Preservation Across Initiator Start

Establishes the store-extension lemma `rfs_RF_append_store` and proves
`trRecvFreshAll_snoc_aliceStart`: `Move.aliceStart` preserves `TRRecvFreshAll r₀` when no
session descriptor built from a fresh random draw has prior receiver events.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR

cref_open

open DY DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain)
open DY.Libsignal.TripleRatchet (TRState TREvent isCurrentSnapshot)
open DY.Libsignal.PQXDH (PQXDHEvent)
open Symbolic.Swarm.CREF.TR.RecvDec (StEntry TREntry at?_append_non_entry at?_append_of_lt
  isCurrentSnapshot_append_non_st getLocalState_fst getLocalState_append_stEntry_ne_or_old)
open Symbolic.Swarm.COMPOSED.CompTrace (Preserves Preserves.bind Preserves.pure
  Preserves.failure Preserves.guardP Preserves.getLocalState_pq)

/-! ## Appending a State Store -/

private theorem rfs_isCurrentSnapshot_of_append_stEntry_lt (tr₀ : ExecTrace) (p : Participant)
    (st' : TRState) {idx : Nat} (hlt : idx < tr₀.length)
    (hcur : isCurrentSnapshot (tr₀.append (⟨⟨p, st'⟩⟩ : StEntry)) idx = true) :
    isCurrentSnapshot tr₀ idx = true := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur ⊢
  rw [at?_append_of_lt tr₀ (⟨⟨p, st'⟩⟩ : StEntry) hlt] at hcur
  rcases hat : (tr₀.at? idx : Option StEntry) with _ | ⟨⟨q, st_q⟩⟩
  · rw [hat] at hcur; cases hcur
  · rw [hat] at hcur; dsimp only at hcur ⊢
    have hlen : (tr₀.append (⟨⟨p, st'⟩⟩ : StEntry)).length - (idx + 1) =
        (tr₀.length - (idx + 1)) + 1 := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
    have hsum : (idx + 1) + 1 * (tr₀.length - (idx + 1)) = tr₀.length := by omega
    rw [hlen, List.range'_concat, hsum, List.all_append, Bool.and_eq_true] at hcur
    obtain ⟨hall, _⟩ := hcur
    rw [List.all_eq_true] at hall ⊢
    intro j hj
    have hj_lt : j < tr₀.length := by
      rw [List.mem_range'] at hj
      rcases hj with ⟨i, hi, rfl⟩
      omega
    have hj_step := hall j hj
    rw [at?_append_of_lt tr₀ (⟨⟨p, st'⟩⟩ : StEntry) hj_lt] at hj_step
    exact hj_step

/-- Storing `st'` for `p` preserves `rfs_RF` when `st'` satisfies `TRRecvCountersFresh` and
`TRSkippedRIdxChainRel` on the pre-store trace. -/
theorem rfs_RF_append_store {r₀ : ProtocolSetup} {tr : ExecTrace} (p : Participant) (st' : TRState)
    (hcf' : TRRecvCountersFresh tr p st') (hsk' : TRSkippedRIdxChainRel tr p st')
    (h : rfs_RF r₀ tr) : rfs_RF r₀ (tr.append (⟨⟨p, st'⟩⟩ : StEntry)) := by
  intro q idx st_q hq hget hcur
  have hcf_up : ∀ {q' st''}, TRRecvCountersFresh tr q' st'' →
      TRRecvCountersFresh (tr.append (⟨⟨p, st'⟩⟩ : StEntry)) q' st'' := fun hc =>
    trRecvCountersFresh_of_imp
      (fun _ _ _ _ _ i hev => by
        simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev ⊢; rwa [at?_append_non_entry tr _ rfl i] at hev)
      (fun _ _ _ _ _ i hev => by
        simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev ⊢; rwa [at?_append_non_entry tr _ rfl i] at hev) hc
  have hsk_up : ∀ {q' st''}, TRSkippedRIdxChainRel tr q' st'' →
      TRSkippedRIdxChainRel (tr.append (⟨⟨p, st'⟩⟩ : StEntry)) q' st'' := fun hs =>
    trSkippedRIdxChainRel_of_imp
      (fun _ _ _ _ _ i hev => by
        simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev ⊢; rwa [at?_append_non_entry tr _ rfl i] at hev) hs
  rcases getLocalState_append_stEntry_ne_or_old (tr := tr) (fun _ => rfl) p st' q idx st_q hget with
    ⟨rfl, _, rfl⟩ | hold
  · exact ⟨hcf_up hcf', hsk_up hsk'⟩
  · have hlt : idx < tr.length := by
      rw [getLocalState_fst] at hold
      rcases h1 : (tr.at? idx : Option StEntry) with _ | ⟨⟨q', st_q'⟩⟩
      · rw [h1] at hold; cases hold
      · have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr idx
        rw [h1] at this; exact this
    have hcur₀ := rfs_isCurrentSnapshot_of_append_stEntry_lt tr p st' hlt hcur
    obtain ⟨hcf, hsk⟩ := h q idx st_q hq hold hcur₀
    exact ⟨hcf_up hcf, hsk_up hsk⟩

/-- No receiver `MessageKey` or `SkippedKeyStored` event of descriptor `s` is logged on `tr`. -/
def rfs_NoRecvEv (tr : ExecTrace) (s : SessionInfo) : Prop :=
  (∀ seed pqSalt n r pIdx i,
    ¬ tr.EventLoggedAt (TREvent.MessageKey s .receiver seed pqSalt n r pIdx) i) ∧
  (∀ pk n seed r srcIdx i, ¬ tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed r srcIdx) i)

/-- No stored `TRState` on `tr` has session descriptor `s`. -/
def rfs_NoStored (tr : ExecTrace) (s : SessionInfo) : Prop :=
  ∀ q j st, ((PersistentLocalState.getLocalState q j : Traceful TRState).run tr).1 = some st →
    st.sessionInfo q ≠ s

theorem rfs_fresh_of_noRecvEv {tr : ExecTrace} {p : Participant} {st : TRState}
    (hno : rfs_NoRecvEv tr (st.sessionInfo p)) (hle : ∀ c ∈ st.recv, c.rIdx ≤ st.rIdx)
    (hnd : (st.recv.map RecvChain.rIdx).Nodup) :
    TRRecvCountersFresh tr p st ∧ TRSkippedRIdxChainRel tr p st := by
  obtain ⟨hmk, hsk⟩ := hno
  refine ⟨⟨fun c _ => ⟨fun seed pqSalt n pIdx i hl =>
      absurd hl (hmk seed pqSalt n _ pIdx i),
    fun pk n seed srcIdx i hl => absurd hl (hsk pk n seed _ srcIdx i)⟩,
    fun seed pqSalt n r pIdx i hl => absurd hl (hmk seed pqSalt n r pIdx i),
    fun pk n seed r srcIdx i hl => absurd hl (hsk pk n seed r srcIdx i), hle, hnd⟩,
    fun _ _ _ _ i₁ _ _ _ _ _ rIdx h₁ _ => absurd h₁ (hsk _ _ _ rIdx _ i₁),
    fun c _ pk n seed srcIdx i hl => absurd hl (hsk pk n seed _ srcIdx i)⟩

/-! ## Initiator Walk Invariant and `aliceStart` Step -/

section Alice

open Symbolic.Swarm.COMPOSED.CompTrace (mkRand run_genRand_bind_snd Preserves.receiveMessage
  Preserves.getEntry Preserves.traceLength)

/-- Walk invariant of `aliceStart` from base length `lb`: `rfs_RF`, `lb ≤ tr.length`, and no
descriptor whose `sid` is built from a draw at index `L ≥ lb` has receiver events on `tr`. -/
def rfs_AInv (r₀ : ProtocolSetup) (lb : Nat) (tr : ExecTrace) : Prop :=
  rfs_RF r₀ tr ∧ lb ≤ tr.length ∧
  ∀ L, lb ≤ L → ∀ (rk : DY.Bytes) (s : SessionInfo),
    s.sid = DY.Concat.concat (DY.DiffieHellman.dhPk (mkRand L 32)) rk → rfs_NoRecvEv tr s

theorem rfs_noRecvEv_of_imp {tr tr' : ExecTrace} {s : SessionInfo}
    (himp : ∀ (ev : TREvent) i, tr'.EventLoggedAt ev i →
      (∀ seed pqSalt n r pIdx,
        ev = TREvent.MessageKey s .receiver seed pqSalt n r pIdx → tr.EventLoggedAt ev i) ∧
      (∀ pk n seed r srcIdx, ev = TREvent.SkippedKeyStored s pk n seed r srcIdx → tr.EventLoggedAt ev i))
    (h : rfs_NoRecvEv tr s) : rfs_NoRecvEv tr' s :=
  ⟨fun seed pqSalt n r pIdx i hl =>
      h.1 seed pqSalt n r pIdx i ((himp _ i hl).1 _ _ _ _ _ rfl),
    fun pk n seed r srcIdx i hl => h.2 pk n seed r srcIdx i ((himp _ i hl).2 _ _ _ _ _ rfl)⟩

theorem rfs_AInv_append_non {E : Type} [ExecTraceTypes.Has E] {r₀ : ProtocolSetup} {lb : Nat}
    {tr : ExecTrace} (e : E)
    (hnone_st : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option StEntry) = none)
    (hnone_tr : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (h : rfs_AInv r₀ lb tr) : rfs_AInv r₀ lb (tr.append e) := by
  obtain ⟨hrf, hlen, hno⟩ := h
  have hev : ∀ (ev : TREvent) i, (tr.append e).EventLoggedAt ev i → tr.EventLoggedAt ev i := by
    intro ev i hl; simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hl ⊢; rwa [at?_append_non_entry tr e hnone_tr i] at hl
  refine ⟨rfs_RF_append_non e hnone_st hnone_tr hrf,
    Nat.le_trans hlen (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; exact Nat.le_succ _), ?_⟩
  intro L hL rk s hs
  exact rfs_noRecvEv_of_imp (fun ev i hl => ⟨fun _ _ _ _ _ _ => hev ev i hl,
    fun _ _ _ _ _ _ => hev ev i hl⟩) (hno L hL rk s hs)

theorem rfs_AInv_append_tr {r₀ : ProtocolSetup} {lb : Nat} {tr : ExecTrace} (ev₀ : TREvent)
    (hmk : ∀ s seed pqSalt n r pIdx,
      ev₀ ≠ TREvent.MessageKey s .receiver seed pqSalt n r pIdx)
    (hsk : ∀ s pk n seed r srcIdx, ev₀ ≠ TREvent.SkippedKeyStored s pk n seed r srcIdx)
    (h : rfs_AInv r₀ lb tr) : rfs_AInv r₀ lb (tr.append (⟨ev₀⟩ : TREntry)) := by
  obtain ⟨hrf, hlen, hno⟩ := h
  have hmk' : ∀ s seed pqSalt n r pIdx i,
      (tr.append (⟨ev₀⟩ : TREntry)).EventLoggedAt
        (TREvent.MessageKey s .receiver seed pqSalt n r pIdx) i →
      tr.EventLoggedAt (TREvent.MessageKey s .receiver seed pqSalt n r pIdx) i := by
    intro s seed pqSalt n r pIdx i hl
    rcases (eventLoggedAt_append_trEntry_iff tr _ _ i).mp hl with hl | ⟨_, he⟩
    · exact hl
    · exact absurd he (hmk s seed pqSalt n r pIdx)
  have hsk' : ∀ s pk n seed r srcIdx i,
      (tr.append (⟨ev₀⟩ : TREntry)).EventLoggedAt (TREvent.SkippedKeyStored s pk n seed r srcIdx) i →
      tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed r srcIdx) i := by
    intro s pk n seed r srcIdx i hl
    rcases (eventLoggedAt_append_trEntry_iff tr _ _ i).mp hl with hl | ⟨_, he⟩
    · exact hl
    · exact absurd he (hsk s pk n seed r srcIdx)
  refine ⟨?_,
    Nat.le_trans hlen (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; exact Nat.le_succ _), ?_⟩
  · intro q stateIdx st hq hget hcur
    rw [getLocalState_fst, at?_append_non_entry _ _ rfl, ← getLocalState_fst] at hget
    rw [isCurrentSnapshot_append_non_st _ _ rfl] at hcur
    obtain ⟨hcf, hskr⟩ := hrf q stateIdx st hq hget hcur
    exact ⟨trRecvCountersFresh_of_imp (fun _ _ _ _ _ _ hl => hmk' _ _ _ _ _ _ _ hl)
        (fun _ _ _ _ _ _ hl => hsk' _ _ _ _ _ _ _ hl) hcf,
      trSkippedRIdxChainRel_of_imp (fun _ _ _ _ _ _ hl => hsk' _ _ _ _ _ _ _ hl) hskr⟩
  · intro L hL rk s hs
    obtain ⟨h1, h2⟩ := hno L hL rk s hs
    exact ⟨fun seed pqSalt n r pIdx i hl =>
        h1 seed pqSalt n r pIdx i (hmk' _ _ _ _ _ _ _ hl),
      fun pk n seed r srcIdx i hl => h2 pk n seed r srcIdx i (hsk' _ _ _ _ _ _ _ hl)⟩

variable {r₀ : ProtocolSetup} {lb : Nat}

theorem rfs_ainv_sendMessage (m : DY.Bytes) : Preserves (rfs_AInv r₀ lb) (Network.sendMessage m) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact rfs_AInv_append_non (⟨m⟩ : DY.Network.ExecEntryT) rfl rfl h

theorem rfs_ainv_genRand (n : Nat) : Preserves (rfs_AInv r₀ lb) (Random.genRand n) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact rfs_AInv_append_non (⟨n⟩ : DY.Random.ExecEntryT) rfl rfl h

theorem rfs_ainv_logPQ (ev : PQXDHEvent) : Preserves (rfs_AInv r₀ lb) (ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact rfs_AInv_append_non (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl rfl h

theorem rfs_ainv_logC (ev : ComposedEvent) : Preserves (rfs_AInv r₀ lb) (ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact rfs_AInv_append_non (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT ComposedEvent) rfl rfl h

theorem rfs_ainv_getKey (p : Participant) (h : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    Preserves (rfs_AInv r₀ lb) (DY.Libsignal.PQXDH.getKey p h kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

theorem rfs_ainv_lookupIdentity (p : Participant) (h : Nat) :
    Preserves (rfs_AInv r₀ lb) (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

theorem rfs_ainv_aliceHandshake (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves (rfs_AInv r₀ lb) (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  repeat (first
    | with_reducible apply Preserves.bind | with_reducible apply Preserves.pure
    | with_reducible apply Preserves.failure | with_reducible apply rfs_ainv_genRand
    | with_reducible apply rfs_ainv_getKey | with_reducible apply rfs_ainv_lookupIdentity
    | with_reducible apply Preserves.receiveMessage | with_reducible apply Preserves.guardP
    | split | with_reducible intro)

theorem rfs_ainv_genRand_bind {α : Type} (n : Nat) (k : DY.Bytes → Traceful α)
    (hk : ∀ L, lb ≤ L → Preserves (rfs_AInv r₀ lb) (k (mkRand L n))) :
    Preserves (rfs_AInv r₀ lb) (Random.genRand n >>= k) := by
  intro tr h
  rw [run_genRand_bind_snd]
  exact hk tr.length h.2.1 _ (rfs_AInv_append_non (⟨n⟩ : DY.Random.ExecEntryT) rfl rfl h)

theorem rfs_ainv_storeAlice (a : Participant) (st : TRState) (L : Nat) (hL : lb ≤ L) (rk : DY.Bytes)
    (hsid : st.sid = DY.Concat.concat (DY.DiffieHellman.dhPk (mkRand L 32)) rk)
    (hle : ∀ c ∈ st.recv, c.rIdx ≤ st.rIdx) (hnd : (st.recv.map RecvChain.rIdx).Nodup) :
    Preserves (rfs_AInv r₀ lb) (PersistentLocalState.storeLocalState a st) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  show rfs_AInv r₀ lb (tr.append (⟨⟨a, st⟩⟩ : StEntry))
  obtain ⟨hrf, hlen, hno⟩ := h
  obtain ⟨hcf, hsk⟩ := rfs_fresh_of_noRecvEv (hno L hL rk (st.sessionInfo a) hsid) hle hnd
  have hev : ∀ (ev : TREvent) i, (tr.append (⟨⟨a, st⟩⟩ : StEntry)).EventLoggedAt ev i →
      tr.EventLoggedAt ev i := by
    intro ev i hl; simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hl ⊢; rwa [at?_append_non_entry tr _ rfl i] at hl
  refine ⟨rfs_RF_append_store a st hcf hsk hrf,
    Nat.le_trans hlen (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; exact Nat.le_succ _), ?_⟩
  intro L' hL' rk' s hs
  exact rfs_noRecvEv_of_imp (fun ev i hl => ⟨fun _ _ _ _ _ _ => hev ev i hl,
    fun _ _ _ _ _ _ => hev ev i hl⟩) (hno L' hL' rk' s hs)

theorem rfs_ainv_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves (rfs_AInv r₀ lb) (aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine Preserves.bind (rfs_ainv_aliceHandshake a b idStateIdx regIdxB h) fun o => ?_
  refine rfs_ainv_genRand_bind 32 _ fun L hL => ?_
  refine Preserves.bind (rfs_ainv_sendMessage _) fun _ => ?_
  refine Preserves.bind (rfs_ainv_sendMessage _) fun _ => ?_
  refine Preserves.bind Preserves.traceLength fun _ => ?_
  refine Preserves.bind (rfs_ainv_logPQ _) fun _ => ?_
  refine Preserves.bind (fun tr h => by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
    exact rfs_AInv_append_tr _ (fun _ _ _ _ _ _ he => by cases he)
      (fun _ _ _ _ _ _ he => by cases he) h) fun _ => ?_
  refine Preserves.bind (rfs_ainv_logC _) fun _ => ?_
  refine rfs_ainv_storeAlice a _ L hL o.keys.rk rfl ?_ ?_
  · intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact Nat.le_refl _
  · simp

end Alice

open Symbolic.Swarm.COMPOSED.CompTrace (mkRand) in
/-- `Move.aliceStart` preserves `TRRecvFreshAll r₀` when no session descriptor built from a draw
at index `L ≥ (runTraceMoves r₀ ms).length` has prior receiver events (`trRecvSid_fresh_alice`). -/
theorem trRecvFreshAll_snoc_aliceStart (r₀ : ProtocolSetup) (ms : List Move) (a b : Participant)
    (idStateIdx regIdxB : Nat) (bh : DY.Libsignal.PQXDH.BundleHandles) (shown : Nat)
    (h : TRRecvFreshAll r₀ ms)
    (hA : ∀ L, (runTraceMoves r₀ ms).length ≤ L → ∀ (rk : DY.Bytes) (s : SessionInfo),
      s.sid = DY.Concat.concat (DY.DiffieHellman.dhPk (mkRand L 32)) rk →
      rfs_NoRecvEv (runTraceMoves r₀ ms) s) :
    TRRecvFreshAll r₀ (ms ++ [Move.aliceStart a b idStateIdx regIdxB bh shown]) := by
  rw [rfs_RF_iff, runTrace_snoc]
  have hinv : rfs_AInv r₀ (runTraceMoves r₀ ms).length (runTraceMoves r₀ ms) := ⟨h, Nat.le_refl _, hA⟩
  have hp : Preserves (rfs_AInv r₀ (runTraceMoves r₀ ms).length)
      (Move.aliceStart a b idStateIdx regIdxB bh shown).act := by
    unfold Move.act
    exact Preserves.bind (rfs_ainv_aliceStart a b idStateIdx regIdxB bh) fun _ => Preserves.pure _
  exact (hp _ hinv).1

end Symbolic.Swarm.CREF.TR
