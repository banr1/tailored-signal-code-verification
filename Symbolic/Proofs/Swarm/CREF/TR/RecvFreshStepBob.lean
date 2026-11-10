/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvFreshStepStart
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
# Receiver Freshness Preservation Across Responder Start

Proves `trRecvFreshAll_snoc_bobStart`: `Move.bobStart` preserves `TRRecvFreshAll r₀` whenever
its newly derived session descriptor has no prior receiver events or stored snapshots on the
pre-step trace.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR

cref_open

open DY DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain findRecvChain setRecvChain recvChainFor
  consumeMessageKey x25519LowOrder)
open DY.Libsignal.TripleRatchet (TRState TREvent)
open DY.Libsignal.PQXDH (PQXDHEvent)
open Symbolic.Swarm.CREF.TR.RecvDec (StEntry TREntry at?_append_non_entry
  isCurrentSnapshot_append_non_st getLocalState_fst trDhRatchetState
  ensureReceiverChain_run_ratchet)
open Symbolic.Swarm.COMPOSED.CompTrace (Preserves Preserves.bind Preserves.pure Preserves.failure
  Preserves.guardP Preserves.getLocalState_pq Preserves.receiveMessage Preserves.getEntry
  Preserves.traceLength Preserves.requireTracePredicate Preserves.guardTrace Preserves.receiveSignalMsg
  Preserves.verifyMacAndDecrypt)

/-- `ev` is a receiver `MessageKey` or `SkippedKeyStored` event of descriptor `s`. -/
def rfs_EvOf (s : SessionInfo) (ev : TREvent) : Prop :=
  (∃ seed pqSalt n r pIdx,
    ev = TREvent.MessageKey s .receiver seed pqSalt n r pIdx) ∨
  (∃ pk n seed r srcIdx, ev = TREvent.SkippedKeyStored s pk n seed r srcIdx)

theorem rfs_RF_append_tr_of {r₀ : ProtocolSetup} {tr : ExecTrace} (ev₀ : TREvent)
    (hof : ∀ q j st, ((PersistentLocalState.getLocalState q j : Traceful TRState).run tr).1 = some st →
      ¬ rfs_EvOf (st.sessionInfo q) ev₀)
    (h : rfs_RF r₀ tr) : rfs_RF r₀ (tr.append (⟨ev₀⟩ : TREntry)) := by
  intro q stateIdx st hq hget hcur
  rw [getLocalState_fst, at?_append_non_entry _ _ rfl, ← getLocalState_fst] at hget
  rw [isCurrentSnapshot_append_non_st _ _ rfl] at hcur
  obtain ⟨hcf, hskr⟩ := h q stateIdx st hq hget hcur
  have hne := hof q stateIdx st hget
  have hmk : ∀ seed pqSalt n r pIdx i,
      (tr.append (⟨ev₀⟩ : TREntry)).EventLoggedAt
        (TREvent.MessageKey (st.sessionInfo q) .receiver seed pqSalt n r pIdx) i →
      tr.EventLoggedAt (TREvent.MessageKey (st.sessionInfo q) .receiver seed pqSalt n r pIdx) i := by
    intro seed pqSalt n r pIdx i hl
    rcases (eventLoggedAt_append_trEntry_iff tr _ _ i).mp hl with hl | ⟨_, he⟩
    · exact hl
    · exact (hne (Or.inl ⟨seed, pqSalt, n, r, pIdx, he⟩)).elim
  have hsk : ∀ pk n seed r srcIdx i,
      (tr.append (⟨ev₀⟩ : TREntry)).EventLoggedAt (TREvent.SkippedKeyStored (st.sessionInfo q) pk n seed r srcIdx) i →
      tr.EventLoggedAt (TREvent.SkippedKeyStored (st.sessionInfo q) pk n seed r srcIdx) i := by
    intro pk n seed r srcIdx i hl
    rcases (eventLoggedAt_append_trEntry_iff tr _ _ i).mp hl with hl | ⟨_, he⟩
    · exact hl
    · exact (hne (Or.inr ⟨pk, n, seed, r, srcIdx, he⟩)).elim
  exact ⟨trRecvCountersFresh_of_imp (fun _ _ _ _ _ _ hl => hmk _ _ _ _ _ _ hl)
      (fun _ _ _ _ _ _ hl => hsk _ _ _ _ _ _ hl) hcf,
    trSkippedRIdxChainRel_of_imp (fun _ _ _ _ _ _ hl => hsk _ _ _ _ _ _ hl) hskr⟩

/-! ## Responder Walk Invariant -/

/-- Every receiver `MessageKey` or `SkippedKeyStored` event of `s` on `tr` belongs to the
initial responder chain at `rIdx = 2` for ratchet key `pk`, consumed up to counter `N`. -/
def rfs_BEv (s : SessionInfo) (pk : DY.Bytes) (N : UInt32) (tr : ExecTrace) : Prop :=
  (∀ seed pqSalt n r pIdx i,
    tr.EventLoggedAt (TREvent.MessageKey s .receiver seed pqSalt n r pIdx) i →
    r = 2 ∧ n ≤ N) ∧
  (∀ pk' n seed r srcIdx i, tr.EventLoggedAt (TREvent.SkippedKeyStored s pk' n seed r srcIdx) i →
    r = 2 ∧ n < N ∧ pk' = pk)

/-- Walk invariant before storing the initial responder state: `rfs_RF`, no stored state with
descriptor `s`, and `rfs_BEv s pk N`. -/
def rfs_BInv (r₀ : ProtocolSetup) (s : SessionInfo) (pk : DY.Bytes) (N : UInt32) (tr : ExecTrace) : Prop :=
  rfs_RF r₀ tr ∧ rfs_NoStored tr s ∧ rfs_BEv s pk N tr

theorem rfs_uint32_succ_toNat {N : UInt32} (hN : N.toNat + 1 < 2 ^ 32) :
    (N + 1).toNat = N.toNat + 1 := by
  rw [UInt32.toNat_add]
  exact Nat.mod_eq_of_lt hN

theorem rfs_consumeMessageKey_bound {c c' : RecvChain} {n : UInt32} {seed : DY.Bytes}
    (h : consumeMessageKey c n = some (seed, c')) : n.toNat + 1 < 2 ^ 32 := by
  unfold consumeMessageKey at h
  split at h
  · nomatch h
  · split at h
    · nomatch h
    · split at h
      · nomatch h
      · next hne =>
        have hlt : n.toNat < 2 ^ 32 := n.toNat_lt
        have hne_val : n.toNat ≠ 2 ^ 32 - 1 := by
          intro hEq; apply hne
          apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq; exact hEq
        omega

theorem rfs_fresh_of_BEv {tr : ExecTrace} {p : Participant} {st : TRState} {pk : DY.Bytes}
    {N : UInt32} {c' : RecvChain} (hev : rfs_BEv (st.sessionInfo p) pk N tr)
    (hrecv : st.recv = [c']) (hrIdx : st.rIdx = 2) (hc'r : c'.rIdx = 2) (hc'k : c'.ratchetKey = pk)
    (hc'i : c'.index = N + 1) (hN : N.toNat + 1 < 2 ^ 32) :
    TRRecvCountersFresh tr p st ∧ TRSkippedRIdxChainRel tr p st := by
  obtain ⟨hmk, hsk⟩ := hev
  have hsucc := rfs_uint32_succ_toNat hN
  have hle_lt : ∀ n : UInt32, n ≤ N → n < c'.index := fun n hn => by
    rw [hc'i]; rw [UInt32.le_iff_toNat_le] at hn; rw [UInt32.lt_iff_toNat_lt, hsucc]; omega
  have hlt_lt : ∀ n : UInt32, n < N → n < c'.index := fun n hn => by
    rw [hc'i]; rw [UInt32.lt_iff_toNat_lt] at hn; rw [UInt32.lt_iff_toNat_lt, hsucc]; omega
  refine ⟨⟨fun c hc => ?_, fun seed pqSalt n r pIdx i hl => ?_,
      fun pk' n seed r srcIdx i hl => ?_, fun c hc => ?_, ?_⟩, ?_, fun c hc => ?_⟩
  · rw [hrecv, List.mem_singleton] at hc; subst hc
    exact ⟨fun seed pqSalt n pIdx i hl => hle_lt n (hmk _ _ _ _ _ i hl).2,
      fun pk' n seed srcIdx i hl => hlt_lt n (hsk _ _ _ _ _ i hl).2.1⟩
  · have := (hmk _ _ _ _ _ i hl).1; omega
  · have := (hsk _ _ _ _ _ i hl).1; omega
  · rw [hrecv, List.mem_singleton] at hc; subst hc; omega
  · rw [hrecv]; exact List.nodup_singleton _
  · intro pk₁ n₁ seed₁ srcIdx₁ i₁ pk₂ n₂ seed₂ srcIdx₂ i₂ rIdx h₁ h₂
    rw [(hsk _ _ _ _ _ _ h₁).2.2, (hsk _ _ _ _ _ _ h₂).2.2]
  · rw [hrecv, List.mem_singleton] at hc; subst hc
    intro pk' n seed srcIdx i hl
    rw [(hsk _ _ _ _ _ _ hl).2.2, hc'k]

section BInv

variable {r₀ : ProtocolSetup} {s : SessionInfo} {pk : DY.Bytes} {N : UInt32}

theorem rfs_BInv_append_non {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} (e : E)
    (hnone_st : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option StEntry) = none)
    (hnone_tr : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (h : rfs_BInv r₀ s pk N tr) : rfs_BInv r₀ s pk N (tr.append e) := by
  obtain ⟨hrf, hns, hmk, hsk⟩ := h
  have hev : ∀ (ev : TREvent) i, (tr.append e).EventLoggedAt ev i → tr.EventLoggedAt ev i := by
    intro ev i hl; simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hl ⊢; rwa [at?_append_non_entry tr e hnone_tr i] at hl
  refine ⟨rfs_RF_append_non e hnone_st hnone_tr hrf, ?_, fun _ _ _ _ _ i hl =>
    hmk _ _ _ _ _ i (hev _ i hl), fun _ _ _ _ _ i hl => hsk _ _ _ _ _ i (hev _ i hl)⟩
  intro q j st hget
  rw [getLocalState_fst, at?_append_non_entry tr e hnone_st, ← getLocalState_fst] at hget
  exact hns q j st hget

theorem rfs_BInv_append_tr {tr : ExecTrace} (ev₀ : TREvent)
    (hof : ∀ s', rfs_EvOf s' ev₀ → s' = s)
    (hmk : ∀ seed pqSalt n r pIdx,
      ev₀ = TREvent.MessageKey s .receiver seed pqSalt n r pIdx → r = 2 ∧ n ≤ N)
    (hsk : ∀ pk' n seed r srcIdx, ev₀ = TREvent.SkippedKeyStored s pk' n seed r srcIdx →
      r = 2 ∧ n < N ∧ pk' = pk)
    (h : rfs_BInv r₀ s pk N tr) : rfs_BInv r₀ s pk N (tr.append (⟨ev₀⟩ : TREntry)) := by
  obtain ⟨hrf, hns, hbm, hbs⟩ := h
  refine ⟨rfs_RF_append_tr_of ev₀ (fun q j st hget hev => hns q j st hget (hof _ hev)) hrf,
    ?_, ?_, ?_⟩
  · intro q j st hget
    rw [getLocalState_fst, at?_append_non_entry _ _ rfl, ← getLocalState_fst] at hget
    exact hns q j st hget
  · intro seed pqSalt n r pIdx i hl
    rcases (eventLoggedAt_append_trEntry_iff tr _ _ i).mp hl with hl | ⟨_, he⟩
    · exact hbm _ _ _ _ _ i hl
    · exact hmk _ _ _ _ _ he
  · intro pk' n seed r srcIdx i hl
    rcases (eventLoggedAt_append_trEntry_iff tr _ _ i).mp hl with hl | ⟨_, he⟩
    · exact hbs _ _ _ _ _ i hl
    · exact hsk _ _ _ _ _ he

theorem rfs_BInv_append_tr_irrel {tr : ExecTrace} (ev₀ : TREvent)
    (hmk : ∀ s' seed pqSalt n r pIdx,
      ev₀ ≠ TREvent.MessageKey s' .receiver seed pqSalt n r pIdx)
    (hsk : ∀ s' pk' n seed r srcIdx, ev₀ ≠ TREvent.SkippedKeyStored s' pk' n seed r srcIdx)
    (h : rfs_BInv r₀ s pk N tr) : rfs_BInv r₀ s pk N (tr.append (⟨ev₀⟩ : TREntry)) :=
  rfs_BInv_append_tr ev₀
    (fun s' hev => by
      rcases hev with ⟨_, _, _, _, _, he⟩ | ⟨_, _, _, _, _, he⟩
      · exact (hmk _ _ _ _ _ _ he).elim
      · exact (hsk _ _ _ _ _ _ he).elim)
    (fun _ _ _ _ _ he => (hmk _ _ _ _ _ _ he).elim)
    (fun _ _ _ _ _ he => (hsk _ _ _ _ _ _ he).elim) h

theorem rfs_binv_sendMessage (m : DY.Bytes) :
    Preserves (rfs_BInv r₀ s pk N) (Network.sendMessage m) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact rfs_BInv_append_non (⟨m⟩ : DY.Network.ExecEntryT) rfl rfl h

theorem rfs_binv_genRand (n : Nat) : Preserves (rfs_BInv r₀ s pk N) (Random.genRand n) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact rfs_BInv_append_non (⟨n⟩ : DY.Random.ExecEntryT) rfl rfl h

theorem rfs_binv_logPQ (ev : PQXDHEvent) :
    Preserves (rfs_BInv r₀ s pk N) (ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact rfs_BInv_append_non (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl rfl h

theorem rfs_binv_logC (ev : ComposedEvent) : Preserves (rfs_BInv r₀ s pk N) (ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact rfs_BInv_append_non (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT ComposedEvent) rfl rfl h

theorem rfs_binv_logTR_irrel (ev₀ : TREvent)
    (hmk : ∀ s' seed pqSalt n r pIdx,
      ev₀ ≠ TREvent.MessageKey s' .receiver seed pqSalt n r pIdx)
    (hsk : ∀ s' pk' n seed r srcIdx, ev₀ ≠ TREvent.SkippedKeyStored s' pk' n seed r srcIdx) :
    Preserves (rfs_BInv r₀ s pk N) (ProtocolEvent.logEvent ev₀) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact rfs_BInv_append_tr_irrel ev₀ hmk hsk h

theorem rfs_binv_logSkippedKeys (srcIdx : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32), n.toNat + k ≤ N.toNat →
      Preserves (rfs_BInv r₀ s pk N) (TripleRatchet.logSkippedKeys s pk 2 srcIdx ck n k)
  | 0, _, _, _ => Preserves.pure _
  | k + 1, ck, n, hk => by
    have hNlt : N.toNat < 2 ^ 32 := N.toNat_lt
    have hn1 : n.toNat + 1 < 2 ^ 32 := by omega
    have hsucc := rfs_uint32_succ_toNat hn1
    have hlt : n < N := by rw [UInt32.lt_iff_toNat_lt]; omega
    refine Preserves.bind ?_ fun _ =>
      rfs_binv_logSkippedKeys srcIdx k _ (n + 1) (by rw [hsucc]; omega)
    intro tr h
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
    refine rfs_BInv_append_tr _ ?_ ?_ ?_ h
    · intro s' hev
      rcases hev with ⟨_, _, _, _, _, he⟩ | ⟨_, _, _, _, _, he⟩
      · cases he
      · cases he; rfl
    · intro _ _ _ _ _ he; cases he
    · intro _ _ _ _ _ he; cases he; exact ⟨rfl, hlt, rfl⟩

end BInv

/-! ## Pre/Post Trace Triples and `bobStart` Step -/

/-- Running `m` from a trace satisfying `P` produces a trace satisfying `Q`. -/
def rfs_Trip (P Q : ExecTrace → Prop) {α : Type} (m : Traceful α) : Prop :=
  ∀ tr, P tr → Q (m.run tr).2.val

theorem rfs_Trip.bind {P Q : ExecTrace → Prop} {α β : Type} {x : Traceful α}
    {f : α → Traceful β} (hPQ : ∀ tr, P tr → Q tr) (hx : Preserves P x)
    (hf : ∀ a, rfs_Trip P Q (f a)) : rfs_Trip P Q (x >>= f) := by
  intro tr h
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
  rcases hr : (x.run tr).1 with _ | a
  · exact hPQ _ (hx tr h)
  · exact hf a _ (hx tr h)

theorem rfs_Trip.failure {P Q : ExecTrace → Prop} {α : Type} (hPQ : ∀ tr, P tr → Q tr) :
    rfs_Trip P Q (failure : Traceful α) := by
  intro tr h
  rw [Traceful.run_failure]
  exact hPQ tr h

theorem rfs_Trip.ensureReceiverChain {P Q : ExecTrace → Prop} {β : Type} {st : TRState}
    {pk : DY.Bytes} {f : TRState × RecvChain × Bool → Traceful β}
    (hfind : findRecvChain st.recv pk = none)
    (hPQ : ∀ tr, P tr → Q tr) (hgen : Preserves P (Random.genRand 32))
    (hf : ∀ L, rfs_Trip P Q
      (f ((trDhRatchetState st pk L).1, (trDhRatchetState st pk L).2, true))) :
    rfs_Trip P Q (TripleRatchet.ensureReceiverChain st pk >>= f) := by
  intro tr h
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
  by_cases hlow : x25519LowOrder pk = true
  · have h0 : ((TripleRatchet.ensureReceiverChain st pk).run tr).1 = none ∧
        ((TripleRatchet.ensureReceiverChain st pk).run tr).2.val = tr := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor TRState.toDRState
      dsimp only; rw [hfind]; simp only [hlow, ↓reduceIte, Traceful.run_failure, and_self]
    rw [h0.1, h0.2]; exact hPQ _ h
  · have hlow' : x25519LowOrder pk = false := by simpa using hlow
    obtain ⟨h1, h2⟩ := ensureReceiverChain_run_ratchet (st := st) tr hfind hlow'
    rw [h1, h2]
    have hgen' : P (tr.append (⟨32⟩ : DY.Random.ExecEntryT)) := by
      have hg := hgen tr h
      simpa only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
        Traceful.run_bind, Traceful.run_mk, Traceful.run_pure] using hg
    exact hf tr.length _ hgen'

theorem rfs_Trip.ensureReceiverChain_fresh {P Q : ExecTrace → Prop} {β : Type} {st : TRState}
    {pk : DY.Bytes} {f : TRState × RecvChain × Bool → Traceful β}
    (hrecv : st.recv = []) (hrIdx : st.rIdx = 0)
    (hPQ : ∀ tr, P tr → Q tr) (hgen : Preserves P (Random.genRand 32))
    (hf : ∀ (st1 : TRState) (c : RecvChain), st1.sid = st.sid → st1.initiator = st.initiator →
      st1.peer = st.peer → st1.recv = [c] → st1.rIdx = 2 → c.rIdx = 2 → c.ratchetKey = pk →
      rfs_Trip P Q (f (st1, c, true))) :
    rfs_Trip P Q (TripleRatchet.ensureReceiverChain st pk >>= f) := by
  refine rfs_Trip.ensureReceiverChain (by rw [hrecv]; rfl) hPQ hgen fun L => ?_
  refine hf _ _ rfl rfl rfl ?_ ?_ ?_ rfl
  · show (st.recv ++ _).drop _ = _
    rw [hrecv]; rfl
  · show st.rIdx + 2 = 2
    rw [hrIdx]
  · show st.rIdx + 2 = 2
    rw [hrIdx]

theorem rfs_ro_getKey (p : Participant) (h : Nat) (kind : DY.Libsignal.PQXDH.KeyKind)
    (T : ExecTrace) : Preserves (· = T) (DY.Libsignal.PQXDH.getKey p h kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

theorem rfs_ro_lookupIdentity (p : Participant) (h : Nat) (T : ExecTrace) :
    Preserves (· = T) (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

theorem rfs_ro_bobHandshake (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (regIdxA ekIdx ctIdx : Nat) (T : ExecTrace) :
    ((DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx).run T).2.val = T := by
  have hp : Preserves (· = T) (DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx) := by
    unfold DY.Libsignal.PQXDH.bobHandshake
    repeat (first
      | with_reducible apply Preserves.bind | with_reducible apply Preserves.pure
      | with_reducible apply Preserves.failure | with_reducible apply rfs_ro_getKey
      | with_reducible apply rfs_ro_lookupIdentity
      | with_reducible apply Preserves.receiveMessage | with_reducible apply Preserves.guardP
      | split | with_reducible intro)
  exact hp T rfl

theorem rfs_Trip_bobStore {r₀ : ProtocolSetup} {s : SessionInfo} {pk : DY.Bytes} {N : UInt32}
    (b : Participant) (seed pqSalt : DY.Bytes) (pIdx : Nat) (st' : TRState) (c' : RecvChain)
    (hs : st'.sessionInfo b = s) (hrecv : st'.recv = [c']) (hrIdx : st'.rIdx = 2) (hc'r : c'.rIdx = 2)
    (hc'k : c'.ratchetKey = pk) (hc'i : c'.index = N + 1) (hN : N.toNat + 1 < 2 ^ 32) :
    rfs_Trip (rfs_BInv r₀ s pk N) (rfs_RF r₀)
      (TripleRatchet.logMessageKeyAndStore b s .receiver seed pqSalt N 2 pIdx st') := by
  subst hs
  intro tr h
  have h1 := rfs_BInv_append_tr (tr := tr)
    (TREvent.MessageKey (st'.sessionInfo b) .receiver seed pqSalt N 2 pIdx)
    (fun s' hev => by
      rcases hev with ⟨_, _, _, _, _, he⟩ | ⟨_, _, _, _, _, he⟩
      · cases he; rfl
      · cases he)
    (fun _ _ _ _ _ he => by cases he; exact ⟨rfl, UInt32.le_iff_toNat_le.mpr (Nat.le_refl _)⟩)
    (fun _ _ _ _ _ he => by cases he) h
  obtain ⟨hrf, -, hev⟩ := h1
  obtain ⟨hcf, hsk⟩ := rfs_fresh_of_BEv hev hrecv hrIdx hc'r hc'k hc'i hN
  unfold TripleRatchet.logMessageKeyAndStore
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_pure, Traceful.run_mk]
  exact rfs_RF_append_store b st' hcf hsk hrf

theorem rfs_RF_bobStart (r₀ : ProtocolSetup) (T : ExecTrace) (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32)
    (hrf : rfs_RF r₀ T)
    (hB : ∀ o,
      ((DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA mh.ek mh.ct).run T).1 = some o →
      ∀ (rkey : DY.Bytes),
        let s : SessionInfo := ⟨DY.Concat.concat (DY.X25519.normalizeX25519Key rkey) o.keys.rk, false, b, a⟩
        rfs_NoRecvEv T s ∧ rfs_NoStored T s) :
    rfs_RF r₀ ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run T).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
  rcases ho : ((DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA mh.ek mh.ct).run T).1 with _ | o
  · dsimp only; rw [rfs_ro_bobHandshake]; exact hrf
  · dsimp only
    rw [rfs_ro_bobHandshake, Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
    have hro : ((TripleRatchet.receiveSignalMsg mh.msg).run T).2.val = T :=
      (Preserves.receiveSignalMsg (Inv := (· = T)) mh.msg) T rfl
    rcases hm : ((TripleRatchet.receiveSignalMsg mh.msg).run T).1 with _ | msg
    · dsimp only; rw [hro]; exact hrf
    · dsimp only; rw [hro]
      obtain ⟨hno, hns⟩ := hB o ho msg.ratchetKey
      refine rfs_Trip.ensureReceiverChain_fresh
        (P := rfs_BInv r₀ ⟨DY.Concat.concat (DY.X25519.normalizeX25519Key msg.ratchetKey) o.keys.rk, false, b, a⟩
          msg.ratchetKey msg.counter) (by rfl) (by rfl) (fun _ h => h.1) (rfs_binv_genRand 32)
          (fun st1 c hsid hini hpeer hrecv1 hrIdx1 hcr0 hck0 => ?_) T
        ⟨hrf, hns, fun _ _ _ _ _ i hl => (hno.1 _ _ _ _ _ i hl).elim,
          fun _ _ _ _ _ i hl => (hno.2 _ _ _ _ _ i hl).elim⟩
      have hsb : st1.sessionInfo b =
          ⟨DY.Concat.concat (DY.X25519.normalizeX25519Key msg.ratchetKey) o.keys.rk, false, b, a⟩ := by
        show (⟨st1.sid, st1.initiator, b, st1.peer⟩ : SessionInfo) = _
        rw [hsid, hini, hpeer]
      dsimp only
      rw [hsb, hcr0]
      split
      · next seed c' hcons =>
        obtain ⟨hidx, hck, hcr, hci⟩ := consumeMessageKey_props hcons
        have hN := rfs_consumeMessageKey_bound hcons
        have hk : c'.ratchetKey = msg.ratchetKey := hck.trans hck0
        have hr : c'.rIdx = 2 := hcr.trans hcr0
        have hidx' : c.index.toNat ≤ msg.counter.toNat := UInt32.le_iff_toNat_le.mp hidx
        have hrecv' : setRecvChain st1.recv c' = [c'] := by
          rw [hrecv1]; simp [setRecvChain, hck0, hk]
        have hPQ : ∀ tr, rfs_BInv r₀
            ⟨DY.Concat.concat (DY.X25519.normalizeX25519Key msg.ratchetKey) o.keys.rk, false, b, a⟩
            msg.ratchetKey msg.counter tr → rfs_RF r₀ tr := fun _ h => h.1
        have hskb : c.index.toNat + (msg.counter.toNat - c.index.toNat) ≤ msg.counter.toNat := by
          omega
        repeat (first
          | with_reducible (exact rfs_Trip.failure hPQ)
          | (exfalso; exact ‹¬true = true› rfl)
          | (with_reducible refine rfs_Trip.bind hPQ ?_ fun _ => ?_
             first
               | with_reducible apply rfs_binv_sendMessage
               | with_reducible apply Preserves.receiveMessage
               | with_reducible apply Preserves.verifyMacAndDecrypt
               | with_reducible apply Preserves.requireTracePredicate
               | with_reducible apply Preserves.traceLength
               | with_reducible apply Preserves.pure
               | with_reducible apply rfs_binv_logPQ
               | with_reducible apply rfs_binv_logC
               | ((with_reducible apply rfs_binv_logSkippedKeys); exact hskb)
               | exact rfs_binv_logTR_irrel _ (fun _ _ _ _ _ _ he => by cases he)
                   (fun _ _ _ _ _ _ he => by cases he))
          | split
          | (exact rfs_Trip_bobStore b seed _ _ _ c' (by exact hsb) (by exact hrecv')
                (by exact hrIdx1) hr hk hci hN))
      · exact rfs_Trip.failure (fun _ h => h.1)

theorem trRecvFreshAll_snoc_bobStart (r₀ : ProtocolSetup) (ms : List Move) (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32)
    (shown : Nat) (h : TRRecvFreshAll r₀ ms)
    (hB : ∀ o,
      ((DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA mh.ek mh.ct).run (runTraceMoves r₀ ms)).1 = some o →
      ∀ (rkey : DY.Bytes),
        let s : SessionInfo := ⟨DY.Concat.concat (DY.X25519.normalizeX25519Key rkey) o.keys.rk, false, b, a⟩
        rfs_NoRecvEv (runTraceMoves r₀ ms) s ∧ rfs_NoStored (runTraceMoves r₀ ms) s) :
    TRRecvFreshAll r₀ (ms ++ [Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown]) := by
  rw [rfs_RF_iff, runTrace_snoc]
  rw [rfs_RF_iff] at h
  have key := rfs_RF_bobStart r₀ (runTraceMoves r₀ ms) b a kh regIdxA mh pqIdx spqrMsgIdx h hB
  unfold Move.next Move.act
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
  split
  · rw [Traceful.run_pure]; exact key
  · exact key

end Symbolic.Swarm.CREF.TR
