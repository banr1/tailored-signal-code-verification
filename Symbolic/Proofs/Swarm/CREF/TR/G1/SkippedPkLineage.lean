/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTR
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.COMPOSED.CompLineage
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.Leaks
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
# Skipped Message-Key Chain Lineage

Proves `SkippedPkLineageInv` on all reachable traces (`skippedPkLineageInv_reachable`): every
`TREvent.SkippedKeyStored s pk n seed rIdx src` entry originates from a receive chain `c` keyed by
`pk` at index `rIdx` whose message seed at `n` is `seed`, paired with both a post-state witness
`st_post` holding the advanced chain `c'` and a source-index witness `st` at `src`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

open DY DY.Comparse DY.DiffieHellman DY.Libsignal DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet (SessionInfo KeyComponent KeyDir RecvChain findRecvChain
  setRecvChain recvChainFor consumeMessageKey chainKeyAt kdfCk maxForwardJumps maxReceiverChains
  u32Max createChain x25519LowOrder)
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys BundleHandles BobKeyHandles PreKeyMsgHandles
  registerIdentity registerCorruptIdentity genSignedPrekey genPQPrekey genOneTimePrekey compromiseIK
  compromiseSPK compromisePQSPK compromiseOPK invertDH invertKEM opkUsedB)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace Symbolic.Swarm.COMPOSED.CompRatchet
open Symbolic.Swarm.COMPOSED.CompInv (EvE)

private theorem at?_eq_none_of_le {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) {i : Nat}
    (hi : tr.length ≤ i) : (tr.at? i : Option E) = none := by
  have h : ¬ i < tr.length := by omega
  simp only [Trace.at?, h, ↓reduceDIte]

private theorem trace_snoc_at_length {Entry : Type} (tr : DY.Trace Entry) (x : Entry)
    (h : tr.length < (tr.snoc x).length) :
    (tr.snoc x).at tr.length h = x := by
  simp only [Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

private theorem trace_append_at_length {Entry E1 : Type} [DY.TraceEntryHas E1 Entry]
    (tr : DY.Trace Entry) (e : E1) (h : tr.length < (tr.append e).length) :
    (tr.append e).at tr.length h = DY.TraceEntryHas.inj e := by
  have h' : tr.length < (tr.snoc (DY.TraceEntryHas.inj e)).length := by
    rwa [Symbolic.DYBridge.DY.Trace.append_eq_1] at h
  simpa only [Symbolic.DYBridge.DY.Trace.append_eq_1] using
    trace_snoc_at_length tr (DY.TraceEntryHas.inj e) h'

private theorem at?_append_non_entry {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = none)
    (i : Nat) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  by_cases hlt : i < tr.length
  · exact at?_append_of_lt tr e hlt
  · by_cases heq : i = tr.length
    · subst heq
      have h1 : tr.length < (tr.append e).length := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
      have h2 : ¬ tr.length < tr.length := Nat.lt_irrefl _
      simp only [Trace.at?, h1, h2, ↓reduceDIte, trace_append_at_length, hnone]
    · rw [at?_eq_none_of_le (tr.append e)
            (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
          at?_eq_none_of_le tr (by omega)]

private def logSkippedKeysTr (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat) :
    DY.Bytes → UInt32 → Nat → ExecTrace → ExecTrace
  | _, _, 0, tr => tr
  | ck, n, k + 1, tr =>
    logSkippedKeysTr s pk rIdx sourceStateIdx (kdfCk ck).1 (n + 1) k
      (tr.append (⟨TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx⟩ : TREntry))

private theorem logSkippedKeys_run (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) :
    ((logSkippedKeys s pk rIdx sourceStateIdx ck n k).run tr).1 = some () ∧
      ((logSkippedKeys s pk rIdx sourceStateIdx ck n k).run tr).2.val =
        logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr := by
  induction k generalizing ck n tr with
  | zero =>
    unfold logSkippedKeys logSkippedKeysTr
    rw [Traceful.run_pure]
    exact ⟨rfl, rfl⟩
  | succ k ih =>
    unfold logSkippedKeys logSkippedKeysTr
    rw [run_bind_fst, run_bind_snd]
    have hlog1 : ((DY.ProtocolEvent.logEvent
        (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx)).run tr).1 = some () := by
      rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
        run_bind_fst, Traceful.run_mk]
      dsimp only; rw [Traceful.run_pure]
    have hlog2 : ((DY.ProtocolEvent.logEvent
        (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx)).run tr).2.val =
        tr.append (⟨TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx⟩ : TREntry) := by
      rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
        run_bind_snd, Traceful.run_mk]
      dsimp only; rw [Traceful.run_pure]
    rw [hlog1, hlog2]
    exact ih (kdfCk ck).1 (n + 1) _

private theorem logSkippedKeysTr_length (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) :
    (logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).length = tr.length + k := by
  induction k generalizing ck n tr with
  | zero => exact (Nat.add_zero _).symm
  | succ k ih =>
    unfold logSkippedKeysTr; rw [ih]
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega

private theorem logSkippedKeysTr_le (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) :
    tr ≤ logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr := by
  induction k generalizing ck n tr with
  | zero => exact Trace.le_refl tr
  | succ k ih =>
    unfold logSkippedKeysTr
    exact Trace.le_trans _ _ _ (Trace.append_le tr _) (ih (kdfCk ck).1 (n + 1) _)

private theorem at?_trEntry_logSkippedKeysTr_lt (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) {i : Nat} (hi : i < tr.length) :
    ((logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).at? i : Option TREntry) =
      (tr.at? i : Option TREntry) := by
  induction k generalizing ck n tr with
  | zero => rfl
  | succ k ih =>
    unfold logSkippedKeysTr
    rw [ih _ _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
      at?_append_of_lt tr _ hi]

private theorem at?_trEntry_logSkippedKeysTr_add (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
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
      rw [at?_trEntry_logSkippedKeysTr_lt _ _ _ _ _ _ _ _
        (show tr.length < (tr.append _).length by
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)]
      rw [Trace.at?_append]
      have hn : n + UInt32.ofNat 0 = n := UInt32.add_zero n
      rw [hn]; rfl
    | succ j' =>
      have hj' : j' < k := by omega
      have hlen : tr.length + (j' + 1) =
          (tr.append (⟨TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx⟩ : TREntry)).length + j' := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
      rw [hlen, ih (kdfCk ck).1 (n + 1) _ hj']
      have hn : (n + 1) + UInt32.ofNat j' = n + UInt32.ofNat (j' + 1) := by
        apply UInt32.eq_of_toBitVec_eq
        change n.toBitVec + 1#32 + BitVec.ofNat 32 j' = n.toBitVec + BitVec.ofNat 32 (j' + 1)
        rw [BitVec.ofNat_add]; ac_rfl
      rw [hn]; rfl

/-- The receive chain created by `dhRatchetStep st pk`. -/
def freshRecvChain (st : TRState) (pk : DY.Bytes) : RecvChain :=
  { ratchetKey := pk, chainKey := (createChain st.rk pk st.dhs).2, index := 0, rIdx := st.rIdx + 2 }

/-- Lineage witness for a `TREvent.SkippedKeyStored s pk n seed rIdx src` entry on `tr`. -/
def SkippedPkLineageAt (tr : ExecTrace) (s : SessionInfo) (pk : DY.Bytes) (n : UInt32)
    (seed : DY.Bytes) (rIdx src : Nat) : Prop :=
  ∃ (p : Participant) (k_post : Nat) (st_post st : TRState) (c c' : RecvChain)
    (cnt : UInt32) (seed_m : DY.Bytes),
    ((PersistentLocalState.getLocalState p k_post : Traceful TRState).run tr).1 = some st_post ∧
    st_post.sessionInfo p = s ∧
    c' ∈ st_post.recv ∧
    c.ratchetKey = pk ∧
    c.rIdx = rIdx ∧
    (consumeMessageKey c n).map Prod.fst = some seed ∧
    n < cnt ∧
    consumeMessageKey c cnt = some (seed_m, c') ∧
    ((PersistentLocalState.getLocalState p src : Traceful TRState).run tr).1 = some st ∧
    st.sessionInfo p = s ∧
    (c ∈ st.recv ∨ c = freshRecvChain st pk ∨
      (k_post = src ∧ st = st_post ∧ rIdx = 2 ∧ c.index = 0))

/-- Trace invariant: every `SkippedKeyStored` event on `tr` satisfies `SkippedPkLineageAt`. -/
def SkippedPkLineageInv (tr : ExecTrace) : Prop :=
  ∀ (i : Nat) (s : SessionInfo) (pk : DY.Bytes) (n : UInt32) (seed : DY.Bytes) (rIdx src : Nat),
    (tr.at? i : Option CompTrace.TREntry) =
      some ⟨TREvent.SkippedKeyStored s pk n seed rIdx src⟩ →
    SkippedPkLineageAt tr s pk n seed rIdx src

/-! ## Helper Lemmas on `getLocalState`, `setRecvChain`, and `consumeMessageKey` -/

theorem getLocalState_some_iff_trStateStoredAt {p : Participant} {st : TRState} {idx : Nat}
    {tr : ExecTrace} :
    ((PersistentLocalState.getLocalState p idx : Traceful TRState).run tr).1 = some st ↔
      TRStateStoredAt p st idx tr := by
  rw [CompTrace.getLocalState_tr_fst]
  unfold TRStateStoredAt
  rcases h : (tr.at? idx : Option CompTrace.TRStEntry) with _ | ⟨⟨q, st'⟩⟩
  · simp
  · simp only [Option.some.injEq, PersistentGlobalState.State.ExecEntryT.mk.injEq,
      PersistentLocalState.LocalState.mk.injEq]
    by_cases hq : q = p
    · subst hq; simp
    · simp [hq]

theorem SkippedPkLineageAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr')
    {s : SessionInfo} {pk : DY.Bytes} {n : UInt32} {seed : DY.Bytes} {rIdx src : Nat}
    (h : SkippedPkLineageAt tr s pk n seed rIdx src) :
    SkippedPkLineageAt tr' s pk n seed rIdx src := by
  obtain ⟨p, k_post, st_post, st, c, c', cnt, seed_m,
    hst_post, hs_post, hc'_mem, hrk, hridx, hseed, hlt, hcons, hst_src, hs_src, hdisj⟩ := h
  refine ⟨p, k_post, st_post, st, c, c', cnt, seed_m,
    getLocalState_some_iff_trStateStoredAt.mpr
      (CompTrace.trStateStoredAt_mono hle (getLocalState_some_iff_trStateStoredAt.mp hst_post)),
    hs_post, hc'_mem, hrk, hridx, hseed, hlt, hcons,
    getLocalState_some_iff_trStateStoredAt.mpr
      (CompTrace.trStateStoredAt_mono hle (getLocalState_some_iff_trStateStoredAt.mp hst_src)),
    hs_src, hdisj⟩

theorem mem_setRecvChain_of_mem {recv : List RecvChain} {c c' : RecvChain}
    (hc : c ∈ recv) (hrk : c.ratchetKey = c'.ratchetKey) :
    c' ∈ setRecvChain recv c' := by
  unfold setRecvChain
  rw [List.mem_map]
  refine ⟨c, hc, ?_⟩
  simp [hrk]

theorem mem_drop_append_singleton_maxReceiverChains (recv : List RecvChain) (c : RecvChain) :
    c ∈ (recv ++ [c]).drop ((recv.length + 1) - maxReceiverChains) := by
  have hle : (recv.length + 1) - maxReceiverChains ≤ recv.length := by
    unfold maxReceiverChains; omega
  rw [List.drop_append_of_le_length hle]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem consumeMessageKey_ratchetKey_eq {c c' : RecvChain} {cnt : UInt32} {seed_m : DY.Bytes}
    (hcons : consumeMessageKey c cnt = some (seed_m, c')) :
    c.ratchetKey = c'.ratchetKey := by
  unfold consumeMessageKey at hcons
  split at hcons; · cases hcons
  split at hcons; · cases hcons
  split at hcons; · cases hcons
  cases hcons; rfl

theorem consumeMessageKey_skipped_at {c c' : RecvChain} {cnt : UInt32} {seed_m : DY.Bytes}
    (hcons : consumeMessageKey c cnt = some (seed_m, c'))
    {j : Nat} (hj : j < cnt.toNat - c.index.toNat) :
    c.index + UInt32.ofNat j < cnt ∧
      (consumeMessageKey c (c.index + UInt32.ofNat j)).map Prod.fst =
        some (kdfCk (chainKeyAt c.chainKey j)).2 := by
  unfold consumeMessageKey at hcons
  split at hcons; · cases hcons
  next hnot_lt =>
    split at hcons; · cases hcons
    next hnot_jmp =>
      split at hcons; · cases hcons
      next hnot_max =>
        have hidx_le : c.index.toNat ≤ cnt.toNat := Nat.le_of_not_lt hnot_lt
        have hjmp_le : cnt.toNat - c.index.toNat ≤ maxForwardJumps := Nat.le_of_not_lt hnot_jmp
        have hcnt_lt_size : cnt.toNat < 4294967296 := cnt.toBitVec.isLt
        have hn_toNat : (c.index + UInt32.ofNat j).toNat = c.index.toNat + j := by
          have hj_mod : (UInt32.ofNat j).toNat = j := Nat.mod_eq_of_lt (by omega)
          rw [UInt32.toNat_add, hj_mod, Nat.mod_eq_of_lt (by omega)]
        have hn_lt_cnt : c.index + UInt32.ofNat j < cnt := by
          rw [UInt32.lt_iff_toNat_lt, hn_toNat]; omega
        have hnot_n_lt : ¬ (c.index + UInt32.ofNat j < c.index) := by
          rw [UInt32.lt_iff_toNat_lt, hn_toNat]; omega
        have hsub_eq : (c.index + UInt32.ofNat j).toNat - c.index.toNat = j := by
          rw [hn_toNat]; omega
        have hnot_n_jmp : ¬ (maxForwardJumps < (c.index + UInt32.ofNat j).toNat - c.index.toNat) := by
          rw [hsub_eq]; omega
        have hnot_n_max : c.index + UInt32.ofNat j ≠ u32Max := by
          intro heq
          have h1 : (c.index + UInt32.ofNat j).toNat = u32Max.toNat := congrArg UInt32.toNat heq
          have h2 : u32Max.toNat = 4294967295 := rfl
          omega
        refine ⟨hn_lt_cnt, ?_⟩
        unfold consumeMessageKey
        rw [ite_eq_right_iff.mpr fun h => absurd h hnot_n_lt,
            ite_eq_right_iff.mpr fun h => absurd h hnot_n_jmp,
            ite_eq_right_iff.mpr fun h => absurd h hnot_n_max, hsub_eq]
        rfl

/-! ## Preservation Under Non-`SkippedKeyStored` Appends and `decryptTail` -/

theorem skippedPkLineageInv_nil : SkippedPkLineageInv Trace.nil := by
  intro i _ _ _ _ _ _ hat
  have hnil : (Trace.nil : ExecTrace).length ≤ i := by
    rw [Symbolic.DYBridge.DY.Trace.length_eq_1]
    exact Nat.zero_le i
  rw [at?_eq_none_of_le Trace.nil hnil] at hat
  cases hat

theorem skippedPkLineageInv_append_non_tr {tr : ExecTrace} {E : Type} [ExecTraceTypes.Has E] {e : E}
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option CompTrace.TREntry) = none := by rfl)
    (hInv : SkippedPkLineageInv tr) :
    SkippedPkLineageInv (tr.append e) := by
  intro i s pk n seed rIdx src hat
  rw [at?_append_non_entry tr e hnone i] at hat
  exact (hInv i s pk n seed rIdx src hat).mono (Trace.append_le tr e)

theorem skippedPkLineageInv_append_trEv_nonSkip {tr : ExecTrace} {ev : TREvent}
    (hne : ∀ s pk n seed rIdx src, ev ≠ TREvent.SkippedKeyStored s pk n seed rIdx src)
    (hInv : SkippedPkLineageInv tr) :
    SkippedPkLineageInv (tr.append (TREvE ev)) := by
  intro i s pk n seed rIdx src hat
  have hle : tr ≤ tr.append (TREvE ev) := Trace.append_le tr (TREvE ev)
  by_cases hlt : i < tr.length
  · rw [at?_append_of_lt tr (TREvE ev) hlt] at hat
    exact (hInv i s pk n seed rIdx src hat).mono hle
  · by_cases heq : i = tr.length
    · subst heq
      rw [Trace.at?_append] at hat
      injection hat with h1
      injection h1 with h2
      exact False.elim (hne s pk n seed rIdx src h2)
    · rw [at?_eq_none_of_le (tr.append (TREvE ev))
            (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)] at hat
      cases hat

theorem skippedPkLineageInv_decryptTail {tr : ExecTrace}
    (me : Participant) (st1 st_src : TRState) (pk : DY.Bytes) (c c' : RecvChain)
    (cnt : UInt32) (seed_m pqSalt m spqr' : DY.Bytes) (src parIdx : Nat)
    (hInv : SkippedPkLineageInv tr)
    (hc_rk : c.ratchetKey = pk)
    (hc_mem1 : c ∈ st1.recv)
    (hcons : consumeMessageKey c cnt = some (seed_m, c'))
    (hsrc :
      (((PersistentLocalState.getLocalState me src : Traceful TRState).run tr).1 = some st_src ∧
        st_src.sessionInfo me = st1.sessionInfo me ∧
        (c ∈ st_src.recv ∨ c = freshRecvChain st_src pk)) ∨
      (src = tr.length + (cnt.toNat - c.index.toNat) + 2 ∧
        st_src = { st1 with recv := setRecvChain st1.recv c', spqr := spqr' } ∧
        c.rIdx = 2 ∧ c.index = 0)) :
    let skipped := cnt.toNat - c.index.toNat
    let st_post : TRState := { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }
    SkippedPkLineageInv (((do
      DY.Libsignal.TripleRatchet.logSkippedKeys (st1.sessionInfo me) pk c.rIdx src c.chainKey c.index skipped
      ProtocolEvent.logEvent (TREvent.Received me st1.peer pk cnt m)
      DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st1.sessionInfo me) .receiver seed_m pqSalt
        cnt c.rIdx parIdx st_post).run tr).2.val) := by
  intro skipped st_post
  let tr₁ := logSkippedKeysTr (st1.sessionInfo me) pk c.rIdx src c.chainKey c.index skipped tr
  let tr₂ := tr₁.append (TREvE (.Received me st1.peer pk cnt m))
  let tr₃ := tr₂.append (TREvE (.MessageKey (st1.sessionInfo me) .receiver seed_m pqSalt
    cnt c.rIdx parIdx))
  let tr_end := tr₃.append (TRStE me st_post)
  have hrun : (((do
      DY.Libsignal.TripleRatchet.logSkippedKeys (st1.sessionInfo me) pk c.rIdx src c.chainKey c.index skipped
      ProtocolEvent.logEvent (TREvent.Received me st1.peer pk cnt m)
      DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st1.sessionInfo me) .receiver seed_m pqSalt
        cnt c.rIdx parIdx st_post).run tr).2.val) = tr_end := by
    simp only [DY.Libsignal.TripleRatchet.logMessageKeyAndStore,
      Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_pure, Traceful.run_mk,
      logSkippedKeys_run]
    rfl
  rw [hrun]
  have hle₀₁ : tr ≤ tr₁ := logSkippedKeysTr_le _ _ _ _ _ _ _ tr
  have hle₁₂ : tr₁ ≤ tr₂ := Trace.append_le tr₁ _
  have hle₂₃ : tr₂ ≤ tr₃ := Trace.append_le tr₂ _
  have hle₃₄ : tr₃ ≤ tr_end := Trace.append_le tr₃ _
  have hle₀₄ : tr ≤ tr_end :=
    Trace.le_trans _ _ _ hle₀₁ (Trace.le_trans _ _ _ hle₁₂ (Trace.le_trans _ _ _ hle₂₃ hle₃₄))
  have hlen₁ : tr₁.length = tr.length + skipped :=
    logSkippedKeysTr_length _ _ _ _ _ _ _ tr
  have hlen₃ : tr₃.length = tr.length + skipped + 2 := by
    simp only [tr₃, tr₂, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  have hst_post_stored : TRStateStoredAt me st_post tr₃.length tr_end :=
    CompTrace.at?_append_here tr₃ (TRStE me st_post)
  have hst_post_get :
      ((PersistentLocalState.getLocalState me tr₃.length : Traceful TRState).run tr_end).1 = some st_post :=
    getLocalState_some_iff_trStateStoredAt.mpr hst_post_stored
  have hc'_mem : c' ∈ st_post.recv :=
    mem_setRecvChain_of_mem hc_mem1 (consumeMessageKey_ratchetKey_eq hcons)
  intro i s' pk' n' seed' rIdx' src' hat
  rw [at?_append_non_entry tr₃ (TRStE me st_post) rfl i] at hat
  have hat₂ : (tr₂.at? i : Option CompTrace.TREntry) =
      some ⟨TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src'⟩ := by
    by_cases hlt₂ : i < tr₂.length
    · rwa [at?_append_of_lt tr₂ _ hlt₂] at hat
    · by_cases heq₂ : i = tr₂.length
      · subst heq₂; rw [Trace.at?_append] at hat; nomatch hat
      · rw [at?_eq_none_of_le tr₃
              (by simp only [tr₃, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)] at hat
        cases hat
  have hat₁ : (tr₁.at? i : Option CompTrace.TREntry) =
      some ⟨TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src'⟩ := by
    by_cases hlt₁ : i < tr₁.length
    · rwa [at?_append_of_lt tr₁ _ hlt₁] at hat₂
    · by_cases heq₁ : i = tr₁.length
      · subst heq₁; rw [Trace.at?_append] at hat₂; nomatch hat₂
      · rw [at?_eq_none_of_le tr₂
              (by simp only [tr₂, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)] at hat₂
        cases hat₂
  rcases Nat.lt_or_ge i tr.length with hi_lt | hi_ge
  · rw [at?_trEntry_logSkippedKeysTr_lt _ _ _ _ _ _ _ tr hi_lt] at hat₁
    exact (hInv i s' pk' n' seed' rIdx' src' hat₁).mono hle₀₄
  · have hi_lt₁ : i < tr₁.length := by
      have hlen := Trace.at?_eq_some_implies_length_le (EntryT := CompTrace.TREntry) tr₁ i
      rwa [hat₁] at hlen
    have hj_lt : i - tr.length < skipped := by omega
    have hi_eq : i = tr.length + (i - tr.length) := by omega
    have hat_add := at?_trEntry_logSkippedKeysTr_add
      (st1.sessionInfo me) pk c.rIdx src c.chainKey c.index skipped tr hj_lt
    rw [hi_eq, hat_add] at hat₁
    injection hat₁ with hE
    injection hE with hE'
    injection hE' with hs_eq hpk_eq hn_eq hseed_eq hridx_eq hsrc_eq
    subst hs_eq hpk_eq hn_eq hseed_eq hridx_eq hsrc_eq
    obtain ⟨hn_lt_cnt, hcons_n⟩ := consumeMessageKey_skipped_at hcons hj_lt
    rcases hsrc with ⟨hst_src_tr, hs_src, hdisj_src⟩ | ⟨hsrc_eq, hst_src_eq, hridx2, hidx0⟩
    · have hst_src_end :
          ((PersistentLocalState.getLocalState me src : Traceful TRState).run tr_end).1 = some st_src :=
        getLocalState_some_iff_trStateStoredAt.mpr
          (CompTrace.trStateStoredAt_mono hle₀₄ (getLocalState_some_iff_trStateStoredAt.mp hst_src_tr))
      refine ⟨me, tr₃.length, st_post, st_src, c, c', cnt, seed_m,
        hst_post_get, rfl, hc'_mem, hc_rk, rfl, hcons_n, hn_lt_cnt, hcons,
        hst_src_end, hs_src, ?_⟩
      rcases hdisj_src with hmem | hfresh
      · exact .inl hmem
      · exact .inr (.inl hfresh)
    · have hk_post_eq : tr₃.length = src := by omega
      exact ⟨me, tr₃.length, st_post, st_post, c, c', cnt, seed_m,
        hst_post_get, rfl, hc'_mem, hc_rk, rfl, hcons_n, hn_lt_cnt, hcons,
        hk_post_eq ▸ hst_post_get, rfl, .inr (.inr ⟨hk_post_eq, rfl, hridx2, hidx0⟩)⟩

/-! ## `PQSkLinAt` Combinators and Transition Preservation -/

def PQSkLinAt (tr : ExecTrace) {α : Type} (Q : ExecTrace → α → Prop) (x : Traceful α) : Prop :=
  SkippedPkLineageInv tr →
    SkippedPkLineageInv (x.run tr).2.val ∧
    ∀ a, (x.run tr).1 = some a → Q (x.run tr).2.val a

theorem PQSkLinAt.bind {tr : ExecTrace} {α β : Type}
    {Q : ExecTrace → α → Prop} {R : ExecTrace → β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : PQSkLinAt tr Q x) (hf : ∀ tr1 a, tr ≤ tr1 → Q tr1 a → PQSkLinAt tr1 R (f a)) :
    PQSkLinAt tr R (x >>= f) := by
  intro hJ
  rw [Traceful.run_bind]
  have hx0 := hx hJ
  rcases h : x.run tr with ⟨_ | a, trMid, hmid⟩ <;> rw [h] at hx0
  · exact ⟨hx0.1, fun _ hb => by cases hb⟩
  · exact hf trMid a hmid (hx0.2 a rfl) hx0.1

theorem PQSkLinAt.of_id {tr : ExecTrace} {α : Type} {x : Traceful α}
    (hx : (x.run tr).2.val = tr) : PQSkLinAt tr (fun tr1 _ => tr1 = tr) x := by
  intro hJ; rw [hx]; exact ⟨hJ, fun _ _ => rfl⟩

theorem PQSkLinAt.pure {tr : ExecTrace} {α : Type} {Q : ExecTrace → α → Prop}
    (a : α) (ha : Q tr a) : PQSkLinAt tr Q (Pure.pure a : Traceful α) := by
  unfold PQSkLinAt
  rw [Traceful.run_pure]
  intro hJ
  refine ⟨hJ, fun b hb => ?_⟩; cases hb; exact ha

theorem PQSkLinAt.failure {tr : ExecTrace} {α : Type} {Q : ExecTrace → α → Prop} :
    PQSkLinAt tr Q (Alternative.failure : Traceful α) := by
  unfold PQSkLinAt
  rw [Traceful.run_failure]
  exact fun hJ => ⟨hJ, fun _ hb => by cases hb⟩

theorem PQSkLinAt.guardP {tr : ExecTrace} (p : Prop) [Decidable p] :
    PQSkLinAt tr (fun tr1 _ => tr1 = tr ∧ p) (_root_.guard p : Traceful Unit) := by
  unfold _root_.guard
  split
  · rename_i hp; exact PQSkLinAt.pure () ⟨rfl, hp⟩
  · exact PQSkLinAt.failure

theorem PQSkLinAt.guardTrace {tr : ExecTrace} (p : ExecTrace → Bool) :
    PQSkLinAt tr (fun tr1 _ => tr1 = tr) (DY.Libsignal.TripleRatchet.guardTrace p) := by
  apply PQSkLinAt.of_id
  unfold DY.Libsignal.TripleRatchet.guardTrace
  rw [Traceful.run_mk]

theorem PQSkLinAt.traceLength {tr : ExecTrace} :
    PQSkLinAt tr (fun tr1 _ => tr1 = tr) DY.Libsignal.TripleRatchet.traceLength := by
  apply PQSkLinAt.of_id
  unfold DY.Libsignal.TripleRatchet.traceLength
  rw [Traceful.run_mk]

theorem PQSkLinAt.genRand {tr : ExecTrace} (n : Nat) :
    PQSkLinAt tr (fun _ _ => True) (Random.genRand n) := by
  intro hJ
  have hg : ((Random.genRand n).run tr).2.val = tr.append (RndE n) := by
    rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      CompTrace.run_bind_snd, Traceful.run_mk]
    dsimp only; rw [Traceful.run_pure]
  rw [hg]
  exact ⟨skippedPkLineageInv_append_non_tr rfl hJ, fun _ _ => trivial⟩

theorem PQSkLinAt.sendMessage {tr : ExecTrace} (m : DY.Bytes) :
    PQSkLinAt tr (fun _ _ => True) (Network.sendMessage m) := by
  intro hJ
  rw [CompPresTRExp.run_sendMessage_snd]
  exact ⟨skippedPkLineageInv_append_non_tr rfl hJ, fun _ _ => trivial⟩

theorem PQSkLinAt.storeLocalState {tr : ExecTrace} (p : Participant) (st : TRState) :
    PQSkLinAt tr (fun _ _ => True) (PersistentLocalState.storeLocalState p st) := by
  intro hJ
  have hg : ((PersistentLocalState.storeLocalState p st).run tr).2.val = tr.append (TRStE p st) := by
    rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  rw [hg]
  exact ⟨skippedPkLineageInv_append_non_tr rfl hJ, fun _ _ => trivial⟩

theorem PQSkLinAt.logEvent_nonSkip {tr : ExecTrace} (ev : TREvent)
    (hne : ∀ s pk n seed rIdx src, ev ≠ TREvent.SkippedKeyStored s pk n seed rIdx src) :
    PQSkLinAt tr (fun _ _ => True) (ProtocolEvent.logEvent ev) := by
  intro hJ
  have hg : ((ProtocolEvent.logEvent ev).run tr).2.val = tr.append (TREvE ev) := by
    rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      CompTrace.run_bind_snd, Traceful.run_mk]
    dsimp only; rw [Traceful.run_pure]
  rw [hg]
  exact ⟨skippedPkLineageInv_append_trEv_nonSkip hne hJ, fun _ _ => trivial⟩

theorem PQSkLinAt.logMessageKeyAndStore {tr : ExecTrace} (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx p : Nat) (st : TRState) :
    PQSkLinAt tr (fun _ _ => True)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx p st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  refine PQSkLinAt.bind (PQSkLinAt.logEvent_nonSkip _ (by intros; rintro ⟨⟩)) fun _ _ _ _ => ?_
  exact PQSkLinAt.storeLocalState me st

theorem PQSkLinAt.getLocalState {tr : ExecTrace} (me : Participant) (stH : Nat) :
    PQSkLinAt tr
      (fun tr1 st => tr1 = tr ∧
        ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 = some st)
      (PersistentLocalState.getLocalState me stH) := by
  intro hJ
  rw [CompTrace.getLocalState_tr_snd]
  exact ⟨hJ, fun st hst => ⟨rfl, hst⟩⟩

theorem PQSkLinAt.getEntryTR {tr : ExecTrace} (evH : Nat) :
    PQSkLinAt tr (fun tr1 _ => tr1 = tr) (DY.getEntry evH : Traceful CompTrace.TREntry) := by
  apply PQSkLinAt.of_id
  rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]

theorem PQSkLinAt.receiveMessage {tr : ExecTrace} (msgH : Nat) :
    PQSkLinAt tr (fun tr1 _ => tr1 = tr) (Network.receiveMessage msgH) := by
  intro hJ
  rw [CompTrace.receiveMessage_snd]
  exact ⟨hJ, fun _ _ => rfl⟩

theorem PQSkLinAt.receiveSignalMsg {tr : ExecTrace} (msgH : Nat) :
    PQSkLinAt tr (fun tr1 _ => tr1 = tr) (DY.Libsignal.TripleRatchet.receiveSignalMsg msgH) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine PQSkLinAt.bind (PQSkLinAt.receiveMessage msgH) fun _ t _ ht => ?_
  subst ht
  rcases parseTrSignalMsg t with _ | msg
  · exact PQSkLinAt.failure
  · exact PQSkLinAt.bind (PQSkLinAt.guardP _) fun _ _ _ ⟨ht1, _⟩ => PQSkLinAt.pure msg ht1

theorem PQSkLinAt.verifyMacAndDecrypt {tr : ExecTrace} (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) :
    PQSkLinAt tr (fun tr1 _ => tr1 = tr)
      (DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed) :=
  PQSkLinAt.of_id (CompTrace.verifyMacAndDecrypt_trace st msg pqSalt seed tr)

theorem findRecvChain_eq_some_iff_mem_and_ratchetKey {recv : List RecvChain} {pk : DY.Bytes}
    {c : RecvChain} (h : findRecvChain recv pk = some c) :
    c ∈ recv ∧ c.ratchetKey = pk := by
  unfold findRecvChain at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

def EnsureChainLin (st0 st1 : TRState) (pk : DY.Bytes) (c : RecvChain) : Prop :=
  (∀ me, st0.sessionInfo me = st1.sessionInfo me) ∧
  c.ratchetKey = pk ∧
  c ∈ st1.recv ∧
  (c ∈ st0.recv ∨ c = freshRecvChain st0 pk)

theorem PQSkLinAt.dhRatchetStep {tr : ExecTrace} (st0 : TRState) (pk : DY.Bytes) :
    PQSkLinAt tr (fun _ (r : TRState × RecvChain) => EnsureChainLin st0 r.1 pk r.2)
      (DY.Libsignal.TripleRatchet.dhRatchetStep st0 pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine PQSkLinAt.bind (PQSkLinAt.guardP _) fun _ _ _ _ => ?_
  rcases hc1 : createChain st0.rk pk st0.dhs with ⟨rk1, ckr⟩
  dsimp only
  refine PQSkLinAt.bind (PQSkLinAt.genRand 32) fun _ dhs _ _ => ?_
  rcases hc2 : createChain rk1 pk dhs with ⟨rk2, cks⟩
  dsimp only
  have hckr_eq : ckr = (createChain st0.rk pk st0.dhs).2 := by rw [hc1]
  refine PQSkLinAt.pure _ ⟨fun _ => rfl, rfl, ?_, .inr ?_⟩
  · exact mem_drop_append_singleton_maxReceiverChains st0.recv _
  · unfold freshRecvChain
    rw [hckr_eq]

theorem PQSkLinAt.ensureReceiverChain {tr : ExecTrace} (st0 : TRState) (pk : DY.Bytes) :
    PQSkLinAt tr (fun _ (r : TRState × RecvChain × Bool) => EnsureChainLin st0 r.1 pk r.2.1)
      (DY.Libsignal.TripleRatchet.ensureReceiverChain st0 pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor
  rcases hfind : findRecvChain st0.recv pk with _ | c
  · dsimp only
    rcases x25519LowOrder pk with _ | _
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact PQSkLinAt.bind (PQSkLinAt.dhRatchetStep st0 pk) fun _ ⟨st', c'⟩ _ hr =>
        PQSkLinAt.pure _ hr
    · simp only [↓reduceIte]
      exact PQSkLinAt.failure
  · dsimp only
    obtain ⟨hmem, hrk⟩ := findRecvChain_eq_some_iff_mem_and_ratchetKey hfind
    exact PQSkLinAt.pure _ ⟨fun _ => rfl, hrk, hmem, .inl hmem⟩

theorem PQSkLinAt.messageEncryptAbort {tr : ExecTrace} (me : Participant) (stH : Nat) :
    PQSkLinAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  exact PQSkLinAt.bind (PQSkLinAt.getLocalState me stH) fun _ _ _ _ =>
    PQSkLinAt.bind (PQSkLinAt.genRand 32) fun _ _ _ _ => PQSkLinAt.failure

theorem PQSkLinAt.messageEncrypt {tr : ExecTrace} (me : Participant) (stH coinsLen pqIdx : Nat) :
    PQSkLinAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine PQSkLinAt.bind (PQSkLinAt.getLocalState me stH) fun _ st _ _ =>
    PQSkLinAt.bind (PQSkLinAt.guardP _) fun _ _ _ _ =>
    PQSkLinAt.bind (PQSkLinAt.genRand 32) fun _ _ _ _ =>
    PQSkLinAt.bind (PQSkLinAt.genRand coinsLen) fun _ coins _ _ => ?_
  rcases Spqr.spqrSend st.spqr coins with ⟨spqr', key, pqMsg⟩
  dsimp only
  refine PQSkLinAt.bind (PQSkLinAt.sendMessage key) fun _ _ _ _ => ?_
  rcases kdfCk st.cks with ⟨ck', seed⟩
  dsimp only
  exact PQSkLinAt.bind (PQSkLinAt.receiveMessage pqIdx) fun _ _ _ _ =>
    PQSkLinAt.bind (PQSkLinAt.logEvent_nonSkip _ (by intros; rintro ⟨⟩)) fun _ _ _ _ =>
    PQSkLinAt.bind (PQSkLinAt.logMessageKeyAndStore me _ _ _ _ _ _ _ _) fun _ _ _ _ =>
    PQSkLinAt.sendMessage _

theorem PQSkLinAt.exposeKey {tr : ExecTrace} (me : Participant) (stH : Nat) (k : KeyComponent) :
    PQSkLinAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeKey me stH k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine PQSkLinAt.bind (PQSkLinAt.getLocalState me stH) fun _ st _ _ => ?_
  cases k with
  | rk => exact PQSkLinAt.bind (PQSkLinAt.logEvent_nonSkip _ (by intros; rintro ⟨⟩)) fun _ _ _ _ => PQSkLinAt.sendMessage _
  | dhs => exact PQSkLinAt.bind (PQSkLinAt.logEvent_nonSkip _ (by intros; rintro ⟨⟩)) fun _ _ _ _ => PQSkLinAt.sendMessage _
  | cks => exact PQSkLinAt.bind (PQSkLinAt.logEvent_nonSkip _ (by intros; rintro ⟨⟩)) fun _ _ _ _ => PQSkLinAt.sendMessage _
  | ckr pk =>
    dsimp only
    rcases findRecvChain st.recv pk with _ | c
    · exact PQSkLinAt.failure
    · exact PQSkLinAt.bind (PQSkLinAt.logEvent_nonSkip _ (by intros; rintro ⟨⟩)) fun _ _ _ _ => PQSkLinAt.sendMessage _

theorem PQSkLinAt.exposeSpqr {tr : ExecTrace} (me : Participant) (stH : Nat) :
    PQSkLinAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeSpqr me stH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  exact PQSkLinAt.bind (PQSkLinAt.getLocalState me stH) fun _ _ _ _ =>
    PQSkLinAt.bind (PQSkLinAt.logEvent_nonSkip _ (by intros; rintro ⟨⟩)) fun _ _ _ _ =>
    PQSkLinAt.sendMessage _

theorem PQSkLinAt.exposeSkipped {tr : ExecTrace} (evH : Nat) :
    PQSkLinAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeSkipped evH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine PQSkLinAt.bind (PQSkLinAt.getEntryTR evH) fun _ ⟨ev⟩ _ _ => ?_
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    exact PQSkLinAt.bind (PQSkLinAt.guardTrace _) fun _ _ _ _ =>
      PQSkLinAt.bind (PQSkLinAt.logEvent_nonSkip _ (by intros; rintro ⟨⟩)) fun _ _ _ _ =>
      PQSkLinAt.sendMessage _
  | _ => exact PQSkLinAt.failure

theorem PQSkLinAt.messageDecryptSkipped {tr : ExecTrace} (me : Participant)
    (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    PQSkLinAt tr (fun _ _ => True)
      (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine PQSkLinAt.bind (PQSkLinAt.getLocalState me stH) fun _ st _ _ =>
    PQSkLinAt.bind (PQSkLinAt.receiveSignalMsg msgH) fun _ msg _ _ =>
    PQSkLinAt.bind (PQSkLinAt.getEntryTR evH) fun _ ⟨ev⟩ _ _ => ?_
  cases ev with
  | SkippedKeyStored s pk n seed rIdx _src =>
    refine PQSkLinAt.bind (PQSkLinAt.guardP _) fun _ _ _ _ =>
      PQSkLinAt.bind (PQSkLinAt.guardTrace _) fun _ _ _ _ => ?_
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · exact PQSkLinAt.failure
    · exact PQSkLinAt.bind (PQSkLinAt.sendMessage key) fun _ _ _ _ =>
        PQSkLinAt.bind (PQSkLinAt.receiveMessage pqIdx) fun _ pqSalt _ _ =>
        PQSkLinAt.bind (PQSkLinAt.verifyMacAndDecrypt st msg pqSalt seed) fun _ _ _ _ =>
        PQSkLinAt.bind (PQSkLinAt.logEvent_nonSkip _ (by intros; rintro ⟨⟩)) fun _ _ _ _ =>
        PQSkLinAt.bind (PQSkLinAt.logEvent_nonSkip _ (by intros; rintro ⟨⟩)) fun _ _ _ _ =>
        PQSkLinAt.logMessageKeyAndStore me _ _ _ _ _ _ _ _
  | _ => exact PQSkLinAt.failure

theorem PQSkLinAt.messageDecrypt {tr : ExecTrace} (me : Participant)
    (stH msgH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    PQSkLinAt tr (fun _ _ => True)
      (DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine PQSkLinAt.bind (PQSkLinAt.getLocalState me stH) fun tr1 st0 _ ⟨ht1, hget0⟩ => ?_
  subst tr1
  refine PQSkLinAt.bind (PQSkLinAt.receiveSignalMsg msgH) fun tr2 msg _ ht2 => ?_
  subst tr2
  refine PQSkLinAt.bind (PQSkLinAt.ensureReceiverChain st0 msg.ratchetKey)
    fun tr3 ⟨st, c, ratcheted⟩ hle3 ⟨hsinfo, hc_rk, hc_mem, hdisj⟩ => ?_
  dsimp only
  rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · exact PQSkLinAt.failure
  · dsimp only
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · exact PQSkLinAt.failure
    · refine PQSkLinAt.bind (PQSkLinAt.sendMessage key) fun tr4 _ hle4 _ =>
        PQSkLinAt.bind (PQSkLinAt.receiveMessage pqIdx) fun tr5 pqSalt _ ht5 => ?_
      subst tr5
      refine PQSkLinAt.bind (PQSkLinAt.verifyMacAndDecrypt st msg pqSalt seed) fun tr6 m _ ht6 => ?_
      subst tr6
      have hle04 : tr ≤ tr4 := Trace.le_trans _ _ _ hle3 hle4
      have htail : ∀ {tr_t : ExecTrace}, tr4 ≤ tr_t →
          PQSkLinAt tr_t (fun _ _ => True) (do
            DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stH c.chainKey c.index
              (msg.counter.toNat - c.index.toNat)
            ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
            DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st.sessionInfo me) KeyDir.receiver seed pqSalt
              msg.counter c.rIdx stH { st with recv := setRecvChain st.recv c', spqr := spqr' }) := by
        intro tr_t hle_t hInv_t
        have hle0_t : tr ≤ tr_t := Trace.le_trans _ _ _ hle04 hle_t
        have hget0_t :
            ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr_t).1 = some st0 :=
          getLocalState_some_iff_trStateStoredAt.mpr
            (CompTrace.trStateStoredAt_mono hle0_t (getLocalState_some_iff_trStateStoredAt.mp hget0))
        exact ⟨skippedPkLineageInv_decryptTail me st st0 msg.ratchetKey c c' msg.counter seed pqSalt m spqr'
          stH stH hInv_t hc_rk hc_mem hcons (.inl ⟨hget0_t, hsinfo me, hdisj⟩),
          fun _ _ => trivial⟩
      cases ratcheted
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact htail (Trace.le_refl tr4)
      · simp only [↓reduceIte]
        exact PQSkLinAt.bind (PQSkLinAt.logEvent_nonSkip _ (by intros; rintro ⟨⟩)) fun _ _ hle_d1 _ =>
          PQSkLinAt.bind (PQSkLinAt.logEvent_nonSkip _ (by intros; rintro ⟨⟩)) fun _ _ hle_d2 _ =>
            htail (Trace.le_trans _ _ _ hle_d1 hle_d2)

theorem skippedPkLineageInv_preserves_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) {tr : ExecTrace} (hJ : SkippedPkLineageInv tr) :
    SkippedPkLineageInv ((aliceStart a b idStateIdx regIdxB bh).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine CompTrace.bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hJ
    (skippedPkLineageInv_append_non_tr rfl hJ)
    fun ikA ikBPk _ spkPk _ pqPk _ opk _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  have htl : ∀ {α : Type} (f : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= f).run t).2.val = ((f t.length).run t).2.val := by
    intro α f t; unfold DY.Libsignal.TripleRatchet.traceLength
    rw [CompTrace.run_bind_snd, Traceful.run_mk]
  have hstore : ∀ (me : Participant) (st : TRState) (t : ExecTrace),
      ((PersistentLocalState.storeLocalState me st).run t).2.val = t.append (TRStE me st) := by
    intro me st t
    rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  let hs := CompPresPQXDH.aliceOut tr ikA ikBPk spkPk pqPk opk
  let tr1 := tr.append (RndE 32)
  let tr2 := tr1.append (RndE 32)
  let dhsA := CompKeyInversion.rnd tr2.length 32
  let stA : TRState :=
    { peer := b, myIk := DY.Libsignal.PQXDH.serializedIk hs.ikA, peerIk := DY.Libsignal.PQXDH.serializedIk hs.ikB,
      rk := (createChain hs.keys.rk hs.spk dhsA).1, dhs := dhsA, cks := (createChain hs.keys.rk hs.spk dhsA).2,
      ns := 0, pn := 0,
      sid := Concat.concat (DiffieHellman.dhPk dhsA) hs.keys.rk,
      initiator := true, rIdx := 1,
      recv := [{ ratchetKey := hs.spk, chainKey := hs.keys.ck, index := 0, rIdx := 1 }],
      spqr := Spqr.spqrInit hs.keys.pqr spqrA2B }
  let tr3 := tr2.append (RndE 32)
  let tr4 := tr3.append (NetE hs.ek)
  let tr5 := tr4.append (NetE hs.ct)
  let tr6 := tr5.append (EvE (PQXDHEvent.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys))
  let tr7 := tr6.append (TREvE (TREvent.InitSession a b (DiffieHellman.dhPk dhsA) hs.spk))
  let tr8 := tr7.append (CEvE (ComposedEvent.HandshakeSession (stA.sessionInfo a) tr5.length))
  rw [CompTrace.run_genRand_bind_snd]
  dsimp only
  rw [CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd,
    htl, CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
    CompPresTRExp.run_logEvent_bind_snd, hstore]
  change SkippedPkLineageInv (tr8.append (TRStE a stA))
  refine skippedPkLineageInv_append_non_tr rfl ?_
  refine skippedPkLineageInv_append_non_tr rfl ?_
  refine skippedPkLineageInv_append_trEv_nonSkip (by intros; rintro ⟨⟩) ?_
  refine skippedPkLineageInv_append_non_tr rfl ?_
  refine skippedPkLineageInv_append_non_tr rfl ?_
  refine skippedPkLineageInv_append_non_tr rfl ?_
  refine skippedPkLineageInv_append_non_tr rfl ?_
  refine skippedPkLineageInv_append_non_tr rfl ?_
  exact skippedPkLineageInv_append_non_tr rfl hJ

theorem skippedPkLineageInv_bobStart_commit {tr : ExecTrace}
    (hJ : SkippedPkLineageInv tr)
    (b a : Participant) (sB sS sQ : DY.Bytes) (o : Option DY.Bytes) (ikA ek ct : DY.Bytes)
    (keys : HandshakeKeys) (msg : TRSignalMsg) (dhs spqr' seed pqSalt m : DY.Bytes) (c' : RecvChain)
    (hConsume : consumeMessageKey (CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS) msg.counter = some (seed, c')) :
    let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
    let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
    SkippedPkLineageInv (((do
      let doneIdx ← DY.Libsignal.TripleRatchet.traceLength
      ProtocolEvent.logEvent (PQXDHEvent.BobDone b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys)
      if true then
        ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs))
        ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
      ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
      let skipped := msg.counter.toNat - c.index.toNat
      let childIdx := (← DY.Libsignal.TripleRatchet.traceLength) + skipped + 2
      DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
      ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx
        { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr).2.val) := by
  intro st c
  have htl : ∀ {α : Type} (f : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= f).run t).2.val = ((f t.length).run t).2.val := by
    intro α f t; unfold DY.Libsignal.TripleRatchet.traceLength
    rw [CompTrace.run_bind_snd, Traceful.run_mk]
  let doneIdx := tr.length
  let tr₁ := tr.append (EvE (.BobDone b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys))
  let tr₂ := tr₁.append (TREvE (.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs)))
  let tr₃ := tr₂.append (TREvE (.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)))
  let tr₄ := tr₃.append (CEvE (.HandshakeSession (st.sessionInfo b) doneIdx))
  have hJ₄ : SkippedPkLineageInv tr₄ :=
    skippedPkLineageInv_append_non_tr rfl
      (skippedPkLineageInv_append_trEv_nonSkip (by intros; rintro ⟨⟩)
        (skippedPkLineageInv_append_trEv_nonSkip (by intros; rintro ⟨⟩)
          (skippedPkLineageInv_append_non_tr rfl hJ)))
  let skipped := msg.counter.toNat - c.index.toNat
  let childIdx := tr₄.length + skipped + 2
  simp only [↓reduceIte]
  rw [htl, CompPresTRExp.run_logEvent_bind_snd,
    CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
    CompPresTRExp.run_logEvent_bind_snd, htl]
  change SkippedPkLineageInv (((do
    DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
    ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
    DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
      msg.counter c.rIdx childIdx
      { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr₄).2.val)
  exact skippedPkLineageInv_decryptTail b st
    { st with recv := setRecvChain st.recv c', spqr := spqr' }
    msg.ratchetKey c c' msg.counter seed pqSalt m spqr' childIdx childIdx hJ₄
    rfl (List.mem_singleton.mpr rfl) hConsume (.inr ⟨rfl, rfl, rfl, rfl⟩)

theorem skippedPkLineageInv_preserves_bobStart (b a : Participant) (kh : BobKeyHandles)
    (regIdxA : Nat) (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32)
    {tr : ExecTrace} (hJ : SkippedPkLineageInv tr) :
    SkippedPkLineageInv ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hJ
    fun sB sS sQ o ikA _ ek ct _ keys _ _ _ _ _ _ _ _ _ => ?_
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  rw [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_receiveMessage_at mh.msg tr hJ fun raw _ _ => ?_
  rcases parseTrSignalMsg raw with _ | msg
  · dsimp only
    change SkippedPkLineageInv (((failure : Traceful TRSignalMsg) >>= _).run tr).2.val
    rw [CompTrace.run_bind_snd, Traceful.run_failure]
    exact hJ
  · dsimp only
    rw [CompTrace.run_bind_assoc_snd]
    refine CompTrace.bind_guardP_at _ tr hJ fun _ => ?_
    refine CompInv.CompPresBob.bind_ensureReceiverChain_bobInitSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey
      tr hJ fun _ => ?_
    let dhs := CompKeyInversion.rnd tr.length 32
    let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
    let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
    let tr₁ := tr.append (RndE 32)
    have hJ₁ : SkippedPkLineageInv tr₁ := skippedPkLineageInv_append_non_tr rfl hJ
    rcases hConsume : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
    · dsimp only
      change SkippedPkLineageInv ((failure : Traceful Nat).run tr₁).2.val
      rw [Traceful.run_failure]
      exact hJ₁
    · dsimp only
      rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
      · dsimp only
        change SkippedPkLineageInv ((failure : Traceful Nat).run tr₁).2.val
        rw [Traceful.run_failure]
        exact hJ₁
      · dsimp only
        let tr₂ := tr₁.append (NetE key)
        have hJ₂ : SkippedPkLineageInv tr₂ := skippedPkLineageInv_append_non_tr rfl hJ₁
        rw [CompPresTRExp.run_sendMessage_bind_snd]
        refine CompTrace.bind_receiveMessage_at pqIdx tr₂ hJ₂ fun pqSalt _ _ =>
          CompInv.CompPresBob.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr₂ hJ₂ fun m _ => ?_
        cases o with
        | none =>
          dsimp only [Option.map]
          exact skippedPkLineageInv_bobStart_commit hJ₂ b a sB sS sQ none ikA ek ct keys msg dhs spqr' seed pqSalt m c' hConsume
        | some oSk =>
          dsimp only [Option.map]
          rw [CompTrace.run_bind_snd]
          unfold DY.Libsignal.PQXDH.guardTrace
          rw [Traceful.run_mk]
          dsimp only
          by_cases hused : (!opkUsedB tr₂ b (DiffieHellman.dhPk oSk)) = true
          · rw [ite_eq_left_iff.mpr fun h => absurd hused h, CompPresTRExp.run_logEvent_bind_snd]
            exact skippedPkLineageInv_bobStart_commit (skippedPkLineageInv_append_non_tr rfl hJ₂)
              b a sB sS sQ (some oSk) ikA ek ct keys msg dhs spqr' seed pqSalt m c' hConsume
          · rw [ite_eq_right_iff.mpr fun h => absurd h hused]
            exact hJ₂

/-- `SkippedPkLineageInv` holds on every reachable trace `tr`. -/
theorem skippedPkLineageInv_reachable (tr : ExecTrace) (hreach : ReachableTrace tr) :
    SkippedPkLineageInv tr := by
  have hLogEv : ∀ {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
      (ev : Ev) (t : ExecTrace),
      ((ProtocolEvent.logEvent ev).run t).2.val = t.append (⟨ev⟩ : ProtocolEvent.ExecEntryT Ev) := by
    intro Ev _ ev t
    rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      CompTrace.run_bind_snd, Traceful.run_mk]
    dsimp only; rw [Traceful.run_pure]
  have hStorePQ_snd : ∀ (me : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) (t : ExecTrace),
      ((PersistentLocalState.storeLocalState me st).run t).2.val = t.append (PQStE me st) := by
    intro me st t
    rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  have hStorePQ_bind : ∀ {α : Type} (me : Participant) (st : DY.Libsignal.PQXDH.PQXDHState)
      (f : Nat → Traceful α) (t : ExecTrace),
      ((PersistentLocalState.storeLocalState me st >>= f).run t).2.val =
        ((f t.length).run (t.append (PQStE me st))).2.val := by
    intro α me st f t
    rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, CompTrace.run_bind_snd, Traceful.run_mk]
  induction hreach with
  | Base => exact skippedPkLineageInv_nil
  | @Step tr_prev input _ _ ih =>
    rcases input with ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k, _⟩, inp⟩
    · let msg : DY.Bytes := inp
      change SkippedPkLineageInv ((Network.sendMessage msg).run tr_prev).2.val
      rw [CompPresTRExp.run_sendMessage_snd]
      exact skippedPkLineageInv_append_non_tr rfl ih
    · let p : Participant := inp
      change SkippedPkLineageInv ((registerIdentity p).run _).2.val
      unfold registerIdentity
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ ih fun _ => ?_
      rw [CompTrace.run_genRand_bind_snd,
        CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_bind_snd,
        CompPresTRExp.run_sendMessage_bind_snd, hStorePQ_snd]
      exact skippedPkLineageInv_append_non_tr rfl (skippedPkLineageInv_append_non_tr rfl
        (skippedPkLineageInv_append_non_tr rfl (skippedPkLineageInv_append_non_tr rfl
          (skippedPkLineageInv_append_non_tr rfl ih))))
    · rcases inp with ⟨p, skIdx⟩
      change SkippedPkLineageInv ((registerCorruptIdentity p skIdx).run _).2.val
      unfold registerCorruptIdentity
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ ih fun _ =>
        CompTrace.bind_receiveMessage_at skIdx _ ih fun _ _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, hLogEv]
      exact skippedPkLineageInv_append_non_tr rfl (skippedPkLineageInv_append_non_tr rfl ih)
    · rcases inp with ⟨b, idStateIdx⟩
      change SkippedPkLineageInv ((genSignedPrekey b idStateIdx).run _).2.val
      unfold genSignedPrekey
      refine CompPresPQXDH.bind_getKey_at b idStateIdx .identity _ ih fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd,
        CompPresTRExp.run_logEvent_bind_snd, hStorePQ_bind,
        CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd,
        Traceful.run_pure]
      exact skippedPkLineageInv_append_non_tr rfl (skippedPkLineageInv_append_non_tr rfl
        (skippedPkLineageInv_append_non_tr rfl (skippedPkLineageInv_append_non_tr rfl
          (skippedPkLineageInv_append_non_tr rfl (skippedPkLineageInv_append_non_tr rfl ih)))))
    · rcases inp with ⟨b, idStateIdx⟩
      change SkippedPkLineageInv ((genPQPrekey b idStateIdx).run _).2.val
      unfold genPQPrekey
      refine CompPresPQXDH.bind_getKey_at b idStateIdx .identity _ ih fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd,
        CompPresTRExp.run_logEvent_bind_snd, hStorePQ_bind,
        CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd,
        Traceful.run_pure]
      exact skippedPkLineageInv_append_non_tr rfl (skippedPkLineageInv_append_non_tr rfl
        (skippedPkLineageInv_append_non_tr rfl (skippedPkLineageInv_append_non_tr rfl
          (skippedPkLineageInv_append_non_tr rfl (skippedPkLineageInv_append_non_tr rfl ih)))))
    · let b : Participant := inp
      change SkippedPkLineageInv ((genOneTimePrekey b).run _).2.val
      unfold genOneTimePrekey
      rw [CompTrace.run_genRand_bind_snd,
        CompPresTRExp.run_logEvent_bind_snd, hStorePQ_bind,
        CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact skippedPkLineageInv_append_non_tr rfl (skippedPkLineageInv_append_non_tr rfl
        (skippedPkLineageInv_append_non_tr rfl (skippedPkLineageInv_append_non_tr rfl ih)))
    · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩
      exact skippedPkLineageInv_preserves_aliceStart a b idStateIdx regIdxB bh ih
    · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩
      exact skippedPkLineageInv_preserves_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx ih
    · rcases inp with ⟨me, stateIdx, coinsLen, pqIdx⟩
      exact (PQSkLinAt.messageEncrypt me stateIdx coinsLen pqIdx ih).1
    · rcases inp with ⟨me, stateIdx⟩
      exact (PQSkLinAt.messageEncryptAbort me stateIdx ih).1
    · rcases inp with ⟨me, stateIdx, msgIdx, pqIdx, spqrMsgIdx⟩
      exact (PQSkLinAt.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx ih).1
    · rcases inp with ⟨me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx⟩
      exact (PQSkLinAt.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx ih).1
    · rcases inp with ⟨me, stateIdx, k⟩
      exact (PQSkLinAt.exposeKey me stateIdx k ih).1
    · rcases inp with ⟨me, stateIdx⟩
      exact (PQSkLinAt.exposeSpqr me stateIdx ih).1
    · exact (PQSkLinAt.exposeSkipped inp ih).1
    · rcases inp with ⟨p, stateIdx⟩
      change SkippedPkLineageInv ((compromiseIK p stateIdx).run _).2.val
      unfold compromiseIK
      refine CompPresPQXDH.bind_getKey_at p stateIdx .identity _ ih fun _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact skippedPkLineageInv_append_non_tr rfl (skippedPkLineageInv_append_non_tr rfl ih)
    · rcases inp with ⟨b, stateIdx⟩
      change SkippedPkLineageInv ((compromiseSPK b stateIdx).run _).2.val
      unfold compromiseSPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .signedPrekey _ ih fun _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact skippedPkLineageInv_append_non_tr rfl (skippedPkLineageInv_append_non_tr rfl ih)
    · rcases inp with ⟨b, stateIdx⟩
      change SkippedPkLineageInv ((compromisePQSPK b stateIdx).run _).2.val
      unfold compromisePQSPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .pqPrekey _ ih fun _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact skippedPkLineageInv_append_non_tr rfl (skippedPkLineageInv_append_non_tr rfl ih)
    · rcases inp with ⟨b, stateIdx⟩
      change SkippedPkLineageInv ((compromiseOPK b stateIdx).run _).2.val
      unfold compromiseOPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .oneTimePrekey _ ih fun _ _ => ?_
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ ih fun _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact skippedPkLineageInv_append_non_tr rfl (skippedPkLineageInv_append_non_tr rfl ih)
    · change SkippedPkLineageInv ((ProtocolEvent.logEvent PQXDHEvent.BrokenDH).run tr_prev).2.val
      rw [hLogEv]
      exact skippedPkLineageInv_append_non_tr rfl ih
    · change SkippedPkLineageInv ((ProtocolEvent.logEvent PQXDHEvent.BrokenKEM).run tr_prev).2.val
      rw [hLogEv]
      exact skippedPkLineageInv_append_non_tr rfl ih
    · let pkIdx : Nat := inp
      change SkippedPkLineageInv ((invertDH pkIdx).run _).2.val
      unfold invertDH
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ ih fun _ =>
        CompTrace.bind_receiveMessage_at pkIdx tr_prev ih fun pk _ _ => ?_
      rcases DY.Libsignal.PQXDH.extractDhSecretKey (X25519.normalizeX25519Key pk) with _ | sk
      · dsimp only
        change SkippedPkLineageInv ((failure : Traceful Nat).run tr_prev).2.val
        rw [Traceful.run_failure]
        exact ih
      · dsimp only
        rw [CompPresTRExp.run_sendMessage_snd]
        exact skippedPkLineageInv_append_non_tr rfl ih
    · let pkIdx : Nat := inp
      change SkippedPkLineageInv ((invertKEM pkIdx).run _).2.val
      unfold invertKEM
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ ih fun _ =>
        CompTrace.bind_receiveMessage_at pkIdx tr_prev ih fun pk _ _ => ?_
      rcases PQKem.invertKemPublicKey pk with _ | sk
      · dsimp [liftM, monadLift, MonadLift.monadLift]
        rw [CompTrace.run_bind_snd, Traceful.run_mk]
        exact ih
      · dsimp [liftM, monadLift, MonadLift.monadLift]
        rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only
        rw [CompPresTRExp.run_sendMessage_snd]
        exact skippedPkLineageInv_append_non_tr rfl ih
    · omega

end Symbolic.Swarm.CREF.TR.G1

namespace Symbolic.Swarm.CREF.TR.RecvDecStep

cref_open
open DY DY.Libsignal.TripleRatchet DY.Libsignal.TripleRatchet
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.CREF.TR.G1
open Symbolic.Swarm.COMPOSED

export Symbolic.Swarm.CREF.TR.G1 (
  ReachableTrace
  freshRecvChain
  SkippedPkLineageAt
  SkippedPkLineageInv
  skippedPkLineageInv_reachable
)

/-- Every `SkippedKeyStored` entry on `runTraceMoves r₀ ms` satisfies `SkippedPkLineageAt`. -/
def SkippedPkLineage (r₀ : ProtocolSetup) (ms : List Move) : Prop :=
  SkippedPkLineageInv (runTraceMoves r₀ ms)

theorem skippedPkLineage_of_reachable {r₀ : ProtocolSetup} {ms : List Move}
    (hreach : ReachableTrace (runTraceMoves r₀ ms)) : SkippedPkLineage r₀ ms :=
  skippedPkLineageInv_reachable (runTraceMoves r₀ ms) hreach

end Symbolic.Swarm.CREF.TR.RecvDecStep
