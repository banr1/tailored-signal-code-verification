/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkSeedSepDefs
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import ProofLib.Lemmas
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil

/-!
# Receiving-Chain and Skipped-Seed Root Linkage

Proves `recvLinkStored_of_reachable` and `recvLinkSkipped_of_reachable`: on any reachable trace
`T`, every receive chain `c ∈ st.recv` of a stored `TRState` and every logged `SkippedKeyStored`
seed derives via `chainKeyAt` from a `RecvRoot T pk R` witness (either a stored state's
`createChain` output, Bob's initial `createChain` output from `BobDoneKeys`, or Alice's initial
chain key from `AliceDoneKeys`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY DY.Comparse DY.DiffieHellman DY.Libsignal.TripleRatchet Symbolic.Swarm.CREF.TR
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir KeyComponent RecvChain findRecvChain
  setRecvChain recvChainFor consumeMessageKey chainKeyAt kdfCk createChain)
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys BundleHandles BobKeyHandles PreKeyMsgHandles
  opkUsedB registerIdentity registerCorruptIdentity genSignedPrekey genPQPrekey genOneTimePrekey
  compromiseIK compromiseSPK compromisePQSPK compromiseOPK invertDH invertKEM)
open DY.Libsignal.Composed (ComposedEvent aliceStart bobStart)
open Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompPresPQXDH Symbolic.Swarm.COMPOSED.CompPresTRExp
open Symbolic.Swarm.COMPOSED.CompInv (SpqrInv spqrInv_of_reachable EvE)
open Symbolic.Swarm.CREF.TR.G1 (chainKeyAt_add consumeMessageKey_eq_spine)

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

/-! ## Monotonicity of `AliceDoneKeys`, `BobDoneKeys`, `RecvRoot`, and `SpineLinkInv` -/

theorem AliceDoneKeys.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {keys : HandshakeKeys}
    (h : AliceDoneKeys tr keys) : AliceDoneKeys tr' keys := by
  obtain ⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, j, hev⟩ := h
  exact ⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, j, CompTrace.eventLoggedAt_mono hle hev⟩

theorem BobDoneKeys.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {keys : HandshakeKeys}
    (h : BobDoneKeys tr keys) : BobDoneKeys tr' keys := by
  obtain ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, j, hev⟩ := h
  exact ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, j, CompTrace.eventLoggedAt_mono hle hev⟩

theorem RecvRoot.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {pk R : DY.Bytes}
    (h : RecvRoot tr pk R) : RecvRoot tr' pk R := by
  rcases h with ⟨p, st₀, i₀, hst, hR⟩ | ⟨keys, t, b, idx, hbob, hspk, hR⟩ | ⟨keys, halice, hR⟩
  · exact .inl ⟨p, st₀, i₀, CompTrace.trStateStoredAt_mono hle hst, hR⟩
  · exact .inr (.inl ⟨keys, t, b, idx, hbob.mono hle, CompTrace.pqxdhStoredAt_mono hle hspk, hR⟩)
  · exact .inr (.inr ⟨keys, halice.mono hle, hR⟩)

def ChainLink (tr : ExecTrace) (c : RecvChain) : Prop :=
  ∃ (R : DY.Bytes) (j : Nat), c.chainKey = chainKeyAt R j ∧ RecvRoot tr c.ratchetKey R

theorem ChainLink.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {c : RecvChain}
    (hc : ChainLink tr c) : ChainLink tr' c := by
  obtain ⟨R, j, hck, hroot⟩ := hc
  exact ⟨R, j, hck, hroot.mono hle⟩

theorem ChainLink.advance {tr : ExecTrace} {c : RecvChain}
    (hc : ChainLink tr c) (d : Nat) (idx' : UInt32) :
    ChainLink tr { c with chainKey := chainKeyAt c.chainKey d, index := idx' } := by
  obtain ⟨R, j, hck, hroot⟩ := hc
  refine ⟨R, j + d, ?_, hroot⟩
  dsimp only
  rw [hck, chainKeyAt_add]

theorem ChainLink.kdfCk_fst {tr : ExecTrace} {c : RecvChain}
    (hc : ChainLink tr c) (idx' : UInt32) :
    ChainLink tr { c with chainKey := (kdfCk c.chainKey).1, index := idx' } :=
  hc.advance 1 idx'

def StLink (tr : ExecTrace) (st : TRState) : Prop :=
  ∀ c ∈ st.recv, ChainLink tr c

theorem StLink.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {st : TRState}
    (hst : StLink tr st) : StLink tr' st :=
  fun c hc => (hst c hc).mono hle

theorem stLink_setRecvChain {tr : ExecTrace} {st : TRState} {c : RecvChain} {spqr' : DY.Bytes}
    (hst : StLink tr st) (hc : ChainLink tr c) :
    StLink tr { st with recv := setRecvChain st.recv c, spqr := spqr' } := by
  intro c0 hc0
  unfold setRecvChain at hc0
  rw [List.mem_map] at hc0
  obtain ⟨c1, hc1, rfl⟩ := hc0
  by_cases hk : (c1.ratchetKey == c.ratchetKey) = true
  · simp only [hk, ↓reduceIte]; exact hc
  · simp only [hk, Bool.false_eq_true, ↓reduceIte]; exact hst c1 hc1

def SeedLink (tr : ExecTrace) (seed : DY.Bytes) : Prop :=
  ∃ (pk' R : DY.Bytes) (j : Nat), seed = (kdfCk (chainKeyAt R j)).2 ∧ RecvRoot tr pk' R

theorem SeedLink.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {seed : DY.Bytes}
    (hs : SeedLink tr seed) : SeedLink tr' seed := by
  obtain ⟨pk', R, j, hseed, hroot⟩ := hs
  exact ⟨pk', R, j, hseed, hroot.mono hle⟩

theorem SeedLink.of_chainLink {tr : ExecTrace} {c : RecvChain} (hc : ChainLink tr c) :
    SeedLink tr (kdfCk c.chainKey).2 := by
  obtain ⟨R, j, hck, hroot⟩ := hc
  exact ⟨c.ratchetKey, R, j, by rw [hck], hroot⟩

def SpineLinkInv (tr : ExecTrace) : Prop :=
  RecvLinkStored tr ∧ RecvLinkSkipped tr

theorem spineLinkInv_nil : SpineLinkInv Trace.nil :=
  ⟨fun h => by simp [TRStateStoredAt, Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1] at h,
   fun h => by simp [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1] at h⟩

theorem spineLinkInv_append_other {tr : ExecTrace} {E : Type} [ExecTraceTypes.Has E] {e : E}
    (h : SpineLinkInv tr)
    (hdr : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option CompTrace.TREntry) = none := by rfl)
    (hst : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option CompTrace.TRStEntry) = none := by rfl) :
    SpineLinkInv (tr.append e) := by
  have hle : tr ≤ tr.append e := Trace.append_le tr e
  refine ⟨fun hs c hc => ?_, fun hev => ?_⟩
  · exact ChainLink.mono hle (h.1 (CompTrace.trStateStoredAt_append_other hst hs) c hc)
  · exact SeedLink.mono hle (h.2 (CompTrace.eventLoggedAt_append_other hdr hev))

theorem spineLinkInv_append_ev {tr : ExecTrace} (ev : TREvent)
    (hev : ∀ s pk n seed rIdx src, ev = .SkippedKeyStored s pk n seed rIdx src → SeedLink tr seed)
    (h : SpineLinkInv tr) : SpineLinkInv (tr.append (TREvE ev)) := by
  have hle : tr ≤ tr.append (TREvE ev) := Trace.append_le tr (TREvE ev)
  refine ⟨fun hs c hc => ChainLink.mono hle (h.1 (CompTrace.trStateStoredAt_append_other rfl hs) c hc),
    fun hevl => ?_⟩
  rcases CompTrace.eventLoggedAt_append_same hevl with ⟨_, hevl⟩ | ⟨_, hp⟩
  · exact SeedLink.mono hle (h.2 hevl)
  · exact SeedLink.mono hle (hev _ _ _ _ _ _ hp)

theorem spineLinkInv_append_st {tr : ExecTrace} (p : Participant) {st : TRState}
    (hst : StLink tr st) (h : SpineLinkInv tr) : SpineLinkInv (tr.append (TRStE p st)) := by
  have hle : tr ≤ tr.append (TRStE p st) := Trace.append_le tr (TRStE p st)
  refine ⟨fun hs c hc => ?_,
    fun hevl => SeedLink.mono hle (h.2 (CompTrace.eventLoggedAt_append_other rfl hevl))⟩
  rcases CompTrace.trStateStoredAt_append_same hs with ⟨_, hs⟩ | ⟨_, rfl, rfl⟩
  · exact ChainLink.mono hle (h.1 hs c hc)
  · exact ChainLink.mono hle (hst c hc)

/-! ## `PQSpineLinkAt` Combinators and Transition Preservation -/

def PQSpineLinkAt (tr : ExecTrace) {α : Type} (Q : ExecTrace → α → Prop) (x : Traceful α) : Prop :=
  SpineLinkInv tr →
    SpineLinkInv (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q (x.run tr).2.val a

theorem PQSpineLinkAt.bind {tr : ExecTrace} {α β : Type} {Q : ExecTrace → α → Prop} {R : ExecTrace → β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : PQSpineLinkAt tr Q x) (hf : ∀ tr1 a, tr ≤ tr1 → Q tr1 a → PQSpineLinkAt tr1 R (f a)) :
    PQSpineLinkAt tr R (x >>= f) := by
  intro hJ
  rw [Traceful.run_bind]
  have hx0 := hx hJ
  rcases h : x.run tr with ⟨_ | a, trMid, hmid⟩ <;> rw [h] at hx0
  · exact ⟨hx0.1, fun _ hb => by cases hb⟩
  · exact hf trMid a hmid (hx0.2 a rfl) hx0.1

theorem PQSpineLinkAt.of_id {tr : ExecTrace} {α : Type} {x : Traceful α} (hx : (x.run tr).2.val = tr) :
    PQSpineLinkAt tr (fun _ _ => True) x := by
  intro hJ; rw [hx]; exact ⟨hJ, fun _ _ => trivial⟩

theorem PQSpineLinkAt.pure {tr : ExecTrace} {α : Type} {Q : ExecTrace → α → Prop} (a : α) (ha : Q tr a) :
    PQSpineLinkAt tr Q (Pure.pure a : Traceful α) := by
  intro hJ; rw [Traceful.run_pure]; refine ⟨hJ, fun b hb => ?_⟩; cases hb; exact ha

theorem PQSpineLinkAt.failure {tr : ExecTrace} {α : Type} {Q : ExecTrace → α → Prop} :
    PQSpineLinkAt tr Q (Alternative.failure : Traceful α) := by
  intro hJ; rw [Traceful.run_failure]; exact ⟨hJ, fun _ hb => by cases hb⟩

theorem PQSpineLinkAt.guardP {tr : ExecTrace} (p : Prop) [Decidable p] :
    PQSpineLinkAt tr (fun _ _ => p) (_root_.guard p : Traceful Unit) := by
  unfold _root_.guard; split <;> [(rename_i hp; exact PQSpineLinkAt.pure () hp); exact PQSpineLinkAt.failure]

theorem PQSpineLinkAt.guardTrace {tr : ExecTrace} (p : ExecTrace → Bool) :
    PQSpineLinkAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.guardTrace p) :=
  PQSpineLinkAt.of_id (by unfold DY.Libsignal.TripleRatchet.guardTrace; rw [Traceful.run_mk])

theorem PQSpineLinkAt.traceLength {tr : ExecTrace} :
    PQSpineLinkAt tr (fun _ _ => True) DY.Libsignal.TripleRatchet.traceLength :=
  PQSpineLinkAt.of_id (by unfold DY.Libsignal.TripleRatchet.traceLength; rw [Traceful.run_mk])

theorem PQSpineLinkAt.genRand {tr : ExecTrace} (n : Nat) :
    PQSpineLinkAt tr (fun _ _ => True) (Random.genRand n) := by
  intro hJ; simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Traceful.run_bind, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]
  exact ⟨spineLinkInv_append_other hJ, fun _ _ => trivial⟩

theorem PQSpineLinkAt.sendMessage {tr : ExecTrace} (m : DY.Bytes) :
    PQSpineLinkAt tr (fun _ _ => True) (Network.sendMessage m) := by
  intro hJ; rw [CompPresTRExp.run_sendMessage_snd]
  exact ⟨spineLinkInv_append_other hJ, fun _ _ => trivial⟩

theorem PQSpineLinkAt.logEvent {tr : ExecTrace} (ev : TREvent)
    (hev : ∀ s pk n seed rIdx src, ev = .SkippedKeyStored s pk n seed rIdx src → SeedLink tr seed) :
    PQSpineLinkAt tr (fun _ _ => True) (ProtocolEvent.logEvent ev) := by
  intro hJ; simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Traceful.run_bind, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]
  exact ⟨spineLinkInv_append_ev ev hev hJ, fun _ _ => trivial⟩

theorem PQSpineLinkAt.storeLocalState {tr : ExecTrace} (p : Participant) {st : TRState} (hst : StLink tr st) :
    PQSpineLinkAt tr (fun _ _ => True) (PersistentLocalState.storeLocalState p st) := by
  intro hJ; simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Traceful.run_mk]
  exact ⟨spineLinkInv_append_st p hst hJ, fun _ _ => trivial⟩

theorem PQSpineLinkAt.getLocalState {tr : ExecTrace} (me : Participant) (stH : Nat) :
    PQSpineLinkAt tr (fun tr1 st => tr1 = tr ∧ StLink tr st ∧ TRStateStoredAt me st stH tr)
      (PersistentLocalState.getLocalState me stH) := by
  intro hJ; rw [CompTrace.getLocalState_tr_snd]; refine ⟨hJ, fun st hst => ?_⟩
  rw [CompTrace.getLocalState_tr_fst] at hst
  rcases he : (tr.at? stH : Option CompTrace.TRStEntry) with _ | ⟨⟨p, st'⟩⟩
  · rw [he] at hst; cases hst
  · rw [he] at hst; dsimp only at hst
    by_cases hp : p = me
    · subst hp; simp only [↓reduceIte] at hst; cases hst
      exact ⟨rfl, hJ.1 he, he⟩
    · simp only [hp, ↓reduceIte] at hst; cases hst

theorem PQSpineLinkAt.getEntryTR {tr : ExecTrace} (evH : Nat) :
    PQSpineLinkAt tr (fun _ _ => True) (DY.getEntry evH : Traceful CompTrace.TREntry) :=
  PQSpineLinkAt.of_id (by simp only [Symbolic.DYBridge.DY.getEntry_eq_1]; rw [Traceful.run_mk])

theorem PQSpineLinkAt.receiveMessage {tr : ExecTrace} (msgH : Nat) :
    PQSpineLinkAt tr (fun _ _ => True) (Network.receiveMessage msgH) := by
  intro hJ; rw [CompTrace.receiveMessage_snd]; exact ⟨hJ, fun _ _ => trivial⟩

theorem PQSpineLinkAt.receiveSignalMsg {tr : ExecTrace} (msgH : Nat) :
    PQSpineLinkAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.receiveSignalMsg msgH) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine PQSpineLinkAt.bind (PQSpineLinkAt.receiveMessage msgH) fun _ t _ _ => ?_
  rcases parseTrSignalMsg t with _ | msg
  · exact PQSpineLinkAt.failure
  · exact PQSpineLinkAt.bind (PQSpineLinkAt.guardP _) fun _ _ _ _ => PQSpineLinkAt.pure msg trivial

theorem PQSpineLinkAt.verifyMacAndDecrypt {tr : ExecTrace} (st : TRState) (msg : TRSignalMsg) (pqSalt seed : DY.Bytes) :
    PQSpineLinkAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  exact PQSpineLinkAt.bind (PQSpineLinkAt.guardP _) fun _ _ _ _ => PQSpineLinkAt.of_id (by erw [Traceful.run_mk])

theorem PQSpineLinkAt.logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (c : RecvChain) (n : UInt32) {tr : ExecTrace},
      ChainLink tr c →
      PQSpineLinkAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src c.chainKey n k)
  | 0, _, _, _, _ => by
    simp only [DY.Libsignal.TripleRatchet.logSkippedKeys]
    exact PQSpineLinkAt.pure () trivial
  | k + 1, c, n, _, hc => by
    simp only [DY.Libsignal.TripleRatchet.logSkippedKeys]
    refine PQSpineLinkAt.bind (PQSpineLinkAt.logEvent _ ?_) fun _ _ hle _ =>
      PQSpineLinkAt.logSkippedKeys s pk rIdx src k
        { c with chainKey := (kdfCk c.chainKey).1, index := n } (n + 1)
        ((hc.mono hle).kdfCk_fst n)
    intro _ _ _ _ _ _ h; cases h; exact SeedLink.of_chainLink hc

theorem PQSpineLinkAt.logMessageKeyAndStore {tr : ExecTrace} (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx p : Nat) {st : TRState} (hst : StLink tr st) :
    PQSpineLinkAt tr (fun _ _ => True)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx p st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact PQSpineLinkAt.bind (PQSpineLinkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ hle2 _ =>
    PQSpineLinkAt.storeLocalState me (hst.mono hle2)

theorem PQSpineLinkAt.dhRatchetStep {tr : ExecTrace} {me : Participant} {st0 : TRState} {stH : Nat}
    {pk : DY.Bytes} (hst0 : StLink tr st0) (hstored0 : TRStateStoredAt me st0 stH tr) :
    PQSpineLinkAt tr (fun tr1 (r : TRState × RecvChain) => StLink tr1 r.1 ∧ ChainLink tr1 r.2)
      (DY.Libsignal.TripleRatchet.dhRatchetStep st0 pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine PQSpineLinkAt.bind (PQSpineLinkAt.guardP _) fun tr1 _ hle1 _ => ?_
  rcases hc1 : createChain st0.rk pk st0.dhs with ⟨rk1, ckr⟩; dsimp only
  have hckr_eq : ckr = (createChain st0.rk pk st0.dhs).2 := by rw [hc1]
  refine PQSpineLinkAt.bind (PQSpineLinkAt.genRand 32) fun tr2 dhs hle2 _ => ?_
  rcases hc2 : createChain rk1 pk dhs with ⟨rk2, cks⟩; dsimp only
  have hle02 : tr ≤ tr2 := Trace.le_trans _ _ _ hle1 hle2
  have hc_link : ChainLink tr2 { ratchetKey := pk, chainKey := ckr, index := 0, rIdx := st0.rIdx + 2 } :=
    ⟨(createChain st0.rk pk st0.dhs).2, 0, hckr_eq,
     .inl ⟨me, st0, stH, CompTrace.trStateStoredAt_mono hle02 hstored0, rfl⟩⟩
  refine PQSpineLinkAt.pure _ ⟨fun c0 hc0 => ?_, hc_link⟩
  have hmem := List.mem_of_mem_drop hc0
  rw [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | rfl
  · exact (hst0 c0 hmem).mono hle02
  · exact hc_link

theorem PQSpineLinkAt.ensureReceiverChain {tr : ExecTrace} {me : Participant} {st0 : TRState} {stH : Nat}
    {pk : DY.Bytes} (hst0 : StLink tr st0) (hstored0 : TRStateStoredAt me st0 stH tr) :
    PQSpineLinkAt tr (fun tr1 (r : TRState × RecvChain × Bool) => StLink tr1 r.1 ∧ ChainLink tr1 r.2.1)
      (DY.Libsignal.TripleRatchet.ensureReceiverChain st0 pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split
  · rename_i c hrc
    refine PQSpineLinkAt.pure _ ⟨hst0, ?_⟩
    unfold recvChainFor at hrc; split at hrc
    · rename_i c0 hfind; injection hrc with hrc; injection hrc with hrc _; subst hrc
      exact hst0 c0 (List.mem_of_find?_eq_some hfind)
    · split at hrc <;> [cases hrc; (injection hrc with hrc; injection hrc with _ hb; cases hb)]
  · refine PQSpineLinkAt.bind (PQSpineLinkAt.dhRatchetStep hst0 hstored0) fun _ ⟨st', c⟩ _ hr =>
      PQSpineLinkAt.pure _ hr
  · exact PQSpineLinkAt.failure

theorem PQSpineLinkAt.messageEncryptAbort {tr : ExecTrace} (me : Participant) (stH : Nat) :
    PQSpineLinkAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  exact PQSpineLinkAt.bind (PQSpineLinkAt.getLocalState me stH) fun _ _ _ _ =>
    PQSpineLinkAt.bind (PQSpineLinkAt.genRand 32) fun _ _ _ _ => PQSpineLinkAt.failure

theorem PQSpineLinkAt.messageEncrypt {tr : ExecTrace} (me : Participant) (stH coinsLen pqIdx : Nat) :
    PQSpineLinkAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine PQSpineLinkAt.bind (PQSpineLinkAt.getLocalState me stH) fun _ st hle0 ⟨_, hst, _⟩ =>
    PQSpineLinkAt.bind (PQSpineLinkAt.guardP _) fun _ _ hle1 _ =>
    PQSpineLinkAt.bind (PQSpineLinkAt.genRand 32) fun _ _ hle2 _ =>
    PQSpineLinkAt.bind (PQSpineLinkAt.genRand coinsLen) fun _ coins hle3 _ => ?_
  rcases Spqr.spqrSend st.spqr coins with ⟨spqr', key, pqMsg⟩; dsimp only
  refine PQSpineLinkAt.bind (PQSpineLinkAt.sendMessage key) fun _ _ hle4 _ => ?_
  rcases kdfCk st.cks with ⟨ck', seed⟩; dsimp only
  refine PQSpineLinkAt.bind (PQSpineLinkAt.receiveMessage pqIdx) fun _ _ hle5 _ =>
    PQSpineLinkAt.bind (PQSpineLinkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun tr6 _ hle6 _ => ?_
  have hle06 : tr ≤ tr6 :=
    Trace.le_trans _ _ _ hle0 (Trace.le_trans _ _ _ hle1 (Trace.le_trans _ _ _ hle2
      (Trace.le_trans _ _ _ hle3 (Trace.le_trans _ _ _ hle4 (Trace.le_trans _ _ _ hle5 hle6)))))
  have hst' : StLink tr6 { st with cks := ck', ns := st.ns + 1, spqr := spqr' } := hst.mono hle06
  exact PQSpineLinkAt.bind (PQSpineLinkAt.logMessageKeyAndStore me _ _ _ _ _ _ _ hst') fun _ _ _ _ =>
    PQSpineLinkAt.sendMessage _

theorem PQSpineLinkAt.exposeKey {tr : ExecTrace} (me : Participant) (stH : Nat) (k : KeyComponent) :
    PQSpineLinkAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeKey me stH k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine PQSpineLinkAt.bind (PQSpineLinkAt.getLocalState me stH) fun _ st _ _ => ?_
  cases k with
  | rk => exact PQSpineLinkAt.bind (PQSpineLinkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ => PQSpineLinkAt.sendMessage _
  | dhs => exact PQSpineLinkAt.bind (PQSpineLinkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ => PQSpineLinkAt.sendMessage _
  | cks => exact PQSpineLinkAt.bind (PQSpineLinkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ => PQSpineLinkAt.sendMessage _
  | ckr pk =>
    dsimp only
    rcases findRecvChain st.recv pk with _ | c <;>
      [exact PQSpineLinkAt.failure;
       exact PQSpineLinkAt.bind (PQSpineLinkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ => PQSpineLinkAt.sendMessage _]

theorem PQSpineLinkAt.exposeSpqr {tr : ExecTrace} (me : Participant) (stH : Nat) :
    PQSpineLinkAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeSpqr me stH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  exact PQSpineLinkAt.bind (PQSpineLinkAt.getLocalState me stH) fun _ _ _ _ =>
    PQSpineLinkAt.bind (PQSpineLinkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ =>
      PQSpineLinkAt.sendMessage _

theorem PQSpineLinkAt.exposeSkipped {tr : ExecTrace} (evH : Nat) :
    PQSpineLinkAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeSkipped evH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine PQSpineLinkAt.bind (PQSpineLinkAt.getEntryTR evH) fun _ ⟨ev⟩ _ _ => ?_
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    exact PQSpineLinkAt.bind (PQSpineLinkAt.guardTrace _) fun _ _ _ _ =>
      PQSpineLinkAt.bind (PQSpineLinkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ =>
        PQSpineLinkAt.sendMessage _
  | _ => exact PQSpineLinkAt.failure

theorem PQSpineLinkAt.messageDecryptSkipped {tr : ExecTrace} (me : Participant)
    (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    PQSpineLinkAt tr (fun _ _ => True)
      (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine PQSpineLinkAt.bind (PQSpineLinkAt.getLocalState me stH) fun _ st hle0 ⟨_, hst, _⟩ =>
    PQSpineLinkAt.bind (PQSpineLinkAt.receiveSignalMsg msgH) fun _ msg hle1 _ =>
    PQSpineLinkAt.bind (PQSpineLinkAt.getEntryTR evH) fun _ ⟨ev⟩ hle2 _ => ?_
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    refine PQSpineLinkAt.bind (PQSpineLinkAt.guardP _) fun _ _ hle3 _ =>
      PQSpineLinkAt.bind (PQSpineLinkAt.guardTrace _) fun _ _ hle4 _ => ?_
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · exact PQSpineLinkAt.failure
    · refine PQSpineLinkAt.bind (PQSpineLinkAt.sendMessage key) fun _ _ hle5 _ =>
        PQSpineLinkAt.bind (PQSpineLinkAt.receiveMessage pqIdx) fun _ pqSalt hle6 _ =>
        PQSpineLinkAt.bind (PQSpineLinkAt.verifyMacAndDecrypt st msg pqSalt seed) fun _ _ hle7 _ =>
        PQSpineLinkAt.bind (PQSpineLinkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ hle8 _ =>
        PQSpineLinkAt.bind (PQSpineLinkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun tr9 _ hle9 _ => ?_
      have hle09 : tr ≤ tr9 :=
        Trace.le_trans _ _ _ hle0 (Trace.le_trans _ _ _ hle1 (Trace.le_trans _ _ _ hle2
          (Trace.le_trans _ _ _ hle3 (Trace.le_trans _ _ _ hle4 (Trace.le_trans _ _ _ hle5
            (Trace.le_trans _ _ _ hle6 (Trace.le_trans _ _ _ hle7 (Trace.le_trans _ _ _ hle8 hle9))))))))
      exact PQSpineLinkAt.logMessageKeyAndStore me _ _ _ _ _ _ _ (hst.mono hle09)
  | _ => exact PQSpineLinkAt.failure

theorem PQSpineLinkAt.messageDecrypt {tr : ExecTrace} (me : Participant)
    (stH msgH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    PQSpineLinkAt tr (fun _ _ => True)
      (DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine PQSpineLinkAt.bind (PQSpineLinkAt.getLocalState me stH) fun _ st0 hle0 ⟨_, hst0, hstored0⟩ =>
    PQSpineLinkAt.bind (PQSpineLinkAt.receiveSignalMsg msgH) fun tr1 msg hle1 _ => ?_
  have hle01 : tr ≤ tr1 := Trace.le_trans _ _ _ hle0 hle1
  refine PQSpineLinkAt.bind
    (PQSpineLinkAt.ensureReceiverChain (hst0.mono hle01) (CompTrace.trStateStoredAt_mono hle01 hstored0))
    fun tr2 ⟨st, c, ratcheted⟩ _ ⟨hst2, hc2⟩ => ?_
  dsimp only
  rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · exact PQSpineLinkAt.failure
  · dsimp only
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · exact PQSpineLinkAt.failure
    · refine PQSpineLinkAt.bind (PQSpineLinkAt.sendMessage key) fun tr3 _ hle3 _ =>
        PQSpineLinkAt.bind (PQSpineLinkAt.receiveMessage pqIdx) fun tr4 pqSalt hle4 _ =>
        PQSpineLinkAt.bind (PQSpineLinkAt.verifyMacAndDecrypt st msg pqSalt seed) fun tr5 m hle5 _ => ?_
      have hle25 : tr2 ≤ tr5 := Trace.le_trans _ _ _ hle3 (Trace.le_trans _ _ _ hle4 hle5)
      obtain ⟨_, hc'_eq⟩ := consumeMessageKey_eq_spine hcons
      let d := msg.counter.toNat - c.index.toNat
      have htail : ∀ {tr_t : ExecTrace}, tr5 ≤ tr_t →
          PQSpineLinkAt tr_t (fun _ _ => True) (do
            DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stH c.chainKey c.index d
            ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
            DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st.sessionInfo me) KeyDir.receiver seed pqSalt
              msg.counter c.rIdx stH { st with recv := setRecvChain st.recv c', spqr := spqr' }) := by
        intro tr_t hle_t
        have hle2_t : tr2 ≤ tr_t := Trace.le_trans _ _ _ hle25 hle_t
        have hc_t : ChainLink tr_t c := hc2.mono hle2_t
        refine PQSpineLinkAt.bind (PQSpineLinkAt.logSkippedKeys _ _ _ _ d c c.index hc_t) fun tr_s _ hle_s _ =>
          PQSpineLinkAt.bind (PQSpineLinkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun tr_r _ hle_r _ => ?_
        have hle_tsr : tr_t ≤ tr_r := Trace.le_trans _ _ _ hle_s hle_r
        have hst_r : StLink tr_r st := (hst2.mono hle2_t).mono hle_tsr
        have hc'_r : ChainLink tr_r c' := by
          rw [hc'_eq]
          exact (hc_t.mono hle_tsr).advance (d + 1) (msg.counter + 1)
        exact PQSpineLinkAt.logMessageKeyAndStore me _ _ _ _ _ _ _ (stLink_setRecvChain hst_r hc'_r)
      split
      · refine PQSpineLinkAt.bind (PQSpineLinkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ hle_d1 _ =>
          PQSpineLinkAt.bind (PQSpineLinkAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ hle_d2 _ =>
            htail (Trace.le_trans _ _ _ hle_d1 hle_d2)
      · exact htail (Trace.le_refl tr5)

theorem spineLinkInv_preserves_aliceStart {tr : ExecTrace}
    (a b : Participant) (idStateIdx regIdxB : Nat) (bh : BundleHandles) (hJ : SpineLinkInv tr) :
    SpineLinkInv ((aliceStart a b idStateIdx regIdxB bh).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine CompTrace.bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hJ (spineLinkInv_append_other hJ)
    fun ikA ikBPk _ spkPk _ pqPk _ opk _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  have htl : ∀ {α : Type} (g : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= g).run t).2.val = ((g t.length).run t).2.val := fun g t => by
    unfold DY.Libsignal.TripleRatchet.traceLength; rw [CompTrace.run_bind_snd, Traceful.run_mk]
  let hs := CompPresPQXDH.aliceOut tr ikA ikBPk spkPk pqPk opk
  let tr1 := tr.append (RndE 32); let tr2 := tr1.append (RndE 32); let dhsA := randTerm tr2.length 32
  let stA : TRState :=
    { peer := b, myIk := DY.Libsignal.PQXDH.serializedIk hs.ikA, peerIk := DY.Libsignal.PQXDH.serializedIk hs.ikB,
      rk := (createChain hs.keys.rk hs.spk dhsA).1, dhs := dhsA, cks := (createChain hs.keys.rk hs.spk dhsA).2,
      ns := 0, pn := 0,
      sid := Concat.concat (DiffieHellman.dhPk dhsA) hs.keys.rk,
      initiator := true, rIdx := 1,
      recv := [{ ratchetKey := hs.spk, chainKey := hs.keys.ck, index := 0, rIdx := 1 }],
      spqr := Spqr.spqrInit hs.keys.pqr spqrA2B }
  let tr3 := tr2.append (RndE 32); let tr4 := tr3.append (NetE hs.ek); let tr5 := tr4.append (NetE hs.ct)
  let tr6 := tr5.append (EvE (PQXDHEvent.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys))
  let tr7 := tr6.append (TREvE (TREvent.InitSession a b (DiffieHellman.dhPk dhsA) hs.spk))
  let tr8 := tr7.append (CEvE (ComposedEvent.HandshakeSession (stA.sessionInfo a) tr5.length))
  rw [CompTrace.run_genRand_bind_snd]; dsimp only
  rw [CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, htl,
    CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  change SpineLinkInv (tr8.append (TRStE a stA))
  have hJ8 : SpineLinkInv tr8 :=
    spineLinkInv_append_other (spineLinkInv_append_ev _ (by intro _ _ _ _ _ _ h; cases h)
      (spineLinkInv_append_other (spineLinkInv_append_other (spineLinkInv_append_other
        (spineLinkInv_append_other (spineLinkInv_append_other (spineLinkInv_append_other hJ)))))))
  have hle68 : tr6 ≤ tr8 :=
    Trace.le_trans _ _ _ (Trace.append_le tr6 _) (Trace.append_le tr7 _)
  have haliceDone8 : AliceDoneKeys tr8 hs.keys :=
    ⟨a, b, hs.ikA, hs.ikB, hs.spk, hs.pqpk, hs.opk, hs.ek, hs.ct, tr5.length,
     CompTrace.eventLoggedAt_mono hle68 (CompTrace.eventLoggedAt_here tr5 _)⟩
  refine spineLinkInv_append_st a (fun c hc => ?_) hJ8
  rw [List.mem_singleton] at hc; subst hc
  exact ⟨hs.keys.ck, 0, rfl, .inr (.inr ⟨hs.keys, haliceDone8, rfl⟩)⟩

theorem spineLinkInv_logSkippedKeys_preserves (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (c : RecvChain) (n : UInt32) (tr : ExecTrace),
      ChainLink tr c →
      SpineLinkInv tr →
      SpineLinkInv ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src c.chainKey n k).run tr).2.val
  | 0, _, _, _, _, hJ => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; rw [Traceful.run_pure]; exact hJ
  | k + 1, c, n, tr, hc, hJ => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
    let e : CompTrace.TREntry := TREvE (TREvent.SkippedKeyStored s pk n (kdfCk c.chainKey).2 rIdx src)
    refine spineLinkInv_logSkippedKeys_preserves s pk rIdx src k
      { c with chainKey := (kdfCk c.chainKey).1, index := n } (n + 1) (tr.append e)
      ((hc.mono (Trace.append_le tr e)).kdfCk_fst n)
      (spineLinkInv_append_ev _ ?_ hJ)
    intro _ _ _ _ _ _ h; cases h; exact SeedLink.of_chainLink hc

theorem spineLinkInv_bobStart_commit {tr : ExecTrace} (hJ : SpineLinkInv tr)
    (b a : Participant) (sB : DY.Bytes) (t_sS : Nat) (sQ : DY.Bytes) (o : Option DY.Bytes)
    (ikA ek ct : DY.Bytes) (keys : HandshakeKeys) (spkIdx : Nat)
    (msg : TRSignalMsg) (dhs spqr' seed pqSalt m : DY.Bytes) (c' : RecvChain)
    (hspk : CompTrace.PQXDHStoredAt tr b { kind := .signedPrekey, sk := randTerm t_sS 32 } spkIdx)
    (hConsume : consumeMessageKey
      (CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey (randTerm t_sS 32)) msg.counter =
      some (seed, c')) :
    let sS := randTerm t_sS 32
    let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
    let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
    SpineLinkInv (((do
      let doneIdx ← DY.Libsignal.TripleRatchet.traceLength
      ProtocolEvent.logEvent (PQXDHEvent.BobDone b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys)
      if true then
        ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs))
        ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
      ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
      let skipped := msg.counter.toNat - c.index.toNat; let childIdx := (← DY.Libsignal.TripleRatchet.traceLength) + skipped + 2
      DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
      ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx
        { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr).2.val) := by
  intro sS st c; let doneIdx := tr.length
  have htl : ∀ {α : Type} (g : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= g).run t).2.val = ((g t.length).run t).2.val := fun g t => by
    unfold DY.Libsignal.TripleRatchet.traceLength; rw [CompTrace.run_bind_snd, Traceful.run_mk]
  let tr₁ := tr.append (EvE (.BobDone b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys))
  let tr₂ := tr₁.append (TREvE (.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs)))
  let tr₃ := tr₂.append (TREvE (.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)))
  let tr₄ := tr₃.append (CEvE (.HandshakeSession (st.sessionInfo b) doneIdx))
  have hJ₄ : SpineLinkInv tr₄ :=
    spineLinkInv_append_other (spineLinkInv_append_ev _ (by intro _ _ _ _ _ _ h; cases h)
      (spineLinkInv_append_ev _ (by intro _ _ _ _ _ _ h; cases h) (spineLinkInv_append_other hJ)))
  have hle₁₄ : tr₁ ≤ tr₄ :=
    Trace.le_trans _ _ _ (Trace.append_le tr₁ _)
      (Trace.le_trans _ _ _ (Trace.append_le tr₂ _) (Trace.append_le tr₃ _))
  have hle₀₄ : tr ≤ tr₄ := Trace.le_trans _ _ _ (Trace.append_le tr _) hle₁₄
  have hbob₄ : BobDoneKeys tr₄ keys :=
    ⟨b, a, DiffieHellman.dhPk sB, ikA, DiffieHellman.dhPk sS, PQKem.kemPk sQ, o.map DiffieHellman.dhPk,
     ek, ct, tr.length, CompTrace.eventLoggedAt_mono hle₁₄ (CompTrace.eventLoggedAt_here tr _)⟩
  have hspk₄ : CompTrace.PQXDHStoredAt tr₄ b { kind := .signedPrekey, sk := randTerm t_sS 32 } spkIdx :=
    CompTrace.pqxdhStoredAt_mono hle₀₄ hspk
  have hc₄ : ChainLink tr₄ c :=
    ⟨(createChain keys.rk msg.ratchetKey (randTerm t_sS 32)).2, 0, rfl,
     .inr (.inl ⟨keys, t_sS, b, spkIdx, hbob₄, hspk₄, rfl⟩)⟩
  let skipped := msg.counter.toNat - c.index.toNat; let childIdx := tr₄.length + skipped + 2
  let skipAct := DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
  let restAct : Unit → Traceful Nat := fun _ => do
    ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
    DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx
      { st with recv := setRecvChain st.recv c', spqr := spqr' }
  rw [htl, CompPresTRExp.run_logEvent_bind_snd]; simp only [↓reduceIte]
  rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, htl]
  change SpineLinkInv (((skipAct >>= restAct).run tr₄).2.val)
  rw [CompInv.CompPresBob.run_logSkippedKeys_bind_snd]
  let tr₅ := (skipAct.run tr₄).2.val
  have hle₄₅ : tr₄ ≤ tr₅ := (skipAct.run tr₄).2.property
  have hJ₅ : SpineLinkInv tr₅ :=
    spineLinkInv_logSkippedKeys_preserves (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx skipped c c.index tr₄ hc₄ hJ₄
  let tr₆ := tr₅.append (TREvE (.Received b st.peer msg.ratchetKey msg.counter m))
  let tr₇ := tr₆.append (TREvE (.MessageKey (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx))
  have hJ₇ : SpineLinkInv tr₇ :=
    spineLinkInv_append_ev _ (by intro _ _ _ _ _ _ h; cases h)
      (spineLinkInv_append_ev _ (by intro _ _ _ _ _ _ h; cases h) hJ₅)
  have hle₄₇ : tr₄ ≤ tr₇ :=
    Trace.le_trans _ _ _ hle₄₅ (Trace.le_trans _ _ _ (Trace.append_le tr₅ _) (Trace.append_le tr₆ _))
  obtain ⟨_, hc'_eq⟩ := consumeMessageKey_eq_spine hConsume
  have hc₇ : ChainLink tr₇ c := hc₄.mono hle₄₇
  have hc'₇ : ChainLink tr₇ c' := by
    rw [hc'_eq]
    exact hc₇.advance (skipped + 1) (msg.counter + 1)
  have hst₇ : StLink tr₇ st := fun c0 hc0 => by
    dsimp [st, CompInv.CompPresBob.bobRatchetedSt] at hc0
    rw [List.mem_singleton] at hc0; subst hc0; exact hc₇
  dsimp only [restAct]
  rw [CompPresTRExp.run_logEvent_bind_snd]
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  rw [CompPresTRExp.run_logEvent_bind_snd]
  simp [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact spineLinkInv_append_st b (stLink_setRecvChain hst₇ hc'₇) hJ₇

theorem spineLinkInv_preserves_bobStart {tr : ExecTrace} (hinv : SpqrInv tr)
    (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (hJ : SpineLinkInv tr) :
    SpineLinkInv ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hJ
    fun sB sS sQ o ikA _ ek ct _ keys _ hspk _ _ _ _ _ _ _ => ?_
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg; rw [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_receiveMessage_at mh.msg tr hJ fun raw _ _ => ?_
  rcases parseTrSignalMsg raw with _ | msg; · dsimp only; rw [CompTrace.run_bind_snd, Traceful.run_failure]; exact hJ
  dsimp only; rw [CompTrace.run_bind_assoc_snd]; refine CompTrace.bind_guardP_at _ tr hJ fun _ => ?_
  refine CompInv.CompPresBob.bind_ensureReceiverChain_bobInitSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey tr hJ fun _ => ?_
  let dhs := CompKeyInversion.rnd tr.length 32
  let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
  let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
  let tr₁ := tr.append (RndE 32); have hJ₁ : SpineLinkInv tr₁ := spineLinkInv_append_other hJ
  rcases hConsume : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hJ₁
  dsimp only; rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hJ₁
  dsimp only
  let tr₂ := tr₁.append (NetE key); have hJ₂ : SpineLinkInv tr₂ := spineLinkInv_append_other hJ₁
  have hle₀₂ : tr ≤ tr₂ := Trace.le_trans _ _ _ (Trace.append_le tr _) (Trace.append_le tr₁ _)
  obtain ⟨t_sS, rfl, _, _, _⟩ := hinv.stOK b { kind := .signedPrekey, sk := sS } kh.spk hspk
  have hspk₂ : CompTrace.PQXDHStoredAt tr₂ b { kind := .signedPrekey, sk := randTerm t_sS 32 } kh.spk :=
    CompTrace.pqxdhStoredAt_mono hle₀₂ hspk
  rw [CompPresTRExp.run_sendMessage_bind_snd]
  change SpineLinkInv (((Network.receiveMessage pqIdx >>= fun pqSalt => DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed >>= fun m => _).run tr₂).2.val)
  refine CompTrace.bind_receiveMessage_at pqIdx tr₂ hJ₂ fun pqSalt _ _ =>
    CompInv.CompPresBob.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr₂ hJ₂ fun m _ => ?_
  cases o with
  | none =>
    dsimp only [Option.map]
    exact spineLinkInv_bobStart_commit hJ₂ b a sB t_sS sQ none ikA ek ct keys kh.spk msg dhs spqr' seed pqSalt m c' hspk₂ hConsume
  | some oSk =>
    dsimp only [Option.map]; rw [CompTrace.run_bind_snd]; unfold DY.Libsignal.PQXDH.guardTrace; rw [Traceful.run_mk]; dsimp only
    by_cases hused : (!opkUsedB tr₂ b (DiffieHellman.dhPk oSk)) = true
    · rw [ite_eq_left_iff.mpr fun h => absurd hused h]; dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd]
      exact spineLinkInv_bobStart_commit (spineLinkInv_append_other hJ₂) b a sB t_sS sQ (some oSk) ikA ek ct keys kh.spk msg dhs spqr' seed pqSalt m c'
        (CompTrace.pqxdhStoredAt_mono (Trace.append_le tr₂ _) hspk₂) hConsume
    · rw [ite_eq_right_iff.mpr fun h => absurd h hused]; dsimp only; exact hJ₂

theorem spineLinkInv_reachable {T : ExecTrace} (hT : ReachableTrace T) :
    SpineLinkInv T := by
  induction hT with
  | Base => exact spineLinkInv_nil
  | @Step tr_prev input _ hReachPre ih =>
    have hinv : SpqrInv tr_prev := spqrInv_of_reachable _ hReachPre
    have hst_bind : ∀ {S α : Type} [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT S)]
        (p : Participant) (s : S) (k : Nat → Traceful α) (t : ExecTrace),
        ((PersistentLocalState.storeLocalState p s >>= k).run t).2.val =
          ((k t.length).run (t.append (⟨⟨p, s⟩⟩ : PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState S)))).2.val :=
      fun p s k t => by
        simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
        rw [CompTrace.run_bind_snd, Traceful.run_mk]
    have hst_snd : ∀ {S : Type} [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT S)]
        (p : Participant) (s : S) (t : ExecTrace),
        ((PersistentLocalState.storeLocalState p s).run t).2.val =
          t.append (⟨⟨p, s⟩⟩ : PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState S)) :=
      fun p s t => by
        simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
    have hlog_snd : ∀ {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)] (ev : E) (t : ExecTrace),
        ((ProtocolEvent.logEvent ev).run t).2.val = t.append (⟨ev⟩ : ProtocolEvent.ExecEntryT E) := fun ev t => by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
      rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]
    rcases input with ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k, _⟩, inp⟩
    · change DY.Bytes at inp; change SpineLinkInv ((Network.sendMessage inp).run _).2.val
      rw [CompPresTRExp.run_sendMessage_snd]; exact spineLinkInv_append_other ih
    · change Participant at inp; change SpineLinkInv ((registerIdentity inp).run _).2.val; unfold registerIdentity
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ ih fun _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, hst_snd]
      exact spineLinkInv_append_other (spineLinkInv_append_other (spineLinkInv_append_other (spineLinkInv_append_other (spineLinkInv_append_other ih))))
    · rcases inp with ⟨p, skIdx⟩; change SpineLinkInv ((registerCorruptIdentity p skIdx).run _).2.val; unfold registerCorruptIdentity
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ ih fun _ =>
        CompTrace.bind_receiveMessage_at skIdx _ ih fun _ _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, hlog_snd]
      exact spineLinkInv_append_other (spineLinkInv_append_other ih)
    · rcases inp with ⟨b, idStateIdx⟩; change SpineLinkInv ((genSignedPrekey b idStateIdx).run _).2.val; unfold genSignedPrekey
      refine CompPresPQXDH.bind_getKey_at b idStateIdx .identity _ ih fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        hst_bind, CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact spineLinkInv_append_other (spineLinkInv_append_other (spineLinkInv_append_other (spineLinkInv_append_other (spineLinkInv_append_other (spineLinkInv_append_other ih)))))
    · rcases inp with ⟨b, idStateIdx⟩; change SpineLinkInv ((genPQPrekey b idStateIdx).run _).2.val; unfold genPQPrekey
      refine CompPresPQXDH.bind_getKey_at b idStateIdx .identity _ ih fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        hst_bind, CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact spineLinkInv_append_other (spineLinkInv_append_other (spineLinkInv_append_other (spineLinkInv_append_other (spineLinkInv_append_other (spineLinkInv_append_other ih)))))
    · change Participant at inp; change SpineLinkInv ((genOneTimePrekey inp).run _).2.val; unfold genOneTimePrekey
      rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd, hst_bind,
        CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact spineLinkInv_append_other (spineLinkInv_append_other (spineLinkInv_append_other (spineLinkInv_append_other ih)))
    · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩; exact spineLinkInv_preserves_aliceStart a b idStateIdx regIdxB bh ih
    · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩; exact spineLinkInv_preserves_bobStart hinv b a kh regIdxA mh pqIdx spqrMsgIdx ih
    · rcases inp with ⟨me, stateIdx, coinsLen, pqIdx⟩; exact (PQSpineLinkAt.messageEncrypt me stateIdx coinsLen pqIdx ih).1
    · rcases inp with ⟨me, stateIdx⟩; exact (PQSpineLinkAt.messageEncryptAbort me stateIdx ih).1
    · rcases inp with ⟨me, stateIdx, msgIdx, pqIdx, spqrMsgIdx⟩; exact (PQSpineLinkAt.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx ih).1
    · rcases inp with ⟨me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx⟩; exact (PQSpineLinkAt.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx ih).1
    · rcases inp with ⟨me, stateIdx, k⟩; exact (PQSpineLinkAt.exposeKey me stateIdx k ih).1
    · rcases inp with ⟨me, stateIdx⟩; exact (PQSpineLinkAt.exposeSpqr me stateIdx ih).1
    · exact (PQSpineLinkAt.exposeSkipped inp ih).1
    · rcases inp with ⟨p, stateIdx⟩; change SpineLinkInv ((compromiseIK p stateIdx).run _).2.val; unfold compromiseIK
      refine CompPresPQXDH.bind_getKey_at p stateIdx .identity _ ih fun _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact spineLinkInv_append_other (spineLinkInv_append_other ih)
    · rcases inp with ⟨b, stateIdx⟩; change SpineLinkInv ((compromiseSPK b stateIdx).run _).2.val; unfold compromiseSPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .signedPrekey _ ih fun _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact spineLinkInv_append_other (spineLinkInv_append_other ih)
    · rcases inp with ⟨b, stateIdx⟩; change SpineLinkInv ((compromisePQSPK b stateIdx).run _).2.val; unfold compromisePQSPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .pqPrekey _ ih fun _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact spineLinkInv_append_other (spineLinkInv_append_other ih)
    · rcases inp with ⟨b, stateIdx⟩; change SpineLinkInv ((compromiseOPK b stateIdx).run _).2.val; unfold compromiseOPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .oneTimePrekey _ ih fun _ _ => ?_
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ ih fun _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact spineLinkInv_append_other (spineLinkInv_append_other ih)
    · change SpineLinkInv ((DY.Libsignal.PQXDH.breakDH).run _).2.val; unfold DY.Libsignal.PQXDH.breakDH
      rw [hlog_snd]; exact spineLinkInv_append_other ih
    · change SpineLinkInv ((DY.Libsignal.PQXDH.breakKEM).run _).2.val; unfold DY.Libsignal.PQXDH.breakKEM
      rw [hlog_snd]; exact spineLinkInv_append_other ih
    · change Nat at inp; change SpineLinkInv ((invertDH inp).run _).2.val; unfold invertDH
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ ih fun _ =>
        CompTrace.bind_receiveMessage_at inp tr_prev ih fun pk _ _ => ?_
      rcases DY.Libsignal.PQXDH.extractDhSecretKey (X25519.normalizeX25519Key pk) with _ | sk
      · dsimp only; rw [Traceful.run_failure]; exact ih
      · dsimp only; rw [CompPresTRExp.run_sendMessage_snd]; exact spineLinkInv_append_other ih
    · change Nat at inp; change SpineLinkInv ((invertKEM inp).run _).2.val; unfold invertKEM
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ ih fun _ =>
        CompTrace.bind_receiveMessage_at inp tr_prev ih fun pk _ _ => ?_
      rcases PQKem.invertKemPublicKey pk with _ | sk
      · rw [CompTrace.run_bind_snd]; erw [Traceful.run_mk]; exact ih
      · rw [CompTrace.run_bind_snd]; erw [Traceful.run_mk]; dsimp [MonadLift.monadLift]
        rw [CompPresTRExp.run_sendMessage_snd]; exact spineLinkInv_append_other ih
    · omega

/-- Every receive chain `c ∈ st.recv` of a stored `TRState` on a reachable trace `T` has
`c.chainKey = chainKeyAt R j` with `RecvRoot T c.ratchetKey R`. -/
theorem recvLinkStored_of_reachable {T : ExecTrace} (hT : ReachableTrace T) : RecvLinkStored T :=
  (spineLinkInv_reachable hT).1

/-- Every `SkippedKeyStored` seed on a reachable trace `T` has `seed = (kdfCk (chainKeyAt R j)).2`
with `RecvRoot T pk' R`. -/
theorem recvLinkSkipped_of_reachable {T : ExecTrace} (hT : ReachableTrace T) : RecvLinkSkipped T :=
  (spineLinkInv_reachable hT).2

end Symbolic.Swarm.CREF.TR.G1.Spine
