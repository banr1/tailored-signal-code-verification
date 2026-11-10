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
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTR
public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTRStrong
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.Lemmas
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Root-Key History of Stored Session States

Proves `rkHist_of_stored`: every `TRState` stored at index `i` on a reachable composed trace `T`
either arises directly from a logged `AliceDone` or `BobDone` handshake (`RkHistBase T st`) or is
obtained by a `dhRatchetStep` from an earlier stored state at index `i' < i` (`RkHistStep T i st`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY DY.Comparse DY.DiffieHellman DY.Libsignal.TripleRatchet Symbolic.Swarm.CREF.TR
open DY.Libsignal.TripleRatchet (RecvChain SessionInfo KeyDir KeyComponent createChain
  consumeMessageKey findRecvChain setRecvChain kdfCk)
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys BundleHandles BobKeyHandles PreKeyMsgHandles
  opkUsedB registerIdentity registerCorruptIdentity genSignedPrekey genPQPrekey genOneTimePrekey
  compromiseIK compromiseSPK compromisePQSPK compromiseOPK invertDH invertKEM)
open Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompPresPQXDH
open Symbolic.Swarm.COMPOSED.CompInv (SpqrInv spqrInv_of_reachable EvE)

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

/-! ## Root-key history predicates -/

/-- A root key produced by a `dhRatchetStep` from an earlier stored `TRState` at `i' < i` on `T`. -/
def RkHistStep (T : ExecTrace) (i : Nat) (st : TRState) : Prop :=
  ∃ (p' : Participant) (st' : TRState) (i' : Nat) (pk : DY.Bytes),
    i' < i ∧ TRStateStoredAt p' st' i' T ∧
    st.rk = (createChain (createChain st'.rk pk st'.dhs).1 pk st.dhs).1

/-- Initial stored root-key forms produced by `aliceStart` (one `createChain` from a logged
`AliceDone` handshake `keys.rk`) and `bobStart` (two `createChain` steps from a logged `BobDone`
handshake `keys.rk`). -/
def RkHistBase (T : ExecTrace) (st : TRState) : Prop :=
  (∃ (a b : Participant) (ikA ikB spk pqpk : DY.Bytes) (opk : Option DY.Bytes)
     (ek ct : DY.Bytes) (keys : HandshakeKeys) (j : Nat),
     T.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) j ∧
     st.rk = (createChain keys.rk spk st.dhs).1) ∨
  (∃ (b a : Participant) (ikB ikA spk pqpk : DY.Bytes) (opk : Option DY.Bytes)
     (ek ct : DY.Bytes) (keys : HandshakeKeys) (j t idx : Nat) (pk : DY.Bytes),
     T.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) j ∧
     CompTrace.PQXDHStoredAt T b { kind := .signedPrekey, sk := randTerm t 32 } idx ∧
     st.rk = (createChain (createChain keys.rk pk (randTerm t 32)).1 pk st.dhs).1)

theorem rkHistBase_of_rk_dhs_eq {T : ExecTrace} (st₀ st₁ : TRState)
    (hrk : st₁.rk = st₀.rk) (hdhs : st₁.dhs = st₀.dhs) (h : RkHistBase T st₀) :
    RkHistBase T st₁ := by
  rcases h with ⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, j, hev, heq⟩ |
    ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, keys, j, t, idx, pk, hev, hspk, heq⟩
  · exact .inl ⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, j, hev, by rw [hrk, hdhs, heq]⟩
  · exact .inr ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, keys, j, t, idx, pk, hev, hspk, by rw [hrk, hdhs, heq]⟩

theorem rkHist_preserve_rk_dhs {T : ExecTrace} {i₀ i₁ : Nat} (st₀ st₁ : TRState)
    (hlt : i₀ < i₁) (hrk : st₁.rk = st₀.rk) (hdhs : st₁.dhs = st₀.dhs)
    (h : RkHistBase T st₀ ∨ RkHistStep T i₀ st₀) :
    RkHistBase T st₁ ∨ RkHistStep T i₁ st₁ := by
  rcases h with hbase | ⟨p', st', i', pk, hi', hst', heq⟩
  · exact .inl (rkHistBase_of_rk_dhs_eq st₀ st₁ hrk hdhs hbase)
  · exact .inr ⟨p', st', i', pk, Nat.lt_trans hi' hlt, hst', by rw [hrk, hdhs, heq]⟩

/-- Trace invariant for `RkHist`: every state stored on `tr` at index `i` satisfies
`RkHistBase T st ∨ RkHistStep T i st`. -/
def JRkHist (T tr : ExecTrace) : Prop :=
  ∀ p st i, TRStateStoredAt p st i tr → RkHistBase T st ∨ RkHistStep T i st

/-! ## `JRkHist` and `PQRkHistAt` combinators -/

theorem JRkHist_nil (T : ExecTrace) : JRkHist T Trace.nil :=
  fun _ _ _ h => by simp [TRStateStoredAt, Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1] at h

theorem JRkHist_append_other {T tr : ExecTrace} {E : Type} [ExecTraceTypes.Has E] {e : E}
    (h : JRkHist T tr)
    (hst : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option CompTrace.TRStEntry) = none := by rfl) :
    JRkHist T (tr.append e) :=
  fun p st i hs => h p st i (CompTrace.trStateStoredAt_append_other hst hs)

theorem JRkHist_append_st {T tr : ExecTrace} (p : Participant) {st : TRState}
    (hst : RkHistBase T st ∨ RkHistStep T tr.length st) (h : JRkHist T tr) :
    JRkHist T (tr.append (TRStE p st)) := by
  intro p' st' i hs
  rcases CompTrace.trStateStoredAt_append_same hs with ⟨_, hs⟩ | ⟨rfl, rfl, rfl⟩
  · exact h p' st' i hs
  · exact hst

def PQRkHistAt (T tr : ExecTrace) {α : Type} (Q : ExecTrace → α → Prop) (x : Traceful α) : Prop :=
  JRkHist T tr → (x.run tr).2.val ≤ T →
    JRkHist T (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q (x.run tr).2.val a

theorem PQRkHistAt.bind {T tr : ExecTrace} {α β : Type} {Q : ExecTrace → α → Prop} {R : ExecTrace → β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : PQRkHistAt T tr Q x) (hf : ∀ tr1 a, tr ≤ tr1 → Q tr1 a → PQRkHistAt T tr1 R (f a)) :
    PQRkHistAt T tr R (x >>= f) := by
  intro hJ hle; rw [CompTrace.run_bind_snd] at hle; rw [Traceful.run_bind]; have hx0 := hx hJ
  rcases h : x.run tr with ⟨_ | a, trMid, hmid⟩ <;> rw [h] at hle hx0
  · exact ⟨(hx0 hle).1, fun b hb => by cases hb⟩
  · have hx' := hx0 (Trace.le_trans _ _ _ ((f a).run trMid).2.property hle)
    exact hf trMid a hmid (hx'.2 a rfl) hx'.1 hle

theorem PQRkHistAt.of_id {T tr : ExecTrace} {α : Type} {x : Traceful α} (hx : (x.run tr).2.val = tr) :
    PQRkHistAt T tr (fun _ _ => True) x := by
  intro hJ _; rw [hx]; exact ⟨hJ, fun _ _ => trivial⟩

theorem PQRkHistAt.pure {T tr : ExecTrace} {α : Type} {Q : ExecTrace → α → Prop} (a : α) (ha : Q tr a) :
    PQRkHistAt T tr Q (Pure.pure a : Traceful α) := by
  intro hJ _; rw [Traceful.run_pure]; refine ⟨hJ, fun b hb => ?_⟩; cases hb; exact ha

theorem PQRkHistAt.failure {T tr : ExecTrace} {α : Type} {Q : ExecTrace → α → Prop} :
    PQRkHistAt T tr Q (Alternative.failure : Traceful α) := by
  intro hJ _; rw [Traceful.run_failure]; exact ⟨hJ, fun _ hb => by cases hb⟩

theorem PQRkHistAt.guardP {T tr : ExecTrace} (p : Prop) [Decidable p] :
    PQRkHistAt T tr (fun _ _ => p) (_root_.guard p : Traceful Unit) := by
  unfold _root_.guard; split <;> [(rename_i hp; exact PQRkHistAt.pure () hp); exact PQRkHistAt.failure]

theorem PQRkHistAt.guardTrace {T tr : ExecTrace} (p : ExecTrace → Bool) :
    PQRkHistAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.guardTrace p) :=
  PQRkHistAt.of_id (by unfold DY.Libsignal.TripleRatchet.guardTrace; rw [Traceful.run_mk])

theorem PQRkHistAt.traceLength {T tr : ExecTrace} :
    PQRkHistAt T tr (fun _ _ => True) DY.Libsignal.TripleRatchet.traceLength :=
  PQRkHistAt.of_id (by unfold DY.Libsignal.TripleRatchet.traceLength; rw [Traceful.run_mk])

theorem PQRkHistAt.genRand {T tr : ExecTrace} (n : Nat) :
    PQRkHistAt T tr (fun _ r => r = randTerm tr.length n) (Random.genRand n) := by
  intro hJ _; simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Traceful.run_bind, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]
  exact ⟨JRkHist_append_other hJ, fun b hb => by cases hb; rfl⟩

theorem PQRkHistAt.sendMessage {T tr : ExecTrace} (m : DY.Bytes) :
    PQRkHistAt T tr (fun _ _ => True) (Network.sendMessage m) := by
  intro hJ _; rw [CompPresTRExp.run_sendMessage_snd]
  exact ⟨JRkHist_append_other hJ, fun _ _ => trivial⟩

theorem PQRkHistAt.logEvent {T tr : ExecTrace} (ev : TREvent) :
    PQRkHistAt T tr (fun tr1 _ => tr1 = tr.append (TREvE ev)) (ProtocolEvent.logEvent ev) := by
  intro hJ _; simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Traceful.run_bind, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]
  exact ⟨JRkHist_append_other hJ, fun b hb => by cases hb; rfl⟩

theorem PQRkHistAt.storeLocalState {T tr : ExecTrace} (p : Participant) {st : TRState}
    (hst : RkHistBase T st ∨ RkHistStep T tr.length st) :
    PQRkHistAt T tr (fun _ _ => True) (PersistentLocalState.storeLocalState p st) := by
  intro hJ _; simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Traceful.run_mk]
  exact ⟨JRkHist_append_st p hst hJ, fun _ _ => trivial⟩

theorem PQRkHistAt.getLocalState {T tr : ExecTrace} (me : Participant) (stH : Nat) :
    PQRkHistAt T tr
      (fun tr1 st => tr1 = tr ∧ stH < tr.length ∧ (RkHistBase T st ∨ RkHistStep T stH st) ∧ TRStateStoredAt me st stH T)
      (PersistentLocalState.getLocalState me stH) := by
  intro hJ hle; rw [CompTrace.getLocalState_tr_snd] at hle ⊢; refine ⟨hJ, fun st hst => ?_⟩
  rw [CompTrace.getLocalState_tr_fst] at hst
  rcases he : (tr.at? stH : Option CompTrace.TRStEntry) with _ | ⟨⟨p, st'⟩⟩
  · rw [he] at hst; cases hst
  · rw [he] at hst; dsimp only at hst
    by_cases hp : p = me
    · subst hp; simp only [↓reduceIte] at hst; cases hst
      have hlt : stH < tr.length := by
        have := Trace.at?_eq_some_implies_length_le (EntryT := CompTrace.TRStEntry) tr stH
        rw [he] at this; exact this
      exact ⟨rfl, hlt, hJ _ _ stH he, CompTrace.trStateStoredAt_mono hle he⟩
    · simp only [hp, ↓reduceIte] at hst; cases hst

theorem PQRkHistAt.getEntryTR {T tr : ExecTrace} (evH : Nat) :
    PQRkHistAt T tr (fun _ _ => True) (DY.getEntry evH : Traceful CompTrace.TREntry) :=
  PQRkHistAt.of_id (by simp only [Symbolic.DYBridge.DY.getEntry_eq_1]; rw [Traceful.run_mk])

theorem PQRkHistAt.receiveMessage {T tr : ExecTrace} (msgH : Nat) :
    PQRkHistAt T tr (fun _ _ => True) (Network.receiveMessage msgH) := by
  intro hJ _; rw [CompTrace.receiveMessage_snd]; exact ⟨hJ, fun _ _ => trivial⟩

theorem PQRkHistAt.receiveSignalMsg {T tr : ExecTrace} (msgH : Nat) :
    PQRkHistAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.receiveSignalMsg msgH) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine PQRkHistAt.bind (PQRkHistAt.receiveMessage msgH) fun _ t _ _ => ?_
  rcases parseTrSignalMsg t with _ | msg
  · exact PQRkHistAt.failure
  · exact PQRkHistAt.bind (PQRkHistAt.guardP _) fun _ _ _ _ => PQRkHistAt.pure msg trivial

theorem PQRkHistAt.verifyMacAndDecrypt {T tr : ExecTrace} (st : TRState) (msg : TRSignalMsg) (pqSalt seed : DY.Bytes) :
    PQRkHistAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  refine PQRkHistAt.bind (PQRkHistAt.guardP _) fun _ _ _ _ =>
    PQRkHistAt.of_id (by erw [Traceful.run_mk])

theorem PQRkHistAt.logSkippedKeys {T : ExecTrace} (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32) {tr : ExecTrace},
      PQRkHistAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k)
  | 0, _, _, _ => by simp only [DY.Libsignal.TripleRatchet.logSkippedKeys]; exact PQRkHistAt.pure () trivial
  | k + 1, ck, n, _ => by
    simp only [DY.Libsignal.TripleRatchet.logSkippedKeys]
    exact PQRkHistAt.bind (PQRkHistAt.logEvent _) fun _ _ _ _ =>
      PQRkHistAt.logSkippedKeys s pk rIdx src k (kdfCk ck).1 (n + 1)

theorem PQRkHistAt.logMessageKeyAndStore {T tr : ExecTrace} (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx p : Nat) {st : TRState} {i₀ : Nat}
    (hle : i₀ ≤ tr.length)
    (hst : RkHistBase T st ∨ RkHistStep T i₀ st) :
    PQRkHistAt T tr (fun _ _ => True)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx p st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  refine PQRkHistAt.bind (PQRkHistAt.logEvent _) fun tr2 _ _ htr2 => ?_
  have hlt : i₀ < tr2.length := by
    subst htr2; simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  exact PQRkHistAt.storeLocalState me (rkHist_preserve_rk_dhs st st hlt rfl rfl hst)

/-! ## Transition preservation and `rkHist_of_stored` -/

theorem PQRkHistAt.dhRatchetStep {T tr : ExecTrace} {me : Participant} {st0 : TRState} {stH : Nat}
    {pk : DY.Bytes} (hlt : stH < tr.length) (hstored0 : TRStateStoredAt me st0 stH T) :
    PQRkHistAt T tr
      (fun tr1 (r : TRState × RecvChain) => stH < tr1.length ∧ (RkHistBase T r.1 ∨ RkHistStep T tr1.length r.1))
      (DY.Libsignal.TripleRatchet.dhRatchetStep st0 pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine PQRkHistAt.bind (PQRkHistAt.guardP _) fun _ _ hle0 _ => ?_
  rcases hc1 : createChain st0.rk pk st0.dhs with ⟨rk1, ckr⟩; dsimp only
  have hrk1_eq : rk1 = (createChain st0.rk pk st0.dhs).1 := by rw [hc1]
  refine PQRkHistAt.bind (PQRkHistAt.genRand 32) fun tr1 dhs hle1 _ => ?_
  rcases hc2 : createChain rk1 pk dhs with ⟨rk2, cks⟩; dsimp only
  have hrk2_eq : rk2 = (createChain (createChain st0.rk pk st0.dhs).1 pk dhs).1 := by
    rw [← hrk1_eq, hc2]
  have hlt1 : stH < tr1.length :=
    Nat.lt_of_lt_of_le hlt (Trace.length_le _ _ (Trace.le_trans _ _ _ hle0 hle1))
  exact PQRkHistAt.pure _ ⟨hlt1, .inr ⟨me, st0, stH, pk, hlt1, hstored0, hrk2_eq⟩⟩

theorem PQRkHistAt.ensureReceiverChain {T tr : ExecTrace} {me : Participant} {st0 : TRState} {stH : Nat}
    {pk : DY.Bytes} (hlt : stH < tr.length) (hst0 : RkHistBase T st0 ∨ RkHistStep T stH st0)
    (hstored0 : TRStateStoredAt me st0 stH T) :
    PQRkHistAt T tr
      (fun tr1 (r : TRState × RecvChain × Bool) =>
        ∃ i₀, i₀ ≤ tr1.length ∧ (RkHistBase T r.1 ∨ RkHistStep T i₀ r.1))
      (DY.Libsignal.TripleRatchet.ensureReceiverChain st0 pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split
  · exact PQRkHistAt.pure _ ⟨stH, Nat.le_of_lt hlt, hst0⟩
  · refine PQRkHistAt.bind (PQRkHistAt.dhRatchetStep hlt hstored0) fun tr1 ⟨st', c⟩ _ ⟨_, hr⟩ =>
      PQRkHistAt.pure _ ⟨tr1.length, Nat.le_refl _, hr⟩
  · exact PQRkHistAt.failure

theorem PQRkHistAt.messageEncryptAbort {T tr : ExecTrace} (me : Participant) (stH : Nat) :
    PQRkHistAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  exact PQRkHistAt.bind (PQRkHistAt.getLocalState me stH) fun _ _ _ _ =>
    PQRkHistAt.bind (PQRkHistAt.genRand 32) fun _ _ _ _ => PQRkHistAt.failure

theorem PQRkHistAt.messageEncrypt {T tr : ExecTrace} (me : Participant) (stH coinsLen pqIdx : Nat) :
    PQRkHistAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine PQRkHistAt.bind (PQRkHistAt.getLocalState me stH) fun _ st _ ⟨rfl, hlt, hst, _⟩ =>
    PQRkHistAt.bind (PQRkHistAt.guardP _) fun _ _ hle0 _ =>
    PQRkHistAt.bind (PQRkHistAt.genRand 32) fun _ _ hle1 _ =>
    PQRkHistAt.bind (PQRkHistAt.genRand coinsLen) fun _ coins hle2 _ => ?_
  rcases Spqr.spqrSend st.spqr coins with ⟨spqr', key, pqMsg⟩; dsimp only
  refine PQRkHistAt.bind (PQRkHistAt.sendMessage key) fun _ _ hle3 _ => ?_
  rcases kdfCk st.cks with ⟨ck', seed⟩; dsimp only
  refine PQRkHistAt.bind (PQRkHistAt.receiveMessage pqIdx) fun _ pqSalt hle4 _ =>
    PQRkHistAt.bind (PQRkHistAt.logEvent _) fun tr_ev _ hle5 _ => ?_
  have hle_all := Trace.le_trans _ _ _ hle0 (Trace.le_trans _ _ _ hle1 (Trace.le_trans _ _ _ hle2
    (Trace.le_trans _ _ _ hle3 (Trace.le_trans _ _ _ hle4 hle5))))
  have hle_ev : stH ≤ tr_ev.length := Nat.le_trans (Nat.le_of_lt hlt) (Trace.length_le _ _ hle_all)
  have hst' : RkHistBase T { st with cks := ck', ns := st.ns + 1, spqr := spqr' } ∨
      RkHistStep T stH { st with cks := ck', ns := st.ns + 1, spqr := spqr' } := by
    rcases hst with hbase | hstep
    · exact .inl (rkHistBase_of_rk_dhs_eq st { st with cks := ck', ns := st.ns + 1, spqr := spqr' } rfl rfl hbase)
    · exact .inr hstep
  exact PQRkHistAt.bind (PQRkHistAt.logMessageKeyAndStore me _ _ _ _ _ _ _ hle_ev hst') fun _ _ _ _ =>
    PQRkHistAt.sendMessage _

theorem PQRkHistAt.exposeKey {T tr : ExecTrace} (me : Participant) (stH : Nat) (k : KeyComponent) :
    PQRkHistAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeKey me stH k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine PQRkHistAt.bind (PQRkHistAt.getLocalState me stH) fun _ st _ _ => ?_
  cases k with
  | rk => exact PQRkHistAt.bind (PQRkHistAt.logEvent _) fun _ _ _ _ => PQRkHistAt.sendMessage _
  | dhs => exact PQRkHistAt.bind (PQRkHistAt.logEvent _) fun _ _ _ _ => PQRkHistAt.sendMessage _
  | cks => exact PQRkHistAt.bind (PQRkHistAt.logEvent _) fun _ _ _ _ => PQRkHistAt.sendMessage _
  | ckr pk =>
    dsimp only
    rcases findRecvChain st.recv pk with _ | c <;>
      [exact PQRkHistAt.failure;
       exact PQRkHistAt.bind (PQRkHistAt.logEvent _) fun _ _ _ _ => PQRkHistAt.sendMessage _]

theorem PQRkHistAt.exposeSpqr {T tr : ExecTrace} (me : Participant) (stH : Nat) :
    PQRkHistAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeSpqr me stH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  exact PQRkHistAt.bind (PQRkHistAt.getLocalState me stH) fun _ _ _ _ =>
    PQRkHistAt.bind (PQRkHistAt.logEvent _) fun _ _ _ _ =>
      PQRkHistAt.sendMessage _

theorem PQRkHistAt.exposeSkipped {T tr : ExecTrace} (evH : Nat) :
    PQRkHistAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeSkipped evH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine PQRkHistAt.bind (PQRkHistAt.getEntryTR evH) fun _ ⟨ev⟩ _ _ => ?_
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    exact PQRkHistAt.bind (PQRkHistAt.guardTrace _) fun _ _ _ _ =>
      PQRkHistAt.bind (PQRkHistAt.logEvent _) fun _ _ _ _ =>
        PQRkHistAt.sendMessage _
  | _ => exact PQRkHistAt.failure

theorem PQRkHistAt.messageDecryptSkipped {T tr : ExecTrace} (me : Participant) (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    PQRkHistAt T tr (fun _ _ => True)
      (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine PQRkHistAt.bind (PQRkHistAt.getLocalState me stH) fun _ st _ ⟨rfl, hlt, hst, _⟩ =>
    PQRkHistAt.bind (PQRkHistAt.receiveSignalMsg msgH) fun _ msg hle1 _ =>
    PQRkHistAt.bind (PQRkHistAt.getEntryTR evH) fun _ ⟨ev⟩ hle2 _ => ?_
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    refine PQRkHistAt.bind (PQRkHistAt.guardP _) fun _ _ hle3 _ =>
      PQRkHistAt.bind (PQRkHistAt.guardTrace _) fun _ _ hle4 _ => ?_
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · exact PQRkHistAt.failure
    · refine PQRkHistAt.bind (PQRkHistAt.sendMessage key) fun _ _ hle5 _ =>
        PQRkHistAt.bind (PQRkHistAt.receiveMessage pqIdx) fun _ pqSalt hle6 _ =>
        PQRkHistAt.bind (PQRkHistAt.verifyMacAndDecrypt st msg pqSalt seed) fun _ _ hle7 _ =>
        PQRkHistAt.bind (PQRkHistAt.logEvent _) fun _ _ hle8 _ =>
        PQRkHistAt.bind (PQRkHistAt.logEvent _) fun tr_ev _ hle9 _ => ?_
      have hle_all := Trace.le_trans _ _ _ hle1 (Trace.le_trans _ _ _ hle2 (Trace.le_trans _ _ _ hle3
        (Trace.le_trans _ _ _ hle4 (Trace.le_trans _ _ _ hle5 (Trace.le_trans _ _ _ hle6
        (Trace.le_trans _ _ _ hle7 (Trace.le_trans _ _ _ hle8 hle9)))))))
      have hle_ev : stH ≤ tr_ev.length := Nat.le_trans (Nat.le_of_lt hlt) (Trace.length_le _ _ hle_all)
      have hst' : RkHistBase T { st with spqr := spqr' } ∨ RkHistStep T stH { st with spqr := spqr' } := by
        rcases hst with hbase | hstep
        · exact .inl (rkHistBase_of_rk_dhs_eq st { st with spqr := spqr' } rfl rfl hbase)
        · exact .inr hstep
      exact PQRkHistAt.logMessageKeyAndStore me _ _ _ _ _ _ _ hle_ev hst'
  | _ => exact PQRkHistAt.failure

theorem PQRkHistAt.messageDecrypt {T tr : ExecTrace} (me : Participant) (stH msgH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    PQRkHistAt T tr (fun _ _ => True)
      (DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine PQRkHistAt.bind (PQRkHistAt.getLocalState me stH) fun _ st0 _ ⟨rfl, hlt, hst0, hstored0⟩ =>
    PQRkHistAt.bind (PQRkHistAt.receiveSignalMsg msgH) fun tr1 msg hle1 _ => ?_
  have hlt1 : stH < tr1.length := Nat.lt_of_lt_of_le hlt (Trace.length_le _ _ hle1)
  refine PQRkHistAt.bind (PQRkHistAt.ensureReceiverChain hlt1 hst0 hstored0)
    fun tr2 ⟨st, c, ratcheted⟩ _ ⟨i₀, hi₀_le, hst⟩ => ?_
  dsimp only
  rcases consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩; · exact PQRkHistAt.failure
  dsimp only
  rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · exact PQRkHistAt.failure
  refine PQRkHistAt.bind (PQRkHistAt.sendMessage key) fun _ _ hle3 _ =>
    PQRkHistAt.bind (PQRkHistAt.receiveMessage pqIdx) fun _ pqSalt hle4 _ =>
    PQRkHistAt.bind (PQRkHistAt.verifyMacAndDecrypt st msg pqSalt seed) fun tr6 m hle5 _ => ?_
  let d := msg.counter.toNat - c.index.toNat
  have hle26 : tr2 ≤ tr6 := Trace.le_trans _ _ _ hle3 (Trace.le_trans _ _ _ hle4 hle5)
  have hst' : RkHistBase T { st with recv := setRecvChain st.recv c', spqr := spqr' } ∨
      RkHistStep T i₀ { st with recv := setRecvChain st.recv c', spqr := spqr' } := by
    rcases hst with hbase | hstep
    · exact .inl (rkHistBase_of_rk_dhs_eq st { st with recv := setRecvChain st.recv c', spqr := spqr' } rfl rfl hbase)
    · exact .inr hstep
  have htail : ∀ {tr_t : ExecTrace}, tr6 ≤ tr_t → PQRkHistAt T tr_t (fun _ _ => True) (do
      DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stH c.chainKey c.index d
      ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
      DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st.sessionInfo me) KeyDir.receiver seed pqSalt msg.counter c.rIdx stH
        { st with recv := setRecvChain st.recv c', spqr := spqr' }) := fun {tr_t} hle6t =>
    PQRkHistAt.bind (PQRkHistAt.logSkippedKeys _ _ _ _ d c.chainKey c.index) fun _ _ hle_sk _ =>
      PQRkHistAt.bind (PQRkHistAt.logEvent _) fun tr_ev _ hle_rc _ => by
        have hle_all := Trace.le_trans _ _ _ hle26 (Trace.le_trans _ _ _ hle6t (Trace.le_trans _ _ _ hle_sk hle_rc))
        have hle_ev : i₀ ≤ tr_ev.length := Nat.le_trans hi₀_le (Trace.length_le _ _ hle_all)
        exact PQRkHistAt.logMessageKeyAndStore me _ _ _ _ _ _ _ hle_ev hst'
  split
  · refine PQRkHistAt.bind (PQRkHistAt.logEvent _) fun _ _ hle7 _ =>
      PQRkHistAt.bind (PQRkHistAt.logEvent _) fun _ _ hle8 _ =>
      htail (Trace.le_trans _ _ _ hle7 hle8)
  · exact htail (Trace.le_refl _)

theorem JRkHist_preserves_aliceStart {T tr : ExecTrace}
    (a b : Participant) (idStateIdx regIdxB : Nat) (bh : BundleHandles)
    (hle : ((aliceStart a b idStateIdx regIdxB bh).run tr).2.val ≤ T) (hJ : JRkHist T tr) :
    JRkHist T ((aliceStart a b idStateIdx regIdxB bh).run tr).2.val := by
  revert hle
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine CompTrace.bind_aliceHandshake_at (Inv := fun tr_end => tr_end ≤ T → JRkHist T tr_end)
    a b idStateIdx regIdxB bh tr (fun _ => hJ) (fun _ => JRkHist_append_other hJ)
    fun ikA ikBPk _ spkPk _ pqPk _ opk _ _ _ _ _ _ _ _ _ _ _ _ hle_end => ?_
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
  rw [CompTrace.run_genRand_bind_snd] at hle_end ⊢; dsimp only at hle_end ⊢
  rw [CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, htl,
    CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd] at hle_end ⊢
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk] at hle_end ⊢
  change (tr8.append (TRStE a stA)) ≤ T at hle_end
  change JRkHist T (tr8.append (TRStE a stA))
  have hJ8 : JRkHist T tr8 :=
    JRkHist_append_other (JRkHist_append_other (JRkHist_append_other (JRkHist_append_other
      (JRkHist_append_other (JRkHist_append_other (JRkHist_append_other (JRkHist_append_other hJ)))))))
  have hle6_end : tr6 ≤ tr8.append (TRStE a stA) :=
    Trace.le_trans _ _ _ (Trace.append_le tr6 _)
      (Trace.le_trans _ _ _ (Trace.append_le tr7 _) (Trace.append_le tr8 _))
  have hev_T : T.EventLoggedAt (PQXDHEvent.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys) tr5.length :=
    CompTrace.eventLoggedAt_mono (Trace.le_trans _ _ _ hle6_end hle_end)
      (CompTrace.eventLoggedAt_here tr5 _)
  exact JRkHist_append_st a
    (.inl (.inl ⟨a, b, hs.ikA, hs.ikB, hs.spk, hs.pqpk, hs.opk, hs.ek, hs.ct, hs.keys, tr5.length, hev_T, rfl⟩))
    hJ8

theorem JRkHist_logSkippedKeys_preserves {T : ExecTrace} (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32) (tr : ExecTrace),
      JRkHist T tr →
      JRkHist T ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k).run tr).2.val
  | 0, _, _, _, hJ => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; rw [Traceful.run_pure]; exact hJ
  | k + 1, ck, n, tr, hJ => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
    exact JRkHist_logSkippedKeys_preserves s pk rIdx src k (kdfCk ck).1 (n + 1) _ (JRkHist_append_other hJ)

theorem JRkHist_bobStart_commit {T tr : ExecTrace} (hJ : JRkHist T tr)
    (b a : Participant) (sB : DY.Bytes) (t_sS idx_spk : Nat) (sQ : DY.Bytes) (o : Option DY.Bytes)
    (ikA ek ct : DY.Bytes) (keys : HandshakeKeys)
    (msg : TRSignalMsg) (dhs spqr' seed pqSalt m : DY.Bytes) (c' : RecvChain)
    (hspk_T : CompTrace.PQXDHStoredAt T b { kind := .signedPrekey, sk := randTerm t_sS 32 } idx_spk) :
    let sS := randTerm t_sS 32
    let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
    let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
    (((do
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
        { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr).2.val) ≤ T →
    JRkHist T (((do
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
  intro sS st c hle_end; let doneIdx := tr.length
  have htl : ∀ {α : Type} (g : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= g).run t).2.val = ((g t.length).run t).2.val := fun g t => by
    unfold DY.Libsignal.TripleRatchet.traceLength; rw [CompTrace.run_bind_snd, Traceful.run_mk]
  let tr₁ := tr.append (EvE (.BobDone b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys))
  let tr₂ := tr₁.append (TREvE (.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs)))
  let tr₃ := tr₂.append (TREvE (.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)))
  let tr₄ := tr₃.append (CEvE (.HandshakeSession (st.sessionInfo b) doneIdx))
  have hJ₄ : JRkHist T tr₄ :=
    JRkHist_append_other (JRkHist_append_other (JRkHist_append_other (JRkHist_append_other hJ)))
  let skipped := msg.counter.toNat - c.index.toNat; let childIdx := tr₄.length + skipped + 2
  let skipAct := DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
  let restAct : Unit → Traceful Nat := fun _ => do
    ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
    DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx
      { st with recv := setRecvChain st.recv c', spqr := spqr' }
  rw [htl, CompPresTRExp.run_logEvent_bind_snd] at hle_end ⊢; simp only [↓reduceIte] at hle_end ⊢
  rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, htl] at hle_end ⊢
  change (((skipAct >>= restAct).run tr₄).2.val) ≤ T at hle_end
  change JRkHist T (((skipAct >>= restAct).run tr₄).2.val)
  rw [CompInv.CompPresBob.run_logSkippedKeys_bind_snd] at hle_end ⊢
  let tr₅ := (skipAct.run tr₄).2.val
  have hle₄₅ : tr₄ ≤ tr₅ := (skipAct.run tr₄).2.property
  have hJ₅ : JRkHist T tr₅ := JRkHist_logSkippedKeys_preserves (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx skipped c.chainKey c.index tr₄ hJ₄
  let tr₆ := tr₅.append (TREvE (.Received b st.peer msg.ratchetKey msg.counter m))
  let tr₇ := tr₆.append (TREvE (.MessageKey (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx))
  have hJ₇ : JRkHist T tr₇ := JRkHist_append_other (JRkHist_append_other hJ₅)
  dsimp only [restAct] at hle_end ⊢
  rw [CompPresTRExp.run_logEvent_bind_snd] at hle_end ⊢
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore at hle_end ⊢
  rw [CompPresTRExp.run_logEvent_bind_snd] at hle_end ⊢
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk] at hle_end ⊢
  change (tr₇.append (TRStE b { st with recv := setRecvChain st.recv c', spqr := spqr' })) ≤ T at hle_end
  change JRkHist T (tr₇.append (TRStE b { st with recv := setRecvChain st.recv c', spqr := spqr' }))
  have hle₁₄ : tr₁ ≤ tr₄ :=
    Trace.le_trans _ _ _ (Trace.append_le tr₁ _)
      (Trace.le_trans _ _ _ (Trace.append_le tr₂ _) (Trace.append_le tr₃ _))
  have hle₁_end : tr₁ ≤ tr₇.append (TRStE b { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
    Trace.le_trans _ _ _ hle₁₄ (Trace.le_trans _ _ _ hle₄₅
      (Trace.le_trans _ _ _ (Trace.append_le tr₅ _)
        (Trace.le_trans _ _ _ (Trace.append_le tr₆ _) (Trace.append_le tr₇ _))))
  have hev_T : T.EventLoggedAt (PQXDHEvent.BobDone b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys) tr.length :=
    CompTrace.eventLoggedAt_mono (Trace.le_trans _ _ _ hle₁_end hle_end)
      (CompTrace.eventLoggedAt_here tr _)
  exact JRkHist_append_st b
    (.inl (.inr ⟨b, a, DiffieHellman.dhPk sB, ikA, DiffieHellman.dhPk sS, PQKem.kemPk sQ, o.map DiffieHellman.dhPk, ek, ct, keys, tr.length, t_sS, idx_spk, msg.ratchetKey, hev_T, hspk_T, rfl⟩))
    hJ₇

abbrev JRkHistLe (T tr_end : ExecTrace) : Prop :=
  tr_end ≤ T → JRkHist T tr_end

theorem JRkHist_preserves_bobStart {T tr : ExecTrace} (hle_tr_T : tr ≤ T)
    (hinv : SpqrInv tr) (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32)
    (hle_end : ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val ≤ T) (hJ : JRkHist T tr) :
    JRkHist T ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val := by
  revert hle_end
  change JRkHistLe T ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at (Inv := JRkHistLe T)
    b a kh regIdxA mh.ek mh.ct tr (fun _ => hJ)
    fun sB sS sQ o ikA _ ek ct _ keys _ hspk _ _ _ _ _ _ _ => ?_
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg; rw [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_receiveMessage_at (Inv := JRkHistLe T) mh.msg tr (fun _ => hJ) fun raw _ _ => ?_
  rcases parseTrSignalMsg raw with _ | msg; · dsimp only; rw [CompTrace.run_bind_snd, Traceful.run_failure]; exact fun _ => hJ
  dsimp only; rw [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_guardP_at (Inv := JRkHistLe T) _ tr (fun _ => hJ) fun _ => ?_
  refine CompInv.CompPresBob.bind_ensureReceiverChain_bobInitSt (Inv := JRkHistLe T)
    a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey tr (fun _ => hJ) fun _ => ?_
  let dhs := CompKeyInversion.rnd tr.length 32
  let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
  let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
  let tr₁ := tr.append (RndE 32); have hJ₁ : JRkHist T tr₁ := JRkHist_append_other hJ
  rcases consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact fun _ => hJ₁
  dsimp only; rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact fun _ => hJ₁
  dsimp only
  let tr₂ := tr₁.append (NetE key); have hJ₂ : JRkHist T tr₂ := JRkHist_append_other hJ₁
  rw [CompPresTRExp.run_sendMessage_bind_snd]
  change JRkHistLe T (((Network.receiveMessage pqIdx >>= fun pqSalt => DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed >>= fun m => _).run tr₂).2.val)
  refine CompTrace.bind_receiveMessage_at (Inv := JRkHistLe T) pqIdx tr₂ (fun _ => hJ₂) fun pqSalt _ _ =>
    CompInv.CompPresBob.bind_verifyMacAndDecrypt_at (Inv := JRkHistLe T) st msg pqSalt seed tr₂ (fun _ => hJ₂) fun m _ => ?_
  obtain ⟨t_sS, rfl, _, _, _⟩ := hinv.stOK b { kind := .signedPrekey, sk := sS } kh.spk hspk
  have hspk_T : CompTrace.PQXDHStoredAt T b { kind := .signedPrekey, sk := randTerm t_sS 32 } kh.spk :=
    CompTrace.pqxdhStoredAt_mono hle_tr_T hspk
  cases o with
  | none =>
    dsimp only [Option.map]
    exact JRkHist_bobStart_commit hJ₂ b a sB t_sS kh.spk sQ none ikA ek ct keys msg dhs spqr' seed pqSalt m c' hspk_T
  | some oSk =>
    dsimp only [Option.map]; rw [CompTrace.run_bind_snd]; unfold DY.Libsignal.PQXDH.guardTrace; rw [Traceful.run_mk]; dsimp only
    by_cases hused : (!opkUsedB tr₂ b (DiffieHellman.dhPk oSk)) = true
    · rw [ite_eq_left_iff.mpr fun h => absurd hused h]; dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd]
      exact JRkHist_bobStart_commit (JRkHist_append_other hJ₂) b a sB t_sS kh.spk sQ (some oSk) ikA ek ct keys msg dhs spqr' seed pqSalt m c' hspk_T
    · rw [ite_eq_right_iff.mpr fun h => absurd h hused]; dsimp only; exact fun _ => hJ₂

theorem jRkHist_reachable {T tr : ExecTrace} (hreach : ReachableTrace tr) (hle : tr ≤ T) :
    JRkHist T tr := by
  induction hreach with
  | Base => exact JRkHist_nil T
  | @Step tr_prev input hPre hReachPre ih =>
    have hprev_le : tr_prev ≤ T := Trace.le_trans _ _ _ ((reachability.step input).snd.run _).2.property hle
    have hJ : JRkHist T tr_prev := ih hprev_le
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
    · change DY.Bytes at inp; change JRkHist T ((Network.sendMessage inp).run _).2.val
      rw [CompPresTRExp.run_sendMessage_snd]; exact JRkHist_append_other hJ
    · change Participant at inp; change JRkHist T ((registerIdentity inp).run _).2.val; unfold registerIdentity
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ hJ fun _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, hst_snd]
      exact JRkHist_append_other (JRkHist_append_other (JRkHist_append_other (JRkHist_append_other (JRkHist_append_other hJ))))
    · rcases inp with ⟨p, skIdx⟩; change JRkHist T ((registerCorruptIdentity p skIdx).run _).2.val; unfold registerCorruptIdentity
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ hJ fun _ =>
        CompTrace.bind_receiveMessage_at skIdx _ hJ fun _ _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, hlog_snd]
      exact JRkHist_append_other (JRkHist_append_other hJ)
    · rcases inp with ⟨b, idStateIdx⟩; change JRkHist T ((genSignedPrekey b idStateIdx).run _).2.val; unfold genSignedPrekey
      refine CompPresPQXDH.bind_getKey_at b idStateIdx .identity _ hJ fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        hst_bind, CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact JRkHist_append_other (JRkHist_append_other (JRkHist_append_other (JRkHist_append_other (JRkHist_append_other (JRkHist_append_other hJ)))))
    · rcases inp with ⟨b, idStateIdx⟩; change JRkHist T ((genPQPrekey b idStateIdx).run _).2.val; unfold genPQPrekey
      refine CompPresPQXDH.bind_getKey_at b idStateIdx .identity _ hJ fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        hst_bind, CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact JRkHist_append_other (JRkHist_append_other (JRkHist_append_other (JRkHist_append_other (JRkHist_append_other (JRkHist_append_other hJ)))))
    · change Participant at inp; change JRkHist T ((genOneTimePrekey inp).run _).2.val; unfold genOneTimePrekey
      rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd, hst_bind,
        CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact JRkHist_append_other (JRkHist_append_other (JRkHist_append_other (JRkHist_append_other hJ)))
    · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩; exact JRkHist_preserves_aliceStart a b idStateIdx regIdxB bh hle hJ
    · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩; exact JRkHist_preserves_bobStart hprev_le hinv b a kh regIdxA mh pqIdx spqrMsgIdx hle hJ
    · rcases inp with ⟨me, stateIdx, coinsLen, pqIdx⟩; exact (PQRkHistAt.messageEncrypt me stateIdx coinsLen pqIdx hJ hle).1
    · rcases inp with ⟨me, stateIdx⟩; exact (PQRkHistAt.messageEncryptAbort me stateIdx hJ hle).1
    · rcases inp with ⟨me, stateIdx, msgIdx, pqIdx, spqrMsgIdx⟩; exact (PQRkHistAt.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx hJ hle).1
    · rcases inp with ⟨me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx⟩; exact (PQRkHistAt.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx hJ hle).1
    · rcases inp with ⟨me, stateIdx, k⟩; exact (PQRkHistAt.exposeKey me stateIdx k hJ hle).1
    · rcases inp with ⟨me, stateIdx⟩; exact (PQRkHistAt.exposeSpqr me stateIdx hJ hle).1
    · exact (PQRkHistAt.exposeSkipped inp hJ hle).1
    · rcases inp with ⟨p, stateIdx⟩; change JRkHist T ((compromiseIK p stateIdx).run _).2.val; unfold compromiseIK
      refine CompPresPQXDH.bind_getKey_at p stateIdx .identity _ hJ fun _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact JRkHist_append_other (JRkHist_append_other hJ)
    · rcases inp with ⟨b, stateIdx⟩; change JRkHist T ((compromiseSPK b stateIdx).run _).2.val; unfold compromiseSPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .signedPrekey _ hJ fun _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact JRkHist_append_other (JRkHist_append_other hJ)
    · rcases inp with ⟨b, stateIdx⟩; change JRkHist T ((compromisePQSPK b stateIdx).run _).2.val; unfold compromisePQSPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .pqPrekey _ hJ fun _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact JRkHist_append_other (JRkHist_append_other hJ)
    · rcases inp with ⟨b, stateIdx⟩; change JRkHist T ((compromiseOPK b stateIdx).run _).2.val; unfold compromiseOPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .oneTimePrekey _ hJ fun _ _ => ?_
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ hJ fun _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact JRkHist_append_other (JRkHist_append_other hJ)
    · change JRkHist T ((DY.Libsignal.PQXDH.breakDH).run _).2.val; unfold DY.Libsignal.PQXDH.breakDH
      rw [hlog_snd]; exact JRkHist_append_other hJ
    · change JRkHist T ((DY.Libsignal.PQXDH.breakKEM).run _).2.val; unfold DY.Libsignal.PQXDH.breakKEM
      rw [hlog_snd]; exact JRkHist_append_other hJ
    · change Nat at inp; change JRkHist T ((invertDH inp).run _).2.val; unfold invertDH
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ hJ fun _ =>
        CompTrace.bind_receiveMessage_at inp tr_prev hJ fun pk _ _ => ?_
      rcases DY.Libsignal.PQXDH.extractDhSecretKey (X25519.normalizeX25519Key pk) with _ | sk
      · dsimp only; rw [Traceful.run_failure]; exact hJ
      · dsimp only; rw [CompPresTRExp.run_sendMessage_snd]; exact JRkHist_append_other hJ
    · change Nat at inp; change JRkHist T ((invertKEM inp).run _).2.val; unfold invertKEM
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ hJ fun _ =>
        CompTrace.bind_receiveMessage_at inp tr_prev hJ fun pk _ _ => ?_
      rcases PQKem.invertKemPublicKey pk with _ | sk
      · rw [CompTrace.run_bind_snd]; erw [Traceful.run_mk]; exact hJ
      · rw [CompTrace.run_bind_snd]; erw [Traceful.run_mk]; dsimp [MonadLift.monadLift]
        rw [CompPresTRExp.run_sendMessage_snd]; exact JRkHist_append_other hJ
    · omega

/-- Every `TRState` stored on a reachable trace `T` at index `i` satisfies
`RkHistBase T st ∨ RkHistStep T i st`. -/
theorem rkHist_of_stored {T : ExecTrace} (hT : ReachableTrace T)
    {p : Participant} {st : TRState} {i : Nat} (h : TRStateStoredAt p st i T) :
    RkHistBase T st ∨ RkHistStep T i st :=
  jRkHist_reachable hT (Trace.le_refl T) p st i h

end Symbolic.Swarm.CREF.TR.G1
