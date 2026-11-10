/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces
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
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
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
# Alice Identity-Key Trace Invariant

Proves `alice_myIk_of_getLocalState`: every stored `TRState` snapshot for `r₀.alice` along any
`ModelRun r₀ ms` satisfies `st.myIk = serializedIk (setupPublic r₀ 0)`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.AliceIk

cref_open
open DY DY.Comparse DY.Libsignal DY.DiffieHellman
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding SignalMsg MessageKeys lit litByte hmac hkdfBlock1
  hkdfBlock2 hkdfBlock3 x25519LowOrder zeroSalt messageVersion maxForwardJumps u32Max
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.CREF.TR.FreshSigma (run_bind_fst run_bind_snd)

local notation "IkStEntry" => PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
local notation "IkPQStEntry" => PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState PQXDHState)
local notation "IkPQEvEntry" => DY.ProtocolEvent.ExecEntryT PQXDHEvent

private theorem proj_inj_ik {E : Type} [ExecTraceTypes.Has E] (e : E) :
    (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by
  rw [TraceEntryHas.inj_proj_eq]

def AliceTRIk (a : Participant) (ls : PersistentLocalState.LocalState TRState) : Prop :=
  ls.participant = a → ls.state.myIk = serializedIk (dhPk (randTerm 0 32))

def AlicePQIk (a : Participant) (ls : PersistentLocalState.LocalState PQXDHState) : Prop :=
  ls.participant = a → ls.state.kind = .identity → ls.state.sk = randTerm 0 32

def AliceIkEntryOk (a : Participant) (ent : ExecTrace.Entry) : Prop :=
  (∀ e : IkStEntry, TraceEntryHas.proj ent = some e → AliceTRIk a e.st) ∧
  (∀ e : IkPQStEntry, TraceEntryHas.proj ent = some e → AlicePQIk a e.st)

def TraceAliceIk (a : Participant) (tr : ExecTrace) : Prop :=
  ∀ j (hj : j < tr.length), AliceIkEntryOk a (tr.at j hj)

theorem traceAliceIk_nil (a : Participant) : TraceAliceIk a (DY.Trace.nil : ExecTrace) :=
  fun _ hj => by simp [Symbolic.DYBridge.DY.Trace.length_eq_1] at hj

theorem traceAliceIk_append {a : Participant} {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hent : AliceIkEntryOk a (TraceEntryHas.inj e)) (htr : TraceAliceIk a tr) :
    TraceAliceIk a (tr.append e) := by
  have hle : tr ≤ tr.append e := DY.Trace.append_le tr e
  intro j hj
  by_cases hlt : j < tr.length
  · rw [← DY.Trace.at_le tr (tr.append e) j hlt hle]; exact htr j hlt
  · have heq : j = tr.length := by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hj; omega
    subst heq; simpa [Symbolic.DYBridge.DY.Trace.append_eq_1, DY.Trace.snoc, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.nil_length_not_lt, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] using hent

def TracefulAliceIk (a : Participant) {α : Type} (Q : α → Prop) (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, TraceAliceIk a tr →
    TraceAliceIk a (x.run tr).2.val ∧ ∀ v : α, (x.run tr).1 = some v → Q v

theorem TracefulAliceIk.pure {a : Participant} {α : Type} {Q : α → Prop} {v : α} (hv : Q v) :
    TracefulAliceIk a Q (Pure.pure v) := by
  intro _ htr
  simp only [DY.Traceful.run_pure]
  exact ⟨htr, fun _ hb => by cases hb; exact hv⟩

theorem TracefulAliceIk.failure {a : Participant} {α : Type} {Q : α → Prop} :
    TracefulAliceIk a Q (Alternative.failure : Traceful α) := by
  intro _ htr
  simp only [DY.Traceful.run_failure]
  exact ⟨htr, fun _ hb => by cases hb⟩

theorem TracefulAliceIk.bind {a : Participant} {α β : Type} {Q₁ : α → Prop} {Q₂ : β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulAliceIk a Q₁ x) (hf : ∀ v : α, Q₁ v → TracefulAliceIk a Q₂ (f v)) :
    TracefulAliceIk a Q₂ (x >>= f) := by
  intro tr htr; rw [FreshSigma.run_bind_snd, FreshSigma.run_bind_fst]; have h1 := hx tr htr
  cases hres : (x.run tr).1 with
  | none => exact ⟨h1.1, fun _ hb => by cases hb⟩
  | some v => exact hf v (h1.2 v hres) _ h1.1

theorem tracefulAliceIk_run_snd {a : Participant} {α : Type} {Q : α → Prop} {x : Traceful α}
    (hx : TracefulAliceIk a Q x) {tr : ExecTrace} (htr : TraceAliceIk a tr) :
    TraceAliceIk a ((x >>= fun _ => Pure.pure ()).run tr).2.val :=
  (TracefulAliceIk.bind hx (fun _ _ => TracefulAliceIk.pure (Q := fun _ => True) trivial) tr htr).1

theorem TracefulAliceIk.guardP {a : Participant} (p : Prop) [Decidable p] :
    TracefulAliceIk a (fun _ => p) (_root_.guard p) := by
  intro tr htr; unfold _root_.guard; split
  · next hp => exact TracefulAliceIk.pure hp tr htr
  · exact TracefulAliceIk.failure tr htr

theorem tracefulAliceIk_guardTrace {a : Participant} (p : ExecTrace → Bool) :
    TracefulAliceIk a (fun _ => True) (guardTrace p) := by
  intro _ htr; unfold guardTrace; erw [DY.Traceful.run_mk]; exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulAliceIk_traceLength {a : Participant} :
    TracefulAliceIk a (fun _ => True) traceLength := by
  intro _ htr; unfold traceLength; erw [DY.Traceful.run_mk]; exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulAliceIk.getEntry_any {a : Participant} {E : Type} [ExecTraceTypes.Has E] (j : Nat) :
    TracefulAliceIk a (fun (_ : E) => True) (getEntry j : Traceful E) := by
  intro tr htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1]
  erw [DY.Traceful.run_mk]
  dsimp only
  cases (tr.at? j : Option E) <;> exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulAliceIk.getEntry_st (a : Participant) (j : Nat) :
    TracefulAliceIk a (fun (e : IkStEntry) => AliceTRIk a e.st) (getEntry j) := by
  intro tr htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1]
  erw [DY.Traceful.run_mk]
  dsimp only
  rcases h : (tr.at? j : Option IkStEntry) with _ | e
  · exact ⟨htr, fun _ hb => by cases hb⟩
  · refine ⟨htr, fun _ hb => ?_⟩
    cases hb
    unfold DY.Trace.at? at h; split at h
    · next hj => exact (htr j hj).1 e h
    · cases h

theorem TracefulAliceIk.getEntry_pq (a : Participant) (j : Nat) :
    TracefulAliceIk a (fun (e : IkPQStEntry) => AlicePQIk a e.st) (getEntry j) := by
  intro tr htr
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1]
  erw [DY.Traceful.run_mk]
  dsimp only
  rcases h : (tr.at? j : Option IkPQStEntry) with _ | e
  · exact ⟨htr, fun _ hb => by cases hb⟩
  · refine ⟨htr, fun _ hb => ?_⟩
    cases hb
    unfold DY.Trace.at? at h; split at h
    · next hj => exact (htr j hj).2 e h
    · cases h

theorem TracefulAliceIk.receiveMessage {a : Participant} (j : Nat) :
    TracefulAliceIk a (fun _ => True) (Network.receiveMessage j) := by
  rw [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact TracefulAliceIk.bind (TracefulAliceIk.getEntry_any j) fun _ _ => TracefulAliceIk.pure trivial

theorem tracefulAliceIk_receiveSignalMsg {a : Participant} (msgIdx : Nat) :
    TracefulAliceIk a (fun _ => True) (receiveSignalMsg msgIdx) := by
  unfold receiveSignalMsg; refine TracefulAliceIk.bind (TracefulAliceIk.receiveMessage msgIdx) fun _ _ => ?_
  split
  · exact TracefulAliceIk.bind (TracefulAliceIk.guardP _) fun _ _ => TracefulAliceIk.pure trivial
  · exact TracefulAliceIk.failure

theorem TracefulAliceIk.getLocalState (a p : Participant) (j : Nat) :
    TracefulAliceIk a (fun (st : TRState) => p = a → st.myIk = serializedIk (dhPk (randTerm 0 32)))
      (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact TracefulAliceIk.bind (TracefulAliceIk.bind (TracefulAliceIk.getEntry_st a j) fun _ he =>
    TracefulAliceIk.pure (Q := fun (ls : PersistentLocalState.LocalState TRState) => AliceTRIk a ls) he)
    fun ls hls => TracefulAliceIk.bind (TracefulAliceIk.guardP (ls.participant = p)) fun _ hp =>
      TracefulAliceIk.pure fun hpa => hls (hp.trans hpa)

theorem TracefulAliceIk.getLocalStatePQ (a p : Participant) (j : Nat) :
    TracefulAliceIk a (fun (st : PQXDHState) => p = a → st.kind = .identity → st.sk = randTerm 0 32)
      (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact TracefulAliceIk.bind (TracefulAliceIk.bind (TracefulAliceIk.getEntry_pq a j) fun _ he =>
    TracefulAliceIk.pure (Q := fun (ls : PersistentLocalState.LocalState PQXDHState) => AlicePQIk a ls) he)
    fun ls hls => TracefulAliceIk.bind (TracefulAliceIk.guardP (ls.participant = p)) fun _ hp =>
      TracefulAliceIk.pure fun hpa hk => hls (hp.trans hpa) hk

theorem TracefulAliceIk.getKey (a p : Participant) (j : Nat) (kind : KeyKind) :
    TracefulAliceIk a (fun (sk : DY.Bytes) => p = a → kind = .identity → sk = randTerm 0 32) (getKey p j kind) :=
  TracefulAliceIk.bind (TracefulAliceIk.getLocalStatePQ a p j) fun st hst =>
    TracefulAliceIk.bind (TracefulAliceIk.guardP (st.kind = kind)) fun _ hk =>
      TracefulAliceIk.pure fun hpa hkind => hst hpa (hk.trans hkind)

theorem TracefulAliceIk.lookupIdentity {a : Participant} (p : Participant) (j : Nat) :
    TracefulAliceIk a (fun (_ : DY.Bytes × DY.Bytes) => True) (lookupIdentity p j) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine TracefulAliceIk.bind (TracefulAliceIk.getEntry_any (E := IkPQEvEntry) j) fun _ _ => ?_
  split
  · exact TracefulAliceIk.bind (TracefulAliceIk.guardP _) fun _ _ => TracefulAliceIk.pure trivial
  · exact TracefulAliceIk.failure

theorem TracefulAliceIk.genRand {a : Participant} (n : Nat) :
    TracefulAliceIk a (fun _ => True) (DY.Random.genRand n) := by
  intro _ htr
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  erw [DY.Traceful.run_mk]
  dsimp only
  erw [DY.Traceful.run_pure]
  exact ⟨traceAliceIk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩

theorem TracefulAliceIk.sendMessage {a : Participant} (msg : DY.Bytes) :
    TracefulAliceIk a (fun _ => True) (Network.sendMessage msg) := by
  intro _ htr
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  erw [DY.Traceful.run_mk]
  exact ⟨traceAliceIk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩

theorem TracefulAliceIk.logEvent {a : Participant} (ev : TREvent) :
    TracefulAliceIk a (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  erw [DY.Traceful.run_mk]
  dsimp only
  erw [DY.Traceful.run_pure]
  exact ⟨traceAliceIk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩

theorem TracefulAliceIk.logEventPQ {a : Participant} (ev : PQXDHEvent) :
    TracefulAliceIk a (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  erw [DY.Traceful.run_mk]
  dsimp only
  erw [DY.Traceful.run_pure]
  exact ⟨traceAliceIk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩

theorem TracefulAliceIk.logEventC {a : Participant} (ev : DY.Libsignal.Composed.ComposedEvent) :
    TracefulAliceIk a (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  intro _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  erw [DY.Traceful.run_mk]
  dsimp only
  erw [DY.Traceful.run_pure]
  exact ⟨traceAliceIk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩

theorem TracefulAliceIk.storeLocalState {a : Participant} (p : Participant) {st : TRState}
    (hst : p = a → st.myIk = serializedIk (dhPk (randTerm 0 32))) :
    TracefulAliceIk a (fun _ => True) (PersistentLocalState.storeLocalState p st) := by
  intro tr htr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  erw [DY.Traceful.run_mk]
  refine ⟨traceAliceIk_append ⟨?_, fun _ h => (by cases h)⟩ htr, fun _ _ => trivial⟩
  intro e h; rw [proj_inj_ik] at h; injection h with h; subst h; exact hst

theorem TracefulAliceIk.storeLocalStatePQ {a : Participant} (p : Participant) {st : PQXDHState}
    (hst : p = a → st.kind = .identity → st.sk = randTerm 0 32) :
    TracefulAliceIk a (fun _ => True) (PersistentLocalState.storeLocalState p st) := by
  intro tr htr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  erw [DY.Traceful.run_mk]
  refine ⟨traceAliceIk_append ⟨fun _ h => (by cases h), ?_⟩ htr, fun _ _ => trivial⟩
  intro e h; rw [proj_inj_ik] at h; injection h with h; subst h; exact hst

theorem tracefulAliceIk_guardOnTrace {a : Participant} (p : ExecTrace → Bool) :
    TracefulAliceIk a (fun _ => True) (DY.Libsignal.PQXDH.guardTrace p) := by
  intro _ htr; unfold DY.Libsignal.PQXDH.guardTrace; erw [DY.Traceful.run_mk]; exact ⟨htr, fun _ _ => trivial⟩

private theorem tracefulAliceIk_pqGuardOnTrace {a : Participant} (p : ExecTrace → Bool) :
    TracefulAliceIk a (fun _ => True) (DY.Libsignal.PQXDH.guardTrace p) := by
  intro _ htr; unfold DY.Libsignal.PQXDH.guardTrace; erw [DY.Traceful.run_mk]; exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulAliceIk_logMessageKeyAndStore {a : Participant} (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) {st : TRState}
    (hst : me = a → st.myIk = serializedIk (dhPk (randTerm 0 32))) :
    TracefulAliceIk a (fun _ => True) (logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) :=
  TracefulAliceIk.bind (TracefulAliceIk.logEvent _) fun _ _ => TracefulAliceIk.storeLocalState me hst

theorem tracefulAliceIk_logSkippedKeys {a : Participant} (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    TracefulAliceIk a (fun _ => True) (logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => unfold logSkippedKeys; exact TracefulAliceIk.pure trivial
  | succ k ih => unfold logSkippedKeys; exact TracefulAliceIk.bind (TracefulAliceIk.logEvent _) fun _ _ => ih (kdfCk ck).1 (n + 1)

theorem tracefulAliceIk_verifyMacAndDecrypt {a : Participant} (st : TRState) (msg : TRSignalMsg) (pqSalt seed : DY.Bytes) :
    TracefulAliceIk a (fun _ => True) (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold verifyMacAndDecrypt
  refine TracefulAliceIk.bind (TracefulAliceIk.guardP _) fun _ _ tr htr => ?_
  cases DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg.ciphertext
  · dsimp only [liftM, monadLift, MonadLift.monadLift]; erw [DY.Traceful.run_mk]; exact ⟨htr, fun _ _ => trivial⟩
  · dsimp only [liftM, monadLift, MonadLift.monadLift]; erw [DY.Traceful.run_mk]; exact ⟨htr, fun _ _ => trivial⟩

theorem tracefulAliceIk_ensureReceiverChain {a p : Participant} {st : TRState} (pk : DY.Bytes)
    (hst : p = a → st.myIk = serializedIk (dhPk (randTerm 0 32))) :
    TracefulAliceIk a (fun (res : TRState × RecvChain × Bool) => p = a → res.1.myIk = serializedIk (dhPk (randTerm 0 32)))
      (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor, DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]; split
  · exact TracefulAliceIk.pure hst
  · refine TracefulAliceIk.bind (Q₁ := fun (x : TRState × RecvChain) => p = a → x.1.myIk = serializedIk (dhPk (randTerm 0 32))) ?_
      fun ⟨_, _⟩ hst' => TracefulAliceIk.pure hst'
    exact TracefulAliceIk.bind (TracefulAliceIk.guardP _) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.genRand 32) fun _ _ => TracefulAliceIk.pure hst
  · exact TracefulAliceIk.failure

theorem tracefulAliceIk_messageEncrypt {a : Participant} (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    TracefulAliceIk a (fun _ => True) (TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx) :=
  TracefulAliceIk.bind (TracefulAliceIk.getLocalState a me stateIdx) fun _ hst =>
    TracefulAliceIk.bind (TracefulAliceIk.guardP _) fun _ _ =>
    TracefulAliceIk.bind (TracefulAliceIk.genRand 32) fun _ _ =>
    TracefulAliceIk.bind (TracefulAliceIk.genRand coinsLen) fun _ _ =>
    TracefulAliceIk.bind (TracefulAliceIk.sendMessage _) fun _ _ =>
    TracefulAliceIk.bind (TracefulAliceIk.receiveMessage pqIdx) fun _ _ =>
    TracefulAliceIk.bind (TracefulAliceIk.logEvent _) fun _ _ =>
    TracefulAliceIk.bind (tracefulAliceIk_logMessageKeyAndStore me _ .sender _ _ _ _ _ hst) fun _ _ =>
      TracefulAliceIk.sendMessage _

theorem tracefulAliceIk_messageDecrypt {a : Participant} (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    TracefulAliceIk a (fun _ => True) (messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine TracefulAliceIk.bind (TracefulAliceIk.getLocalState a me stateIdx) fun _ hst₀ =>
    TracefulAliceIk.bind (tracefulAliceIk_receiveSignalMsg msgIdx) fun msg _ =>
    TracefulAliceIk.bind (tracefulAliceIk_ensureReceiverChain msg.ratchetKey hst₀) fun res hst => ?_
  rcases res with ⟨st, c, _⟩; dsimp only; split
  · next seed c' _ =>
    split
    · next spqr' key _ =>
      refine TracefulAliceIk.bind (TracefulAliceIk.sendMessage key) fun _ _ =>
        TracefulAliceIk.bind (TracefulAliceIk.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulAliceIk.bind (tracefulAliceIk_verifyMacAndDecrypt st msg pqSalt seed) fun m _ => ?_
      have hrest : TracefulAliceIk a (fun _ => True)
          (do logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
                (msg.counter.toNat - c.index.toNat)
              DY.ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
              logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx stateIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
        TracefulAliceIk.bind (tracefulAliceIk_logSkippedKeys _ _ _ _ _ _ _) fun _ _ =>
          TracefulAliceIk.bind (TracefulAliceIk.logEvent _) fun _ _ =>
            tracefulAliceIk_logMessageKeyAndStore me _ .receiver _ _ _ _ _ hst
      split
      · exact TracefulAliceIk.bind (TracefulAliceIk.logEvent _) fun _ _ =>
          TracefulAliceIk.bind (TracefulAliceIk.logEvent _) fun _ _ => hrest
      · exact hrest
    · exact TracefulAliceIk.failure
  · exact TracefulAliceIk.failure

theorem tracefulAliceIk_messageDecryptSkipped {a : Participant} (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulAliceIk a (fun _ => True)
      (messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold messageDecryptSkipped
  refine TracefulAliceIk.bind (TracefulAliceIk.getLocalState a me stateIdx) fun st hst =>
    TracefulAliceIk.bind (tracefulAliceIk_receiveSignalMsg msgIdx) fun msg _ =>
    TracefulAliceIk.bind (TracefulAliceIk.getEntry_any skippedKeyEventIdx) fun _ _ => ?_
  split
  · refine TracefulAliceIk.bind (TracefulAliceIk.guardP _) fun _ _ =>
      TracefulAliceIk.bind (tracefulAliceIk_guardTrace _) fun _ _ => ?_
    split
    · next spqr' key _ =>
      exact TracefulAliceIk.bind (TracefulAliceIk.sendMessage key) fun _ _ =>
        TracefulAliceIk.bind (TracefulAliceIk.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulAliceIk.bind (tracefulAliceIk_verifyMacAndDecrypt st msg pqSalt _) fun _ _ =>
        TracefulAliceIk.bind (TracefulAliceIk.logEvent _) fun _ _ =>
        TracefulAliceIk.bind (TracefulAliceIk.logEvent _) fun _ _ =>
        tracefulAliceIk_logMessageKeyAndStore me _ .receiver _ _ _ _ _ hst
    · exact TracefulAliceIk.failure
  · exact TracefulAliceIk.failure

theorem tracefulAliceIk_aliceStart {a₀ : Participant} (a b : Participant)
    (idStateIdx regIdxB : Nat) (h : BundleHandles) :
    TracefulAliceIk a₀ (fun _ => True) (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  have hhs : TracefulAliceIk a₀
      (fun (o : AliceHandshakeOut) => a = a₀ → o.ikA = dhPk (randTerm 0 32))
      (aliceHandshake a b idStateIdx regIdxB h) := by
    unfold aliceHandshake
    apply TracefulAliceIk.bind (TracefulAliceIk.getKey a₀ a idStateIdx _); intro ikA hikA
    apply TracefulAliceIk.bind (TracefulAliceIk.lookupIdentity b regIdxB); intro ⟨ikB, vkB⟩ _; dsimp only
    apply TracefulAliceIk.bind (TracefulAliceIk.receiveMessage h.spk); intro spk _
    apply TracefulAliceIk.bind (TracefulAliceIk.receiveMessage h.spkSig); intro _ _
    apply TracefulAliceIk.bind (TracefulAliceIk.receiveMessage h.pqpk); intro pqpk _
    apply TracefulAliceIk.bind (TracefulAliceIk.receiveMessage h.pqpkSig); intro _ _
    apply TracefulAliceIk.bind (TracefulAliceIk.guardP _); intro _ _
    apply TracefulAliceIk.bind (TracefulAliceIk.guardP _); intro _ _; split
    all_goals first | (apply TracefulAliceIk.bind (TracefulAliceIk.receiveMessage _); intro _ _) | skip
    all_goals
      apply TracefulAliceIk.bind (TracefulAliceIk.pure (Q := fun _ => True) trivial); intro opk _
      apply TracefulAliceIk.bind (TracefulAliceIk.genRand 32); intro ek _
      apply TracefulAliceIk.bind (TracefulAliceIk.guardP _); intro _ _
      apply TracefulAliceIk.bind (TracefulAliceIk.guardP _); intro _ _
      apply TracefulAliceIk.bind (TracefulAliceIk.genRand 32); intro entropy _
      rcases aliceAgreement ikA ek ikB spk pqpk opk entropy with ⟨ct, keys⟩; try dsimp only
      exact TracefulAliceIk.pure fun ha => congrArg dhPk (hikA ha rfl)
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine TracefulAliceIk.bind hhs fun o ho =>
    TracefulAliceIk.bind (TracefulAliceIk.genRand 32) fun dhsA _ => ?_
  rcases createChain o.keys.rk o.spk dhsA with ⟨rkA, cksA⟩; dsimp only
  exact TracefulAliceIk.bind (TracefulAliceIk.sendMessage _) fun _ _ =>
    TracefulAliceIk.bind (TracefulAliceIk.sendMessage _) fun _ _ =>
    TracefulAliceIk.bind tracefulAliceIk_traceLength fun _ _ =>
    TracefulAliceIk.bind (TracefulAliceIk.logEventPQ _) fun _ _ =>
    TracefulAliceIk.bind (TracefulAliceIk.logEvent _) fun _ _ =>
    TracefulAliceIk.bind (TracefulAliceIk.logEventC _) fun _ _ =>
    TracefulAliceIk.storeLocalState a (fun ha => congrArg serializedIk (ho ha))

theorem tracefulAliceIk_bobStart {a₀ : Participant} (b a : Participant) (kh : BobKeyHandles)
    (regIdxA : Nat) (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulAliceIk a₀ (fun _ => True)
      (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  have hhs : TracefulAliceIk a₀
      (fun (o : BobHandshakeOut) => b = a₀ → o.ikB = dhPk (randTerm 0 32))
      (bobHandshake b a kh regIdxA mh.ek mh.ct) := by
    unfold bobHandshake
    apply TracefulAliceIk.bind (TracefulAliceIk.getKey a₀ b kh.ik _); intro ikB hikB
    apply TracefulAliceIk.bind (TracefulAliceIk.getKey a₀ b kh.spk _); intro _ _
    apply TracefulAliceIk.bind (TracefulAliceIk.getKey a₀ b kh.pqspk _); intro _ _
    dsimp only; split
    all_goals first | (apply TracefulAliceIk.bind (TracefulAliceIk.getKey a₀ b _ _); intro _ _) | skip
    all_goals
      apply TracefulAliceIk.bind (TracefulAliceIk.pure (Q := fun _ => True) trivial); intro _ _
      apply TracefulAliceIk.bind (TracefulAliceIk.lookupIdentity a regIdxA); intro ⟨ikA, vkA⟩ _; dsimp only
      apply TracefulAliceIk.bind (TracefulAliceIk.receiveMessage mh.ek); intro _ _
      apply TracefulAliceIk.bind (TracefulAliceIk.receiveMessage mh.ct); intro _ _
      apply TracefulAliceIk.bind (TracefulAliceIk.guardP _); intro _ _; split
      · exact TracefulAliceIk.pure fun hb => congrArg dhPk (hikB hb rfl)
      · exact TracefulAliceIk.failure
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine TracefulAliceIk.bind hhs fun o ho =>
    TracefulAliceIk.bind (tracefulAliceIk_receiveSignalMsg mh.msg) fun msg _ =>
    TracefulAliceIk.bind
      (tracefulAliceIk_ensureReceiverChain (p := b) msg.ratchetKey (fun hb => congrArg serializedIk (ho hb)))
      fun res hst => ?_
  rcases res with ⟨st, c, _⟩; dsimp only at hst ⊢; split
  · next seed c' _ =>
    split
    · next spqr' key _ =>
      refine TracefulAliceIk.bind (TracefulAliceIk.sendMessage key) fun _ _ =>
        TracefulAliceIk.bind (TracefulAliceIk.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulAliceIk.bind (tracefulAliceIk_verifyMacAndDecrypt st msg pqSalt seed) fun _ _ => ?_
      split
      all_goals first |
        (refine TracefulAliceIk.bind (tracefulAliceIk_guardOnTrace _) fun _ _ =>
          TracefulAliceIk.bind (TracefulAliceIk.logEventPQ _) fun _ _ => ?_) | skip
      all_goals refine TracefulAliceIk.bind tracefulAliceIk_traceLength fun _ _ =>
        TracefulAliceIk.bind (TracefulAliceIk.logEventPQ _) fun _ _ => ?_
      all_goals split
      all_goals first |
        (refine TracefulAliceIk.bind (TracefulAliceIk.logEvent _) fun _ _ =>
          TracefulAliceIk.bind (TracefulAliceIk.logEvent _) fun _ _ => ?_) | skip
      all_goals exact TracefulAliceIk.bind (TracefulAliceIk.logEventC _) fun _ _ =>
        TracefulAliceIk.bind tracefulAliceIk_traceLength fun _ _ =>
        TracefulAliceIk.bind (tracefulAliceIk_logSkippedKeys _ _ _ _ _ _ _) fun _ _ =>
        TracefulAliceIk.bind (TracefulAliceIk.logEvent _) fun _ _ =>
        tracefulAliceIk_logMessageKeyAndStore b _ .receiver _ _ _ _ _ hst
    · exact TracefulAliceIk.failure
  · exact TracefulAliceIk.failure

private theorem traceAliceIk_registerIdentity_at {a : Participant} (p : Participant) {tr : ExecTrace}
    (htr : TraceAliceIk a tr) (hp : p = a → tr.length = 0) :
    TraceAliceIk a ((registerIdentity p).run tr).2.val := by
  unfold registerIdentity
  have hreq : (DY.Libsignal.PQXDH.guardTrace fun tr => !isRegisteredB tr p).run tr =
      (if (!isRegisteredB tr p) = true then some () else none, ⟨tr, DY.Trace.le_refl tr⟩) := by
    unfold DY.Libsignal.PQXDH.guardTrace; erw [DY.Traceful.run_mk]
  rw [FreshSigma.run_bind_snd, hreq]
  dsimp only
  split
  · let ik := randTerm tr.length 32
    have hstep : TracefulAliceIk a (fun _ => True)
        (do DY.ProtocolEvent.logEvent (PQXDHEvent.IdentityRegistered p (dhPk ik) (DY.Signature.vk ik) true)
            let _ ← Network.sendMessage (dhPk ik); let _ ← Network.sendMessage (DY.Signature.vk ik)
            PersistentLocalState.storeLocalState p ({ kind := .identity, sk := ik } : PQXDHState)) :=
      TracefulAliceIk.bind (TracefulAliceIk.logEventPQ _) fun _ _ =>
        TracefulAliceIk.bind (TracefulAliceIk.sendMessage _) fun _ _ =>
        TracefulAliceIk.bind (TracefulAliceIk.sendMessage _) fun _ _ =>
        TracefulAliceIk.storeLocalStatePQ p (fun hpa _ => by dsimp only [ik]; rw [hp hpa])
    have hgen : (DY.Random.genRand 32).run tr =
        (some ik, ⟨tr.append (RndE 32), DY.Trace.append_le tr _⟩) := by
      simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, DY.Traceful.run_bind,
        Symbolic.DYBridge.DY.appendEntry_eq_1]
      erw [DY.Traceful.run_mk]
      dsimp only
      erw [DY.Traceful.run_pure]
      rfl
    rw [FreshSigma.run_bind_snd, hgen]
    exact (hstep (tr.append (RndE 32))
      (traceAliceIk_append ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩ htr)).1
  · exact htr

private theorem traceAliceIk_setupTrace (r₀ : ProtocolSetup) (hNe : r₀.alice ≠ r₀.bob) :
    TraceAliceIk r₀.alice (setupTrace r₀) := by
  have htr1 : TraceAliceIk r₀.alice (TR.setupTr1 r₀.alice) := by
    have h := traceAliceIk_registerIdentity_at r₀.alice (traceAliceIk_nil r₀.alice)
      (fun _ => Symbolic.DYBridge.DY.Trace.length_eq_1)
    rwa [(runs_registerIdentity_a r₀.alice).2] at h
  have htr2 : TraceAliceIk r₀.alice (TR.setupTr2 r₀.alice r₀.bob) := by
    have h := traceAliceIk_registerIdentity_at r₀.bob htr1 (fun hba => False.elim (hNe hba.symm))
    rwa [(runs_registerIdentity_b hNe).2] at h
  have h3 : TracefulAliceIk r₀.alice (fun _ => True) (genSignedPrekey r₀.bob 9) := by
    unfold genSignedPrekey
    refine TracefulAliceIk.bind (TracefulAliceIk.getKey r₀.alice r₀.bob 9 _) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.genRand 32) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.genRand 64) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.logEventPQ _) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.storeLocalStatePQ r₀.bob fun hba _ => False.elim (hNe hba.symm)) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.sendMessage _) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.sendMessage _) fun _ _ =>
      TracefulAliceIk.pure (Q := fun _ => True) trivial
  have htr3 : TraceAliceIk r₀.alice (TR.setupTr3 r₀.alice r₀.bob) := by
    have h := (h3 (TR.setupTr2 r₀.alice r₀.bob) htr2).1; rwa [(runs_genSignedPrekey r₀.alice r₀.bob).2] at h
  have h4 : TracefulAliceIk r₀.alice (fun _ => True) (genPQPrekey r₀.bob 9) := by
    unfold genPQPrekey
    refine TracefulAliceIk.bind (TracefulAliceIk.getKey r₀.alice r₀.bob 9 _) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.genRand 64) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.genRand 64) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.logEventPQ _) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.storeLocalStatePQ r₀.bob fun hba _ => False.elim (hNe hba.symm)) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.sendMessage _) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.sendMessage _) fun _ _ =>
      TracefulAliceIk.pure (Q := fun _ => True) trivial
  have htr4 : TraceAliceIk r₀.alice (TR.setupTr4 r₀.alice r₀.bob) := by
    have h := (h4 (TR.setupTr3 r₀.alice r₀.bob) htr3).1; rwa [(runs_genPQPrekey r₀.alice r₀.bob).2] at h
  have h5 : TracefulAliceIk r₀.alice (fun _ => True) (genOneTimePrekey r₀.bob) := by
    unfold genOneTimePrekey
    refine TracefulAliceIk.bind (TracefulAliceIk.genRand 32) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.logEventPQ _) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.storeLocalStatePQ r₀.bob fun hba _ => False.elim (hNe hba.symm)) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.sendMessage _) fun _ _ =>
      TracefulAliceIk.pure (Q := fun _ => True) trivial
  have htr5 : TraceAliceIk r₀.alice (TR.setupTr5 r₀.alice r₀.bob) := by
    have h := (h5 (TR.setupTr4 r₀.alice r₀.bob) htr4).1; rwa [(runs_genOneTimePrekey r₀.alice r₀.bob).2] at h
  rw [setupTrace_eq r₀ hNe]
  cases r₀.withOpk
  · exact htr4
  · exact htr5

theorem traceAliceIk_move_next {a₀ : Participant} {tr : ExecTrace} {m : Move} (hm : m.isSetup = false)
    (htr : TraceAliceIk a₀ tr) : TraceAliceIk a₀ (m.next tr) := by
  unfold Move.next Move.act; cases m with
  | setup a b withOpk => simp [Move.isSetup] at hm
  | aliceStart a b idStateIdx regIdxB h _ =>
    exact tracefulAliceIk_run_snd (tracefulAliceIk_aliceStart a b idStateIdx regIdxB h) htr
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ =>
    exact tracefulAliceIk_run_snd (tracefulAliceIk_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) htr
  | encrypt me stateIdx coinsLen pqIdx _ =>
    exact tracefulAliceIk_run_snd (tracefulAliceIk_messageEncrypt me stateIdx coinsLen pqIdx) htr
  | encryptAbort me stateIdx =>
    exact tracefulAliceIk_run_snd (TracefulAliceIk.bind (TracefulAliceIk.getLocalState a₀ me stateIdx) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.genRand 32) fun _ _ => TracefulAliceIk.failure (Q := fun _ => True)) htr
  | encryptFail me stateIdx coinsLen =>
    dsimp only
    exact (TracefulAliceIk.bind tracefulAliceIk_traceLength (fun n _ =>
      TracefulAliceIk.bind (tracefulAliceIk_messageEncrypt me stateIdx coinsLen (n + 3)) fun _ _ =>
        TracefulAliceIk.pure (Q := fun _ => True) trivial) tr htr).1
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ =>
    exact tracefulAliceIk_run_snd (tracefulAliceIk_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) htr
  | decryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ =>
    exact tracefulAliceIk_run_snd
      (tracefulAliceIk_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) htr
  | reject _ =>
    dsimp only
    rw [DY.Traceful.run_pure]
    exact htr
  | compromiseIK p stateIdx | compromiseSPK p stateIdx | compromisePQSPK p stateIdx =>
    exact tracefulAliceIk_run_snd (TracefulAliceIk.bind (TracefulAliceIk.getKey a₀ p stateIdx _) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.logEventPQ _) fun _ _ => TracefulAliceIk.sendMessage _) htr
  | compromiseOPK p stateIdx =>
    exact tracefulAliceIk_run_snd (TracefulAliceIk.bind (TracefulAliceIk.getKey a₀ p stateIdx _) fun _ _ =>
      TracefulAliceIk.bind (tracefulAliceIk_pqGuardOnTrace _) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.logEventPQ _) fun _ _ => TracefulAliceIk.sendMessage _) htr
  | exposeKey me stateIdx k =>
    refine tracefulAliceIk_run_snd (Q := fun _ => True) ?_ htr
    unfold exposeKey; refine TracefulAliceIk.bind (TracefulAliceIk.getLocalState a₀ me stateIdx) fun _ _ => ?_
    cases k with
    | rk | dhs | cks =>
      exact TracefulAliceIk.bind (TracefulAliceIk.logEvent _) fun _ _ => TracefulAliceIk.sendMessage _
    | ckr _ =>
      dsimp only; split
      · exact TracefulAliceIk.bind (TracefulAliceIk.logEvent _) fun _ _ => TracefulAliceIk.sendMessage _
      · exact TracefulAliceIk.failure (Q := fun _ => True)
  | exposeSpqr me stateIdx =>
    exact tracefulAliceIk_run_snd (TracefulAliceIk.bind (TracefulAliceIk.getLocalState a₀ me stateIdx) fun _ _ =>
      TracefulAliceIk.bind (TracefulAliceIk.logEvent _) fun _ _ => TracefulAliceIk.sendMessage _) htr
  | exposeSkipped skippedKeyEventIdx =>
    refine tracefulAliceIk_run_snd (Q := fun _ => True) ?_ htr; unfold exposeSkipped
    refine TracefulAliceIk.bind (TracefulAliceIk.getEntry_any skippedKeyEventIdx) fun _ _ => ?_; split
    · exact TracefulAliceIk.bind (tracefulAliceIk_guardTrace _) fun _ _ =>
        TracefulAliceIk.bind (TracefulAliceIk.logEvent _) fun _ _ => TracefulAliceIk.sendMessage _
    · exact TracefulAliceIk.failure (Q := fun _ => True)
  | attackerSend msg => exact tracefulAliceIk_run_snd (TracefulAliceIk.sendMessage msg) htr
  | brkDH =>
    dsimp only [breakDH]
    exact (TracefulAliceIk.logEventPQ .BrokenDH tr htr).1
  | brkKEM =>
    dsimp only [breakKEM]
    exact (TracefulAliceIk.logEventPQ .BrokenKEM tr htr).1

theorem traceAliceIk_runMoves {a₀ : Participant} :
    ∀ (L : List Move) (tr : ExecTrace), (∀ m ∈ L, m.isSetup = false) →
      TraceAliceIk a₀ tr → TraceAliceIk a₀ (runMoves L tr).1
  | [], _, _, htr => htr
  | m :: ms, tr, hL, htr =>
    traceAliceIk_runMoves ms (m.next tr) (fun m' hm' => hL m' (List.mem_cons_of_mem m hm'))
      (traceAliceIk_move_next (hL m List.mem_cons_self) htr)

theorem alice_myIk_of_getLocalState {r₀ : ProtocolSetup} (hNe : r₀.alice ≠ r₀.bob) {ms : List Move}
    {stateIdx : Nat} {st : TRState} (hrun : ModelRun r₀ ms)
    (hst : ((PersistentLocalState.getLocalState r₀.alice stateIdx : Traceful TRState).run (runTraceMoves r₀ ms)).1 = some st) :
    st.myIk = serializedIk (setupPublic r₀ 0) := by
  have htr_ik : TraceAliceIk r₀.alice (runTraceMoves r₀ ms) := by
    rw [runTraceMoves, runMoves, setupMove_next_nil]
    exact traceAliceIk_runMoves ms (setupTrace r₀) hrun.2.1 (traceAliceIk_setupTrace r₀ hNe)
  have hik := (TracefulAliceIk.getLocalState r₀.alice r₀.alice stateIdx (runTraceMoves r₀ ms) htr_ik).2 st hst rfl
  rwa [(setupPublic_eq r₀ hNe).1, (setupSecret_eq r₀ hNe).1]

end Symbolic.Swarm.CREF.AliceIk
