/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvFreshStepBobSid
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.Lemmas
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Swarm.CREF.Prelude
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
# Provenance of Non-Initiator `HandshakeSession` Descriptors

Proves `bobSessionSidInv_of_reachable` (`BobSidLink`) and `bobStart_sid_fresh`: on any
reachable composed trace, every logged `ComposedEvent.HandshakeSession s d` with
`s.initiator = false` has a `PQXDHEvent.BobDone s.me` event logged at index `d` whose
root key is bound in `s.sid`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR

cref_open
open DY.Libsignal.TripleRatchet (SessionInfo)
open DY.Libsignal.TripleRatchet (TREvent TRState)
open DY.Libsignal.PQXDH (PQXDHEvent PQXDHState HandshakeKeys)
open Symbolic.Swarm.COMPOSED.CompTrace (eventLoggedAt_mono eventLoggedAt_here
  eventLogged_append_other_iff eventLogged_append_same_iff)

/-- Every non-initiator `HandshakeSession s d` has a `BobDone s.me` event logged at `d` whose root
key is bound in `s.sid`. -/
def BobSessionSidInv (tr : ExecTrace) : Prop := BobSidLink tr

/-! ## Trace Extension -/

theorem bss_witness_mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {s : SessionInfo} {d : Nat}
    (h : ∃ (pk : DY.Bytes) (a : Participant) (ikB ikA spk pqpk ek ct : DY.Bytes)
      (opk : Option DY.Bytes) (keys : HandshakeKeys),
      tr.EventLoggedAt (PQXDHEvent.BobDone s.me a ikB ikA spk pqpk opk ek ct keys) d ∧
      s.sid = DY.Concat.concat (DY.X25519.normalizeX25519Key pk) keys.rk) :
    ∃ (pk : DY.Bytes) (a : Participant) (ikB ikA spk pqpk ek ct : DY.Bytes)
      (opk : Option DY.Bytes) (keys : HandshakeKeys),
      tr'.EventLoggedAt (PQXDHEvent.BobDone s.me a ikB ikA spk pqpk opk ek ct keys) d ∧
      s.sid = DY.Concat.concat (DY.X25519.normalizeX25519Key pk) keys.rk := by
  obtain ⟨pk, a, ikB, ikA, spk, pqpk, ek, ct, opk, keys, hev, hsid⟩ := h
  exact ⟨pk, a, ikB, ikA, spk, pqpk, ek, ct, opk, keys, eventLoggedAt_mono hle hev, hsid⟩

theorem bss_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT ComposedEvent)) = none)
    (h : BobSessionSidInv tr) : BobSessionSidInv (tr.append e) := fun s d hl hinit =>
  bss_witness_mono (DY.Trace.append_le tr e) (h s d ((eventLogged_append_other_iff hnone).mp hl) hinit)

/-! ## Non-`HandshakeSession` Primitives -/

section Walks

open Symbolic.Swarm.COMPOSED.CompTrace
open DY.Libsignal.Composed
open DY.Libsignal.TripleRatchet (KeyDir)

theorem bss_pres_sendMessage (m : DY.Bytes) :
    Preserves BobSessionSidInv (Network.sendMessage m) := by
  intro tr h
  have htr : ((Network.sendMessage m).run tr).2.val = tr.append (NetE m) := by
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_mk]
  rw [htr]; exact bss_append_other (e := NetE m) rfl h

theorem bss_pres_genRand (n : Nat) : Preserves BobSessionSidInv (Random.genRand n) := by
  intro tr h
  have htr : ((Random.genRand n).run tr).2.val = tr.append (RndE n) := by
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]; rfl
  rw [htr]; exact bss_append_other (e := RndE n) rfl h

theorem bss_pres_logTR (ev : TREvent) :
    Preserves BobSessionSidInv (ProtocolEvent.logEvent ev) := by
  intro tr h
  have htr : ((ProtocolEvent.logEvent ev).run tr).2.val = tr.append (TREvE ev) := by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]; rfl
  rw [htr]; exact bss_append_other (e := TREvE ev) rfl h

theorem bss_pres_logPQ (ev : PQXDHEvent) :
    Preserves BobSessionSidInv (ProtocolEvent.logEvent ev) := by
  intro tr h
  have htr : ((ProtocolEvent.logEvent ev).run tr).2.val = tr.append (PQEvE ev) := by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]; rfl
  rw [htr]; exact bss_append_other (e := PQEvE ev) rfl h

theorem bss_pres_storeTR (p : Participant) (st : TRState) :
    Preserves BobSessionSidInv (PersistentLocalState.storeLocalState p st) := by
  intro tr h
  have htr : ((PersistentLocalState.storeLocalState p st).run tr).2.val = tr.append (TRStE p st) := by
    simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  rw [htr]; exact bss_append_other (e := TRStE p st) rfl h

theorem bss_pres_storePQ (p : Participant) (st : PQXDHState) :
    Preserves BobSessionSidInv (PersistentLocalState.storeLocalState p st) := by
  intro tr h
  have htr : ((PersistentLocalState.storeLocalState p st).run tr).2.val = tr.append (PQStE p st) := by
    simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  rw [htr]; exact bss_append_other (e := PQStE p st) rfl h

/-- An initiator `HandshakeSession` (Alice's) does not touch the invariant. -/
theorem bss_pres_logHS_init (s : SessionInfo) (d : Nat) (hs : s.initiator = true) :
    Preserves BobSessionSidInv (ProtocolEvent.logEvent (ComposedEvent.HandshakeSession s d)) := by
  intro tr h s' d' hl hinit
  have hle := ((ProtocolEvent.logEvent (ComposedEvent.HandshakeSession s d) : Traceful Unit).run tr).2.property
  have htr : ((ProtocolEvent.logEvent (ComposedEvent.HandshakeSession s d)).run tr).2.val =
      tr.append ({ ev := ComposedEvent.HandshakeSession s d } : ProtocolEvent.ExecEntryT ComposedEvent) := by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]; rfl
  rw [htr] at hl
  rcases eventLogged_append_same_iff.mp hl with hl | heq
  · exact bss_witness_mono hle (h s' d' hl hinit)
  · cases heq; rw [hs] at hinit; cases hinit

theorem bss_pres_prodCasesOn {α β γ : Type} (p : α × β) (f : α → β → Traceful γ)
    (hf : ∀ a b, Preserves BobSessionSidInv (f a b)) :
    Preserves BobSessionSidInv (Prod.casesOn p f) := by
  rcases p with ⟨a, b⟩; exact hf a b

theorem bss_pres_optionCasesOn {α β : Type} (o : Option α) (noneCase : Traceful β)
    (someCase : α → Traceful β) (hn : Preserves BobSessionSidInv noneCase)
    (hs : ∀ a, Preserves BobSessionSidInv (someCase a)) :
    Preserves BobSessionSidInv (Option.casesOn o noneCase someCase) := by
  rcases o with _ | a; exact hn; exact hs a

theorem bss_pres_getKey (p : Participant) (h : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    Preserves BobSessionSidInv (DY.Libsignal.PQXDH.getKey p h kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

theorem bss_pres_lookupIdentity (p : Participant) (h : Nat) :
    Preserves BobSessionSidInv (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

theorem bss_pres_dhRatchetStep (st : TRState) (pk : DY.Bytes) :
    Preserves BobSessionSidInv (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact Preserves.bind (Preserves.guardP _) fun _ =>
    Preserves.bind (bss_pres_genRand 32) fun _ => Preserves.pure _

theorem bss_pres_ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    Preserves BobSessionSidInv (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact Preserves.pure _
  · exact Preserves.bind (bss_pres_dhRatchetStep st pk) fun _ => Preserves.pure _
  · exact Preserves.failure

theorem bss_pres_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    Preserves BobSessionSidInv (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => unfold DY.Libsignal.TripleRatchet.logSkippedKeys; exact Preserves.pure _
  | succ k ih =>
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    exact Preserves.bind (bss_pres_logTR _) fun _ => ih _ _

theorem bss_pres_logMessageKeyAndStore (me : Participant) (s : SessionInfo) (dir : KeyDir)
    (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState) :
    Preserves BobSessionSidInv
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx par
        st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact Preserves.bind (bss_pres_logTR _) fun _ => bss_pres_storeTR me st

local macro "bss_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply Preserves.bind | with_reducible apply bss_pres_prodCasesOn
  | with_reducible apply bss_pres_optionCasesOn
  | with_reducible apply Preserves.pure | with_reducible apply Preserves.failure
  | with_reducible apply bss_pres_genRand | with_reducible apply bss_pres_storeTR
  | with_reducible apply bss_pres_storePQ
  | with_reducible apply bss_pres_sendMessage | with_reducible apply Preserves.getLocalState_tr
  | with_reducible apply Preserves.getLocalState_pq | with_reducible apply bss_pres_getKey
  | with_reducible apply bss_pres_lookupIdentity | with_reducible apply Preserves.receiveMessage
  | with_reducible apply Preserves.getEntry | with_reducible apply Preserves.receiveSignalMsg
  | with_reducible apply Preserves.verifyMacAndDecrypt | with_reducible apply bss_pres_dhRatchetStep
  | with_reducible apply bss_pres_ensureReceiverChain
  | with_reducible apply bss_pres_logSkippedKeys
  | with_reducible apply Preserves.guardP | with_reducible apply Preserves.monadLiftErr
  | with_reducible apply Preserves.guardTrace | with_reducible apply Preserves.requireTracePredicate
  | with_reducible apply Preserves.traceLength
  | with_reducible apply bss_pres_logMessageKeyAndStore
  | with_reducible apply bss_pres_logPQ | with_reducible apply bss_pres_logTR
  | ((with_reducible apply bss_pres_logHS_init); rfl)
  | split | with_reducible intro))

theorem bss_pres_aliceHandshake (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves BobSessionSidInv (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake; bss_tac

theorem bss_pres_bobHandshake (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (regIdxA ekIdx ctIdx : Nat) :
    Preserves BobSessionSidInv
      (DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake; bss_tac

theorem bss_pres_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves BobSessionSidInv (aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine Preserves.bind (bss_pres_aliceHandshake a b idStateIdx regIdxB h) fun o => ?_
  bss_tac

/-! ## `bobStart` Preservation -/

/-- Return-value postcondition of a `Traceful` computation on any starting trace. -/
def BssRet {α : Type} (Q : α → Prop) (x : Traceful α) : Prop :=
  ∀ tr a, (x.run tr).1 = some a → Q a

theorem BssRet.bind {α β : Type} {Q₁ : α → Prop} {Q₂ : β → Prop} {x : Traceful α}
    {f : α → Traceful β} (hx : BssRet Q₁ x) (hf : ∀ a, Q₁ a → BssRet Q₂ (f a)) :
    BssRet Q₂ (x >>= f) := by
  intro tr b hb
  rw [run_bind_fst] at hb
  revert hb
  cases h1 : (x.run tr).1 with
  | none => intro hb; cases hb
  | some a => intro hb; exact hf a (hx tr a h1) _ b hb

theorem BssRet.pure {α : Type} {Q : α → Prop} {a : α} (ha : Q a) :
    BssRet Q (Pure.pure a : Traceful α) := by
  intro tr b hb
  simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1] at hb
  injection hb with hb; exact hb ▸ ha

theorem BssRet.failure {α : Type} {Q : α → Prop} : BssRet Q (Alternative.failure : Traceful α) := by
  intro tr b hb
  rw [Traceful.run_failure] at hb
  cases hb

theorem BssRet.triv {α : Type} (x : Traceful α) : BssRet (fun _ => True) x :=
  fun _ _ _ => trivial

theorem bss_ret_dhRatchetStep (st : TRState) (pk : DY.Bytes) :
    BssRet (fun r : TRState × DY.Libsignal.TripleRatchet.RecvChain => r.1.sid = st.sid)
      (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine BssRet.bind (BssRet.triv _) fun _ _ => ?_
  split
  refine BssRet.bind (BssRet.triv _) fun _ _ => ?_
  split
  exact BssRet.pure rfl

theorem bss_ret_ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    BssRet (fun r : TRState × DY.Libsignal.TripleRatchet.RecvChain × Bool => r.1.sid = st.sid)
      (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact BssRet.pure rfl
  · refine BssRet.bind (bss_ret_dhRatchetStep st pk) fun r hr => ?_
    rcases r with ⟨st', c⟩
    exact BssRet.pure hr
  · exact BssRet.failure

theorem bss_bind_post {α β : Type} {Q : α → Prop} {x : Traceful α} {f : α → Traceful β}
    (hx : Preserves BobSessionSidInv x) (hQ : BssRet Q x)
    (hf : ∀ a, Q a → Preserves BobSessionSidInv (f a)) :
    Preserves BobSessionSidInv (x >>= f) := by
  intro tr hInv
  rw [run_bind_snd]
  have hMid := hx tr hInv
  revert hMid
  cases h1 : (x.run tr).1 with
  | none => intro hMid; exact hMid
  | some a => intro hMid; exact hf a (hQ tr a h1) _ hMid

theorem bss_pres_and_logged {α : Type} {ev : PQXDHEvent} {d : Nat} {x : Traceful α}
    (hx : Preserves BobSessionSidInv x) :
    Preserves (fun t => BobSessionSidInv t ∧ t.EventLoggedAt ev d) x :=
  fun tr h => ⟨hx tr h.1, eventLoggedAt_mono (x.run tr).2.property h.2⟩

theorem bss_pres_traceLength_bind {α : Type} (f : Nat → Traceful α)
    (hf : ∀ tr, BobSessionSidInv tr → BobSessionSidInv ((f tr.length).run tr).2.val) :
    Preserves BobSessionSidInv (DY.Libsignal.TripleRatchet.traceLength >>= f) := by
  intro tr h
  unfold DY.Libsignal.TripleRatchet.traceLength
  rw [run_bind_snd, Traceful.run_mk]
  exact hf tr h

theorem bss_logBobDone_at {α : Type} (ev : PQXDHEvent) (x : Traceful α) (tr : ExecTrace)
    (hInv : BobSessionSidInv tr)
    (hk : Preserves (fun t => BobSessionSidInv t ∧ t.EventLoggedAt ev tr.length) x) :
    BobSessionSidInv (x.run (tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT PQXDHEvent))).2.val :=
  (hk _ ⟨bss_append_other (e := PQEvE ev) rfl hInv, eventLoggedAt_here tr ev⟩).1

theorem bss_pres_logHS_bob (s : SessionInfo) (d : Nat) (me a : Participant)
    (ikB ikA spk pqpk ek ct : DY.Bytes) (opk : Option DY.Bytes) (keys : HandshakeKeys)
    (hme : s.me = me)
    (hsid : ∃ pk, s.sid = DY.Concat.concat (DY.X25519.normalizeX25519Key pk) keys.rk) :
    Preserves (fun t => BobSessionSidInv t ∧
        t.EventLoggedAt (PQXDHEvent.BobDone me a ikB ikA spk pqpk opk ek ct keys) d)
      (ProtocolEvent.logEvent (ComposedEvent.HandshakeSession s d)) := by
  intro tr ⟨h, hbd⟩
  have hle := ((ProtocolEvent.logEvent (ComposedEvent.HandshakeSession s d) : Traceful Unit).run tr).2.property
  refine ⟨fun s' d' hl hinit => ?_, eventLoggedAt_mono hle hbd⟩
  have htr : ((ProtocolEvent.logEvent (ComposedEvent.HandshakeSession s d)).run tr).2.val =
      tr.append ({ ev := ComposedEvent.HandshakeSession s d } : ProtocolEvent.ExecEntryT ComposedEvent) := by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]; rfl
  rw [htr] at hl
  rcases eventLogged_append_same_iff.mp hl with hl | heq
  · exact bss_witness_mono hle (h s' d' hl hinit)
  · cases heq
    subst hme
    obtain ⟨pk, hpk⟩ := hsid
    exact ⟨pk, a, ikB, ikA, spk, pqpk, ek, ct, opk, keys, eventLoggedAt_mono hle hbd, hpk⟩

local macro "bssQ_tac" : tactic => `(tactic| repeat (first
  | ((with_reducible apply bss_pres_logHS_bob) <;> assumption)
  | with_reducible apply Preserves.bind
  | with_reducible apply Preserves.pure | with_reducible apply Preserves.failure
  | with_reducible apply Preserves.traceLength
  | exact bss_pres_and_logged (bss_pres_logSkippedKeys _ _ _ _ _ _ _)
  | exact bss_pres_and_logged (bss_pres_logTR _)
  | exact bss_pres_and_logged (bss_pres_logMessageKeyAndStore _ _ _ _ _ _ _ _ _)
  | ((refine bss_pres_and_logged ?_); bss_tac; done)
  | split | with_reducible intro))

theorem bss_pres_bobStart (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (regIdxA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    Preserves BobSessionSidInv (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine Preserves.bind (bss_pres_bobHandshake b a kh regIdxA mh.ek mh.ct) fun o => ?_
  refine Preserves.bind (Preserves.receiveSignalMsg mh.msg) fun msg => ?_
  refine bss_bind_post (bss_pres_ensureReceiverChain _ msg.ratchetKey)
    (bss_ret_ensureReceiverChain _ msg.ratchetKey) fun r hr => ?_
  rcases r with ⟨st, c, ratcheted⟩
  dsimp only at hr ⊢
  have hsid : ∃ pk, (st.sessionInfo b).sid = DY.Concat.concat (DY.X25519.normalizeX25519Key pk) o.keys.rk :=
    ⟨msg.ratchetKey, hr⟩
  have hme : (st.sessionInfo b).me = b := rfl
  cases ratcheted <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals repeat (first
    | with_reducible apply bss_pres_traceLength_bind
    | with_reducible refine Preserves.bind ?_ fun _ => ?_
    | with_reducible refine bss_pres_prodCasesOn _ _ fun _ _ => ?_
    | with_reducible refine bss_pres_optionCasesOn _ _ _ ?_ fun _ => ?_
    | with_reducible apply Preserves.pure | with_reducible apply Preserves.failure
    | with_reducible apply bss_pres_sendMessage | with_reducible apply Preserves.receiveMessage
    | with_reducible apply Preserves.verifyMacAndDecrypt
    | with_reducible apply Preserves.guardP | with_reducible apply Preserves.monadLiftErr
    | with_reducible apply Preserves.guardTrace | with_reducible apply Preserves.requireTracePredicate
    | with_reducible apply bss_pres_logPQ | with_reducible apply bss_pres_logTR
    | split)
  all_goals try exact Preserves.failure
  all_goals try refine bss_pres_traceLength_bind _ ?_
  all_goals
    intro tr hInv
    rw [Symbolic.Swarm.COMPOSED.CompPresTRExp.run_logEvent_bind_snd]
    refine bss_logBobDone_at _ _ tr hInv ?_
    bssQ_tac

/-! ## Reachability Induction -/

theorem bobSessionSidInv_of_reachable {tr : ExecTrace}
    (h : tr.Reachable DY.Libsignal.Composed.reachability) : BobSessionSidInv tr := by
  refine composed_reachable_induction (Inv := BobSessionSidInv)
    (by
      intro _ _ hl _
      obtain ⟨_, hev⟩ := hl
      simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, DY.Trace.at?,
        Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at hev)
    (fun msg tr _ hinv => bss_append_other (e := NetE msg) rfl hinv)
    (fun p => by unfold DY.Libsignal.PQXDH.registerIdentity; bss_tac)
    (fun p skIdx => by unfold DY.Libsignal.PQXDH.registerCorruptIdentity; bss_tac)
    (fun b idStateIdx => by unfold DY.Libsignal.PQXDH.genSignedPrekey; bss_tac)
    (fun b idStateIdx => by unfold DY.Libsignal.PQXDH.genPQPrekey; bss_tac)
    (fun b => by unfold DY.Libsignal.PQXDH.genOneTimePrekey; bss_tac)
    (fun a b idStateIdx regIdxB bh => bss_pres_aliceStart a b idStateIdx regIdxB bh)
    (fun b a kh regIdxA mh pqIdx spqrMsgIdx => bss_pres_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx)
    (fun me stH coinsLen pqIdx => by unfold DY.Libsignal.TripleRatchet.messageEncrypt; bss_tac)
    (fun me stH => by unfold DY.Libsignal.TripleRatchet.messageEncryptAbort; bss_tac)
    (fun me stH msgH pqIdx spqrMsgIdx => by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]; bss_tac)
    (fun me stH msgH evH pqIdx spqrMsgIdx => by
      unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped; bss_tac)
    (fun me stH k => by unfold DY.Libsignal.TripleRatchet.exposeKey; bss_tac)
    (fun me stH => by unfold DY.Libsignal.TripleRatchet.exposeSpqr; bss_tac)
    (fun evH => by unfold DY.Libsignal.TripleRatchet.exposeSkipped; bss_tac)
    (fun p stateIdx => by unfold DY.Libsignal.PQXDH.compromiseIK; bss_tac)
    (fun b stateIdx => by unfold DY.Libsignal.PQXDH.compromiseSPK; bss_tac)
    (fun b stateIdx => by unfold DY.Libsignal.PQXDH.compromisePQSPK; bss_tac)
    (fun b stateIdx => by unfold DY.Libsignal.PQXDH.compromiseOPK; bss_tac)
    (by unfold DY.Libsignal.PQXDH.breakDH; bss_tac)
    (by unfold DY.Libsignal.PQXDH.breakKEM; bss_tac)
    (fun msgIdx => by unfold DY.Libsignal.PQXDH.invertDH; bss_tac)
    (fun msgIdx => by unfold DY.Libsignal.PQXDH.invertKEM; bss_tac)
    h

end Walks

theorem bobSidLink_of_reachable {tr : ExecTrace}
    (h : tr.Reachable DY.Libsignal.Composed.reachability) : BobSidLink tr :=
  bobSessionSidInv_of_reachable h

/-- On a reachable pre-step trace with a fresh base key `o.ek`, `bobStart`'s session descriptor has
no logged receiver key, no skipped key, and no stored local state. -/
theorem bobStart_sid_fresh {T : ExecTrace}
    (hreach : T.Reachable DY.Libsignal.Composed.reachability)
    {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regIdxA ekIdx ctIdx : Nat}
    {o : DY.Libsignal.PQXDH.BobHandshakeOut}
    (ho : ((DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx).run T).1 = some o)
    (hek : o.ek ∉ DY.Libsignal.Composed.Refinement.bobDoneBaseKeys T)
    (rkey : DY.Bytes) :
    let s : SessionInfo := ⟨DY.Concat.concat (DY.X25519.normalizeX25519Key rkey) o.keys.rk, false, b, a⟩
    ((∀ seed pqSalt n r pIdx i, ¬ T.EventLoggedAt
        (TREvent.MessageKey s .receiver seed pqSalt n r pIdx) i) ∧
      (∀ pk n seed r srcIdx i, ¬ T.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed r srcIdx) i)) ∧
    (∀ q j st, ((PersistentLocalState.getLocalState q j : Traceful TRState).run T).1 = some st →
      st.sessionInfo q ≠ s) :=
  bobStart_sid_fresh_of_link hreach (bobSidLink_of_reachable hreach) ho hek rkey

end Symbolic.Swarm.CREF.TR
