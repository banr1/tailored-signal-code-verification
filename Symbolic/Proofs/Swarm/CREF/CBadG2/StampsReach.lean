/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaReach
import Comparse.Basic
import DY.Comparse
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompRatchet
import Symbolic.Proofs.Swarm.CREF.CBadG2.StampsReachBob
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core
import Symbolic.DYBridge.Comparse.Basic
import Symbolic.DYBridge.DY.Comparse
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Stamp Bounds for Stored Terms on Reachable Traces

Proves that on any reachable composed trace `tr` with `tr.length ≤ n`, all fresh values in
serialized stored session states (`storedStates`), serialized stored PQXDH secrets
(`storedSecrets`), and `BobDone` base keys (`bobDoneBaseKeys`) have timestamps below `n`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.FreshSigma (StampsLt VisStampsLt StateStampsLt TraceEntriesLt)
open DY.Libsignal.TripleRatchet (TRState)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent)

/-! ## Serialization compatibility -/

instance g2s_stampsLt_compat (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (n : Nat) :
    Comparse.BytesCompatiblePred (StampsLt i S g n) where
  pred_empty := by
    simp only [Comparse.BytesLike.empty]; exact TR.FreshSigma.stampsLt_literalToBytes i S g n _
  pred_concat := by
    simp only [Comparse.BytesLike.concat]; intro _ _ h1 h2; exact TR.FreshSigma.stampsLt_concat h1 h2
  pred_split := by
    intro buf j hbuf; simp only [Comparse.BytesLike.split]
    rcases hsp : DY.Concat.split buf j with _ | ⟨b1, b2⟩
    · trivial
    · rw [← DY.Concat.concat_split buf j b1 b2 hsp] at hbuf
      exact (TR.FreshSigma.stampsLt_concat_pack i S g n ⟨b1, b2⟩).mp hbuf
  pred_fromByteArray := by
    intro b; simp only [Comparse.BytesLike.fromByteArray]
    exact TR.FreshSigma.stampsLt_literalToBytes i S g n b

theorem g2s_stampsLt_serialize_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) {n : Nat}
    (ls : PersistentLocalState.LocalState TRState)
    (hst : StateStampsLt i S g n ls.state) (hsid : StampsLt i S g n ls.state.sid) :
    StampsLt i S g n (serialize ls) := by
  rw [Symbolic.DYBridge.DY.Comparse.serialize_eq_1,
    ← Comparse.ExtensibleMessageFormat.wf_eq _ (StampsLt i S g n) ls]
  obtain ⟨hmy, hpeer, hrk, hdhs, hcks, hspqr, hrecv⟩ := hst
  simp [Comparse.ParseableSerializeable.mf, Comparse.ParseableSerializeableNE.mf]
  exact ⟨hmy, hpeer, hrk, hdhs, hcks, hsid, hspqr, hrecv⟩

theorem g2s_stampsLt_serialize_pq (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) {n : Nat}
    (ls : PersistentLocalState.LocalState PQXDHState) (hsk : StampsLt i S g n ls.state.sk) :
    StampsLt i S g n (serialize ls) := by
  rw [Symbolic.DYBridge.DY.Comparse.serialize_eq_1,
    ← Comparse.ExtensibleMessageFormat.wf_eq _ (StampsLt i S g n) ls]
  simp [Comparse.ParseableSerializeable.mf]
  exact hsk

/-! ## Stored session identifiers and reachability invariant -/

/-- Every stored `TRState` on `tr` has `sid` stamped below `ts`. -/
def g2s_SidLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (tr : ExecTrace) :
    Prop :=
  ∀ j (e : TR.FreshSigma.StEntry), (tr.at? j : Option TR.FreshSigma.StEntry) = some e →
      StampsLt i S g ts e.st.state.sid

/-- Every `HandshakeSession` event logged on `tr` has a `sid` stamped below `ts`. -/
def g2s_HSLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (tr : ExecTrace) :
    Prop :=
  ∀ s d, tr.EventLogged (ComposedEvent.HandshakeSession s d) → StampsLt i S g ts s.sid

theorem g2s_baseAttackerKnows_mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : DY.Bytes}
    (hb : tr.BaseAttackerKnows b) : tr'.BaseAttackerKnows b := by
  induction hle with
  | equal => exact hb
  | extend _ _ _ ih =>
    rw [Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2]
    exact Or.inr ih

theorem g2s_tel_of_le {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {tr tr' : ExecTrace} (hle : tr ≤ tr') (h : TraceEntriesLt i S g ts tr') :
    TraceEntriesLt i S g ts tr := by
  refine ⟨fun b hb => h.1 b (g2s_baseAttackerKnows_mono hle hb), fun j hj => ?_⟩
  rw [DY.Trace.at_le tr tr' j hj hle]
  exact h.2 j _

section Walks

open Symbolic.Swarm.COMPOSED.CompTrace
open DY.Libsignal.Composed
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir)
open DY.Libsignal.TripleRatchet (TREvent)

variable {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}

theorem g2s_hsLt_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT ComposedEvent)) = none)
    (h : g2s_HSLt i S g ts tr) : g2s_HSLt i S g ts (tr.append e) :=
  fun s d hl => h s d ((eventLogged_append_other_iff hnone).mp hl)

theorem g2s_pres_sendMessage (m : DY.Bytes) :
    Preserves (g2s_HSLt i S g ts) (Network.sendMessage m) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  erw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact g2s_hsLt_append_other (e := NetE m) rfl h

theorem g2s_pres_genRand (n : Nat) : Preserves (g2s_HSLt i S g ts) (Random.genRand n) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  exact g2s_hsLt_append_other (e := RndE n) rfl h

theorem g2s_pres_logTR (ev : TREvent) :
    Preserves (g2s_HSLt i S g ts) (ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  exact g2s_hsLt_append_other (e := TREvE ev) rfl h

theorem g2s_pres_logPQ (ev : PQXDHEvent) :
    Preserves (g2s_HSLt i S g ts) (ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  exact g2s_hsLt_append_other (e := PQEvE ev) rfl h

theorem g2s_pres_storeTR (p : Participant) (st : TRState) :
    Preserves (g2s_HSLt i S g ts) (PersistentLocalState.storeLocalState p st) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  erw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact g2s_hsLt_append_other (e := TRStE p st) rfl h

theorem g2s_pres_storePQ (p : Participant) (st : PQXDHState) :
    Preserves (g2s_HSLt i S g ts) (PersistentLocalState.storeLocalState p st) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  erw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact g2s_hsLt_append_other (e := PQStE p st) rfl h

theorem g2s_pres_logHS (s : SessionInfo) (d : Nat) (hs : StampsLt i S g ts s.sid) :
    Preserves (g2s_HSLt i S g ts) (ProtocolEvent.logEvent (ComposedEvent.HandshakeSession s d)) := by
  intro tr h s' d' hl
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1] at hl
  rcases eventLogged_append_same_iff.mp hl with hl | heq
  · exact h s' d' hl
  · cases heq; exact hs

theorem g2s_pres_prodCasesOn {α β γ : Type} (p : α × β) (f : α → β → Traceful γ)
    (hf : ∀ a b, Preserves (g2s_HSLt i S g ts) (f a b)) :
    Preserves (g2s_HSLt i S g ts) (Prod.casesOn p f) := by
  rcases p with ⟨a, b⟩; exact hf a b

theorem g2s_pres_optionCasesOn {α β : Type} (o : Option α) (noneCase : Traceful β)
    (someCase : α → Traceful β) (hn : Preserves (g2s_HSLt i S g ts) noneCase)
    (hs : ∀ a, Preserves (g2s_HSLt i S g ts) (someCase a)) :
    Preserves (g2s_HSLt i S g ts) (Option.casesOn o noneCase someCase) := by
  rcases o with _ | a; exact hn; exact hs a

theorem g2s_pres_getKey (p : Participant) (h : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    Preserves (g2s_HSLt i S g ts) (DY.Libsignal.PQXDH.getKey p h kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

theorem g2s_pres_lookupIdentity (p : Participant) (h : Nat) :
    Preserves (g2s_HSLt i S g ts) (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

theorem g2s_pres_dhRatchetStep (st : TRState) (pk : DY.Bytes) :
    Preserves (g2s_HSLt i S g ts) (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact Preserves.bind (Preserves.guardP _) fun _ =>
    Preserves.bind (g2s_pres_genRand 32) fun _ => Preserves.pure _

theorem g2s_pres_ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    Preserves (g2s_HSLt i S g ts) (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact Preserves.pure _
  · exact Preserves.bind (g2s_pres_dhRatchetStep st pk) fun _ => Preserves.pure _
  · exact Preserves.failure

theorem g2s_pres_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    Preserves (g2s_HSLt i S g ts)
      (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => unfold DY.Libsignal.TripleRatchet.logSkippedKeys; exact Preserves.pure _
  | succ k ih =>
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    exact Preserves.bind (g2s_pres_logTR _) fun _ => ih _ _

theorem g2s_pres_logMessageKeyAndStore (me : Participant) (s : SessionInfo) (dir : KeyDir)
    (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState) :
    Preserves (g2s_HSLt i S g ts)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx par
        st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact Preserves.bind (g2s_pres_logTR _) fun _ => g2s_pres_storeTR me st

local macro "g2s_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply Preserves.bind | with_reducible apply g2s_pres_prodCasesOn
  | with_reducible apply g2s_pres_optionCasesOn
  | with_reducible apply Preserves.pure | with_reducible apply Preserves.failure
  | with_reducible apply g2s_pres_genRand | with_reducible apply g2s_pres_storeTR
  | with_reducible apply g2s_pres_storePQ
  | with_reducible apply g2s_pres_sendMessage | with_reducible apply Preserves.getLocalState_tr
  | with_reducible apply Preserves.getLocalState_pq | with_reducible apply g2s_pres_getKey
  | with_reducible apply g2s_pres_lookupIdentity | with_reducible apply Preserves.receiveMessage
  | with_reducible apply Preserves.getEntry | with_reducible apply Preserves.receiveSignalMsg
  | with_reducible apply Preserves.verifyMacAndDecrypt | with_reducible apply g2s_pres_dhRatchetStep
  | with_reducible apply g2s_pres_ensureReceiverChain
  | with_reducible apply g2s_pres_logSkippedKeys
  | with_reducible apply Preserves.guardP | with_reducible apply Preserves.monadLiftErr
  | with_reducible apply Preserves.guardTrace | with_reducible apply Preserves.requireTracePredicate
  | with_reducible apply Preserves.traceLength
  | with_reducible apply g2s_pres_logMessageKeyAndStore
  | with_reducible apply g2s_pres_logPQ | with_reducible apply g2s_pres_logTR
  | ((with_reducible apply g2s_pres_logHS); assumption)
  | split | with_reducible intro))

theorem g2s_pres_aliceHandshake (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves (g2s_HSLt i S g ts)
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake; g2s_tac

theorem g2s_pres_bobHandshake (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (regIdxA ekIdx ctIdx : Nat) :
    Preserves (g2s_HSLt i S g ts)
      (DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake; g2s_tac

def g2s_W (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) {α : Type} (Q : α → Prop)
    (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, (x.run tr).2.val.length ≤ ts → TraceEntriesLt i S g ts (x.run tr).2.val →
    g2s_HSLt i S g ts tr → g2s_HSLt i S g ts (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q a

theorem g2s_W.bind {α β : Type} {Q₁ : α → Prop} {Q₂ : β → Prop} {x : Traceful α}
    {f : α → Traceful β} (hx : g2s_W i S g ts Q₁ x) (hf : ∀ a, Q₁ a → g2s_W i S g ts Q₂ (f a)) :
    g2s_W i S g ts Q₂ (x >>= f) := by
  intro tr hlen htel hhs
  rw [run_bind_snd] at hlen htel ⊢
  rw [run_bind_fst]
  revert hlen htel
  cases h1 : (x.run tr).1 with
  | none =>
    intro hlen htel
    exact ⟨(hx tr hlen htel hhs).1, fun _ hb => by cases hb⟩
  | some a =>
    intro hlen htel
    have hle2 := ((f a).run (x.run tr).2.val).2.property
    have h1' := hx tr (Nat.le_trans (DY.Trace.length_le _ _ hle2) hlen)
      (g2s_tel_of_le hle2 htel) hhs
    exact hf a (h1'.2 a h1) (x.run tr).2.val hlen htel h1'.1

theorem g2s_W.of_lt {α : Type} {Q : α → Prop} {x : Traceful α}
    (hlt : TR.FreshSigma.TracefulLt i S g ts Q x) (hp : Preserves (g2s_HSLt i S g ts) x) :
    g2s_W i S g ts Q x := by
  intro tr hlen htel hhs
  exact ⟨hp tr hhs, (hlt tr hlen (g2s_tel_of_le (x.run tr).2.property htel)).2⟩

theorem g2s_W.of_pres {α : Type} {x : Traceful α} (hp : Preserves (g2s_HSLt i S g ts) x) :
    g2s_W i S g ts (fun _ => True) x :=
  fun tr _ _ hhs => ⟨hp tr hhs, fun _ _ => trivial⟩

theorem g2s_W.pure {α : Type} {Q : α → Prop} {a : α} (ha : Q a) :
    g2s_W i S g ts Q (Pure.pure a : Traceful α) := by
  intro tr _ _ hhs
  simp only [DY.Traceful.run_pure]
  refine ⟨hhs, fun b hb => ?_⟩
  cases hb; exact ha

theorem g2s_W.failure {α : Type} {Q : α → Prop} :
    g2s_W i S g ts Q (Alternative.failure : Traceful α) := by
  intro tr _ _ hhs
  simp only [DY.Traceful.run_failure]
  exact ⟨hhs, fun _ hb => by cases hb⟩

theorem g2s_W_dhRatchetStep (st : TRState) (pk : DY.Bytes) :
    g2s_W i S g ts (fun r : TRState × DY.Libsignal.TripleRatchet.RecvChain => r.1.sid = st.sid)
      (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine g2s_W.bind (g2s_W.of_pres (Preserves.guardP _)) fun _ _ => ?_
  split
  refine g2s_W.bind (g2s_W.of_pres (g2s_pres_genRand 32)) fun _ _ => ?_
  split
  exact g2s_W.pure (by rfl)

theorem g2s_W_ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    g2s_W i S g ts
      (fun r : TRState × DY.Libsignal.TripleRatchet.RecvChain × Bool => r.1.sid = st.sid)
      (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact g2s_W.pure rfl
  · refine g2s_W.bind (g2s_W_dhRatchetStep st pk) fun r hr => ?_
    rcases r with ⟨st', c⟩
    exact g2s_W.pure hr
  · exact g2s_W.failure

theorem g2s_W_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    g2s_W i S g ts (fun _ => True) (aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine g2s_W.bind (g2s_W.of_lt (TR.FreshSigma.TracefulLt.aliceHandshake a b idStateIdx regIdxB h)
    (g2s_pres_aliceHandshake a b idStateIdx regIdxB h)) fun o ho => ?_
  refine g2s_W.bind (g2s_W.of_lt (TR.FreshSigma.TracefulLt.genRand 32) (g2s_pres_genRand 32))
    fun dhsA hdhsA => ?_
  have hsid : StampsLt i S g ts (DY.Concat.concat (DY.DiffieHellman.dhPk dhsA) o.keys.rk) :=
    TR.FreshSigma.stampsLt_concat (TR.FreshSigma.stampsLt_dhPk hdhsA) ho.2.2.2.2.2.2.2.1
  refine g2s_W.of_pres ?_
  g2s_tac

theorem g2s_W_bobStart (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (regIdxA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    g2s_W i S g ts (fun _ => True) (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine g2s_W.bind (g2s_W.of_lt (TR.FreshSigma.TracefulLt.bobHandshake b a kh regIdxA mh.ek mh.ct)
    (g2s_pres_bobHandshake b a kh regIdxA mh.ek mh.ct)) fun o ho => ?_
  refine g2s_W.bind (g2s_W.of_lt (TR.FreshSigma.TracefulLt.receiveSignalMsg mh.msg)
    (Preserves.receiveSignalMsg mh.msg)) fun msg hmsg => ?_
  refine g2s_W.bind (g2s_W_ensureReceiverChain _ msg.ratchetKey) fun r hr => ?_
  have hsid : StampsLt i S g ts r.1.sid := by
    rw [hr]
    exact TR.FreshSigma.stampsLt_concat (TR.FreshSigma.stampsLt_x25519Key hmsg.2.2.1) ho.2.2.2.1
  rcases r with ⟨st, c, ratcheted⟩
  dsimp only at hsid ⊢
  refine g2s_W.of_pres ?_
  g2s_tac

def g2s_Inv (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace) : Prop :=
  ∀ ts, tr.length ≤ ts → TraceEntriesLt i S g ts tr → g2s_HSLt i S g ts tr

theorem g2s_inv_of_W {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {α : Type} {x : Traceful α}
    (hx : ∀ ts, g2s_W i S g ts (fun _ => True) x) : Preserves (g2s_Inv i S g) x := by
  intro tr hinv ts hlen htel
  have hle := (x.run tr).2.property
  exact (hx ts tr hlen htel (hinv ts (Nat.le_trans (DY.Trace.length_le _ _ hle) hlen)
    (g2s_tel_of_le hle htel))).1

theorem g2s_inv_of_pres {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {α : Type}
    {x : Traceful α} (hx : ∀ ts, Preserves (g2s_HSLt i S g ts) x) :
    Preserves (g2s_Inv i S g) x :=
  g2s_inv_of_W fun ts => g2s_W.of_pres (hx ts)

theorem g2s_inv_of_reachable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) {tr : ExecTrace}
    (hreach : tr.Reachable reachability) : g2s_Inv i S g tr := by
  refine composed_reachable_induction (Inv := g2s_Inv i S g)
    (by
      intro _ _ _ _ _ hl; obtain ⟨_, hev⟩ := hl
      simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, DY.Trace.at?,
        Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at hev)
    (fun msg tr _ hinv => by
      have h := g2s_inv_of_pres (fun _ => g2s_pres_sendMessage msg) tr hinv
      simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1] at h
      erw [Symbolic.DYBridge.DY.Traceful.run_eq_1] at h
      exact h)
    (fun p => g2s_inv_of_pres fun _ => by
      unfold DY.Libsignal.PQXDH.registerIdentity; g2s_tac)
    (fun p skIdx => g2s_inv_of_pres fun _ => by
      unfold DY.Libsignal.PQXDH.registerCorruptIdentity; g2s_tac)
    (fun b idStateIdx => g2s_inv_of_pres fun _ => by
      unfold DY.Libsignal.PQXDH.genSignedPrekey; g2s_tac)
    (fun b idStateIdx => g2s_inv_of_pres fun _ => by
      unfold DY.Libsignal.PQXDH.genPQPrekey; g2s_tac)
    (fun b => g2s_inv_of_pres fun _ => by unfold DY.Libsignal.PQXDH.genOneTimePrekey; g2s_tac)
    (fun a b idStateIdx regIdxB bh => g2s_inv_of_W fun _ => g2s_W_aliceStart a b idStateIdx regIdxB bh)
    (fun b a kh regIdxA mh pqIdx spqrMsgIdx =>
      g2s_inv_of_W fun _ => g2s_W_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx)
    (fun me stH coinsLen pqIdx => g2s_inv_of_pres fun _ => by
      unfold DY.Libsignal.TripleRatchet.messageEncrypt; g2s_tac)
    (fun me stH => g2s_inv_of_pres fun _ => by
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort; g2s_tac)
    (fun me stH msgH pqIdx spqrMsgIdx => g2s_inv_of_pres fun _ => by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]; g2s_tac)
    (fun me stH msgH evH pqIdx spqrMsgIdx => g2s_inv_of_pres fun _ => by
      unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped; g2s_tac)
    (fun me stH k => g2s_inv_of_pres fun _ => by
      unfold DY.Libsignal.TripleRatchet.exposeKey; g2s_tac)
    (fun me stH => g2s_inv_of_pres fun _ => by
      unfold DY.Libsignal.TripleRatchet.exposeSpqr; g2s_tac)
    (fun evH => g2s_inv_of_pres fun _ => by
      unfold DY.Libsignal.TripleRatchet.exposeSkipped; g2s_tac)
    (fun p stateIdx => g2s_inv_of_pres fun _ => by
      unfold DY.Libsignal.PQXDH.compromiseIK; g2s_tac)
    (fun b stateIdx => g2s_inv_of_pres fun _ => by
      unfold DY.Libsignal.PQXDH.compromiseSPK; g2s_tac)
    (fun b stateIdx => g2s_inv_of_pres fun _ => by
      unfold DY.Libsignal.PQXDH.compromisePQSPK; g2s_tac)
    (fun b stateIdx => g2s_inv_of_pres fun _ => by
      unfold DY.Libsignal.PQXDH.compromiseOPK; g2s_tac)
    (g2s_inv_of_pres fun _ => by unfold DY.Libsignal.PQXDH.breakDH; g2s_tac)
    (g2s_inv_of_pres fun _ => by unfold DY.Libsignal.PQXDH.breakKEM; g2s_tac)
    (fun msgIdx => g2s_inv_of_pres fun _ => by unfold DY.Libsignal.PQXDH.invertDH; g2s_tac)
    (fun msgIdx => g2s_inv_of_pres fun _ => by unfold DY.Libsignal.PQXDH.invertKEM; g2s_tac)
    hreach

end Walks

theorem g2s_sidLt_of_reachable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat)
    {tr : ExecTrace} (hreach : tr.Reachable reachability) (hlen : tr.length ≤ ts) :
    g2s_SidLt i S g ts tr := by
  have hhs := g2s_inv_of_reachable i S g hreach ts hlen
    (TR.FreshSigma.traceEntriesLt_of_reachable i S g ts hreach hlen)
  have horig := Symbolic.Swarm.COMPOSED.CompRatchet.compSessionOriginInv_reachable hreach
  intro j e he
  rcases e with ⟨⟨p, st⟩⟩
  obtain ⟨_, _, ⟨doneIdx, _, hev, _⟩, _⟩ := horig.storedOK p st j he
  exact hhs _ doneIdx hev

/-- All `prefixTerms` of a reachable trace of length `≤ n` have timestamps below `n` when its
visible entries do. -/
theorem cbadG2_stampsLt_prefixTerms (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (r : ProtocolSetup) {tr : ExecTrace} {vis : List VisEntry} {n : Nat}
    (hreach : tr.Reachable reachability) (hlen : tr.length ≤ n)
    (hvis : ∀ v ∈ vis, VisStampsLt interpretation S g n v) :
    ∀ t ∈ prefixTerms r tr vis, StampsLt interpretation S g n t := by
  have htr := TR.FreshSigma.traceEntriesLt_of_reachable interpretation S g n hreach hlen
  have hx := g2s_sidLt_of_reachable interpretation S g n hreach hlen
  intro t ht
  simp only [prefixTerms, principalTerms, plaintextTerms, storedSecrets, storedStates,
    DY.ExecTrace.getLocalStateAt, Option.map_map, List.mem_append,
    List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_filterMap,
    Option.map_eq_some_iff] at ht
  rcases ht with ((⟨v, ⟨hv, _⟩, ht⟩ | ⟨ls, ⟨j, _, e, he, rfl⟩, rfl⟩) | ⟨j, _, e, he, rfl⟩) |
    ⟨v, ⟨hv, _⟩, ht⟩
  · exact (hvis v hv).1 t ht
  · exact g2s_stampsLt_serialize_tr _ _ _ _ (TR.FreshSigma.traceEntriesLt_at?_st htr he)
      (hx j e he)
  · exact g2s_stampsLt_serialize_pq _ _ _ _ (TR.FreshSigma.traceEntriesLt_at?_pqst htr he)
  · exact (hvis v hv).1 t ht

theorem cbadG2_stampsLt_bobDoneBaseKeys_of_reachable (interpretation : ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) {tr : ExecTrace} {n : Nat}
    (hreach : tr.Reachable reachability) (hlen : tr.length ≤ n) :
    ∀ ek ∈ bobDoneBaseKeys tr, StampsLt interpretation S g n ek := by
  have hx := g2b_bobDoneEk_stampsLt_of_reachable interpretation S g n hreach hlen
  intro ek hek
  simp only [bobDoneBaseKeys, List.mem_filterMap] at hek
  obtain ⟨j, _, hj⟩ := hek
  split at hj
  · next hev => cases hj; exact hx j _ _ _ _ _ _ _ _ _ _ hev
  · cases hj

end Symbolic.Swarm.CREF
