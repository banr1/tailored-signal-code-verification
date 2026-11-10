/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import DY.Trace.Basic
import DY.Trace.Monad
import DY.ALaCarte.Basic
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.EquationalTheory.DiffieHellman
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Timestamp Bounds Along Reachable Composed Traces

Establishes `TracefulLt` across all composed protocol transitions and proves
`traceEntriesLt_of_reachable`: every entry of a reachable trace of length at most `ts` has random
timestamps strictly below `ts`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR.FreshSigma

cref_open
open Symbolic.Swarm.CREF.TR
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg parseTrSignalMsg spqrB2A)
open DY.Libsignal.TripleRatchet (RecvChain SessionInfo KeyComponent KeyDir hmac createChain kdfCk
  zeroSalt consumeMessageKey findRecvChain setRecvChain recvChainFor)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent KeyKind BundleHandles BobKeyHandles
  PreKeyMsgHandles HandshakeKeys AliceHandshakeOut BobHandshakeOut agree pqxdhIkm pqxdhKdf
  pqxdhLabel aliceAgreement bobAgreement extractDhSecretKey serializedIk)

/-! ## `TracefulLt` combinators and primitive steps -/

def TracefulLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat)
    {α : Type} (Q : α → Prop) (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, (x.run tr).2.val.length ≤ ts → TraceEntriesLt i S g ts tr →
    TraceEntriesLt i S g ts (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q a

theorem TracefulLt.pure {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {α : Type} {Q : α → Prop} {a : α} (ha : Q a) : TracefulLt i S g ts Q (pure a) := by
  unfold TracefulLt
  intro tr _ htr; simp only [Traceful.run_pure]; refine ⟨htr, fun b hb => ?_⟩; cases hb; exact ha

theorem TracefulLt.failure {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {α : Type} {Q : α → Prop} : TracefulLt i S g ts Q (failure : Traceful α) := by
  unfold TracefulLt
  intro tr _ htr; simp only [Traceful.run_failure]; refine ⟨htr, fun _ hb => by cases hb⟩

theorem TracefulLt.bind {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {α β : Type} {Q₁ : α → Prop} {Q₂ : β → Prop} {x : Traceful α} {f : α → Traceful β}
    (hx : TracefulLt i S g ts Q₁ x) (hf : ∀ a, Q₁ a → TracefulLt i S g ts Q₂ (f a)) :
    TracefulLt i S g ts Q₂ (x >>= f) := by
  intro tr hlen htr
  rw [run_bind_snd] at hlen ⊢
  rw [run_bind_fst]
  revert hlen
  cases h1 : (x.run tr).1 with
  | none =>
    intro hlen
    exact ⟨(hx tr hlen htr).1, fun _ hb => by cases hb⟩
  | some a =>
    intro hlen
    have hle2 : (x.run tr).2.val.length ≤ ((f a).run (x.run tr).2.val).2.val.length :=
      DY.Trace.length_le _ _ ((f a).run (x.run tr).2.val).2.property
    have h1' := hx tr (Nat.le_trans hle2 hlen) htr
    exact hf a (h1'.2 a h1) (x.run tr).2.val hlen h1'.1

theorem TracefulLt.guardP {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (p : Prop) {_ : Decidable p} : TracefulLt i S g ts (fun _ => True) (@_root_.guard Traceful _ p _) := by
  unfold _root_.guard; split
  · exact TracefulLt.pure trivial
  · exact TracefulLt.failure

theorem TracefulLt.guardTrace {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (p : ExecTrace → Bool) :
    TracefulLt i S g ts (fun _ => True) (DY.Libsignal.TripleRatchet.guardTrace p) := by
  unfold TracefulLt DY.Libsignal.TripleRatchet.guardTrace
  intro tr _ htr; simp only [Traceful.run_mk]; exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulLt.requireTracePredicate {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (p : ExecTrace → Bool) :
    TracefulLt i S g ts (fun _ => True) (DY.Libsignal.PQXDH.guardTrace p) := by
  unfold TracefulLt DY.Libsignal.PQXDH.guardTrace
  intro tr _ htr
  by_cases hp : p tr = true <;> simp only [Traceful.run_mk, hp, Bool.false_eq_true, ↓reduceIte] <;>
    exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulLt.traceLength {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} :
    TracefulLt i S g ts (fun _ => True) DY.Libsignal.TripleRatchet.traceLength := by
  unfold TracefulLt DY.Libsignal.TripleRatchet.traceLength
  intro tr _ htr; simp only [Traceful.run_mk]; exact ⟨htr, fun _ _ => trivial⟩

theorem TracefulLt.getEntry_net {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (j : Nat) : TracefulLt i S g ts (fun e : Network.ExecEntryT => StampsLt i S g ts e.msg) (DY.getEntry j) := by
  unfold TracefulLt
  intro tr _ htr; simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  refine ⟨htr, fun e he => traceEntriesLt_at?_net htr he⟩

theorem TracefulLt.getEntry_st {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (j : Nat) : TracefulLt i S g ts (fun e : StEntry => StateStampsLt i S g ts e.st.state) (DY.getEntry j) := by
  unfold TracefulLt
  intro tr _ htr; simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  refine ⟨htr, fun e he => traceEntriesLt_at?_st htr he⟩

theorem TracefulLt.getEntry_tr {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (j : Nat) : TracefulLt i S g ts (fun e : TREntry => EventStampsLt i S g ts e.ev) (DY.getEntry j) := by
  unfold TracefulLt
  intro tr _ htr; simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  refine ⟨htr, fun e he => traceEntriesLt_at?_tr htr he⟩

theorem TracefulLt.getEntry_pqst {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (j : Nat) : TracefulLt i S g ts (fun e : PQStEntry => StampsLt i S g ts e.st.state.sk) (DY.getEntry j) := by
  unfold TracefulLt
  intro tr _ htr; simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  refine ⟨htr, fun e he => traceEntriesLt_at?_pqst htr he⟩

theorem TracefulLt.getEntry_pqev {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (j : Nat) : TracefulLt i S g ts (fun e : PQEvEntry => PQEventStampsLt i S g ts e.ev) (DY.getEntry j) := by
  unfold TracefulLt
  intro tr _ htr; simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  refine ⟨htr, fun e he => traceEntriesLt_at?_pqev htr he⟩

theorem TracefulLt.receiveMessage {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (j : Nat) : TracefulLt i S g ts (StampsLt i S g ts) (Network.receiveMessage j) := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact TracefulLt.bind (TracefulLt.getEntry_net j) fun _ he => TracefulLt.pure he

theorem TracefulLt.getLocalState {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (p : Participant) (j : Nat) :
    TracefulLt i S g ts (StateStampsLt i S g ts) (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine TracefulLt.bind
    (TracefulLt.bind (TracefulLt.getEntry_st j) fun _ he =>
      TracefulLt.pure (Q := fun ls : PersistentLocalState.LocalState TRState => StateStampsLt i S g ts ls.state) he)
    fun _ hst => ?_
  exact TracefulLt.bind (TracefulLt.guardP _) fun _ _ => TracefulLt.pure hst

theorem TracefulLt.getPQLocalState {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (p : Participant) (j : Nat) :
    TracefulLt i S g ts (fun s : PQXDHState => StampsLt i S g ts s.sk)
      (PersistentLocalState.getLocalState p j) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine TracefulLt.bind
    (TracefulLt.bind (TracefulLt.getEntry_pqst j) fun _ he =>
      TracefulLt.pure (Q := fun ls : PersistentLocalState.LocalState PQXDHState =>
        StampsLt i S g ts ls.state.sk) he)
    fun _ hst => TracefulLt.bind (TracefulLt.guardP _) fun _ _ => TracefulLt.pure hst

theorem TracefulLt.getKey {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (p : Participant) (stateIdx : Nat) (kind : KeyKind) :
    TracefulLt i S g ts (StampsLt i S g ts) (DY.Libsignal.PQXDH.getKey p stateIdx kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact TracefulLt.bind (TracefulLt.getPQLocalState p stateIdx) fun _ hst =>
    TracefulLt.bind (TracefulLt.guardP _) fun _ _ => TracefulLt.pure hst

theorem TracefulLt.lookupIdentity {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (p : Participant) (regIdx : Nat) :
    TracefulLt i S g ts
      (fun kv : DY.Bytes × DY.Bytes => StampsLt i S g ts kv.1 ∧ StampsLt i S g ts kv.2)
      (DY.Libsignal.PQXDH.lookupIdentity p regIdx) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine TracefulLt.bind (TracefulLt.getEntry_pqev regIdx) fun e he => ?_
  cases hev : e.ev with
  | IdentityRegistered p' ikPk vkPk honest =>
    rw [hev] at he
    exact TracefulLt.bind (TracefulLt.guardP (p' = p)) fun _ _ => TracefulLt.pure he
  | _ => exact TracefulLt.failure

theorem baseAttackerKnows_append_network (tr : ExecTrace) (msg b : DY.Bytes) :
    DY.Trace.BaseAttackerKnows (tr.append (Network.ExecEntryT.mk msg)) b ↔
      b = msg ∨ DY.Trace.BaseAttackerKnows tr b := by
  let e' : ExecTrace.Entry := TraceEntryHas.inj (Network.ExecEntryT.mk msg)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e' b = (b = msg) :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e' b).trans
      (Symbolic.DYBridge.DY.Network.baseAttackerKnowledge_attackerKnows tr (Network.ExecEntryT.mk msg) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]

theorem baseAttackerKnows_append_random (tr : ExecTrace) (n : Nat) (b : DY.Bytes) :
    DY.Trace.BaseAttackerKnows (tr.append (DY.Random.ExecEntryT.mk n)) b ↔
      DY.Trace.BaseAttackerKnows tr b := by
  let e' : ExecTrace.Entry := TraceEntryHas.inj (DY.Random.ExecEntryT.mk n)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e' b = False :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e' b).trans
      (Symbolic.DYBridge.DY.Random.baseAttackerKnowledge_attackerKnows tr (DY.Random.ExecEntryT.mk n) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)

theorem baseAttackerKnows_append_tr (tr : ExecTrace) (ev : TREvent) (b : DY.Bytes) :
    DY.Trace.BaseAttackerKnows (tr.append (⟨ev⟩ : TREntry)) b ↔
      DY.Trace.BaseAttackerKnows tr b := by
  let e' : ExecTrace.Entry := TraceEntryHas.inj (⟨ev⟩ : TREntry)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e' b = False :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e' b).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows TREvent tr (⟨ev⟩ : TREntry) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)

theorem baseAttackerKnows_append_st (tr : ExecTrace) (e : StEntry) (b : DY.Bytes) :
    DY.Trace.BaseAttackerKnows (tr.append e) b ↔
      DY.Trace.BaseAttackerKnows tr b := by
  let e' : ExecTrace.Entry := TraceEntryHas.inj e
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e' b = False :=
    (((Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e' b).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.CompromisableState.baseAttackerKnowledge.internal TRState) tr e'.entry b)).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.State.baseAttackerKnowledge.internal TRState) tr e'.entry.entry b)).trans
      (Symbolic.DYBridge.DY.PersistentGlobalState.State.baseAttackerKnowledge_attackerKnows
        (PersistentLocalState.LocalState TRState) tr e b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)

theorem baseAttackerKnows_append_pqst (tr : ExecTrace) (e : PQStEntry) (b : DY.Bytes) :
    DY.Trace.BaseAttackerKnows (tr.append e) b ↔
      DY.Trace.BaseAttackerKnows tr b := by
  let e' : ExecTrace.Entry := TraceEntryHas.inj e
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e' b = False :=
    (((Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e' b).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.CompromisableState.baseAttackerKnowledge.internal PQXDHState) tr e'.entry b)).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.State.baseAttackerKnowledge.internal PQXDHState) tr e'.entry.entry b)).trans
      (Symbolic.DYBridge.DY.PersistentGlobalState.State.baseAttackerKnowledge_attackerKnows
        (PersistentLocalState.LocalState PQXDHState) tr e b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)

theorem baseAttackerKnows_append_pqev (tr : ExecTrace) (ev : PQXDHEvent) (b : DY.Bytes) :
    DY.Trace.BaseAttackerKnows (tr.append (⟨ev⟩ : PQEvEntry)) b ↔
      DY.Trace.BaseAttackerKnows tr b := by
  let e' : ExecTrace.Entry := TraceEntryHas.inj (⟨ev⟩ : PQEvEntry)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e' b = False :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e' b).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows PQXDHEvent tr (⟨ev⟩ : PQEvEntry) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)

theorem baseAttackerKnows_append_cev (tr : ExecTrace) (ev : ComposedEvent) (b : DY.Bytes) :
    DY.Trace.BaseAttackerKnows (tr.append (⟨ev⟩ : CEvEntry)) b ↔
      DY.Trace.BaseAttackerKnows tr b := by
  let e' : ExecTrace.Entry := TraceEntryHas.inj (⟨ev⟩ : CEvEntry)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e' b = False :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e' b).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows ComposedEvent tr (⟨ev⟩ : CEvEntry) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)

theorem TracefulLt.genRand {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (n : Nat) : TracefulLt i S g ts (StampsLt i S g ts) (DY.Random.genRand n) := by
  unfold TracefulLt
  intro tr hlen htr
  have hg1 : ((DY.Random.genRand n).run tr).1 = some (randTerm tr.length n) := by
    rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      run_bind_fst, Traceful.run_mk]
    dsimp only; rw [Traceful.run_pure]; rfl
  have hg2 : ((DY.Random.genRand n).run tr).2.val = tr.append (DY.Random.ExecEntryT.mk n) := by
    rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      run_bind_snd, Traceful.run_mk]
    dsimp only; rw [Traceful.run_pure]
  rw [hg2] at hlen ⊢; rw [hg1]
  have hlt : tr.length < ts := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hlen; omega
  refine ⟨traceEntriesLt_append
    (fun b hb => htr.1 b ((baseAttackerKnows_append_random tr n b).mp hb))
    ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h),
     (fun _ h => by cases h), (fun _ h => by cases h)⟩ htr, ?_⟩
  intro a ha; injection ha with ha; subst ha
  exact stampsLt_rand_of_lt i S g n hlt

private theorem proj_inj {E : Type} [ExecTraceTypes.Has E] (e : E) :
    (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by
  rw [TraceEntryHas.inj_proj_eq]

theorem TracefulLt.sendMessage {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {msg : DY.Bytes} (hm : StampsLt i S g ts msg) :
    TracefulLt i S g ts (fun _ => True) (Network.sendMessage msg) := by
  unfold TracefulLt
  intro tr _ htr
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_mk]
  refine ⟨traceEntriesLt_append
    (fun b hb => ?_)
    ⟨(fun e h => by rw [proj_inj] at h; injection h with h; subst h; exact hm),
     (fun _ h => by cases h), (fun _ h => by cases h),
     (fun _ h => by cases h), (fun _ h => by cases h)⟩ htr, fun _ _ => trivial⟩
  rcases (baseAttackerKnows_append_network tr msg b).mp hb with rfl | hb'
  · exact hm
  · exact htr.1 b hb'

theorem TracefulLt.storeLocalState {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (p : Participant) {st : TRState} (hst : StateStampsLt i S g ts st) :
    TracefulLt i S g ts (fun _ => True) (PersistentLocalState.storeLocalState p st) := by
  unfold TracefulLt
  intro tr _ htr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  refine ⟨traceEntriesLt_append
    (fun b hb => htr.1 b ((baseAttackerKnows_append_st tr ⟨⟨p, st⟩⟩ b).mp hb))
    ⟨(fun _ h => by cases h),
     (fun e h => by rw [proj_inj] at h; injection h with h; subst h; exact hst),
     (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulLt.storePQLocalState {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (p : Participant) {st : PQXDHState} (hsk : StampsLt i S g ts st.sk) :
    TracefulLt i S g ts (fun _ => True) (PersistentLocalState.storeLocalState p st) := by
  unfold TracefulLt
  intro tr _ htr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  refine ⟨traceEntriesLt_append
    (fun b hb => htr.1 b ((baseAttackerKnows_append_pqst tr ⟨⟨p, st⟩⟩ b).mp hb))
    ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h),
     (fun e h => by rw [proj_inj] at h; injection h with h; subst h; exact hsk),
     (fun _ h => by cases h)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulLt.logEvent {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {ev : TREvent} (hev : EventStampsLt i S g ts ev) :
    TracefulLt i S g ts (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulLt
  intro tr _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  refine ⟨traceEntriesLt_append
    (fun b hb => htr.1 b ((baseAttackerKnows_append_tr tr ev b).mp hb))
    ⟨(fun _ h => by cases h), (fun _ h => by cases h),
     (fun e h => by rw [proj_inj] at h; injection h with h; subst h; exact hev),
     (fun _ h => by cases h), (fun _ h => by cases h)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulLt.logPQEvent {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {ev : PQXDHEvent} (hev : PQEventStampsLt i S g ts ev) :
    TracefulLt i S g ts (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulLt
  intro tr _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  refine ⟨traceEntriesLt_append
    (fun b hb => htr.1 b ((baseAttackerKnows_append_pqev tr ev b).mp hb))
    ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h),
     (fun _ h => by cases h),
     (fun e h => by rw [proj_inj] at h; injection h with h; subst h; exact hev)⟩ htr,
    fun _ _ => trivial⟩

theorem TracefulLt.logCEvent {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (ev : ComposedEvent) :
    TracefulLt i S g ts (fun _ => True) (DY.ProtocolEvent.logEvent ev) := by
  unfold TracefulLt
  intro tr _ htr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  refine ⟨traceEntriesLt_append
    (fun b hb => htr.1 b ((baseAttackerKnows_append_cev tr ev b).mp hb))
    ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h),
     (fun _ h => by cases h), (fun _ h => by cases h)⟩ htr,
    fun _ _ => trivial⟩

/-! ## Triple Ratchet helpers and transitions -/

def TRSignalMsgStampsLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat)
    (msg : TRSignalMsg) : Prop :=
  StampsLt i S g ts msg.wire ∧ StampsLt i S g ts msg.mac ∧
  StampsLt i S g ts msg.ratchetKey ∧ StampsLt i S g ts msg.ciphertext ∧
  StampsLt i S g ts msg.pqRatchet

theorem stampsLt_parseTrSignalMsg {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {t : DY.Bytes} {msg : TRSignalMsg} (ht : StampsLt i S g ts t) (hp : parseTrSignalMsg t = some msg) :
    TRSignalMsgStampsLt i S g ts msg := by
  unfold parseTrSignalMsg at hp
  simp only [bind, Option.bind] at hp
  split at hp <;> try cases hp
  next p hsp =>
  rcases p with ⟨wire, mac⟩
  have hcat := DY.Concat.concat_split t (t.length - DY.Trunc.trunc8Length) wire mac hsp
  rw [← hcat] at ht
  obtain ⟨hw, hm⟩ := (stampsLt_concat_pack i S g ts ⟨wire, mac⟩).mp ht
  dsimp only at hp
  split at hp <;> try cases hp
  next x hx =>
  have hpv := DY.Bytes.pack_view? DY.TrWire.TrWireMsg.SubF wire
  change wire.view? DY.TrWire.TrWireMsg.SubF = some x at hx
  rw [hx] at hpv
  have hwf := hw; rw [← hpv] at hwf
  have h3 := (stampsLt_trWire_pack i S g ts x).mp hwf
  exact ⟨hw, hm, h3.1, h3.2.1, h3.2.2⟩

theorem TracefulLt.receiveSignalMsg {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (msgIdx : Nat) :
    TracefulLt i S g ts (TRSignalMsgStampsLt i S g ts)
      (DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine TracefulLt.bind (TracefulLt.receiveMessage msgIdx) fun t ht => ?_
  split
  · next msg hp =>
    exact TracefulLt.bind (TracefulLt.guardP _) fun _ _ =>
      TracefulLt.pure (stampsLt_parseTrSignalMsg ht hp)
  · exact TracefulLt.failure

def ChainStampsLt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (c : RecvChain) : Prop :=
  StampsLt i S g ts c.ratchetKey ∧ StampsLt i S g ts c.chainKey

theorem stampsLt_findRecvChain {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {st : TRState} {pk : DY.Bytes} {c : RecvChain} (hst : StateStampsLt i S g ts st)
    (hf : findRecvChain st.recv pk = some c) : ChainStampsLt i S g ts c :=
  hst.2.2.2.2.2.2 c (List.mem_of_find?_eq_some hf)

theorem stampsLt_recvChainFor {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {st : TRState} {pk : DY.Bytes} {c : RecvChain} {b : Bool}
    (hst : StateStampsLt i S g ts st) (hpk : StampsLt i S g ts pk)
    (hr : recvChainFor st.toDRState pk = some (c, b)) : ChainStampsLt i S g ts c := by
  unfold recvChainFor at hr
  split at hr
  · next c' hf =>
    injection hr with hr; injection hr with hc _; subst hc
    exact stampsLt_findRecvChain hst hf
  · split at hr
    · cases hr
    · injection hr with hr; injection hr with hc _; subst hc
      exact ⟨hpk, (stampsLt_createChain hst.2.2.1 hpk hst.2.2.2.1).2⟩

theorem TracefulLt.dhRatchetStep {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {st : TRState} {pk : DY.Bytes} (hst : StateStampsLt i S g ts st) (hpk : StampsLt i S g ts pk) :
    TracefulLt i S g ts (fun p : TRState × RecvChain => StateStampsLt i S g ts p.1 ∧ ChainStampsLt i S g ts p.2)
      (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine TracefulLt.bind (TracefulLt.guardP _) fun _ _ => ?_
  refine TracefulLt.bind (TracefulLt.genRand 32) fun dhs hdhs => ?_
  have hc1 := stampsLt_createChain hst.2.2.1 hpk hst.2.2.2.1
  have hc2 := stampsLt_createChain hc1.1 hpk hdhs
  have hc_new : ChainStampsLt i S g ts
      { ratchetKey := pk, chainKey := (createChain st.rk pk st.dhs).2, index := 0, rIdx := st.rIdx + 2 } :=
    ⟨hpk, hc1.2⟩
  refine TracefulLt.pure ⟨⟨hst.1, hst.2.1, hc2.1, hdhs, hc2.2, hst.2.2.2.2.2.1, fun c' hc' => ?_⟩, hc_new⟩
  rcases List.mem_append.mp (List.mem_of_mem_drop hc') with hmem | hmem
  · exact hst.2.2.2.2.2.2 c' hmem
  · rcases List.mem_singleton.mp hmem with rfl
    exact hc_new

theorem TracefulLt.ensureReceiverChain {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {st : TRState} {pk : DY.Bytes} (hst : StateStampsLt i S g ts st) (hpk : StampsLt i S g ts pk) :
    TracefulLt i S g ts (fun p : TRState × RecvChain × Bool => StateStampsLt i S g ts p.1 ∧ ChainStampsLt i S g ts p.2.1)
      (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · next c hr => exact TracefulLt.pure ⟨hst, stampsLt_recvChainFor hst hpk hr⟩
  · exact TracefulLt.bind (TracefulLt.dhRatchetStep hst hpk) fun ⟨st', c⟩ h => TracefulLt.pure h
  · exact TracefulLt.failure

theorem stampsLt_consumeMessageKey {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (hc : ChainStampsLt i S g ts c) (hcm : consumeMessageKey c counter = some (seed, c')) :
    StampsLt i S g ts seed ∧ ChainStampsLt i S g ts c' := by
  unfold consumeMessageKey at hcm
  split at hcm <;> try cases hcm
  split at hcm <;> try cases hcm
  split at hcm <;> try cases hcm
  have hck := stampsLt_kdfCk (stampsLt_chainKeyAt (counter.toNat - c.index.toNat) hc.2)
  exact ⟨hck.2, hc.1, hck.1⟩

theorem stateStampsLt_setRecvChain {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {st : TRState} {c' : RecvChain} {spqr' : DY.Bytes}
    (hst : StateStampsLt i S g ts st) (hc' : ChainStampsLt i S g ts c')
    (hspqr' : StampsLt i S g ts spqr') :
    StateStampsLt i S g ts { st with recv := setRecvChain st.recv c', spqr := spqr' } := by
  refine ⟨hst.1, hst.2.1, hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2.1, hspqr', fun c hc => ?_⟩
  unfold setRecvChain at hc
  obtain ⟨c₀, hc₀, heq⟩ := List.mem_map.mp hc
  split at heq <;> subst heq
  · exact hc'
  · exact hst.2.2.2.2.2.2 c₀ hc₀

theorem TracefulLt.verifyMacAndDecrypt {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {st : TRState} {msg : TRSignalMsg} {pqSalt seed : DY.Bytes}
    (hmsg : TRSignalMsgStampsLt i S g ts msg) :
    TracefulLt i S g ts (StampsLt i S g ts)
      (DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  refine TracefulLt.bind (TracefulLt.guardP _) fun _ _ => ?_
  unfold TracefulLt
  intro tr _ htr
  dsimp [liftM, monadLift, MonadLift.monadLift]
  simp only [Traceful.run_mk]
  refine ⟨htr, fun m hm => stampsLt_symDec hm hmsg.2.2.2.1⟩

theorem TracefulLt.logSkippedKeys {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) (hpk : StampsLt i S g ts pk) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat),
      StampsLt i S g ts ck →
      TracefulLt i S g ts (fun _ => True)
        (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0, _ => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; exact TracefulLt.pure trivial
  | ck, n, k + 1, hck => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    have hkdf := stampsLt_kdfCk hck
    exact TracefulLt.bind (TracefulLt.logEvent ⟨hkdf.2, hpk⟩) fun _ _ =>
      TracefulLt.logSkippedKeys s pk rIdx src hpk (kdfCk ck).1 (n + 1) k hkdf.1

theorem TracefulLt.logMessageKeyAndStore {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (me : Participant) (s : SessionInfo) (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) {st : TRState} (hst : StateStampsLt i S g ts st) :
    TracefulLt i S g ts (fun _ => True)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact TracefulLt.bind (TracefulLt.logEvent trivial) fun _ _ =>
    TracefulLt.storeLocalState me hst

theorem TracefulLt.messageEncrypt {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    TracefulLt i S g ts (fun _ => True)
      (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine TracefulLt.bind (TracefulLt.getLocalState me stateIdx) fun st hst =>
    TracefulLt.bind (TracefulLt.guardP _) fun _ _ =>
    TracefulLt.bind (TracefulLt.genRand 32) fun m hm =>
    TracefulLt.bind (TracefulLt.genRand coinsLen) fun coins hcoins => ?_
  have hspqr := stampsLt_spqrSend hst.2.2.2.2.2.1 hcoins
  refine TracefulLt.bind (TracefulLt.sendMessage hspqr.2.1) fun _ _ =>
    TracefulLt.bind (TracefulLt.receiveMessage pqIdx) fun pqSalt hpqSalt =>
    TracefulLt.bind (TracefulLt.logEvent trivial) fun _ _ => ?_
  have hck := stampsLt_kdfCk hst.2.2.2.2.1
  have hkeys := stampsLt_trMsgKeys hpqSalt hck.2
  have hwire := stampsLt_trHonestWireMsg (stampsLt_dhPk hst.2.2.2.1) st.ns st.pn
    (stampsLt_symEnc hkeys.1 hkeys.2.2 hm) hspqr.2.2
  have hmac := stampsLt_computeMac hkeys.2.1 hst.1 hst.2.1 hwire
  exact TracefulLt.bind
    (TracefulLt.logMessageKeyAndStore me _ .sender _ _ _ _ _
      ⟨hst.1, hst.2.1, hst.2.2.1, hst.2.2.2.1, hck.1, hspqr.1, hst.2.2.2.2.2.2⟩)
    fun _ _ => TracefulLt.sendMessage (stampsLt_concat hwire hmac)

theorem TracefulLt.messageEncryptAbort {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (me : Participant) (stateIdx : Nat) :
    TracefulLt i S g ts (fun _ => True)
      (DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  exact TracefulLt.bind (TracefulLt.getLocalState me stateIdx) fun _ _ =>
    TracefulLt.bind (TracefulLt.genRand 32) fun _ _ => TracefulLt.failure

theorem TracefulLt.messageDecrypt {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (me : Participant) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulLt i S g ts (fun _ => True)
      (DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine TracefulLt.bind (TracefulLt.getLocalState me stateIdx) fun st₀ hst₀ =>
    TracefulLt.bind (TracefulLt.receiveSignalMsg msgIdx) fun msg hmsg =>
    TracefulLt.bind (TracefulLt.ensureReceiverChain hst₀ hmsg.2.2.1)
      fun ⟨st, c, ratcheted⟩ ⟨hst, hc⟩ => ?_
  dsimp only
  split
  · next seed c' hcm =>
    obtain ⟨hseed, hc'⟩ := stampsLt_consumeMessageKey hc hcm
    split
    · next spqr' key hspqr =>
      obtain ⟨hspqr', hkey⟩ := stampsLt_spqrRecv hst.2.2.2.2.2.1 hmsg.2.2.2.2 hspqr
      refine TracefulLt.bind (TracefulLt.sendMessage hkey) fun _ _ =>
        TracefulLt.bind (TracefulLt.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulLt.bind (TracefulLt.verifyMacAndDecrypt hmsg) fun m hm => ?_
      have hrest : TracefulLt i S g ts (fun _ => True)
          (do DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
                (msg.counter.toNat - c.index.toNat)
              DY.ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
              DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx stateIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
        TracefulLt.bind (TracefulLt.logSkippedKeys _ _ _ _ hmsg.2.2.1 _ _ _ hc.2) fun _ _ =>
          TracefulLt.bind (TracefulLt.logEvent hm) fun _ _ =>
            TracefulLt.logMessageKeyAndStore me _ .receiver _ _ _ _ _
              (stateStampsLt_setRecvChain hst hc' hspqr')
      split
      · exact TracefulLt.bind (TracefulLt.logEvent trivial) fun _ _ =>
          TracefulLt.bind (TracefulLt.logEvent trivial) fun _ _ => hrest
      · exact hrest
    · exact TracefulLt.failure
  · exact TracefulLt.failure

theorem TracefulLt.messageDecryptSkipped {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (me : Participant) (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulLt i S g ts (fun _ => True)
      (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine TracefulLt.bind (TracefulLt.getLocalState me stateIdx) fun st hst =>
    TracefulLt.bind (TracefulLt.receiveSignalMsg msgIdx) fun msg hmsg =>
    TracefulLt.bind (TracefulLt.getEntry_tr skippedKeyEventIdx) fun e _ => ?_
  split
  · refine TracefulLt.bind (TracefulLt.guardP _) fun _ _ =>
      TracefulLt.bind (TracefulLt.guardTrace _) fun _ _ => ?_
    split
    · next spqr' key hspqr =>
      obtain ⟨hspqr', hkey⟩ := stampsLt_spqrRecv hst.2.2.2.2.2.1 hmsg.2.2.2.2 hspqr
      exact TracefulLt.bind (TracefulLt.sendMessage hkey) fun _ _ =>
        TracefulLt.bind (TracefulLt.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulLt.bind (TracefulLt.verifyMacAndDecrypt hmsg) fun m hm =>
        TracefulLt.bind (TracefulLt.logEvent trivial) fun _ _ =>
        TracefulLt.bind (TracefulLt.logEvent hm) fun _ _ =>
        TracefulLt.logMessageKeyAndStore me _ .receiver _ _ _ _ _
          ⟨hst.1, hst.2.1, hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2.1, hspqr', hst.2.2.2.2.2.2⟩
    · exact TracefulLt.failure
  · exact TracefulLt.failure

theorem TracefulLt.exposeKey {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    TracefulLt i S g ts (fun _ => True) (DY.Libsignal.TripleRatchet.exposeKey me stateIdx k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine TracefulLt.bind (TracefulLt.getLocalState me stateIdx) fun st hst => ?_
  cases k with
  | rk => exact TracefulLt.bind (TracefulLt.logEvent trivial) fun _ _ => TracefulLt.sendMessage hst.2.2.1
  | dhs => exact TracefulLt.bind (TracefulLt.logEvent trivial) fun _ _ => TracefulLt.sendMessage hst.2.2.2.1
  | cks => exact TracefulLt.bind (TracefulLt.logEvent trivial) fun _ _ => TracefulLt.sendMessage hst.2.2.2.2.1
  | ckr pk =>
    dsimp only; split
    · next c hf =>
      exact TracefulLt.bind (TracefulLt.logEvent trivial) fun _ _ =>
        TracefulLt.sendMessage (stampsLt_findRecvChain hst hf).2
    · exact TracefulLt.failure

theorem TracefulLt.exposeSpqr {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (me : Participant) (stateIdx : Nat) :
    TracefulLt i S g ts (fun _ => True) (DY.Libsignal.TripleRatchet.exposeSpqr me stateIdx) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  refine TracefulLt.bind (TracefulLt.getLocalState me stateIdx) fun st hst => ?_
  exact TracefulLt.bind (TracefulLt.logEvent hst.2.2.2.2.2.1) fun _ _ =>
    TracefulLt.sendMessage hst.2.2.2.2.2.1

theorem TracefulLt.exposeSkipped {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (skippedKeyEventIdx : Nat) :
    TracefulLt i S g ts (fun _ => True) (DY.Libsignal.TripleRatchet.exposeSkipped skippedKeyEventIdx) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine TracefulLt.bind (TracefulLt.getEntry_tr skippedKeyEventIdx) fun e he => ?_
  split
  · next s pk n seed rIdx src heq =>
    rw [heq] at he
    have he' : StampsLt i S g ts seed ∧ StampsLt i S g ts pk := he
    exact TracefulLt.bind (TracefulLt.guardTrace _) fun _ _ =>
      TracefulLt.bind (TracefulLt.logEvent he'.1) fun _ _ =>
      TracefulLt.sendMessage he'.1
  · exact TracefulLt.failure

/-! ## PQXDH setup, threat-model, and session-start transitions -/

theorem TracefulLt.registerIdentity {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (p : Participant) :
    TracefulLt i S g ts (fun _ => True) (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  exact TracefulLt.bind (TracefulLt.requireTracePredicate _) fun _ _ =>
    TracefulLt.bind (TracefulLt.genRand 32) fun _ hik =>
    TracefulLt.bind (TracefulLt.logPQEvent ⟨stampsLt_dhPk hik, stampsLt_vk hik⟩) fun _ _ =>
    TracefulLt.bind (TracefulLt.sendMessage (stampsLt_dhPk hik)) fun _ _ =>
    TracefulLt.bind (TracefulLt.sendMessage (stampsLt_vk hik)) fun _ _ =>
    TracefulLt.storePQLocalState p hik

theorem TracefulLt.registerCorruptIdentity {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (p : Participant) (skIdx : Nat) :
    TracefulLt i S g ts (fun _ => True) (DY.Libsignal.PQXDH.registerCorruptIdentity p skIdx) := by
  unfold DY.Libsignal.PQXDH.registerCorruptIdentity
  exact TracefulLt.bind (TracefulLt.requireTracePredicate _) fun _ _ =>
    TracefulLt.bind (TracefulLt.receiveMessage skIdx) fun _ hik =>
    TracefulLt.bind (TracefulLt.logPQEvent ⟨stampsLt_dhPk hik, stampsLt_vk hik⟩) fun _ _ =>
    TracefulLt.logPQEvent trivial

theorem TracefulLt.genSignedPrekey {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (b : Participant) (idStateIdx : Nat) :
    TracefulLt i S g ts (fun _ => True) (DY.Libsignal.PQXDH.genSignedPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  exact TracefulLt.bind (TracefulLt.getKey b idStateIdx .identity) fun _ hik =>
    TracefulLt.bind (TracefulLt.genRand 32) fun _ hspk =>
    TracefulLt.bind (TracefulLt.genRand 64) fun _ hnonce =>
    TracefulLt.bind (TracefulLt.logPQEvent trivial) fun _ _ =>
    TracefulLt.bind (TracefulLt.storePQLocalState b hspk) fun _ _ =>
    TracefulLt.bind (TracefulLt.sendMessage (stampsLt_dhPk hspk)) fun _ _ =>
    TracefulLt.bind
      (TracefulLt.sendMessage
        (stampsLt_sign hik hnonce
          (stampsLt_concat (stampsLt_literalToBytes i S g ts _) (stampsLt_dhPk hspk))))
      fun _ _ => TracefulLt.pure trivial

theorem TracefulLt.genPQPrekey {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (b : Participant) (idStateIdx : Nat) :
    TracefulLt i S g ts (fun _ => True) (DY.Libsignal.PQXDH.genPQPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  exact TracefulLt.bind (TracefulLt.getKey b idStateIdx .identity) fun _ hik =>
    TracefulLt.bind (TracefulLt.genRand 64) fun _ hpqsk =>
    TracefulLt.bind (TracefulLt.genRand 64) fun _ hnonce =>
    TracefulLt.bind (TracefulLt.logPQEvent trivial) fun _ _ =>
    TracefulLt.bind (TracefulLt.storePQLocalState b hpqsk) fun _ _ =>
    TracefulLt.bind (TracefulLt.sendMessage (stampsLt_kemPk hpqsk)) fun _ _ =>
    TracefulLt.bind
      (TracefulLt.sendMessage
        (stampsLt_sign hik hnonce
          (stampsLt_concat (stampsLt_literalToBytes i S g ts _) (stampsLt_kemPk hpqsk))))
      fun _ _ => TracefulLt.pure trivial

theorem TracefulLt.genOneTimePrekey {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (b : Participant) :
    TracefulLt i S g ts (fun _ => True) (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  exact TracefulLt.bind (TracefulLt.genRand 32) fun _ hopk =>
    TracefulLt.bind (TracefulLt.logPQEvent trivial) fun _ _ =>
    TracefulLt.bind (TracefulLt.storePQLocalState b hopk) fun _ _ =>
    TracefulLt.bind (TracefulLt.sendMessage (stampsLt_dhPk hopk)) fun _ _ =>
    TracefulLt.pure trivial

theorem stampsLt_serializedIk {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {pk : DY.Bytes} (hpk : StampsLt i S g ts pk) :
    StampsLt i S g ts (serializedIk pk) :=
  stampsLt_concat (stampsLt_literalToBytes i S g ts _) hpk

theorem stampsLt_agree {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {pk sk : DY.Bytes} (hpk : StampsLt i S g ts pk) (hsk : StampsLt i S g ts sk) :
    StampsLt i S g ts (agree pk sk) :=
  stampsLt_dh (stampsLt_x25519Key hpk) hsk

theorem stampsLt_pqxdhIkm {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {dh1 dh2 dh3 : DY.Bytes} {dh4 : Option DY.Bytes} {ss : DY.Bytes}
    (h1 : StampsLt i S g ts dh1) (h2 : StampsLt i S g ts dh2) (h3 : StampsLt i S g ts dh3)
    (h4 : ∀ x, dh4 = some x → StampsLt i S g ts x) (hss : StampsLt i S g ts ss) :
    StampsLt i S g ts (pqxdhIkm dh1 dh2 dh3 dh4 ss) := by
  unfold pqxdhIkm
  refine stampsLt_concat (stampsLt_literalToBytes i S g ts _)
    (stampsLt_concat h1 (stampsLt_concat h2 (stampsLt_concat h3 ?_)))
  cases dh4 with
  | none => exact hss
  | some d => exact stampsLt_concat (h4 d rfl) hss

theorem stampsLt_pqxdhKdf {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {ikm : DY.Bytes} (hikm : StampsLt i S g ts ikm) :
    StampsLt i S g ts (pqxdhKdf ikm).rk ∧
    StampsLt i S g ts (pqxdhKdf ikm).ck ∧
    StampsLt i S g ts (pqxdhKdf ikm).pqr := by
  have hprk : StampsLt i S g ts (hmac zeroSalt ikm) :=
    stampsLt_hmac (stampsLt_literalToBytes i S g ts _) hikm
  have hinfo : StampsLt i S g ts pqxdhLabel := stampsLt_literalToBytes i S g ts _
  exact ⟨stampsLt_hkdfBlock1 hprk hinfo,
    stampsLt_hkdfBlock2 hprk hinfo,
    stampsLt_hkdfBlock3 hprk hinfo⟩

theorem stampsLt_aliceAgreement {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {ikA ek ikBPk spk pqpk : DY.Bytes} {opk : Option DY.Bytes} {entropy : DY.Bytes}
    (hikA : StampsLt i S g ts ikA) (hek : StampsLt i S g ts ek)
    (hikB : StampsLt i S g ts ikBPk) (hspk : StampsLt i S g ts spk)
    (hpqpk : StampsLt i S g ts pqpk) (hopk : ∀ o, opk = some o → StampsLt i S g ts o)
    (hent : StampsLt i S g ts entropy) :
    StampsLt i S g ts (aliceAgreement ikA ek ikBPk spk pqpk opk entropy).1 ∧
    StampsLt i S g ts (aliceAgreement ikA ek ikBPk spk pqpk opk entropy).2.rk ∧
    StampsLt i S g ts (aliceAgreement ikA ek ikBPk spk pqpk opk entropy).2.ck ∧
    StampsLt i S g ts (aliceAgreement ikA ek ikBPk spk pqpk opk entropy).2.pqr := by
  unfold aliceAgreement
  obtain ⟨hct, hss⟩ := stampsLt_kemEncap hpqpk hent
  have hikm : StampsLt i S g ts
      (pqxdhIkm (agree spk ikA) (agree ikBPk ek) (agree spk ek)
        (opk.map (agree · ek)) (DY.PQKem.kemEncap pqpk entropy).2) := by
    refine stampsLt_pqxdhIkm (stampsLt_agree hspk hikA) (stampsLt_agree hikB hek)
      (stampsLt_agree hspk hek) ?_ hss
    intro d hd
    cases opk with
    | none => cases hd
    | some o =>
      simp only [Option.map_some, Option.some.injEq] at hd
      subst hd
      exact stampsLt_agree (hopk o rfl) hek
  obtain ⟨hrk, hck, hpqr⟩ := stampsLt_pqxdhKdf hikm
  exact ⟨hct, hrk, hck, hpqr⟩

theorem stampsLt_bobAgreement {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {ikB spkSk pqsk : DY.Bytes} {opkSk : Option DY.Bytes} {ikAPk ek ct : DY.Bytes}
    {keys : HandshakeKeys}
    (hikB : StampsLt i S g ts ikB) (hspkSk : StampsLt i S g ts spkSk) (hpqsk : StampsLt i S g ts pqsk)
    (hopkSk : ∀ o, opkSk = some o → StampsLt i S g ts o)
    (hikA : StampsLt i S g ts ikAPk) (hek : StampsLt i S g ts ek) (hct : StampsLt i S g ts ct)
    (hba : bobAgreement ikB spkSk pqsk opkSk ikAPk ek ct = some keys) :
    StampsLt i S g ts keys.rk ∧ StampsLt i S g ts keys.ck ∧ StampsLt i S g ts keys.pqr := by
  have hdh4 : ∀ x, (opkSk.map fun o => agree ek o) = some x → StampsLt i S g ts x := by
    intro x hx; obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact stampsLt_agree hek (hopkSk o ho)
  rcases hdec : DY.PQKem.kemDecap pqsk ct with _ | ss
  · simp only [bobAgreement, DY.Libsignal.PQXDH.errToOption, hdec, Option.getD_none,
      Option.pure_def, Option.some.injEq] at hba
    subst hba
    exact stampsLt_pqxdhKdf (stampsLt_pqxdhIkm
      (stampsLt_agree hikA hspkSk) (stampsLt_agree hek hikB) (stampsLt_agree hek hspkSk)
      hdh4 (stampsLt_kemRejKey hpqsk hct))
  · simp only [bobAgreement, DY.Libsignal.PQXDH.errToOption, hdec, Option.getD_some,
      Option.pure_def, Option.some.injEq] at hba
    subst hba
    exact stampsLt_pqxdhKdf (stampsLt_pqxdhIkm
      (stampsLt_agree hikA hspkSk) (stampsLt_agree hek hikB) (stampsLt_agree hek hspkSk)
      hdh4 (stampsLt_kemDecap hdec hct))

def AliceHandshakeOk (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat)
    (o : AliceHandshakeOut) : Prop :=
  StampsLt i S g ts o.ikA ∧
  StampsLt i S g ts o.ikB ∧
  StampsLt i S g ts o.spk ∧
  StampsLt i S g ts o.pqpk ∧
  (∀ opk, o.opk = some opk → StampsLt i S g ts opk) ∧
  StampsLt i S g ts o.ek ∧
  StampsLt i S g ts o.ct ∧
  StampsLt i S g ts o.keys.rk ∧
  StampsLt i S g ts o.keys.ck ∧
  StampsLt i S g ts o.keys.pqr

theorem TracefulLt.aliceHandshake {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (a b : Participant) (idStateIdx regIdxB : Nat) (h : BundleHandles) :
    TracefulLt i S g ts (AliceHandshakeOk i S g ts)
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  apply TracefulLt.bind (TracefulLt.getKey a idStateIdx .identity); intro ikA hikA
  apply TracefulLt.bind (TracefulLt.lookupIdentity b regIdxB); intro p hkv
  rcases p with ⟨ikB, vkB⟩; dsimp only
  apply TracefulLt.bind (TracefulLt.receiveMessage h.spk); intro spk hspk
  apply TracefulLt.bind (TracefulLt.receiveMessage h.spkSig); intro _ _
  apply TracefulLt.bind (TracefulLt.receiveMessage h.pqpk); intro pqpk hpqpk
  apply TracefulLt.bind (TracefulLt.receiveMessage h.pqpkSig); intro _ _
  apply TracefulLt.bind (TracefulLt.guardP _); intro _ _
  apply TracefulLt.bind (TracefulLt.guardP _); intro _ _
  cases h.opk <;> dsimp only
  · apply TracefulLt.bind (TracefulLt.pure (Q := fun opk : Option DY.Bytes =>
        ∀ o, opk = some o → StampsLt i S g ts o) (fun _ h => by cases h)); intro opk hopk
    apply TracefulLt.bind (TracefulLt.genRand 32); intro ek hek
    apply TracefulLt.bind (TracefulLt.guardP _); intro _ _
    apply TracefulLt.bind (TracefulLt.guardP _); intro _ _
    apply TracefulLt.bind (TracefulLt.genRand 32); intro entropy hent
    obtain ⟨hct, hrk, hck, hpqr⟩ :=
      stampsLt_aliceAgreement hikA hek hkv.1 hspk hpqpk hopk hent
    exact TracefulLt.pure ⟨stampsLt_dhPk hikA, hkv.1, hspk, hpqpk, hopk,
      stampsLt_dhPk hek, hct, hrk, hck, hpqr⟩
  · apply TracefulLt.bind (TracefulLt.receiveMessage _); intro o ho
    apply TracefulLt.bind (TracefulLt.pure (Q := fun opk : Option DY.Bytes =>
        ∀ o', opk = some o' → StampsLt i S g ts o') (fun _ h => Option.some.inj h ▸ ho)); intro opk hopk
    apply TracefulLt.bind (TracefulLt.genRand 32); intro ek hek
    apply TracefulLt.bind (TracefulLt.guardP _); intro _ _
    apply TracefulLt.bind (TracefulLt.guardP _); intro _ _
    apply TracefulLt.bind (TracefulLt.genRand 32); intro entropy hent
    obtain ⟨hct, hrk, hck, hpqr⟩ :=
      stampsLt_aliceAgreement hikA hek hkv.1 hspk hpqpk hopk hent
    exact TracefulLt.pure ⟨stampsLt_dhPk hikA, hkv.1, hspk, hpqpk, hopk,
      stampsLt_dhPk hek, hct, hrk, hck, hpqr⟩

theorem TracefulLt.aliceStart {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (a b : Participant) (idStateIdx regIdxB : Nat) (h : BundleHandles) :
    TracefulLt i S g ts (fun _ => True)
      (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine TracefulLt.bind (TracefulLt.aliceHandshake a b idStateIdx regIdxB h) fun o ho =>
    TracefulLt.bind (TracefulLt.genRand 32) fun dhsA hdhsA =>
    TracefulLt.bind (TracefulLt.sendMessage ho.2.2.2.2.2.1) fun _ _ =>
    TracefulLt.bind (TracefulLt.sendMessage ho.2.2.2.2.2.2.1) fun _ _ =>
    TracefulLt.bind TracefulLt.traceLength fun _ _ =>
    TracefulLt.bind (TracefulLt.logPQEvent trivial) fun _ _ =>
    TracefulLt.bind (TracefulLt.logEvent trivial) fun _ _ =>
    TracefulLt.bind (TracefulLt.logCEvent _) fun _ _ => ?_
  rcases ho with ⟨hikA, hikB, hspk, _, _, _, _, hrk, hck, hpqr⟩
  have hc := stampsLt_createChain hrk hspk hdhsA
  have hspqrA := stampsLt_spqrInit hpqr (stampsLt_spqrParams i S g ts .a2b)
  refine TracefulLt.storeLocalState a
    ⟨stampsLt_serializedIk hikA, stampsLt_serializedIk hikB, hc.1, hdhsA, hc.2, hspqrA,
     fun c hmem => ?_⟩
  rcases List.mem_singleton.mp hmem with rfl
  exact ⟨hspk, hck⟩

def BobHandshakeOk (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat)
    (o : BobHandshakeOut) : Prop :=
  StampsLt i S g ts o.ikA ∧
  StampsLt i S g ts o.ikB ∧
  StampsLt i S g ts o.spkSk ∧
  StampsLt i S g ts o.keys.rk ∧
  StampsLt i S g ts o.keys.ck ∧
  StampsLt i S g ts o.keys.pqr ∧
  StampsLt i S g ts o.ek

theorem TracefulLt.bobHandshake {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (b a : Participant) (h : BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    TracefulLt i S g ts (BobHandshakeOk i S g ts)
      (DY.Libsignal.PQXDH.bobHandshake b a h regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  refine TracefulLt.bind (TracefulLt.getKey b h.ik .identity) fun ikB hikB =>
    TracefulLt.bind (TracefulLt.getKey b h.spk .signedPrekey) fun spkSk hspkSk =>
    TracefulLt.bind (TracefulLt.getKey b h.pqspk .pqPrekey) fun pqsk hpqsk => ?_
  cases h.opk <;> dsimp only
  · refine TracefulLt.bind (TracefulLt.pure (Q := fun opkSk : Option DY.Bytes =>
        ∀ o, opkSk = some o → StampsLt i S g ts o) (fun _ h => by cases h)) fun opkSk hopk =>
      TracefulLt.bind (TracefulLt.lookupIdentity a regIdxA) fun p hkv => ?_
    rcases p with ⟨ikA, vkA⟩; dsimp only
    refine TracefulLt.bind (TracefulLt.receiveMessage ekIdx) fun ek hek =>
      TracefulLt.bind (TracefulLt.receiveMessage ctIdx) fun ct hct =>
      TracefulLt.bind (TracefulLt.guardP _) fun _ _ => ?_
    split
    · next keys hba =>
      obtain ⟨hrk, hck, hpqr⟩ := stampsLt_bobAgreement hikB hspkSk hpqsk hopk hkv.1 hek hct hba
      exact TracefulLt.pure ⟨hkv.1, stampsLt_dhPk hikB, hspkSk, hrk, hck, hpqr, hek⟩
    · exact TracefulLt.failure
  · refine TracefulLt.bind (TracefulLt.getKey b _ .oneTimePrekey) fun o ho =>
      TracefulLt.bind (TracefulLt.pure (Q := fun opkSk : Option DY.Bytes =>
        ∀ o', opkSk = some o' → StampsLt i S g ts o') (fun _ h => Option.some.inj h ▸ ho)) fun opkSk hopk =>
      TracefulLt.bind (TracefulLt.lookupIdentity a regIdxA) fun p hkv => ?_
    rcases p with ⟨ikA, vkA⟩; dsimp only
    refine TracefulLt.bind (TracefulLt.receiveMessage ekIdx) fun ek hek =>
      TracefulLt.bind (TracefulLt.receiveMessage ctIdx) fun ct hct =>
      TracefulLt.bind (TracefulLt.guardP _) fun _ _ => ?_
    split
    · next keys hba =>
      obtain ⟨hrk, hck, hpqr⟩ := stampsLt_bobAgreement hikB hspkSk hpqsk hopk hkv.1 hek hct hba
      exact TracefulLt.pure ⟨hkv.1, stampsLt_dhPk hikB, hspkSk, hrk, hck, hpqr, hek⟩
    · exact TracefulLt.failure

theorem TracefulLt.bobStart {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat) (mh : PreKeyMsgHandles)
    (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulLt i S g ts (fun _ => True)
      (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine TracefulLt.bind (TracefulLt.bobHandshake b a kh regIdxA mh.ek mh.ct) fun o ho =>
    TracefulLt.bind (TracefulLt.receiveSignalMsg mh.msg) fun msg hmsg => ?_
  rcases ho with ⟨hikA, hikB, hspkSk, hrk, hck, hpqr, hek⟩
  have hst0 : StateStampsLt i S g ts
      { peer := a, myIk := serializedIk o.ikB, peerIk := serializedIk o.ikA, rk := o.keys.rk,
        dhs := o.spkSk, cks := o.keys.ck, ns := 0, pn := 0,
        sid := Concat.concat (DY.X25519.normalizeX25519Key msg.ratchetKey) o.keys.rk,
        initiator := false, rIdx := 0, recv := [],
        spqr := DY.Spqr.spqrInit o.keys.pqr spqrB2A } :=
    ⟨stampsLt_serializedIk hikB, stampsLt_serializedIk hikA, hrk, hspkSk, hck,
     stampsLt_spqrInit hpqr (stampsLt_spqrParams i S g ts .b2a),
     fun _ hmem => nomatch hmem⟩
  refine TracefulLt.bind (TracefulLt.ensureReceiverChain hst0 hmsg.2.2.1)
    fun r ⟨hst, hc⟩ => ?_
  rcases r with ⟨st, c, ratcheted⟩
  dsimp only
  split
  · next seed c' hcm =>
    obtain ⟨hseed, hc'⟩ := stampsLt_consumeMessageKey hc hcm
    split
    · next spqr' key hspqr =>
      obtain ⟨hspqr', hkey⟩ := stampsLt_spqrRecv hst.2.2.2.2.2.1 hmsg.2.2.2.2 hspqr
      refine TracefulLt.bind (TracefulLt.sendMessage hkey) fun _ _ =>
        TracefulLt.bind (TracefulLt.receiveMessage pqIdx) fun pqSalt _ =>
        TracefulLt.bind (TracefulLt.verifyMacAndDecrypt hmsg) fun m hm => ?_
      cases o.opk <;> dsimp only
      · refine TracefulLt.bind TracefulLt.traceLength fun doneIdx _ =>
          TracefulLt.bind (TracefulLt.logPQEvent hek) fun _ _ => ?_
        split
        · exact TracefulLt.bind (TracefulLt.logEvent trivial) fun _ _ =>
            TracefulLt.bind (TracefulLt.logEvent trivial) fun _ _ =>
            TracefulLt.bind (TracefulLt.logCEvent _) fun _ _ =>
            TracefulLt.bind TracefulLt.traceLength fun _ _ =>
            TracefulLt.bind (TracefulLt.logSkippedKeys _ _ _ _ hmsg.2.2.1 _ _ _ hc.2) fun _ _ =>
            TracefulLt.bind (TracefulLt.logEvent hm) fun _ _ =>
            TracefulLt.logMessageKeyAndStore b _ .receiver _ _ _ _ _
              (stateStampsLt_setRecvChain hst hc' hspqr')
        · exact TracefulLt.bind (TracefulLt.logCEvent _) fun _ _ =>
            TracefulLt.bind TracefulLt.traceLength fun _ _ =>
            TracefulLt.bind (TracefulLt.logSkippedKeys _ _ _ _ hmsg.2.2.1 _ _ _ hc.2) fun _ _ =>
            TracefulLt.bind (TracefulLt.logEvent hm) fun _ _ =>
            TracefulLt.logMessageKeyAndStore b _ .receiver _ _ _ _ _
              (stateStampsLt_setRecvChain hst hc' hspqr')
      · refine TracefulLt.bind (TracefulLt.requireTracePredicate _) fun _ _ =>
          TracefulLt.bind (TracefulLt.logPQEvent trivial) fun _ _ =>
          TracefulLt.bind TracefulLt.traceLength fun doneIdx _ =>
          TracefulLt.bind (TracefulLt.logPQEvent hek) fun _ _ => ?_
        split
        · exact TracefulLt.bind (TracefulLt.logEvent trivial) fun _ _ =>
            TracefulLt.bind (TracefulLt.logEvent trivial) fun _ _ =>
            TracefulLt.bind (TracefulLt.logCEvent _) fun _ _ =>
            TracefulLt.bind TracefulLt.traceLength fun _ _ =>
            TracefulLt.bind (TracefulLt.logSkippedKeys _ _ _ _ hmsg.2.2.1 _ _ _ hc.2) fun _ _ =>
            TracefulLt.bind (TracefulLt.logEvent hm) fun _ _ =>
            TracefulLt.logMessageKeyAndStore b _ .receiver _ _ _ _ _
              (stateStampsLt_setRecvChain hst hc' hspqr')
        · exact TracefulLt.bind (TracefulLt.logCEvent _) fun _ _ =>
            TracefulLt.bind TracefulLt.traceLength fun _ _ =>
            TracefulLt.bind (TracefulLt.logSkippedKeys _ _ _ _ hmsg.2.2.1 _ _ _ hc.2) fun _ _ =>
            TracefulLt.bind (TracefulLt.logEvent hm) fun _ _ =>
            TracefulLt.logMessageKeyAndStore b _ .receiver _ _ _ _ _
              (stateStampsLt_setRecvChain hst hc' hspqr')
    · exact TracefulLt.failure
  · exact TracefulLt.failure

theorem stampsLt_of_dhSkOf {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {pk sk : DY.Bytes} (h : extractDhSecretKey (DY.X25519.normalizeX25519Key pk) = some sk)
    (hpk : StampsLt i S g ts pk) :
    StampsLt i S g ts sk := by
  have hk := stampsLt_x25519Key hpk
  unfold DY.Libsignal.PQXDH.extractDhSecretKey at h
  split at h <;> try cases h
  next hx =>
  have hpv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF (DY.X25519.normalizeX25519Key pk)
  change (DY.X25519.normalizeX25519Key pk).view? DY.DiffieHellman.DhPk.SubF = some { sk := sk } at hx
  rw [hx] at hpv
  rw [← hpv] at hk
  exact (stampsLt_dhPk_pack i S g ts { sk := sk }).mp hk

theorem stampsLt_of_kemPkInvert {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {pk sk : DY.Bytes} (h : (DY.PQKem.invertKemPublicKey pk : Option DY.Bytes) = some sk)
    (hpk : StampsLt i S g ts pk) :
    StampsLt i S g ts sk := by
  unfold DY.PQKem.invertKemPublicKey at h
  split at h <;> try cases h
  next hx =>
  have hpv := DY.Bytes.pack_view? DY.PQKem.Pk.SubF pk
  change pk.view? DY.PQKem.Pk.SubF = some { sk := sk } at hx
  rw [hx] at hpv
  rw [← hpv] at hpk
  exact (stampsLt_kemPk_pack i S g ts { sk := sk }).mp hpk

theorem TracefulLt.compromiseIK {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (p : Participant) (stateIdx : Nat) :
    TracefulLt i S g ts (fun _ => True) (DY.Libsignal.PQXDH.compromiseIK p stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseIK
  exact TracefulLt.bind (TracefulLt.getKey p stateIdx .identity) fun _ hik =>
    TracefulLt.bind (TracefulLt.logPQEvent trivial) fun _ _ =>
    TracefulLt.sendMessage hik

theorem TracefulLt.compromiseSPK {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (b : Participant) (stateIdx : Nat) :
    TracefulLt i S g ts (fun _ => True) (DY.Libsignal.PQXDH.compromiseSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  exact TracefulLt.bind (TracefulLt.getKey b stateIdx .signedPrekey) fun _ hspk =>
    TracefulLt.bind (TracefulLt.logPQEvent trivial) fun _ _ =>
    TracefulLt.sendMessage hspk

theorem TracefulLt.compromisePQSPK {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (b : Participant) (stateIdx : Nat) :
    TracefulLt i S g ts (fun _ => True) (DY.Libsignal.PQXDH.compromisePQSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  exact TracefulLt.bind (TracefulLt.getKey b stateIdx .pqPrekey) fun _ hpqsk =>
    TracefulLt.bind (TracefulLt.logPQEvent trivial) fun _ _ =>
    TracefulLt.sendMessage hpqsk

theorem TracefulLt.compromiseOPK {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (b : Participant) (stateIdx : Nat) :
    TracefulLt i S g ts (fun _ => True) (DY.Libsignal.PQXDH.compromiseOPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  exact TracefulLt.bind (TracefulLt.getKey b stateIdx .oneTimePrekey) fun _ hopk =>
    TracefulLt.bind (TracefulLt.requireTracePredicate _) fun _ _ =>
    TracefulLt.bind (TracefulLt.logPQEvent trivial) fun _ _ =>
    TracefulLt.sendMessage hopk

theorem TracefulLt.breakDH {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} :
    TracefulLt i S g ts (fun _ => True) DY.Libsignal.PQXDH.breakDH := by
  unfold DY.Libsignal.PQXDH.breakDH
  exact TracefulLt.logPQEvent trivial

theorem TracefulLt.breakKEM {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} :
    TracefulLt i S g ts (fun _ => True) DY.Libsignal.PQXDH.breakKEM := by
  unfold DY.Libsignal.PQXDH.breakKEM
  exact TracefulLt.logPQEvent trivial

theorem TracefulLt.invertDH {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (pkIdx : Nat) :
    TracefulLt i S g ts (fun _ => True) (DY.Libsignal.PQXDH.invertDH pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertDH
  refine TracefulLt.bind (TracefulLt.requireTracePredicate _) fun _ _ =>
    TracefulLt.bind (TracefulLt.receiveMessage pkIdx) fun pk hpk => ?_
  rcases hdh : extractDhSecretKey (DY.X25519.normalizeX25519Key pk) with _ | sk
  · exact TracefulLt.failure
  · exact TracefulLt.sendMessage (stampsLt_of_dhSkOf hdh hpk)

theorem TracefulLt.invertKEM {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (pkIdx : Nat) :
    TracefulLt i S g ts (fun _ => True) (DY.Libsignal.PQXDH.invertKEM pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertKEM
  refine TracefulLt.bind (TracefulLt.requireTracePredicate _) fun _ _ =>
    TracefulLt.bind (TracefulLt.receiveMessage pkIdx) fun pk hpk =>
    TracefulLt.bind (Q₁ := StampsLt i S g ts) ?_ fun _ hsk => TracefulLt.sendMessage hsk
  unfold TracefulLt
  intro _ _ htr
  dsimp [liftM, monadLift, MonadLift.monadLift]
  simp only [Traceful.run_mk]
  exact ⟨htr, fun _ hsk => stampsLt_of_kemPkInvert hsk hpk⟩

/-! ## Reachability preservation -/

theorem traceEntriesLt_step {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    (input : reachability.Input) (tr : ExecTrace) (hpre : reachability.PreCond input tr)
    (hlen : (((reachability.step input).snd).run tr).2.val.length ≤ ts)
    (htr : TraceEntriesLt i S g ts tr) :
    TraceEntriesLt i S g ts (((reachability.step input).snd).run tr).2.val := by
  rcases input with ⟨⟨k, hk⟩, inp⟩
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k'
  · exact (TracefulLt.sendMessage (traceEntriesLt_knows htr hpre) tr hlen htr).1
  · exact (TracefulLt.registerIdentity inp tr hlen htr).1
  · rcases inp with ⟨p, skIdx⟩
    exact (TracefulLt.registerCorruptIdentity p skIdx tr hlen htr).1
  · rcases inp with ⟨b, idStateIdx⟩
    exact (TracefulLt.genSignedPrekey b idStateIdx tr hlen htr).1
  · rcases inp with ⟨b, idStateIdx⟩
    exact (TracefulLt.genPQPrekey b idStateIdx tr hlen htr).1
  · exact (TracefulLt.genOneTimePrekey inp tr hlen htr).1
  · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩
    exact (TracefulLt.aliceStart a b idStateIdx regIdxB bh tr hlen htr).1
  · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩
    exact (TracefulLt.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx tr hlen htr).1
  · rcases inp with ⟨me, stH, coinsLen, pqIdx⟩
    exact (TracefulLt.messageEncrypt me stH coinsLen pqIdx tr hlen htr).1
  · rcases inp with ⟨me, stH⟩
    exact (TracefulLt.messageEncryptAbort me stH tr hlen htr).1
  · rcases inp with ⟨me, stH, msgH, pqIdx, spqrMsgIdx⟩
    exact (TracefulLt.messageDecrypt me stH msgH pqIdx spqrMsgIdx tr hlen htr).1
  · rcases inp with ⟨me, stH, msgH, evH, pqIdx, spqrMsgIdx⟩
    exact (TracefulLt.messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx tr hlen htr).1
  · rcases inp with ⟨me, stH, comp⟩
    exact (TracefulLt.exposeKey me stH comp tr hlen htr).1
  · rcases inp with ⟨me, stH⟩
    exact (TracefulLt.exposeSpqr me stH tr hlen htr).1
  · exact (TracefulLt.exposeSkipped inp tr hlen htr).1
  · rcases inp with ⟨p, stateIdx⟩
    exact (TracefulLt.compromiseIK p stateIdx tr hlen htr).1
  · rcases inp with ⟨b, stateIdx⟩
    exact (TracefulLt.compromiseSPK b stateIdx tr hlen htr).1
  · rcases inp with ⟨b, stateIdx⟩
    exact (TracefulLt.compromisePQSPK b stateIdx tr hlen htr).1
  · rcases inp with ⟨b, stateIdx⟩
    exact (TracefulLt.compromiseOPK b stateIdx tr hlen htr).1
  · exact (TracefulLt.breakDH tr hlen htr).1
  · exact (TracefulLt.breakKEM tr hlen htr).1
  · exact (TracefulLt.invertDH inp tr hlen htr).1
  · exact (TracefulLt.invertKEM inp tr hlen htr).1
  · omega

/-- Every entry of a reachable trace of length `≤ ts` has random timestamps `< ts`. -/
theorem traceEntriesLt_of_reachable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat)
    {tr : ExecTrace} (hreach : tr.Reachable reachability) (hlen : tr.length ≤ ts) :
    TraceEntriesLt i S g ts tr := by
  induction hreach with
  | Base => exact traceEntriesLt_nil i S g ts
  | @Step tr₀ input hpre _ ih =>
    have hle : tr₀.length ≤ (((reachability.step input).snd).run tr₀).2.val.length :=
      DY.Trace.length_le _ _ (((reachability.step input).snd).run tr₀).2.property
    exact traceEntriesLt_step input tr₀ hpre hlen (ih (Nat.le_trans hle hlen))

end Symbolic.Swarm.CREF.TR.FreshSigma
