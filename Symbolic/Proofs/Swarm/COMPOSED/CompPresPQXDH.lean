/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Specifications.Model.EquationalTheory.Kem
public import Symbolic.Proofs.Swarm.COMPOSED.CompInvDefs
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
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
# Composed PQXDH-Side Invariant Preservation

Proves preservation of `SpqrInv` across the network, identity registration, prekey generation,
`aliceStart`, key compromise, cryptographic break, and public-key inversion transitions of
`DY.Libsignal.Composed`.
-/

@[expose] public section
set_option autoImplicit false
namespace Symbolic.Swarm.COMPOSED.CompPresPQXDH
open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.PQKem DY.Signature DY.X25519
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding x25519LowOrder
open DY.Libsignal.Composed
open Symbolic.Swarm.COMPOSED.CompKeyInversion
open Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.Swarm.COMPOSED.CompInv.CompPubInv
/-! ## Trace-Append Characterizations and Single-Entry Preservation -/
theorem proj_inj {E : Type} [ExecTraceTypes.Has E] (e : E) :
    (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by
  rw [TraceEntryHas.inj_proj_eq]
theorem at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]
theorem at?_append_eq {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    ((tr.append e).at? tr.length : Option E) = some e :=
  Trace.at?_append tr e
theorem randAt_here (tr : ExecTrace) (n : Nat) : RandAt (tr.append (RndE n)) tr.length n :=
  at?_append_eq tr (RndE n)
theorem netAt_here (tr : ExecTrace) (msg : Bytes) : NetAt (tr.append (NetE msg)) msg tr.length :=
  at?_append_eq tr (NetE msg)
private theorem append_len {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem eventLoggedAt_here {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    (tr : ExecTrace) (ev : Ev) :
    (tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT Ev)).EventLoggedAt ev tr.length := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  exact at?_append_eq tr (⟨ev⟩ : ProtocolEvent.ExecEntryT Ev)

theorem at?_append_cases {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    {tr : ExecTrace} {e : E1} {x : E2} {i : Nat}
    (h : ((tr.append e).at? i : Option E2) = some x) :
    (i < tr.length ∧ (tr.at? i : Option E2) = some x) ∨
    (i = tr.length ∧
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = some x) := by
  have hlt : i < (tr.append e).length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := E2) (tr.append e) i
    rw [h] at this; exact this
  have hlen : (tr.append e).length = tr.length + 1 := append_len tr e
  rcases (show i < tr.length ∨ i = tr.length by omega) with hi | rfl
  · rw [at?_append_of_lt tr e hi] at h
    exact .inl ⟨hi, h⟩
  · simp only [Trace.at?, hlt, ↓reduceDIte] at h
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte] at h
    exact .inr ⟨rfl, h⟩
theorem storedAt_append_st_iff {tr : ExecTrace} {me₀ me : Participant}
    {st₀ st : PQXDHState} {idx : Nat} :
    StoredAt (tr.append (StE me₀ st₀)) me st idx ↔
    (idx < tr.length ∧ StoredAt tr me st idx) ∨ (idx = tr.length ∧ me₀ = me ∧ st₀ = st) := by
  constructor
  · intro h
    rcases at?_append_cases h with ⟨hidx, h⟩ | ⟨rfl, hp⟩
    · exact .inl ⟨hidx, h⟩
    · rw [proj_inj] at hp
      injection hp with hp; injection hp with hp; injection hp with h1 h2
      exact .inr ⟨rfl, h1, h2⟩
  · rintro (⟨_, h⟩ | ⟨rfl, rfl, rfl⟩)
    · exact h.mono (Trace.append_le tr _)
    · exact at?_append_eq tr (StE me₀ st₀)
theorem storedAt_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    {me : Participant} {st : PQXDHState} {idx : Nat}
    (h : StoredAt (tr.append e) me st idx)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option StEntry) = none) :
    StoredAt tr me st idx := by
  rcases at?_append_cases h with ⟨_, h⟩ | ⟨_, hp⟩
  · exact h
  · rw [hnone] at hp; cases hp
theorem trStoredAt_append_trSt_iff {tr : ExecTrace} {me₀ me : Participant}
    {st₀ st : TRState} {idx : Nat} :
    TRStoredAt (tr.append (TRStE me₀ st₀)) me st idx ↔
    (idx < tr.length ∧ TRStoredAt tr me st idx) ∨ (idx = tr.length ∧ me₀ = me ∧ st₀ = st) := by
  constructor
  · intro h
    rcases at?_append_cases h with ⟨hidx, h⟩ | ⟨rfl, hp⟩
    · exact .inl ⟨hidx, h⟩
    · rw [proj_inj] at hp
      injection hp with hp; injection hp with hp; injection hp with h1 h2
      exact .inr ⟨rfl, h1, h2⟩
  · rintro (⟨_, h⟩ | ⟨rfl, rfl, rfl⟩)
    · exact h.mono (Trace.append_le tr _)
    · exact at?_append_eq tr (TRStE me₀ st₀)
theorem trStoredAt_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    {me : Participant} {st : TRState} {idx : Nat}
    (h : TRStoredAt (tr.append e) me st idx)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none) :
    TRStoredAt tr me st idx := by
  rcases at?_append_cases h with ⟨_, h⟩ | ⟨_, hp⟩
  · exact h
  · rw [hnone] at hp; cases hp
theorem eventLoggedAt_append_ev_iff {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr : ExecTrace} {ev₀ ev : Ev} {i : Nat} :
    (tr.append (⟨ev₀⟩ : ProtocolEvent.ExecEntryT Ev)).EventLoggedAt ev i ↔
    (i < tr.length ∧ tr.EventLoggedAt ev i) ∨ (i = tr.length ∧ ev₀ = ev) := by
  constructor
  · intro h
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h
    rcases at?_append_cases h with ⟨hi, h⟩ | ⟨rfl, hp⟩
    · exact .inl ⟨hi, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr h⟩
    · rw [proj_inj] at hp; injection hp with hp; injection hp with hp
      exact .inr ⟨rfl, hp⟩
  · rintro (⟨_, h⟩ | ⟨rfl, rfl⟩)
    · exact evAt_mono (Trace.append_le tr _) h
    · exact eventLoggedAt_here tr ev₀
theorem eventLoggedAt_append_other {E Ev : Type}
    [ExecTraceTypes.Has E] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr : ExecTrace} {e : E} {ev : Ev} {i : Nat}
    (h : (tr.append e).EventLoggedAt ev i)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT Ev)) = none) :
    tr.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  rcases at?_append_cases h with ⟨_, h⟩ | ⟨_, hp⟩
  · exact h
  · rw [hnone] at hp; cases hp
theorem eventLogged_append_ev_iff {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr : ExecTrace} {ev₀ ev : Ev} :
    (tr.append (⟨ev₀⟩ : ProtocolEvent.ExecEntryT Ev)).EventLogged ev ↔
    tr.EventLogged ev ∨ ev₀ = ev := by
  constructor
  · rintro ⟨i, hi⟩
    rcases eventLoggedAt_append_ev_iff.mp hi with ⟨_, hi⟩ | ⟨_, rfl⟩
    · exact .inl ⟨i, hi⟩
    · exact .inr rfl
  · rintro (⟨i, hi⟩ | rfl)
    · exact ⟨i, evAt_mono (Trace.append_le tr _) hi⟩
    · exact ⟨tr.length, eventLoggedAt_here tr ev₀⟩
@[scoped simp] theorem baseAttackerKnows_append_net (tr : ExecTrace) (msg x : Bytes) :
    Trace.BaseAttackerKnows (tr.append (NetE msg)) x ↔
    x = msg ∨ Trace.BaseAttackerKnows tr x := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (NetE msg)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e x = (x = msg) :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e x).trans
      (Symbolic.DYBridge.DY.Network.baseAttackerKnowledge_attackerKnows tr (NetE msg) x)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
@[scoped simp] theorem baseAttackerKnows_append_rnd (tr : ExecTrace) (n : Nat) (x : Bytes) :
    Trace.BaseAttackerKnows (tr.append (RndE n)) x ↔ Trace.BaseAttackerKnows tr x := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (RndE n)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e x = False :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e x).trans
      (Symbolic.DYBridge.DY.Random.baseAttackerKnowledge_attackerKnows tr (RndE n) x)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)
@[scoped simp] theorem baseAttackerKnows_append_trEv (tr : ExecTrace) (ev : TREvent) (x : Bytes) :
    Trace.BaseAttackerKnows (tr.append (TREvE ev)) x ↔ Trace.BaseAttackerKnows tr x := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (TREvE ev)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e x = False :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e x).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows TREvent tr (TREvE ev) x)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)
@[scoped simp] theorem baseAttackerKnows_append_ev (tr : ExecTrace) (ev : PQXDHEvent) (x : Bytes) :
    Trace.BaseAttackerKnows (tr.append (EvE ev)) x ↔ Trace.BaseAttackerKnows tr x := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (EvE ev)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e x = False :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e x).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows PQXDHEvent tr (EvE ev) x)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)
@[scoped simp] theorem baseAttackerKnows_append_cEv (tr : ExecTrace) (ev : ComposedEvent) (x : Bytes) :
    Trace.BaseAttackerKnows (tr.append (CEvE ev)) x ↔ Trace.BaseAttackerKnows tr x := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (CEvE ev)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e x = False :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e x).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows ComposedEvent tr (CEvE ev) x)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)
@[scoped simp] theorem baseAttackerKnows_append_trSt (tr : ExecTrace) (me : Participant) (st : TRState)
    (x : Bytes) :
    Trace.BaseAttackerKnows (tr.append (TRStE me st)) x ↔ Trace.BaseAttackerKnows tr x := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (TRStE me st)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e x = False :=
    (((Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e x).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.CompromisableState.baseAttackerKnowledge.internal TRState) tr e.entry x)).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.State.baseAttackerKnowledge.internal TRState) tr e.entry.entry x)).trans
      (Symbolic.DYBridge.DY.PersistentGlobalState.State.baseAttackerKnowledge_attackerKnows
        (PersistentLocalState.LocalState TRState) tr (TRStE me st) x)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)
@[scoped simp] theorem baseAttackerKnows_append_st (tr : ExecTrace) (me : Participant) (st : PQXDHState)
    (x : Bytes) :
    Trace.BaseAttackerKnows (tr.append (StE me st)) x ↔ Trace.BaseAttackerKnows tr x := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (StE me st)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e x = False :=
    (((Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e x).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.CompromisableState.baseAttackerKnowledge.internal PQXDHState) tr e.entry x)).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.State.baseAttackerKnowledge.internal PQXDHState) tr e.entry.entry x)).trans
      (Symbolic.DYBridge.DY.PersistentGlobalState.State.baseAttackerKnowledge_attackerKnows
        (PersistentLocalState.LocalState PQXDHState) tr (StE me st) x)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)
theorem append_net {tr : ExecTrace} (hinv : SpqrInv tr) {msg : Bytes}
    (hmsg : Pub (tr.append (NetE msg)) msg) : SpqrInv (tr.append (NetE msg)) := by
  have hle : tr ≤ tr.append (NetE msg) := Trace.append_le tr (NetE msg)
  refine
    { netPub := fun x hx => ?_,
      stOK := fun me st idx hst => (hinv.stOK me st idx (storedAt_append_other hst rfl)).mono hle,
      trStOK := fun me st idx hst => (hinv.trStOK me st idx (trStoredAt_append_other hst rfl)).mono hle,
      skipOK := fun s rPk ctr seed rIdx src idx hev =>
        (hinv.skipOK s rPk ctr seed rIdx src idx (eventLoggedAt_append_other hev rfl)).mono hle,
      irHonest := fun p ik vkp r hev => ?_,
      irCorrupt := fun p ik vkp r hev =>
        evAt_mono hle (hinv.irCorrupt p ik vkp r (eventLoggedAt_append_other hev rfl)),
      aliceDone := fun a b ikA ikB spk pqpk opk ek ct keys i hev =>
        (hinv.aliceDone a b ikA ikB spk pqpk opk ek ct keys i (eventLoggedAt_append_other hev rfl)).mono hle,
      bobDone := fun b a ikB ikA spk pqpk opk ek ct keys i hev =>
        (hinv.bobDone b a ikB ikA spk pqpk opk ek ct keys i (eventLoggedAt_append_other hev rfl)).mono hle,
      opkOrder := hinv.opkOrder.append_other rfl }
  · rcases (baseAttackerKnows_append_net tr msg x).mp hx with rfl | hx'
    · exact hmsg
    · exact (hinv.netPub x hx').mono hle
  · obtain ⟨s, hs, h1, h2⟩ := hinv.irHonest p ik vkp r (eventLoggedAt_append_other hev rfl)
    exact ⟨s, hs.mono hle, h1, h2⟩
theorem append_net_of_pub {tr : ExecTrace} (hinv : SpqrInv tr) {msg : Bytes}
    (hmsg : Pub tr msg) : SpqrInv (tr.append (NetE msg)) :=
  append_net hinv (hmsg.mono (Trace.append_le tr (NetE msg)))
theorem append_rnd {tr : ExecTrace} (hinv : SpqrInv tr) (n : Nat) :
    SpqrInv (tr.append (RndE n)) := by
  have hle : tr ≤ tr.append (RndE n) := Trace.append_le tr (RndE n)
  refine
    { netPub := fun x hx => (hinv.netPub x ((baseAttackerKnows_append_rnd tr n x).mp hx)).mono hle,
      stOK := fun me st idx hst => (hinv.stOK me st idx (storedAt_append_other hst rfl)).mono hle,
      trStOK := fun me st idx hst => (hinv.trStOK me st idx (trStoredAt_append_other hst rfl)).mono hle,
      skipOK := fun s rPk ctr seed rIdx src idx hev =>
        (hinv.skipOK s rPk ctr seed rIdx src idx (eventLoggedAt_append_other hev rfl)).mono hle,
      irHonest := fun p ik vkp r hev => ?_,
      irCorrupt := fun p ik vkp r hev =>
        evAt_mono hle (hinv.irCorrupt p ik vkp r (eventLoggedAt_append_other hev rfl)),
      aliceDone := fun a b ikA ikB spk pqpk opk ek ct keys i hev =>
        (hinv.aliceDone a b ikA ikB spk pqpk opk ek ct keys i (eventLoggedAt_append_other hev rfl)).mono hle,
      bobDone := fun b a ikB ikA spk pqpk opk ek ct keys i hev =>
        (hinv.bobDone b a ikB ikA spk pqpk opk ek ct keys i (eventLoggedAt_append_other hev rfl)).mono hle,
      opkOrder := hinv.opkOrder.append_other rfl }
  obtain ⟨s, hs, h1, h2⟩ := hinv.irHonest p ik vkp r (eventLoggedAt_append_other hev rfl)
  exact ⟨s, hs.mono hle, h1, h2⟩
theorem append_st {tr : ExecTrace} (hinv : SpqrInv tr) {me : Participant}
    {st : PQXDHState} (hok : KindOK tr me st) : SpqrInv (tr.append (StE me st)) := by
  have hle : tr ≤ tr.append (StE me st) := Trace.append_le tr (StE me st)
  refine
    { netPub := fun x hx => (hinv.netPub x ((baseAttackerKnows_append_st tr me st x).mp hx)).mono hle,
      stOK := fun me' st' idx hst => ?_,
      trStOK := fun me' st' idx hst => (hinv.trStOK me' st' idx (trStoredAt_append_other hst rfl)).mono hle,
      skipOK := fun s rPk ctr seed rIdx src idx hev =>
        (hinv.skipOK s rPk ctr seed rIdx src idx (eventLoggedAt_append_other hev rfl)).mono hle,
      irHonest := fun p ik vkp r hev => ?_,
      irCorrupt := fun p ik vkp r hev =>
        evAt_mono hle (hinv.irCorrupt p ik vkp r (eventLoggedAt_append_other hev rfl)),
      aliceDone := fun a b ikA ikB spk pqpk opk ek ct keys i hev =>
        (hinv.aliceDone a b ikA ikB spk pqpk opk ek ct keys i (eventLoggedAt_append_other hev rfl)).mono hle,
      bobDone := fun b a ikB ikA spk pqpk opk ek ct keys i hev =>
        (hinv.bobDone b a ikB ikA spk pqpk opk ek ct keys i (eventLoggedAt_append_other hev rfl)).mono hle,
      opkOrder := hinv.opkOrder.append_other rfl }
  · rcases storedAt_append_st_iff.mp hst with ⟨_, hst⟩ | ⟨rfl, rfl, rfl⟩
    · exact (hinv.stOK me' st' idx hst).mono hle
    · exact hok.mono hle
  · obtain ⟨s, hs, h1, h2⟩ := hinv.irHonest p ik vkp r (eventLoggedAt_append_other hev rfl)
    exact ⟨s, hs.mono hle, h1, h2⟩
theorem append_irCorrupt {tr : ExecTrace} (hinv : SpqrInv tr)
    (p : Participant) (ik vkp : Bytes) :
    let tr1 := tr.append (EvE (PQXDHEvent.IdentityRegistered p ik vkp false))
    let tr2 := tr1.append (EvE (PQXDHEvent.CompromisedIK p ik))
    SpqrInv tr2 := by
  intro tr1 tr2
  have hle1 : tr ≤ tr1 := Trace.append_le tr _; have hle2 : tr1 ≤ tr2 := Trace.append_le tr1 _
  have hle : tr ≤ tr2 := Trace.le_trans tr tr1 tr2 hle1 hle2
  refine
    { netPub := fun x hx => ?_,
      stOK := fun me st idx hst =>
        (hinv.stOK me st idx (storedAt_append_other (storedAt_append_other hst rfl) rfl)).mono hle,
      trStOK := fun me st idx hst =>
        (hinv.trStOK me st idx (trStoredAt_append_other (trStoredAt_append_other hst rfl) rfl)).mono hle,
      skipOK := fun s rPk ctr seed rIdx src idx hev =>
        (hinv.skipOK s rPk ctr seed rIdx src idx
          (eventLoggedAt_append_other (eventLoggedAt_append_other hev rfl) rfl)).mono hle,
      irHonest := fun p' ik' vkp' r hev => ?_, irCorrupt := fun p' ik' vkp' r hev => ?_,
      aliceDone := fun a b ikA ikB spk pqpk opk ek ct keys i hev => ?_,
      bobDone := fun b a ikB ikA spk pqpk opk ek ct keys i hev => ?_,
      opkOrder := (hinv.opkOrder.append_ev (fun _ _ _ _ _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h)).append_ev
        (fun _ _ _ _ _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h) }
  · have hx1 := (baseAttackerKnows_append_ev tr1 _ x).mp hx
    exact (hinv.netPub x ((baseAttackerKnows_append_ev tr _ x).mp hx1)).mono hle
  · rcases eventLoggedAt_append_ev_iff.mp hev with ⟨_, hev1⟩ | ⟨_, hEq⟩
    · rcases eventLoggedAt_append_ev_iff.mp hev1 with ⟨_, hev0⟩ | ⟨_, hEq⟩
      · obtain ⟨s, hs, h1, h2⟩ := hinv.irHonest p' ik' vkp' r hev0; exact ⟨s, hs.mono hle, h1, h2⟩
      · cases hEq
    · cases hEq
  · rcases eventLoggedAt_append_ev_iff.mp hev with ⟨_, hev1⟩ | ⟨_, hEq⟩
    · rcases eventLoggedAt_append_ev_iff.mp hev1 with ⟨_, hev0⟩ | ⟨rfl, hEq⟩
      · exact evAt_mono hle (hinv.irCorrupt p' ik' vkp' r hev0)
      · injection hEq with hp hik _; subst hp hik
        rw [show tr.length + 1 = tr1.length by simp [tr1, append_len]]
        exact eventLoggedAt_here tr1 (PQXDHEvent.CompromisedIK p ik)
    · cases hEq
  · rcases eventLoggedAt_append_ev_iff.mp hev with ⟨_, hev1⟩ | ⟨_, hEq⟩
    · rcases eventLoggedAt_append_ev_iff.mp hev1 with ⟨_, hev0⟩ | ⟨_, hEq⟩
      · exact (hinv.aliceDone a b ikA ikB spk pqpk opk ek ct keys i hev0).mono hle
      · cases hEq
    · cases hEq
  · rcases eventLoggedAt_append_ev_iff.mp hev with ⟨_, hev1⟩ | ⟨_, hEq⟩
    · rcases eventLoggedAt_append_ev_iff.mp hev1 with ⟨_, hev0⟩ | ⟨_, hEq⟩
      · exact (hinv.bobDone b a ikB ikA spk pqpk opk ek ct keys i hev0).mono hle
      · cases hEq
    · cases hEq
theorem append_expose_ev {tr : ExecTrace} (hinv : SpqrInv tr) {ev : PQXDHEvent}
    (hno_ir : ∀ p ik vkp hon, ev ≠ PQXDHEvent.IdentityRegistered p ik vkp hon)
    (hno_ad : ∀ a b ikA ikB spk pqpk opk ek ct keys,
      ev ≠ PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys)
    (hno_bd : ∀ b a ikB ikA spk pqpk opk ek ct keys,
      ev ≠ PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys)
    (hno_co : ∀ b o, ev = PQXDHEvent.CompromisedOPK b o → opkUsedB tr b o = false := by exact nofun) :
    SpqrInv (tr.append (EvE ev)) := by
  have hle : tr ≤ tr.append (EvE ev) := Trace.append_le tr (EvE ev)
  refine
    { netPub := fun x hx => (hinv.netPub x ((baseAttackerKnows_append_ev tr ev x).mp hx)).mono hle,
      stOK := fun me st idx hst => (hinv.stOK me st idx (storedAt_append_other hst rfl)).mono hle,
      trStOK := fun me st idx hst => (hinv.trStOK me st idx (trStoredAt_append_other hst rfl)).mono hle,
      skipOK := fun s rPk ctr seed rIdx src idx hev =>
        (hinv.skipOK s rPk ctr seed rIdx src idx (eventLoggedAt_append_other hev rfl)).mono hle,
      irHonest := fun p ik vkp r hev => ?_, irCorrupt := fun p ik vkp r hev => ?_,
      aliceDone := fun a b ikA ikB spk pqpk opk ek ct keys i hev => ?_,
      bobDone := fun b a ikB ikA spk pqpk opk ek ct keys i hev => ?_,
      opkOrder := hinv.opkOrder.append_ev
        (fun b a ikB ikA spk pqpk o ek ct keys hEq =>
          (hno_bd b a ikB ikA spk pqpk (some o) ek ct keys hEq).elim)
        (fun b o hEq => not_loggedBefore_opkUsed_of_opkUsedB_eq_false (hno_co b o hEq)) }
  · rcases eventLoggedAt_append_ev_iff.mp hev with ⟨_, hev0⟩ | ⟨_, hEq⟩
    · obtain ⟨s, hs, h1, h2⟩ := hinv.irHonest p ik vkp r hev0; exact ⟨s, hs.mono hle, h1, h2⟩
    · exact False.elim (hno_ir p ik vkp true hEq)
  · rcases eventLoggedAt_append_ev_iff.mp hev with ⟨_, hev0⟩ | ⟨_, hEq⟩
    · exact evAt_mono hle (hinv.irCorrupt p ik vkp r hev0)
    · exact False.elim (hno_ir p ik vkp false hEq)
  · rcases eventLoggedAt_append_ev_iff.mp hev with ⟨_, hev0⟩ | ⟨_, hEq⟩
    · exact (hinv.aliceDone a b ikA ikB spk pqpk opk ek ct keys i hev0).mono hle
    · exact False.elim (hno_ad a b ikA ikB spk pqpk opk ek ct keys hEq)
  · rcases eventLoggedAt_append_ev_iff.mp hev with ⟨_, hev0⟩ | ⟨_, hEq⟩
    · exact (hinv.bobDone b a ikB ikA spk pqpk opk ek ct keys i hev0).mono hle
    · exact False.elim (hno_bd b a ikB ikA spk pqpk opk ek ct keys hEq)
/-! ## Registration and Prekey Transitions -/
theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩ <;> rfl
theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩ <;> rfl
theorem run_bind_assoc_snd {α β γ : Type}
    (x : Traceful α) (f : α → Traceful β) (g : β → Traceful γ) (tr : ExecTrace) :
    (((x >>= f) >>= g).run tr).2.val = ((x >>= fun a => f a >>= g).run tr).2.val := by
  rw [run_bind_snd, run_bind_fst, run_bind_snd, run_bind_snd]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · exact (run_bind_snd (f a) g tr1.val).symm
theorem run_pure_bind_snd {α β : Type} (a : α) (f : α → Traceful β) (tr : ExecTrace) :
    (((Pure.pure a : Traceful α) >>= f).run tr).2.val = ((f a).run tr).2.val := by
  rw [run_bind_snd, Traceful.run_pure]
theorem run_genRand_bind_snd {α : Type} (n : Nat) (f : Bytes → Traceful α) (tr : ExecTrace) :
    ((Random.genRand n >>= f).run tr).2.val =
      ((f (rnd tr.length n)).run (tr.append (RndE n))).2.val := by
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [run_bind_assoc_snd, run_bind_snd, Traceful.run_mk]
  dsimp only
  rw [run_pure_bind_snd]
theorem getLocalState_fst (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful PQXDHState).run tr).1 =
      match (tr.at? stH : Option StEntry) with
      | some ⟨⟨p, st⟩⟩ => if p = me then some st else none
      | none => none := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1,
    Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [run_bind_fst, run_bind_fst, run_bind_snd, Traceful.run_mk]
  rcases (tr.at? stH : Option StEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · dsimp only
    rw [Traceful.run_pure]
    dsimp only
    unfold _root_.guard
    by_cases hp : p = me
    · rw [ite_eq_left_iff.mpr fun h => absurd hp h, ite_eq_left_iff.mpr fun h => absurd hp h,
        run_bind_fst, Traceful.run_pure]
      dsimp only
      rw [Traceful.run_pure]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hp, ite_eq_right_iff.mpr fun h => absurd h hp,
        run_bind_fst, Traceful.run_failure]
theorem getLocalState_snd (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful PQXDHState).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1,
    Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [run_bind_snd, run_bind_fst, run_bind_snd, Traceful.run_mk]
  rcases (tr.at? stH : Option StEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · dsimp only
    rw [Traceful.run_pure]
    dsimp only
    unfold _root_.guard
    by_cases hp : p = me
    · rw [ite_eq_left_iff.mpr fun h => absurd hp h, run_bind_snd, Traceful.run_pure, Traceful.run_pure]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hp, run_bind_snd, Traceful.run_failure]
theorem bind_guard_at {Inv : ExecTrace → Prop} {α : Type}
    (p : Prop) [Decidable p] {f : Unit → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (hf : p → Inv ((f ()).run tr).2.val) :
    Inv (((_root_.guard p >>= f).run tr).2.val) := by
  unfold _root_.guard
  by_cases hp : p
  · rw [ite_eq_left_iff.mpr fun h => absurd hp h, run_pure_bind_snd]
    exact hf hp
  · rw [ite_eq_right_iff.mpr fun h => absurd h hp, Traceful.run_bind, Traceful.run_failure]
    exact hInv
theorem bind_guardOnTrace_at {Inv : ExecTrace → Prop} {α : Type}
    (p : ExecTrace → Bool) {f : Unit → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (hf : p tr = true → Inv ((f ()).run tr).2.val) :
    Inv (((DY.Libsignal.PQXDH.guardTrace p >>= f).run tr).2.val) := by
  rw [run_bind_snd]
  unfold DY.Libsignal.PQXDH.guardTrace
  rw [Traceful.run_mk]
  dsimp only
  by_cases hp : p tr = true
  · rw [ite_eq_left_iff.mpr fun h => absurd hp h]
    exact hf hp
  · rw [ite_eq_right_iff.mpr fun h => absurd h hp]
    exact hInv
theorem bind_getKey_at {Inv : ExecTrace → Prop} {α : Type}
    (p : Participant) (stateIdx : Nat) (kind : KeyKind) {f : Bytes → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ sk, StoredAt tr p { kind, sk } stateIdx → Inv ((f sk).run tr).2.val) :
    Inv (((getKey p stateIdx kind >>= f).run tr).2.val) := by
  unfold DY.Libsignal.PQXDH.getKey
  rw [run_bind_assoc_snd, run_bind_snd, getLocalState_fst, getLocalState_snd]
  rcases he : (tr.at? stateIdx : Option StEntry) with _ | ⟨⟨p', st⟩⟩
  · exact hInv
  · dsimp only
    by_cases hp : p' = p
    · subst hp
      simp only [↓reduceIte]
      rw [run_bind_assoc_snd]
      refine bind_guard_at (st.kind = kind) tr hInv fun hk => ?_
      rcases st with ⟨k, sk⟩
      cases hk
      rw [run_pure_bind_snd]
      exact hf sk he
    · simp only [hp, ↓reduceIte]
      exact hInv
theorem receiveMessage_fst (h : Nat) (tr : ExecTrace) :
    ((Network.receiveMessage h).run tr).1 =
      match (tr.at? h : Option NetEntry) with
      | some ⟨msg⟩ => some msg
      | none => none := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [run_bind_fst, Traceful.run_mk]
  rcases (tr.at? h : Option NetEntry) with _ | ⟨⟨msg⟩⟩
  · rfl
  · dsimp only; rw [Traceful.run_pure]
theorem receiveMessage_snd (h : Nat) (tr : ExecTrace) :
    ((Network.receiveMessage h).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [run_bind_snd, Traceful.run_mk]
  rcases (tr.at? h : Option NetEntry) with _ | ⟨⟨msg⟩⟩
  · rfl
  · dsimp only; rw [Traceful.run_pure]
theorem NetAt.baseAttackerKnows {tr : ExecTrace} {msg : Bytes} {idx : Nat}
    (h : NetAt tr msg idx) : Trace.BaseAttackerKnows tr msg := by
  unfold NetAt at h
  rw [Trace.at?_eq_some] at h
  obtain ⟨hi, hat⟩ := h
  induction tr with
  | nil => simp [Symbolic.DYBridge.DY.Trace.length_eq_1] at hi
  | snoc tr' entry ih =>
    rw [Symbolic.DYBridge.DY.Trace.at_eq_2] at hat
    rw [Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2]
    split at hat
    · subst hat
      let e : ExecTrace.Entry := TraceEntryHas.inj (NetE msg)
      have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr' e msg = (msg = msg) :=
        (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
          DY.Libsignal.Composed.baseAttackerKnowledge.internal tr' e msg).trans
          (Symbolic.DYBridge.DY.Network.baseAttackerKnowledge_attackerKnows tr' (NetE msg) msg)
      rw [h0]
      exact Or.inl rfl
    · exact Or.inr (ih (Symbolic.DYBridge.DY.Trace.at_snoc_lt_aux hi ‹_›) hat)
theorem NetAt.attackerKnows {tr : ExecTrace} {msg : Bytes} {idx : Nat}
    (h : NetAt tr msg idx) : msg.AttackerKnows tr :=
  Bytes.AttackerKnows.prove_from_base msg tr (NetAt.baseAttackerKnows h)
theorem bind_receiveMessage_at {Inv : ExecTrace → Prop} {α : Type}
    (h : Nat) {f : Bytes → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ msg, NetAt tr msg h → msg.AttackerKnows tr → Inv ((f msg).run tr).2.val) :
    Inv (((Network.receiveMessage h >>= f).run tr).2.val) := by
  rw [run_bind_snd, receiveMessage_fst, receiveMessage_snd]
  rcases he : (tr.at? h : Option NetEntry) with _ | ⟨⟨msg⟩⟩
  · exact hInv
  · exact hf msg he (NetAt.attackerKnows he)

private theorem run_failure_end {Inv : ExecTrace → Prop} {α : Type} {tr : ExecTrace}
    (h : Inv tr) : Inv ((failure : Traceful α).run tr).2.val := by
  rw [Traceful.run_failure]; exact h

private theorem run_pure_end {Inv : ExecTrace → Prop} {α : Type} {a : α} {tr : ExecTrace}
    (h : Inv tr) : Inv ((pure a : Traceful α).run tr).2.val := by
  rw [Traceful.run_pure]; exact h

private theorem logEvent_run_eq {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] (ev : Ev) (tr : ExecTrace) :
    ((ProtocolEvent.logEvent ev).run tr).1 = some () ∧
    ((ProtocolEvent.logEvent ev).run tr).2.val =
      tr.append ({ ev := ev } : ProtocolEvent.ExecEntryT Ev) := by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact ⟨trivial, trivial⟩

private theorem run_logEvent {Inv : ExecTrace → Prop} {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] (ev : Ev) {tr : ExecTrace}
    (hf : Inv (tr.append ({ ev := ev } : ProtocolEvent.ExecEntryT Ev))) :
    Inv ((ProtocolEvent.logEvent ev).run tr).2.val := by
  rw [(logEvent_run_eq ev tr).2]; exact hf

private theorem run_bind_logEvent {Inv : ExecTrace → Prop} {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] {α : Type} (ev : Ev)
    {f : Unit → Traceful α} {tr : ExecTrace}
    (hf : Inv ((f ()).run (tr.append ({ ev := ev } : ProtocolEvent.ExecEntryT Ev))).2.val) :
    Inv ((ProtocolEvent.logEvent ev >>= f).run tr).2.val := by
  rw [run_bind_snd, (logEvent_run_eq ev tr).1, (logEvent_run_eq ev tr).2]
  exact hf

private theorem run_sendMessage {Inv : ExecTrace → Prop} (msg : Bytes) {tr : ExecTrace}
    (hf : Inv (tr.append (NetE msg))) :
    Inv ((Network.sendMessage msg).run tr).2.val := by
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_mk]
  exact hf

private theorem run_bind_sendMessage {Inv : ExecTrace → Prop} {α : Type}
    (msg : Bytes) {f : Nat → Traceful α} (tr : ExecTrace)
    (hf : Inv ((f tr.length).run (tr.append (NetE msg))).2.val) :
    Inv ((Network.sendMessage msg >>= f).run tr).2.val := by
  rw [run_bind_snd, Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact hf

private theorem run_storeLocalState {Inv : ExecTrace → Prop} {St : Type}
    [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT St)]
    (p : Participant) (st : St) {tr : ExecTrace}
    (hf : Inv (tr.append (PersistentGlobalState.State.ExecEntryT.mk
      ({ participant := p, state := st } : PersistentLocalState.LocalState St)))) :
    Inv ((PersistentLocalState.storeLocalState p st).run tr).2.val := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact hf

private theorem run_bind_storeLocalState {Inv : ExecTrace → Prop} {St : Type}
    [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT St)] {α : Type}
    (p : Participant) (st : St) {f : Nat → Traceful α} {tr : ExecTrace}
    (hf : Inv ((f tr.length).run (tr.append (PersistentGlobalState.State.ExecEntryT.mk
      ({ participant := p, state := st } : PersistentLocalState.LocalState St)))).2.val) :
    Inv ((PersistentLocalState.storeLocalState p st >>= f).run tr).2.val := by
  rw [run_bind_snd, Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact hf

private theorem run_bind_traceLength {Inv : ExecTrace → Prop} {α : Type}
    {f : Nat → Traceful α} {tr : ExecTrace}
    (hf : Inv ((f tr.length).run tr).2.val) :
    Inv ((traceLength >>= f).run tr).2.val := by
  unfold traceLength; rw [run_bind_snd, Traceful.run_mk]; exact hf

theorem preserves_net_step (msg : Bytes) (tr : ExecTrace) (hPre : msg.AttackerKnows tr)
    (hinv : SpqrInv tr) : SpqrInv ((Network.sendMessage msg).run tr).2.val :=
  run_sendMessage msg (append_net_of_pub hinv (Pub.of_attackerKnows hinv hPre))
theorem preserves_registerIdentity_step (p : Participant) :
    Preserves SpqrInv (registerIdentity p) := by
  intro tr hinv
  unfold registerIdentity
  refine bind_guardOnTrace_at _ tr hinv fun _ => ?_
  rw [run_genRand_bind_snd]
  refine run_bind_logEvent _ ?_
  refine run_bind_sendMessage _ _ ?_
  refine run_bind_sendMessage _ _ ?_
  refine run_storeLocalState p _ ?_
  change SpqrInv (let s := rnd tr.length 32
    let tr1 := tr.append (RndE 32)
    let tr2 := tr1.append (EvE (PQXDHEvent.IdentityRegistered p (DiffieHellman.dhPk s) (Signature.vk s) true))
    let tr3 := tr2.append (NetE (DiffieHellman.dhPk s))
    let tr4 := tr3.append (NetE (Signature.vk s))
    tr4.append (StE p { kind := .identity, sk := s }))
  dsimp only
  let s := rnd tr.length 32
  let tr1 := tr.append (RndE 32)
  let tr2 := tr1.append (EvE (PQXDHEvent.IdentityRegistered p (DiffieHellman.dhPk s) (Signature.vk s) true))
  have hle1 : tr ≤ tr1 := Trace.append_le tr _
  have hle2 : tr1 ≤ tr2 := Trace.append_le tr1 _
  have hle02 : tr ≤ tr2 := Trace.le_trans tr tr1 tr2 hle1 hle2
  have hrand : RandAt tr2 tr.length 32 :=
    (randAt_here tr 32).mono hle2
  have hev : tr2.EventLoggedAt
      (PQXDHEvent.IdentityRegistered p (DiffieHellman.dhPk s) (Signature.vk s) true)
      (tr.length + 1) := by
    rw [show tr.length + 1 = tr1.length by simp [tr1, append_len]]
    exact eventLoggedAt_here tr1 (PQXDHEvent.IdentityRegistered p (DiffieHellman.dhPk s) (Signature.vk s) true)
  have hik : IKAt tr2 p s := ⟨tr.length, rfl, hrand, hev⟩
  have hinv2 : SpqrInv tr2 :=
    { netPub := fun x hx => by
        have hx1 := (baseAttackerKnows_append_ev tr1 _ x).mp hx
        have hx0 := (baseAttackerKnows_append_rnd tr 32 x).mp hx1
        exact (hinv.netPub x hx0).mono hle02
      stOK := fun me st idx hst =>
        (hinv.stOK me st idx
          (storedAt_append_other (storedAt_append_other hst rfl) rfl)).mono hle02
      trStOK := fun me st idx hst =>
        (hinv.trStOK me st idx
          (trStoredAt_append_other (trStoredAt_append_other hst rfl) rfl)).mono hle02
      skipOK := fun s' rPk ctr seed rIdx src idx hev' =>
        (hinv.skipOK s' rPk ctr seed rIdx src idx
          (eventLoggedAt_append_other (eventLoggedAt_append_other hev' rfl) rfl)).mono hle02
      irHonest := fun p' ik' vkp' r hev' => by
        rcases eventLoggedAt_append_ev_iff.mp hev' with ⟨_, hev1⟩ | ⟨_, hEq⟩
        · have hev0 := eventLoggedAt_append_other hev1 rfl
          obtain ⟨s', hs', h1, h2⟩ := hinv.irHonest p' ik' vkp' r hev0
          exact ⟨s', hs'.mono hle02, h1, h2⟩
        · injection hEq with hp hik' hvkp'
          subst hp hik' hvkp'
          exact ⟨s, hik, rfl, rfl⟩
      irCorrupt := fun p' ik' vkp' r hev' => by
        rcases eventLoggedAt_append_ev_iff.mp hev' with ⟨_, hev1⟩ | ⟨_, hEq⟩
        · have hev0 := eventLoggedAt_append_other hev1 rfl
          exact evAt_mono hle02 (hinv.irCorrupt p' ik' vkp' r hev0)
        · cases hEq
      aliceDone := fun a b ikA ikB spk pqpk opk ek ct keys i hev' => by
        rcases eventLoggedAt_append_ev_iff.mp hev' with ⟨_, hev1⟩ | ⟨_, hEq⟩
        · have hev0 := eventLoggedAt_append_other hev1 rfl
          exact (hinv.aliceDone a b ikA ikB spk pqpk opk ek ct keys i hev0).mono hle02
        · cases hEq
      bobDone := fun b a ikB ikA spk pqpk opk ek ct keys i hev' => by
        rcases eventLoggedAt_append_ev_iff.mp hev' with ⟨_, hev1⟩ | ⟨_, hEq⟩
        · have hev0 := eventLoggedAt_append_other hev1 rfl
          exact (hinv.bobDone b a ikB ikA spk pqpk opk ek ct keys i hev0).mono hle02
        · cases hEq
      opkOrder := (hinv.opkOrder.append_other rfl).append_ev nofun nofun }
  have hinv3 := append_net_of_pub hinv2 (Pub.dhPub (.inl ⟨p, hik⟩))
  have hik3 : IKAt (tr2.append (NetE (DiffieHellman.dhPk s))) p s :=
    hik.mono (Trace.append_le tr2 _)
  have hinv4 := append_net_of_pub hinv3 (Pub.vkPub hik3)
  have hik4 : IKAt ((tr2.append (NetE (DiffieHellman.dhPk s))).append (NetE (Signature.vk s))) p s :=
    hik3.mono (Trace.append_le _ _)
  exact append_st hinv4 hik4
theorem preserves_registerCorruptIdentity_step (p : Participant) (skIdx : Nat) :
    Preserves SpqrInv (registerCorruptIdentity p skIdx) := by
  intro tr hinv
  unfold registerCorruptIdentity
  refine bind_guardOnTrace_at _ tr hinv fun _ => ?_
  refine bind_receiveMessage_at skIdx tr hinv fun sk _ _ => ?_
  exact run_bind_logEvent _ (run_logEvent _
    (append_irCorrupt hinv p (DiffieHellman.dhPk sk) (Signature.vk sk)))
theorem preserves_genSignedPrekey_step (b : Participant) (idStateIdx : Nat) :
    Preserves SpqrInv (genSignedPrekey b idStateIdx) := by
  intro tr hinv
  unfold genSignedPrekey
  refine bind_getKey_at b idStateIdx .identity tr hinv fun ik hst => ?_
  have hik : IKAt tr b ik := hinv.stOK b { kind := .identity, sk := ik } idStateIdx hst
  let spk := rnd tr.length 32
  let tr1 := tr.append (RndE 32)
  let nonce := rnd tr1.length 64
  let tr2 := tr1.append (RndE 64)
  let tr3 := tr2.append (EvE (PQXDHEvent.SignedPrekeyPublished b (DiffieHellman.dhPk spk)))
  let tr4 := tr3.append (StE b { kind := .signedPrekey, sk := spk })
  let tr5 := tr4.append (NetE (DiffieHellman.dhPk spk))
  let tr6 := tr5.append (NetE (Signature.sign ik nonce (encodeEC (DiffieHellman.dhPk spk))))
  rw [run_genRand_bind_snd, run_genRand_bind_snd]
  refine run_bind_logEvent _ ?_
  refine run_bind_storeLocalState b _ ?_
  refine run_bind_sendMessage _ _ ?_
  refine run_bind_sendMessage _ _ ?_
  refine run_pure_end ?_
  change SpqrInv tr6
  have hle01 : tr ≤ tr1 := Trace.append_le tr _
  have hle12 : tr1 ≤ tr2 := Trace.append_le tr1 _
  have hle23 : tr2 ≤ tr3 := Trace.append_le tr2 _
  have hle34 : tr3 ≤ tr4 := Trace.append_le tr3 _
  have hle45 : tr4 ≤ tr5 := Trace.append_le tr4 _
  have hle13 : tr1 ≤ tr3 := Trace.le_trans tr1 tr2 tr3 hle12 hle23
  have hle03 : tr ≤ tr3 := Trace.le_trans tr tr1 tr3 hle01 hle13
  have hr0 : RandAt tr3 tr.length 32 := (randAt_here tr 32).mono hle13
  have hr1 : RandAt tr3 (tr.length + 1) 64 := by
    rw [show tr.length + 1 = tr1.length by simp [tr1, append_len]]
    exact (randAt_here tr1 64).mono hle23
  have hev : tr3.EventLoggedAt (PQXDHEvent.SignedPrekeyPublished b (DiffieHellman.dhPk spk))
      (tr.length + 2) := by
    rw [show tr.length + 2 = tr2.length by simp [tr2, tr1, append_len]]
    exact eventLoggedAt_here tr2 (PQXDHEvent.SignedPrekeyPublished b (DiffieHellman.dhPk spk))
  have hspk3 : SPKAt tr3 b spk := ⟨tr.length, rfl, hr0, hr1, hev⟩
  have hik3 : IKAt tr3 b ik := hik.mono hle03
  have hinv2 : SpqrInv tr2 := append_rnd (append_rnd hinv 32) 64
  have hinv3 : SpqrInv tr3 :=
    append_expose_ev hinv2 (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩)
  have hinv4 : SpqrInv tr4 := append_st hinv3 hspk3
  have hspk4 : SPKAt tr4 b spk := hspk3.mono hle34
  have hik4 : IKAt tr4 b ik := hik3.mono hle34
  have hinv5 : SpqrInv tr5 := append_net_of_pub hinv4 (.dhPub (.inr (.inl ⟨b, hspk4⟩)))
  have hspk5 : SPKAt tr5 b spk := hspk4.mono hle45
  have hik5 : IKAt tr5 b ik := hik4.mono hle45
  exact append_net_of_pub hinv5
    (.sigHonest nonce (encodeEC (DiffieHellman.dhPk spk)) ⟨b, hik5, .inl ⟨spk, hspk5, rfl⟩⟩)
theorem preserves_genPQPrekey_step (b : Participant) (idStateIdx : Nat) :
    Preserves SpqrInv (genPQPrekey b idStateIdx) := by
  intro tr hinv
  unfold genPQPrekey
  refine bind_getKey_at b idStateIdx .identity tr hinv fun ik hst => ?_
  have hik : IKAt tr b ik := hinv.stOK b { kind := .identity, sk := ik } idStateIdx hst
  let pqsk := rnd tr.length 64
  let tr1 := tr.append (RndE 64)
  let nonce := rnd tr1.length 64
  let tr2 := tr1.append (RndE 64)
  let tr3 := tr2.append (EvE (PQXDHEvent.PQPrekeyPublished b (PQKem.kemPk pqsk)))
  let tr4 := tr3.append (StE b { kind := .pqPrekey, sk := pqsk })
  let tr5 := tr4.append (NetE (PQKem.kemPk pqsk))
  let tr6 := tr5.append (NetE (Signature.sign ik nonce (encodeKEM (PQKem.kemPk pqsk))))
  rw [run_genRand_bind_snd, run_genRand_bind_snd]
  refine run_bind_logEvent _ ?_
  refine run_bind_storeLocalState b _ ?_
  refine run_bind_sendMessage _ _ ?_
  refine run_bind_sendMessage _ _ ?_
  refine run_pure_end ?_
  change SpqrInv tr6
  have hle01 : tr ≤ tr1 := Trace.append_le tr _
  have hle12 : tr1 ≤ tr2 := Trace.append_le tr1 _
  have hle23 : tr2 ≤ tr3 := Trace.append_le tr2 _
  have hle34 : tr3 ≤ tr4 := Trace.append_le tr3 _
  have hle45 : tr4 ≤ tr5 := Trace.append_le tr4 _
  have hle13 : tr1 ≤ tr3 := Trace.le_trans tr1 tr2 tr3 hle12 hle23
  have hle03 : tr ≤ tr3 := Trace.le_trans tr tr1 tr3 hle01 hle13
  have hr0 : RandAt tr3 tr.length 64 := (randAt_here tr 64).mono hle13
  have hr1 : RandAt tr3 (tr.length + 1) 64 := by
    rw [show tr.length + 1 = tr1.length by simp [tr1, append_len]]
    exact (randAt_here tr1 64).mono hle23
  have hev : tr3.EventLoggedAt (PQXDHEvent.PQPrekeyPublished b (PQKem.kemPk pqsk))
      (tr.length + 2) := by
    rw [show tr.length + 2 = tr2.length by simp [tr2, tr1, append_len]]
    exact eventLoggedAt_here tr2 (PQXDHEvent.PQPrekeyPublished b (PQKem.kemPk pqsk))
  have hpq3 : PQAt tr3 b pqsk := ⟨tr.length, rfl, hr0, hr1, hev⟩
  have hik3 : IKAt tr3 b ik := hik.mono hle03
  have hinv2 : SpqrInv tr2 := append_rnd (append_rnd hinv 64) 64
  have hinv3 : SpqrInv tr3 :=
    append_expose_ev hinv2 (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩)
  have hinv4 : SpqrInv tr4 := append_st hinv3 hpq3
  have hpq4 : PQAt tr4 b pqsk := hpq3.mono hle34
  have hik4 : IKAt tr4 b ik := hik3.mono hle34
  have hinv5 : SpqrInv tr5 := append_net_of_pub hinv4 (.kemPub ⟨b, hpq4⟩)
  have hpq5 : PQAt tr5 b pqsk := hpq4.mono hle45
  have hik5 : IKAt tr5 b ik := hik4.mono hle45
  exact append_net_of_pub hinv5
    (.sigHonest nonce (encodeKEM (PQKem.kemPk pqsk)) ⟨b, hik5, .inr ⟨pqsk, hpq5, rfl⟩⟩)

theorem preserves_genOneTimePrekey_step (b : Participant) :
    Preserves SpqrInv (genOneTimePrekey b) := by
  intro tr hinv
  unfold genOneTimePrekey
  let opk := rnd tr.length 32
  let tr1 := tr.append (RndE 32)
  let tr2 := tr1.append (EvE (PQXDHEvent.OneTimePrekeyPublished b (DiffieHellman.dhPk opk)))
  let tr3 := tr2.append (StE b { kind := .oneTimePrekey, sk := opk })
  let tr4 := tr3.append (NetE (DiffieHellman.dhPk opk))
  rw [run_genRand_bind_snd]
  refine run_bind_logEvent _ ?_
  refine run_bind_storeLocalState b _ ?_
  refine run_bind_sendMessage _ _ ?_
  refine run_pure_end ?_
  change SpqrInv tr4
  have hle12 : tr1 ≤ tr2 := Trace.append_le tr1 _
  have hle23 : tr2 ≤ tr3 := Trace.append_le tr2 _
  have hr0 : RandAt tr2 tr.length 32 := (randAt_here tr 32).mono hle12
  have hev : tr2.EventLoggedAt (PQXDHEvent.OneTimePrekeyPublished b (DiffieHellman.dhPk opk))
      (tr.length + 1) := by
    rw [show tr.length + 1 = tr1.length by simp [tr1, append_len]]
    exact eventLoggedAt_here tr1 (PQXDHEvent.OneTimePrekeyPublished b (DiffieHellman.dhPk opk))
  have hopk2 : OPKAt tr2 b opk := ⟨tr.length, rfl, hr0, hev⟩
  have hinv1 : SpqrInv tr1 := append_rnd hinv 32
  have hinv2 : SpqrInv tr2 :=
    append_expose_ev hinv1 (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩)
  have hinv3 : SpqrInv tr3 := append_st hinv2 hopk2
  have hopk3 : OPKAt tr3 b opk := hopk2.mono hle23
  exact append_net_of_pub hinv3 (.dhPub (.inr (.inr (.inl ⟨b, hopk3⟩))))

/-! ## Compromise, Break, and Inversion Transitions -/

theorem dhSkOf_eq_some {pk sk : Bytes} (h : extractDhSecretKey pk = some sk) :
    pk = DiffieHellman.dhPk sk := by
  dsimp only [extractDhSecretKey] at h
  have hpack := Bytes.pack_view? DiffieHellman.DhPk.SubF pk
  rcases hpk : pk.view? DiffieHellman.DhPk.SubF with _ | ⟨sk'⟩
  · rw [hpk] at h; cases h
  · rw [hpk] at h hpack
    injection h with hsk
    subst hsk
    exact hpack.symm

theorem kemPkInvert_eq_some {pk sk : Bytes} (h : PQKem.invertKemPublicKey pk = some sk) :
    pk = PQKem.kemPk sk := by
  dsimp only [PQKem.invertKemPublicKey] at h
  have hpack := Bytes.pack_view? PQKem.Pk.SubF pk
  rcases hpk : pk.view? PQKem.Pk.SubF with _ | ⟨sk'⟩
  · rw [hpk] at h; cases h
  · rw [hpk] at h hpack
    injection h with hsk
    subst hsk
    exact hpack.symm

theorem DhClass.is_rnd {tr : ExecTrace} {r : Bytes} (h : DhClass tr r) :
    ∃ t n, r = rnd t n := by
  rcases h with ⟨_, t, rfl, _⟩ | ⟨_, t, rfl, _⟩ | ⟨_, t, rfl, _⟩ |
    ⟨t, rfl, _⟩ | ⟨t, rfl, _⟩ | ⟨t, _, rfl, _⟩
  · exact ⟨t, 32, rfl⟩
  · exact ⟨t, 32, rfl⟩
  · exact ⟨t, 32, rfl⟩
  · exact ⟨t, 32, rfl⟩
  · exact ⟨t + 2, 32, rfl⟩
  · exact ⟨t, 32, rfl⟩

theorem PQClass.is_rnd {tr : ExecTrace} {r : Bytes} (h : PQClass tr r) :
    ∃ t n, r = rnd t n := by
  obtain ⟨_, t, rfl, _⟩ := h
  exact ⟨t, 64, rfl⟩

theorem eventLogged_of_someEventB {tr : ExecTrace} {p : PQXDHEvent → Bool}
    (h : (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) tr p = true) : ∃ ev i, tr.EventLoggedAt ev i ∧ p ev = true := by
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h
  rw [List.any_eq_true] at h
  obtain ⟨i, _, hm⟩ := h
  rcases he : (tr.at? i : Option EvEntry) with _ | ⟨⟨ev⟩⟩
  · rw [he] at hm; cases hm
  · rw [he] at hm
    exact ⟨ev, i, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr he, hm⟩

theorem eventLogged_of_brokenDHB {tr : ExecTrace} (h : brokenDHB tr = true) :
    tr.EventLogged PQXDHEvent.BrokenDH := by
  obtain ⟨ev, i, hev, hp⟩ := eventLogged_of_someEventB h
  cases ev <;> try contradiction
  exact ⟨i, hev⟩

theorem eventLogged_of_brokenKEMB {tr : ExecTrace} (h : brokenKEMB tr = true) :
    tr.EventLogged PQXDHEvent.BrokenKEM := by
  obtain ⟨ev, i, hev, hp⟩ := eventLogged_of_someEventB h
  cases ev <;> try contradiction
  exact ⟨i, hev⟩

theorem Preserves.bind_guardOnTrace {Inv : ExecTrace → Prop} {α : Type}
    (p : ExecTrace → Bool) {f : Unit → Traceful α}
    (hf : ∀ tr, Inv tr → p tr = true → Inv ((f ()).run tr).2.val) :
    Preserves Inv (DY.Libsignal.PQXDH.guardTrace p >>= f) := by
  intro tr hInv
  rw [run_bind_snd]
  unfold DY.Libsignal.PQXDH.guardTrace
  rw [Traceful.run_mk]
  dsimp only
  by_cases hp : p tr = true
  · rw [ite_eq_left_iff.mpr fun h => absurd hp h]
    exact hf tr hInv hp
  · rw [ite_eq_right_iff.mpr fun h => absurd h hp]
    exact hInv

theorem preserves_compromiseIK_step (p : Participant) (stateIdx : Nat) :
    Preserves SpqrInv (compromiseIK p stateIdx) := by
  intro tr hinv
  unfold compromiseIK
  refine bind_getKey_at p stateIdx .identity tr hinv fun sk hst => ?_
  have hik : IKAt tr p sk := hinv.stOK p { kind := .identity, sk := sk } stateIdx hst
  let tr1 := tr.append (EvE (PQXDHEvent.CompromisedIK p (DiffieHellman.dhPk sk)))
  have hle1 : tr ≤ tr1 := Trace.append_le tr _
  have hinv1 : SpqrInv tr1 :=
    append_expose_ev hinv (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩)
  have hik1 : IKAt tr1 p sk := hik.mono hle1
  have hev1 : tr1.EventLogged (PQXDHEvent.CompromisedIK p (DiffieHellman.dhPk sk)) :=
    eventLogged_append_ev_iff.mpr (.inr rfl)
  obtain ⟨t, rfl, _, _⟩ := hik
  exact run_bind_logEvent _ (run_sendMessage _ (append_net_of_pub hinv1 (Pub.rand (.inl ⟨p, hik1, hev1⟩))))

theorem preserves_compromiseSPK_step (b : Participant) (stateIdx : Nat) :
    Preserves SpqrInv (compromiseSPK b stateIdx) := by
  intro tr hinv
  unfold compromiseSPK
  refine bind_getKey_at b stateIdx .signedPrekey tr hinv fun sk hst => ?_
  have hspk : SPKAt tr b sk := hinv.stOK b { kind := .signedPrekey, sk := sk } stateIdx hst
  let tr1 := tr.append (EvE (PQXDHEvent.CompromisedSPK b (DiffieHellman.dhPk sk)))
  have hle1 : tr ≤ tr1 := Trace.append_le tr _
  have hinv1 : SpqrInv tr1 :=
    append_expose_ev hinv (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩)
  have hspk1 : SPKAt tr1 b sk := hspk.mono hle1
  have hev1 : tr1.EventLogged (PQXDHEvent.CompromisedSPK b (DiffieHellman.dhPk sk)) :=
    eventLogged_append_ev_iff.mpr (.inr rfl)
  obtain ⟨t, rfl, _, _, _⟩ := hspk
  exact run_bind_logEvent _ (run_sendMessage _
    (append_net_of_pub hinv1 (Pub.rand (.inr (.inl ⟨b, hspk1, hev1⟩)))))

theorem preserves_compromisePQSPK_step (b : Participant) (stateIdx : Nat) :
    Preserves SpqrInv (compromisePQSPK b stateIdx) := by
  intro tr hinv
  unfold compromisePQSPK
  refine bind_getKey_at b stateIdx .pqPrekey tr hinv fun sk hst => ?_
  have hpq : PQAt tr b sk := hinv.stOK b { kind := .pqPrekey, sk := sk } stateIdx hst
  let tr1 := tr.append (EvE (PQXDHEvent.CompromisedPQSPK b (PQKem.kemPk sk)))
  have hle1 : tr ≤ tr1 := Trace.append_le tr _
  have hinv1 : SpqrInv tr1 :=
    append_expose_ev hinv (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩)
  have hpq1 : PQAt tr1 b sk := hpq.mono hle1
  have hev1 : tr1.EventLogged (PQXDHEvent.CompromisedPQSPK b (PQKem.kemPk sk)) :=
    eventLogged_append_ev_iff.mpr (.inr rfl)
  obtain ⟨t, rfl, _, _, _⟩ := hpq
  exact run_bind_logEvent _ (run_sendMessage _
    (append_net_of_pub hinv1 (Pub.rand (.inr (.inr (.inl ⟨b, hpq1, hev1⟩))))))

theorem preserves_compromiseOPK_step (b : Participant) (stateIdx : Nat) :
    Preserves SpqrInv (compromiseOPK b stateIdx) := by
  intro tr hinv
  unfold compromiseOPK
  refine bind_getKey_at b stateIdx .oneTimePrekey tr hinv fun sk hst => ?_
  refine bind_guardOnTrace_at (fun tr => !opkUsedB tr b (DiffieHellman.dhPk sk)) tr hinv fun hguard => ?_
  have hUnused : opkUsedB tr b (DiffieHellman.dhPk sk) = false :=
    Bool.eq_false_iff.mpr (by simpa using hguard)
  have hopk : OPKAt tr b sk := hinv.stOK b { kind := .oneTimePrekey, sk := sk } stateIdx hst
  let tr1 := tr.append (EvE (PQXDHEvent.CompromisedOPK b (DiffieHellman.dhPk sk)))
  have hle1 : tr ≤ tr1 := Trace.append_le tr _
  have hinv1 : SpqrInv tr1 :=
    append_expose_ev hinv (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩)
      (by rintro _ _ ⟨⟩; exact hUnused)
  have hopk1 : OPKAt tr1 b sk := hopk.mono hle1
  have hev1 : tr1.EventLogged (PQXDHEvent.CompromisedOPK b (DiffieHellman.dhPk sk)) :=
    eventLogged_append_ev_iff.mpr (.inr rfl)
  obtain ⟨t, rfl, _, _⟩ := hopk
  exact run_bind_logEvent _ (run_sendMessage _
    (append_net_of_pub hinv1 (Pub.rand (.inr (.inr (.inr (.inl ⟨b, hopk1, hev1⟩)))))))

theorem preserves_breakDH_step : Preserves SpqrInv breakDH := by
  intro tr hinv
  unfold breakDH
  exact run_logEvent _
    (append_expose_ev hinv (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩))

theorem preserves_breakKEM_step : Preserves SpqrInv breakKEM := by
  intro tr hinv
  unfold breakKEM
  exact run_logEvent _
    (append_expose_ev hinv (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩) (by intros; rintro ⟨⟩))

theorem preserves_invertDH_step (pkIdx : Nat) : Preserves SpqrInv (invertDH pkIdx) := by
  unfold invertDH
  refine Preserves.bind_guardOnTrace brokenDHB fun tr hinv hbrok => ?_
  have hBrokenDH : tr.EventLogged PQXDHEvent.BrokenDH := eventLogged_of_brokenDHB hbrok
  refine bind_receiveMessage_at pkIdx tr hinv fun pk hnet _ => ?_
  have hpub_pk : Pub tr pk := hinv.netPub pk (NetAt.baseAttackerKnows hnet)
  have hpub_x : Pub tr (X25519.normalizeX25519Key pk) := Pub.normalizeX25519Key hinv hpub_pk
  rcases hdh : extractDhSecretKey (X25519.normalizeX25519Key pk) with _ | sk
  · dsimp only; exact run_failure_end hinv
  · dsimp only
    rw [dhSkOf_eq_some hdh] at hpub_x
    have hpub_sk : Pub tr sk := by
      rcases Pub.inv_dhPk hinv hpub_x with hcls | hpub
      · obtain ⟨t, n, rfl⟩ := DhClass.is_rnd hcls
        exact Pub.rand (.inr (.inr (.inr (.inr (.inl ⟨hcls, hBrokenDH⟩)))))
      · exact hpub
    exact run_sendMessage sk (append_net_of_pub hinv hpub_sk)

theorem preserves_invertKEM_step (pkIdx : Nat) : Preserves SpqrInv (invertKEM pkIdx) := by
  unfold invertKEM
  refine Preserves.bind_guardOnTrace brokenKEMB fun tr hinv hbrok => ?_
  have hBrokenKEM : tr.EventLogged PQXDHEvent.BrokenKEM := eventLogged_of_brokenKEMB hbrok
  refine bind_receiveMessage_at pkIdx tr hinv fun pk hnet _ => ?_
  have hpub_pk : Pub tr pk := hinv.netPub pk (NetAt.baseAttackerKnows hnet)
  rcases hkem : PQKem.invertKemPublicKey pk with _ | sk
  · dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift]
    rw [run_bind_snd, Traceful.run_mk]
    exact hinv
  · dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift]
    rw [run_bind_snd, Traceful.run_mk]
    rw [kemPkInvert_eq_some hkem] at hpub_pk
    have hpub_sk : Pub tr sk := by
      rcases Pub.inv_kemPk hinv hpub_pk with hcls | hpub
      · obtain ⟨t, n, rfl⟩ := PQClass.is_rnd hcls
        exact Pub.rand (.inr (.inr (.inr (.inr (.inr (.inl ⟨hcls, hBrokenKEM⟩))))))
      · exact hpub
    exact run_sendMessage sk (append_net_of_pub hinv hpub_sk)

/-! ## `aliceStart` Transition -/

theorem bind_lookupIdentity_at {Inv : ExecTrace → Prop} {α : Type}
    (p : Participant) (regIdx : Nat) {f : Bytes × Bytes → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ ikPk vkPk honest,
      tr.EventLoggedAt (PQXDHEvent.IdentityRegistered p ikPk vkPk honest) regIdx →
      Inv ((f (ikPk, vkPk)).run tr).2.val) :
    Inv (((lookupIdentity p regIdx >>= f).run tr).2.val) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  have hge2 : ((DY.getEntry regIdx : Traceful EvEntry).run tr).2.val = tr := by
    simp only [Symbolic.DYBridge.DY.getEntry_eq_1]
    rw [Traceful.run_mk]
  rw [run_bind_assoc_snd, run_bind_snd, hge2]
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [Traceful.run_mk]
  dsimp only
  rcases he : (tr.at? regIdx : Option EvEntry) with _ | ⟨⟨ev⟩⟩
  · exact hInv
  · dsimp only
    cases ev with
    | IdentityRegistered p' ikPk vkPk honest =>
      dsimp only
      rw [run_bind_assoc_snd]
      refine bind_guard_at (p' = p) tr hInv fun hp => ?_
      subst hp
      rw [run_pure_bind_snd]
      exact hf ikPk vkPk honest ((Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr he)
    | _ =>
      dsimp only
      rw [run_bind_snd, Traceful.run_failure]
      exact hInv

def aliceOut (tr : ExecTrace) (ikA ikBPk spkPk pqPk : Bytes) (opk : Option Bytes) :
    AliceHandshakeOut :=
  let ek := rnd tr.length 32
  let e := rnd (tr.length + 1) 32
  { ikA := DiffieHellman.dhPk ikA, ikB := ikBPk, spk := spkPk, pqpk := pqPk, opk,
    ek := DiffieHellman.dhPk ek,
    ct := (aliceAgreement ikA ek ikBPk spkPk pqPk opk e).1,
    keys := (aliceAgreement ikA ek ikBPk spkPk pqPk opk e).2 }

def aliceHandshakeJp (ikA ikB spk pqpk : Bytes) (opk : Option Bytes) :
    Traceful AliceHandshakeOut := do
  let ek ← Random.genRand 32
  guard (!x25519LowOrder spk)
  guard (opk.all fun o => !x25519LowOrder o)
  let entropy ← Random.genRand 32
  let (ct, keys) := aliceAgreement ikA ek ikB spk pqpk opk entropy
  pure { ikA := DiffieHellman.dhPk ikA, ikB, spk, pqpk, opk, ek := DiffieHellman.dhPk ek, ct, keys }

theorem bind_aliceHandshakeJp_at {Inv : ExecTrace → Prop} {α : Type}
    (ikA ikB spk pqpk : Bytes) (opk : Option Bytes)
    {f : AliceHandshakeOut → Traceful α}
    (tr : ExecTrace) (habort : Inv (tr.append (RndE 32)))
    (hf : x25519LowOrder spk = false →
      (opk.all fun o => !x25519LowOrder o) = true →
      Inv ((f (aliceOut tr ikA ikB spk pqpk opk)).run
        ((tr.append (RndE 32)).append (RndE 32))).2.val) :
    Inv (((aliceHandshakeJp ikA ikB spk pqpk opk >>= f).run tr).2.val) := by
  unfold aliceHandshakeJp
  rw [run_bind_assoc_snd, run_genRand_bind_snd, run_bind_assoc_snd]
  refine bind_guard_at _ (tr.append (RndE 32)) habort fun hlo1 => ?_
  rw [run_bind_assoc_snd]
  refine bind_guard_at _ (tr.append (RndE 32)) habort fun hlo2 => ?_
  rw [run_bind_assoc_snd, run_genRand_bind_snd, run_pure_bind_snd]
  rw [append_len tr (RndE 32)]
  have hlow : x25519LowOrder spk = false := by revert hlo1; cases x25519LowOrder spk <;> decide
  exact hf hlow hlo2

theorem bind_aliceHandshake_at {Inv : ExecTrace → Prop} {α : Type}
    (a b : Participant) (idStateIdx regIdxB : Nat) (bh : BundleHandles)
    {f : AliceHandshakeOut → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (habort : Inv (tr.append (RndE 32)))
    (hf : ∀ (ikA ikB vkB spk spkSig pqpk pqpkSig : Bytes)
      (opk : Option Bytes) (honest : Bool),
      StoredAt tr a { kind := .identity, sk := ikA } idStateIdx →
      tr.EventLoggedAt (PQXDHEvent.IdentityRegistered b ikB vkB honest) regIdxB →
      spkSig.AttackerKnows tr →
      pqpkSig.AttackerKnows tr →
      Signature.verify vkB (encodeEC spk) spkSig = true →
      Signature.verify vkB (encodeKEM pqpk) pqpkSig = true →
      Inv ((f (aliceOut tr ikA ikB spk pqpk opk)).run
        ((tr.append (RndE 32)).append (RndE 32))).2.val) :
    Inv (((aliceHandshake a b idStateIdx regIdxB bh >>= f).run tr).2.val) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  rw [run_bind_assoc_snd]
  apply bind_getKey_at a idStateIdx .identity tr hInv; intro ikA hstA
  rw [run_bind_assoc_snd]
  apply bind_lookupIdentity_at b regIdxB tr hInv; intro ikB vkB honest hregB
  rw [run_bind_assoc_snd]
  apply bind_receiveMessage_at bh.spk tr hInv; intro spk _ _
  rw [run_bind_assoc_snd]
  apply bind_receiveMessage_at bh.spkSig tr hInv; intro spkSig _ hspkSig
  rw [run_bind_assoc_snd]
  apply bind_receiveMessage_at bh.pqpk tr hInv; intro pqpk _ _
  rw [run_bind_assoc_snd]
  apply bind_receiveMessage_at bh.pqpkSig tr hInv; intro pqpkSig _ hpqSig
  rw [run_bind_assoc_snd]
  apply bind_guard_at _ tr hInv; intro hv1
  rw [run_bind_assoc_snd]
  apply bind_guard_at _ tr hInv; intro hv2
  rcases hbh : bh.opk with _ | opkIdx
  · change Inv ((((Pure.pure none : Traceful (Option Bytes)) >>=
      aliceHandshakeJp ikA ikB spk pqpk >>= f).run tr).2.val)
    rw [run_bind_assoc_snd, run_pure_bind_snd]
    exact bind_aliceHandshakeJp_at ikA ikB spk pqpk none tr habort fun _ _ =>
      hf ikA ikB vkB spk spkSig pqpk pqpkSig none honest hstA hregB hspkSig hpqSig hv1 hv2
  · change Inv ((((Network.receiveMessage opkIdx >>= fun o =>
        (Pure.pure (some o) : Traceful (Option Bytes)) >>=
          aliceHandshakeJp ikA ikB spk pqpk) >>= f).run tr).2.val)
    rw [run_bind_assoc_snd]
    apply bind_receiveMessage_at opkIdx tr hInv; intro o _ _
    rw [run_bind_assoc_snd, run_pure_bind_snd]
    exact bind_aliceHandshakeJp_at ikA ikB spk pqpk (some o) tr habort fun _ _ =>
      hf ikA ikB vkB spk spkSig pqpk pqpkSig (some o) honest hstA hregB hspkSig hpqSig hv1 hv2

theorem preserves_aliceStart_step (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) :
    Preserves SpqrInv (aliceStart a b idStateIdx regIdxB bh) := by
  intro tr hinv
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hinv (append_rnd hinv 32)
    fun ikA ikBPk vkBPk spkPk spkSig pqPk pqSig opk honest hstA hregB hspkSig hpqSig hv1 hv2 => ?_
  have hikA : IKAt tr a ikA := hinv.stOK a { kind := .identity, sk := ikA } idStateIdx hstA
  have hbundle : BundleOK tr b ikBPk spkPk pqPk (tr.length + 5) :=
    bundleOK_of_verify hinv hregB hspkSig hpqSig hv1 hv2 (by omega)
  let hs := aliceOut tr ikA ikBPk spkPk pqPk opk
  let tr1 := tr.append (RndE 32)
  let tr2 := tr1.append (RndE 32)
  let dhsA := rnd tr2.length 32
  let rkA := (createChain hs.keys.rk hs.spk dhsA).1
  let cksA := (createChain hs.keys.rk hs.spk dhsA).2
  let stA : TRState :=
    { peer := b, myIk := serializedIk hs.ikA, peerIk := serializedIk hs.ikB,
      rk := rkA, dhs := dhsA, cks := cksA, ns := 0, pn := 0,
      sid := Concat.concat (DiffieHellman.dhPk dhsA) hs.keys.rk,
      initiator := true, rIdx := 1,
      recv := [{ ratchetKey := hs.spk, chainKey := hs.keys.ck, index := 0, rIdx := 1 }],
      spqr := Spqr.spqrInit hs.keys.pqr spqrA2B }
  let tr3 := tr2.append (RndE 32); let tr4 := tr3.append (NetE hs.ek)
  let tr5 := tr4.append (NetE hs.ct)
  let tr6 := tr5.append (EvE (PQXDHEvent.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys))
  let tr7 := tr6.append (TREvE (TREvent.InitSession a b (DiffieHellman.dhPk dhsA) hs.spk))
  let tr8 := tr7.append (CEvE (ComposedEvent.HandshakeSession (stA.sessionInfo a) tr5.length))
  let tr9 := tr8.append (TRStE a stA)
  rw [run_genRand_bind_snd]
  dsimp only
  refine run_bind_sendMessage hs.ek tr3 ?_
  refine run_bind_sendMessage hs.ct tr4 ?_
  refine run_bind_traceLength ?_
  refine run_bind_logEvent
    (PQXDHEvent.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys) ?_
  refine run_bind_logEvent (TREvent.InitSession a b (DiffieHellman.dhPk dhsA) hs.spk) ?_
  refine run_bind_logEvent (ComposedEvent.HandshakeSession (stA.sessionInfo a) tr5.length) ?_
  refine run_storeLocalState a stA ?_
  change SpqrInv tr9
  have hlen1 : tr1.length = tr.length + 1 := append_len tr (RndE 32)
  have hlen2 : tr2.length = tr.length + 2 := by rw [append_len tr1 (RndE 32), hlen1]
  have hlen3 : tr3.length = tr.length + 3 := by rw [append_len tr2 (RndE 32), hlen2]
  have hlen4 : tr4.length = tr.length + 4 := by rw [append_len tr3 (NetE hs.ek), hlen3]
  have hlen5 : tr5.length = tr.length + 5 := by rw [append_len tr4 (NetE hs.ct), hlen4]
  have hle01 : tr ≤ tr1 := Trace.append_le tr _; have hle12 : tr1 ≤ tr2 := Trace.append_le tr1 _
  have hle23 : tr2 ≤ tr3 := Trace.append_le tr2 _; have hle34 : tr3 ≤ tr4 := Trace.append_le tr3 _
  have hle45 : tr4 ≤ tr5 := Trace.append_le tr4 _; have hle56 : tr5 ≤ tr6 := Trace.append_le tr5 _
  have hle67 : tr6 ≤ tr7 := Trace.append_le tr6 _; have hle78 : tr7 ≤ tr8 := Trace.append_le tr7 _
  have hle89 : tr8 ≤ tr9 := Trace.append_le tr8 _
  have hle02 : tr ≤ tr2 := Trace.le_trans tr tr1 tr2 hle01 hle12
  have hle03 : tr ≤ tr3 := Trace.le_trans tr tr2 tr3 hle02 hle23
  have hle04 : tr ≤ tr4 := Trace.le_trans tr tr3 tr4 hle03 hle34
  have hle05 : tr ≤ tr5 := Trace.le_trans tr tr4 tr5 hle04 hle45
  have hle06 : tr ≤ tr6 := Trace.le_trans tr tr5 tr6 hle05 hle56
  have hle07 : tr ≤ tr7 := Trace.le_trans tr tr6 tr7 hle06 hle67
  have hle08 : tr ≤ tr8 := Trace.le_trans tr tr7 tr8 hle07 hle78
  have hle09 : tr ≤ tr9 := Trace.le_trans tr tr8 tr9 hle08 hle89
  have hle46 : tr4 ≤ tr6 := Trace.le_trans tr4 tr5 tr6 hle45 hle56
  have hle36 : tr3 ≤ tr6 := Trace.le_trans tr3 tr4 tr6 hle34 hle46
  have hle26 : tr2 ≤ tr6 := Trace.le_trans tr2 tr3 tr6 hle23 hle36
  have hle16 : tr1 ≤ tr6 := Trace.le_trans tr1 tr2 tr6 hle12 hle26
  have hle68 : tr6 ≤ tr8 := Trace.le_trans tr6 tr7 tr8 hle67 hle78
  have hle69 : tr6 ≤ tr9 := Trace.le_trans tr6 tr8 tr9 hle68 hle89
  have hr0 : RandAt tr6 tr.length 32 := (randAt_here tr 32).mono hle16
  have hr1 : RandAt tr6 (tr.length + 1) 32 := hlen1 ▸ (randAt_here tr1 32).mono hle26
  have hr2 : RandAt tr6 (tr.length + 2) 32 := hlen2 ▸ (randAt_here tr2 32).mono hle36
  have hn3 : NetAt tr6 hs.ek (tr.length + 3) := hlen3 ▸ (netAt_here tr3 hs.ek).mono hle46
  have hn4 : NetAt tr6 hs.ct (tr.length + 4) := hlen4 ▸ (netAt_here tr4 hs.ct).mono hle56
  have had5 : tr6.EventLoggedAt
      (PQXDHEvent.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys)
      (tr.length + 5) :=
    hlen5 ▸ eventLoggedAt_here tr5
      (PQXDHEvent.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys)
  have hslot6 : AliceSlot tr6 tr.length :=
    ⟨hr0, hr1, hr2, a, b, hs.ikA, hs.ikB, hs.spk, hs.pqpk, hs.opk, hs.ek, hs.ct, hs.keys,
      hn3, hn4, had5⟩
  have hslot9 : AliceSlot tr9 tr.length := hslot6.mono hle69
  have hek_pub9 : Pub tr9 hs.ek := Pub.dhPub (.inr (.inr (.inr (.inl ⟨tr.length, rfl, hslot9⟩))))
  have hct_pub9 : Pub tr9 hs.ct := Pub.encap pqPk (rnd (tr.length + 1) 32)
  have had_facts6 : AliceDoneFacts tr6 a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys
      (tr.length + 5) :=
    ⟨tr.length, ikA, rfl, hslot6, hikA.mono hle06, rfl, rfl, Prod.ext rfl rfl, hbundle.mono hle06⟩
  have hstA_ok9 : TRStateOK tr9 a stA := by
    refine ⟨tr5.length, hs.keys, by simp only [tr9, tr8, tr7, tr6, append_len]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨a, b, hs.ikA, hs.ikB, hs.spk, hs.pqpk, hs.opk, .inl ⟨hs.ek, hs.ct, hlen5.symm ▸ evAt_mono hle69 had5⟩⟩
    · exact ⟨tr7.length, evAt_mono hle89 (eventLoggedAt_here tr7 (ComposedEvent.HandshakeSession (stA.sessionInfo a) tr5.length))⟩
    · exact .inl ⟨tr.length, congrArg (rnd · 32) hlen2, hslot9⟩
    · exact .init (.literal _)
    · exact ⟨hs.keys.rk, hs.spk, dhsA, rfl⟩
    · exact ⟨hs.keys.rk, hs.spk, dhsA, 0, .inl rfl, rfl⟩
    · intro c hc; simp only [stA, List.mem_singleton] at hc; subst hc; exact .inl ⟨rfl, rfl, rfl⟩
  refine
    { netPub := fun x hx => ?_, stOK := fun me st idx hst => ?_,
      trStOK := fun me st idx hst => ?_, skipOK := fun s rPk ctr seed rIdx src idx hev => ?_,
      irHonest := fun p ik vkp r hev => ?_, irCorrupt := fun p ik vkp r hev => ?_,
      aliceDone := fun a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys' i hev => ?_,
      bobDone := fun b' a' ikB' ikA' spk' pqpk' opk' ek' ct' keys' i hev => ?_,
      opkOrder := ((((((((hinv.opkOrder.append_other rfl).append_other rfl).append_other rfl).append_other rfl).append_other rfl).append_ev
        (fun _ _ _ _ _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h)).append_other rfl).append_other rfl).append_other rfl }
  · have hx8 := (baseAttackerKnows_append_trSt tr8 a stA x).mp hx
    have hx7 := (baseAttackerKnows_append_cEv tr7 _ x).mp hx8
    have hx6 := (baseAttackerKnows_append_trEv tr6 _ x).mp hx7
    have hx5 := (baseAttackerKnows_append_ev tr5 _ x).mp hx6
    rcases (baseAttackerKnows_append_net tr4 hs.ct x).mp hx5 with rfl | hx4
    · exact hct_pub9
    · rcases (baseAttackerKnows_append_net tr3 hs.ek x).mp hx4 with rfl | hx3
      · exact hek_pub9
      · have hx2 := (baseAttackerKnows_append_rnd tr2 32 x).mp hx3
        have hx1 := (baseAttackerKnows_append_rnd tr1 32 x).mp hx2
        exact (hinv.netPub x ((baseAttackerKnows_append_rnd tr 32 x).mp hx1)).mono hle09
  · have hst8 := storedAt_append_other hst rfl; have hst7 := storedAt_append_other hst8 rfl
    have hst6 := storedAt_append_other hst7 rfl; have hst5 := storedAt_append_other hst6 rfl
    have hst4 := storedAt_append_other hst5 rfl; have hst3 := storedAt_append_other hst4 rfl
    have hst2 := storedAt_append_other hst3 rfl; have hst1 := storedAt_append_other hst2 rfl
    exact (hinv.stOK me st idx (storedAt_append_other hst1 rfl)).mono hle09
  · rcases trStoredAt_append_trSt_iff.mp hst with ⟨_, hst8⟩ | ⟨rfl, rfl, rfl⟩
    · have hst7 := trStoredAt_append_other hst8 rfl; have hst6 := trStoredAt_append_other hst7 rfl
      have hst5 := trStoredAt_append_other hst6 rfl; have hst4 := trStoredAt_append_other hst5 rfl
      have hst3 := trStoredAt_append_other hst4 rfl; have hst2 := trStoredAt_append_other hst3 rfl
      have hst1 := trStoredAt_append_other hst2 rfl
      exact (hinv.trStOK me st idx (trStoredAt_append_other hst1 rfl)).mono hle09
    · exact hstA_ok9
  · have hev8 := eventLoggedAt_append_other hev rfl; have hev7 := eventLoggedAt_append_other hev8 rfl
    rcases eventLoggedAt_append_ev_iff.mp hev7 with ⟨_, hev6⟩ | ⟨_, hEq⟩
    · have hev5 := eventLoggedAt_append_other hev6 rfl; have hev4 := eventLoggedAt_append_other hev5 rfl
      have hev3 := eventLoggedAt_append_other hev4 rfl; have hev2 := eventLoggedAt_append_other hev3 rfl
      have hev1 := eventLoggedAt_append_other hev2 rfl
      exact (hinv.skipOK s rPk ctr seed rIdx src idx (eventLoggedAt_append_other hev1 rfl)).mono hle09
    · cases hEq
  · have hev8 := eventLoggedAt_append_other hev rfl; have hev7 := eventLoggedAt_append_other hev8 rfl
    have hev6 := eventLoggedAt_append_other hev7 rfl
    rcases eventLoggedAt_append_ev_iff.mp hev6 with ⟨_, hev5⟩ | ⟨_, hEq⟩
    · have hev4 := eventLoggedAt_append_other hev5 rfl; have hev3 := eventLoggedAt_append_other hev4 rfl
      have hev2 := eventLoggedAt_append_other hev3 rfl; have hev1 := eventLoggedAt_append_other hev2 rfl
      obtain ⟨s, hs', h1, h2⟩ := hinv.irHonest p ik vkp r (eventLoggedAt_append_other hev1 rfl)
      exact ⟨s, hs'.mono hle09, h1, h2⟩
    · cases hEq
  · have hev8 := eventLoggedAt_append_other hev rfl; have hev7 := eventLoggedAt_append_other hev8 rfl
    have hev6 := eventLoggedAt_append_other hev7 rfl
    rcases eventLoggedAt_append_ev_iff.mp hev6 with ⟨_, hev5⟩ | ⟨_, hEq⟩
    · have hev4 := eventLoggedAt_append_other hev5 rfl; have hev3 := eventLoggedAt_append_other hev4 rfl
      have hev2 := eventLoggedAt_append_other hev3 rfl; have hev1 := eventLoggedAt_append_other hev2 rfl
      exact evAt_mono hle09 (hinv.irCorrupt p ik vkp r (eventLoggedAt_append_other hev1 rfl))
    · cases hEq
  · have hev8 := eventLoggedAt_append_other hev rfl; have hev7 := eventLoggedAt_append_other hev8 rfl
    have hev6 := eventLoggedAt_append_other hev7 rfl
    rcases eventLoggedAt_append_ev_iff.mp hev6 with ⟨_, hev5⟩ | ⟨rfl, hEq⟩
    · have hev4 := eventLoggedAt_append_other hev5 rfl; have hev3 := eventLoggedAt_append_other hev4 rfl
      have hev2 := eventLoggedAt_append_other hev3 rfl; have hev1 := eventLoggedAt_append_other hev2 rfl
      exact (hinv.aliceDone a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys' i (eventLoggedAt_append_other hev1 rfl)).mono hle09
    · injection hEq with ha hb hikA' hikB' hspk' hpqpk' hopk' hek' hct' hkeys'
      subst ha hb hikA' hikB' hspk' hpqpk' hopk' hek' hct' hkeys'
      exact hlen5.symm ▸ had_facts6.mono hle69
  · have hev8 := eventLoggedAt_append_other hev rfl; have hev7 := eventLoggedAt_append_other hev8 rfl
    have hev6 := eventLoggedAt_append_other hev7 rfl
    rcases eventLoggedAt_append_ev_iff.mp hev6 with ⟨_, hev5⟩ | ⟨_, hEq⟩
    · have hev4 := eventLoggedAt_append_other hev5 rfl; have hev3 := eventLoggedAt_append_other hev4 rfl
      have hev2 := eventLoggedAt_append_other hev3 rfl; have hev1 := eventLoggedAt_append_other hev2 rfl
      exact (hinv.bobDone b' a' ikB' ikA' spk' pqpk' opk' ek' ct' keys' i (eventLoggedAt_append_other hev1 rfl)).mono hle09
    · cases hEq

end Symbolic.Swarm.COMPOSED.CompPresPQXDH

namespace Symbolic.Swarm.COMPOSED.CompInv

open DY
open DY.Libsignal.PQXDH hiding x25519LowOrder
open DY.Libsignal.Composed
open Symbolic.Swarm.COMPOSED.CompPresPQXDH

theorem preserves_net (msg : Bytes) (tr : ExecTrace) (hPre : msg.AttackerKnows tr)
    (hInv : SpqrInv tr) : SpqrInv ((Network.sendMessage msg).run tr).2.val :=
  preserves_net_step msg tr hPre hInv

theorem preserves_registerIdentity (p : Participant) :
    Preserves SpqrInv (registerIdentity p) :=
  preserves_registerIdentity_step p

theorem preserves_registerCorruptIdentity (p : Participant) (skIdx : Nat) :
    Preserves SpqrInv (registerCorruptIdentity p skIdx) :=
  preserves_registerCorruptIdentity_step p skIdx

theorem preserves_genSignedPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves SpqrInv (genSignedPrekey b idStateIdx) :=
  preserves_genSignedPrekey_step b idStateIdx

theorem preserves_genPQPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves SpqrInv (genPQPrekey b idStateIdx) :=
  preserves_genPQPrekey_step b idStateIdx

theorem preserves_genOneTimePrekey (b : Participant) :
    Preserves SpqrInv (genOneTimePrekey b) :=
  preserves_genOneTimePrekey_step b

theorem preserves_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat) (bh : BundleHandles) :
    Preserves SpqrInv (aliceStart a b idStateIdx regIdxB bh) :=
  preserves_aliceStart_step a b idStateIdx regIdxB bh

theorem preserves_compromiseIK (p : Participant) (stateIdx : Nat) :
    Preserves SpqrInv (compromiseIK p stateIdx) :=
  preserves_compromiseIK_step p stateIdx

theorem preserves_compromiseSPK (b : Participant) (stateIdx : Nat) :
    Preserves SpqrInv (compromiseSPK b stateIdx) :=
  preserves_compromiseSPK_step b stateIdx

theorem preserves_compromisePQSPK (b : Participant) (stateIdx : Nat) :
    Preserves SpqrInv (compromisePQSPK b stateIdx) :=
  preserves_compromisePQSPK_step b stateIdx

theorem preserves_compromiseOPK (b : Participant) (stateIdx : Nat) :
    Preserves SpqrInv (compromiseOPK b stateIdx) :=
  preserves_compromiseOPK_step b stateIdx

theorem preserves_breakDH : Preserves SpqrInv breakDH :=
  preserves_breakDH_step

theorem preserves_breakKEM : Preserves SpqrInv breakKEM :=
  preserves_breakKEM_step

theorem preserves_invertDH (pkIdx : Nat) : Preserves SpqrInv (invertDH pkIdx) :=
  preserves_invertDH_step pkIdx

theorem preserves_invertKEM (pkIdx : Nat) : Preserves SpqrInv (invertKEM pkIdx) :=
  preserves_invertKEM_step pkIdx

end Symbolic.Swarm.COMPOSED.CompInv
