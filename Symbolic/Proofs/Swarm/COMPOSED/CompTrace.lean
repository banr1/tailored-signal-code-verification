/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Model.Instance
public import Symbolic.Proofs.SpecLemmas.ModelProofDefs
import DY.Bytes.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.Random
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.ProtocolEvent
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState

/-!
# Composed Trace Entries, Monad Lemmas, and Reachability Induction

Defines entry abbreviations, prefix monotonicity and append lemmas, `BaseAttackerKnows`
simplifications, `Traceful` preservation combinators, handshake unpackers, and the 23-branch
reachability induction principle for `DY.Libsignal.Composed`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompTrace

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.PQKem DY.Signature DY.X25519
open DY.Libsignal.TripleRatchet (x25519LowOrder)
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg receiveSignalMsg verifyMacAndDecrypt
  traceLength guardTrace messageEncrypt messageEncryptAbort messageDecrypt messageDecryptSkipped
  exposeKey exposeSpqr exposeSkipped)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent KeyKind HandshakeKeys BundleHandles BobKeyHandles
  AliceHandshakeOut BobHandshakeOut encodeEC encodeKEM isCanonicalKey guardTrace getKey
  lookupIdentity aliceAgreement bobAgreement aliceHandshake bobHandshake registerIdentity
  registerCorruptIdentity genSignedPrekey genPQPrekey genOneTimePrekey compromiseIK compromiseSPK
  compromisePQSPK compromiseOPK breakDH breakKEM invertDH invertKEM)
open DY.Libsignal.Composed

/-! ## Entry Abbreviations and Random Terms -/

abbrev NetEntry : Type := Network.ExecEntryT
abbrev RndEntry : Type := Random.ExecEntryT
abbrev TREntry : Type := ProtocolEvent.ExecEntryT TREvent
abbrev PQXDHEntry : Type := ProtocolEvent.ExecEntryT PQXDHEvent
abbrev CEntry : Type := ProtocolEvent.ExecEntryT ComposedEvent
abbrev TRStEntry : Type :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
abbrev PQXDHStEntry : Type :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState PQXDHState)

abbrev NetE (msg : Bytes) : NetEntry := ⟨msg⟩
abbrev RndE (n : Nat) : RndEntry := ⟨n⟩
abbrev TREvE (ev : TREvent) : TREntry := ⟨ev⟩
abbrev PQEvE (ev : PQXDHEvent) : PQXDHEntry := ⟨ev⟩
abbrev CEvE (ev : ComposedEvent) : CEntry := ⟨ev⟩
abbrev TRStE (me : Participant) (st : TRState) : TRStEntry :=
  ⟨({ participant := me, state := st } : PersistentLocalState.LocalState TRState)⟩
abbrev PQStE (me : Participant) (st : PQXDHState) : PQXDHStEntry :=
  ⟨({ participant := me, state := st } : PersistentLocalState.LocalState PQXDHState)⟩

/-- Symbolic random term generated at trace index `t` with byte length `size`. -/
abbrev mkRand (t size : Nat) : Bytes :=
  BytesView.pack (SubF := Random.Random) { timestamp := t, size := size }

theorem mkRand_inj {t₁ s₁ t₂ s₂ : Nat} (h : mkRand t₁ s₁ = mkRand t₂ s₂) :
    t₁ = t₂ ∧ s₁ = s₂ := by
  have hv := congrArg (fun x : Bytes => x.view? Random.Random) h
  simp only [mkRand, BytesView.view_pack, Option.some.injEq, Random.Random.mk.injEq] at hv
  exact hv

/-! ## Trace Indexing, Monotonicity, and Cross-Entry Disjointness -/

theorem proj_inj_eq {E : Type} [ExecTraceTypes.Has E] (e : E) :
    (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by
  rw [TraceEntryHas.inj_proj_eq]

theorem at?_le_some {E : Type} [ExecTraceTypes.Has E] {tr tr' : ExecTrace} (hle : tr ≤ tr')
    {i : Nat} {x : E} (h : (tr.at? i : Option E) = some x) :
    (tr'.at? i : Option E) = some x := by
  have hat := Trace.at?_le (EntryT := E) tr tr' i hle
  rw [h] at hat
  exact hat

theorem at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]

theorem at?_append_here {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    ((tr.append e).at? tr.length : Option E) = some e :=
  Trace.at?_append tr e

theorem at?_append_cases {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    {tr : ExecTrace} {e : E1} {x : E2} {i : Nat}
    (h : ((tr.append e).at? i : Option E2) = some x) :
    (i < tr.length ∧ (tr.at? i : Option E2) = some x) ∨
    (i = tr.length ∧
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = some x) := by
  have hlt : i < (tr.append e).length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := E2) (tr.append e) i
    rw [h] at this; exact this
  have hlen : (tr.append e).length = tr.length + 1 := by
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rcases (show i < tr.length ∨ i = tr.length by omega) with hi | rfl
  · rw [at?_append_of_lt tr e hi] at h
    exact .inl ⟨hi, h⟩
  · simp only [Trace.at?, hlt, ↓reduceDIte] at h
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte] at h
    exact .inr ⟨rfl, h⟩

theorem at?_disjoint {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    {tr : ExecTrace} {i : Nat} {x₁ : E1} {x₂ : E2}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x₁ : ExecTrace.Entry) : Option E2) = none)
    (h₁ : (tr.at? i : Option E1) = some x₁)
    (h₂ : (tr.at? i : Option E2) = some x₂) : False := by
  rw [Trace.at?_eq_some] at h₁ h₂
  obtain ⟨_, hat₁⟩ := h₁
  obtain ⟨_, hat₂⟩ := h₂
  have hEq : (TraceEntryHas.inj x₁ : ExecTrace.Entry) = TraceEntryHas.inj x₂ :=
    hat₁.symm.trans hat₂
  have hp := congrArg (TraceEntryHas.proj : ExecTrace.Entry → Option E2) hEq
  rw [hnone, proj_inj_eq] at hp
  cases hp

/-! ## Events, Stored States, Randomness, Network, and Base Attacker Knowledge -/

theorem eventLoggedAt_mono {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr tr' : ExecTrace} (hle : tr ≤ tr') {ev : Ev} {i : Nat}
    (h : tr.EventLoggedAt ev i) : tr'.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_le_some hle h

theorem eventLogged_mono {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr tr' : ExecTrace} (hle : tr ≤ tr') {ev : Ev}
    (h : tr.EventLogged ev) : tr'.EventLogged ev :=
  let ⟨i, hi⟩ := h; ⟨i, eventLoggedAt_mono hle hi⟩

theorem eventLoggedAt_here {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    (tr : ExecTrace) (ev : Ev) :
    (tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT Ev)).EventLoggedAt ev tr.length := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  exact Trace.at?_append tr (⟨ev⟩ : ProtocolEvent.ExecEntryT Ev)

theorem eventLogged_here {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    (tr : ExecTrace) (ev : Ev) :
    (tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT Ev)).EventLogged ev :=
  ⟨tr.length, eventLoggedAt_here tr ev⟩

theorem eventLoggedAt_append_same {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr : ExecTrace} {ev₀ ev : Ev} {i : Nat}
    (h : (tr.append (⟨ev₀⟩ : ProtocolEvent.ExecEntryT Ev)).EventLoggedAt ev i) :
    (i < tr.length ∧ tr.EventLoggedAt ev i) ∨ (i = tr.length ∧ ev₀ = ev) := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  rcases at?_append_cases h with ⟨hi, h⟩ | ⟨rfl, hp⟩
  · exact .inl ⟨hi, h⟩
  · rw [proj_inj_eq] at hp; injection hp with hp; injection hp with hp
    exact .inr ⟨rfl, hp⟩

theorem eventLoggedAt_append_other {E Ev : Type}
    [ExecTraceTypes.Has E] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT Ev)) = none)
    {ev : Ev} {i : Nat} (h : (tr.append e).EventLoggedAt ev i) :
    tr.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  rcases at?_append_cases h with ⟨_, h⟩ | ⟨_, hp⟩
  · exact h
  · rw [hnone] at hp; cases hp

theorem eventLogged_append_same_iff {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr : ExecTrace} {ev₀ ev : Ev} :
    (tr.append (⟨ev₀⟩ : ProtocolEvent.ExecEntryT Ev)).EventLogged ev ↔
      tr.EventLogged ev ∨ ev₀ = ev := by
  constructor
  · rintro ⟨i, hi⟩
    rcases eventLoggedAt_append_same hi with ⟨_, hi⟩ | ⟨_, hEq⟩
    · exact .inl ⟨i, hi⟩
    · exact .inr hEq
  · rintro (⟨i, hi⟩ | rfl)
    · exact ⟨i, eventLoggedAt_mono (Trace.append_le tr _) hi⟩
    · exact eventLogged_here tr ev₀

theorem eventLogged_append_other_iff {E Ev : Type}
    [ExecTraceTypes.Has E] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT Ev)) = none)
    {ev : Ev} :
    (tr.append e).EventLogged ev ↔ tr.EventLogged ev :=
  ⟨fun ⟨i, hi⟩ => ⟨i, eventLoggedAt_append_other hnone hi⟩,
   eventLogged_mono (Trace.append_le tr e)⟩

/-- `TRState` snapshot `st` stored for participant `p` at trace index `i`. -/
abbrev TRStateStoredAt (p : Participant) (st : TRState) (i : Nat) (tr : ExecTrace) : Prop :=
  (tr.at? i : Option TRStEntry) = some (TRStE p st)

/-- `PQXDHState` entry `st` stored for participant `p` at trace index `i`. -/
def PQXDHStoredAt (tr : ExecTrace) (p : Participant) (st : PQXDHState) (i : Nat) : Prop :=
  (tr.at? i : Option PQXDHStEntry) = some (PQStE p st)

theorem trStateStoredAt_mono {tr tr' : ExecTrace} (hle : tr ≤ tr')
    {p : Participant} {st : TRState} {i : Nat}
    (h : TRStateStoredAt p st i tr) : TRStateStoredAt p st i tr' :=
  at?_le_some hle h

theorem pqxdhStoredAt_mono {tr tr' : ExecTrace} (hle : tr ≤ tr')
    {p : Participant} {st : PQXDHState} {i : Nat}
    (h : PQXDHStoredAt tr p st i) : PQXDHStoredAt tr' p st i :=
  at?_le_some hle h

theorem trStateStoredAt_here (tr : ExecTrace) (p : Participant) (st : TRState) :
    TRStateStoredAt p st tr.length (tr.append (TRStE p st)) :=
  Trace.at?_append tr (TRStE p st)

theorem trStateStoredAt_append_same {tr : ExecTrace} {p₀ p : Participant}
    {st₀ st : TRState} {j : Nat}
    (h : TRStateStoredAt p st j (tr.append (TRStE p₀ st₀))) :
    (j < tr.length ∧ TRStateStoredAt p st j tr) ∨ (j = tr.length ∧ p₀ = p ∧ st₀ = st) := by
  rcases at?_append_cases h with ⟨hj, h⟩ | ⟨rfl, hp⟩
  · exact .inl ⟨hj, h⟩
  · rw [proj_inj_eq] at hp; injection hp with hp; injection hp with hp; injection hp with hp1 hp2
    exact .inr ⟨rfl, hp1, hp2⟩

theorem trStateStoredAt_append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none)
    {p : Participant} {st : TRState} {j : Nat}
    (h : TRStateStoredAt p st j (tr.append e)) :
    TRStateStoredAt p st j tr := by
  rcases at?_append_cases h with ⟨_, h⟩ | ⟨_, hp⟩
  · exact h
  · rw [hnone] at hp; cases hp

theorem pqxdhStoredAt_append_same {tr : ExecTrace} {p₀ p : Participant}
    {st₀ st : PQXDHState} {j : Nat}
    (h : PQXDHStoredAt (tr.append (PQStE p₀ st₀)) p st j) :
    (j < tr.length ∧ PQXDHStoredAt tr p st j) ∨ (j = tr.length ∧ p₀ = p ∧ st₀ = st) := by
  rcases at?_append_cases h with ⟨hj, h⟩ | ⟨rfl, hp⟩
  · exact .inl ⟨hj, h⟩
  · rw [proj_inj_eq] at hp; injection hp with hp; injection hp with hp; injection hp with hp1 hp2
    exact .inr ⟨rfl, hp1, hp2⟩

theorem pqxdhStoredAt_append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHStEntry) = none)
    {p : Participant} {st : PQXDHState} {j : Nat}
    (h : PQXDHStoredAt (tr.append e) p st j) :
    PQXDHStoredAt tr p st j := by
  rcases at?_append_cases h with ⟨_, h⟩ | ⟨_, hp⟩
  · exact h
  · rw [hnone] at hp; cases hp

/-- Random draw of `n` bytes recorded at trace index `i`. -/
def RandAt (tr : ExecTrace) (i n : Nat) : Prop :=
  (tr.at? i : Option RndEntry) = some (RndE n)

theorem randAt_mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {i n : Nat}
    (h : RandAt tr i n) : RandAt tr' i n :=
  at?_le_some hle h

theorem randAt_here (tr : ExecTrace) (n : Nat) :
    RandAt (tr.append (RndE n)) tr.length n :=
  Trace.at?_append tr (RndE n)

/-- Network message `msg` recorded at trace index `idx`. -/
def NetMsgAt (msg : Bytes) (idx : Nat) (tr : ExecTrace) : Prop :=
  (tr.at? idx : Option NetEntry) = some (NetE msg)

theorem NetMsgAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {msg : Bytes} {idx : Nat}
    (h : NetMsgAt msg idx tr) : NetMsgAt msg idx tr' :=
  at?_le_some hle h

theorem NetMsgAt.baseAttackerKnows {msg : Bytes} {idx : Nat} {tr : ExecTrace}
    (h : NetMsgAt msg idx tr) : Trace.BaseAttackerKnows tr msg := by
  unfold NetMsgAt at h
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

theorem NetMsgAt.attackerKnows {msg : Bytes} {idx : Nat} {tr : ExecTrace}
    (h : NetMsgAt msg idx tr) : msg.AttackerKnows tr :=
  Bytes.AttackerKnows.prove_from_base msg tr h.baseAttackerKnows

@[simp] theorem baseAttackerKnows_append_net (tr : ExecTrace) (msg b : Bytes) :
    Trace.BaseAttackerKnows (tr.append (NetE msg)) b ↔
      b = msg ∨ Trace.BaseAttackerKnows tr b := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (NetE msg)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e b = (b = msg) :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e b).trans
      (Symbolic.DYBridge.DY.Network.baseAttackerKnowledge_attackerKnows tr (NetE msg) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]

@[simp] theorem baseAttackerKnows_append_rnd (tr : ExecTrace) (n : Nat) (b : Bytes) :
    Trace.BaseAttackerKnows (tr.append (RndE n)) b ↔ Trace.BaseAttackerKnows tr b := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (RndE n)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e b = False :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e b).trans
      (Symbolic.DYBridge.DY.Random.baseAttackerKnowledge_attackerKnows tr (RndE n) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)

@[simp] theorem baseAttackerKnows_append_trEv (tr : ExecTrace) (ev : TREvent) (b : Bytes) :
    Trace.BaseAttackerKnows (tr.append (TREvE ev)) b ↔ Trace.BaseAttackerKnows tr b := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (TREvE ev)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e b = False :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e b).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows TREvent tr (TREvE ev) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)

@[simp] theorem baseAttackerKnows_append_pqEv (tr : ExecTrace) (ev : PQXDHEvent) (b : Bytes) :
    Trace.BaseAttackerKnows (tr.append (PQEvE ev)) b ↔ Trace.BaseAttackerKnows tr b := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (PQEvE ev)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e b = False :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e b).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows PQXDHEvent tr (PQEvE ev) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)

@[simp] theorem baseAttackerKnows_append_cEv (tr : ExecTrace) (ev : ComposedEvent) (b : Bytes) :
    Trace.BaseAttackerKnows (tr.append (CEvE ev)) b ↔ Trace.BaseAttackerKnows tr b := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (CEvE ev)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e b = False :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e b).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows ComposedEvent tr (CEvE ev) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)

@[simp] theorem baseAttackerKnows_append_trSt (tr : ExecTrace) (me : Participant) (st : TRState)
    (b : Bytes) :
    Trace.BaseAttackerKnows (tr.append (TRStE me st)) b ↔ Trace.BaseAttackerKnows tr b := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (TRStE me st)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e b = False :=
    (((Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e b).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.CompromisableState.baseAttackerKnowledge.internal TRState) tr e.entry b)).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.State.baseAttackerKnowledge.internal TRState) tr e.entry.entry b)).trans
      (Symbolic.DYBridge.DY.PersistentGlobalState.State.baseAttackerKnowledge_attackerKnows
        (PersistentLocalState.LocalState TRState) tr (TRStE me st) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)

@[simp] theorem baseAttackerKnows_append_pqSt (tr : ExecTrace) (me : Participant) (st : PQXDHState)
    (b : Bytes) :
    Trace.BaseAttackerKnows (tr.append (PQStE me st)) b ↔ Trace.BaseAttackerKnows tr b := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (PQStE me st)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e b = False :=
    (((Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e b).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.CompromisableState.baseAttackerKnowledge.internal PQXDHState) tr e.entry b)).trans
      (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
        (PersistentLocalState.State.baseAttackerKnowledge.internal PQXDHState) tr e.entry.entry b)).trans
      (Symbolic.DYBridge.DY.PersistentGlobalState.State.baseAttackerKnowledge_attackerKnows
        (PersistentLocalState.LocalState PQXDHState) tr (PQStE me st) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)

/-! ## Traceful Monad and Preservation Combinators -/

/-- A `Traceful` computation preserves trace predicate `Inv`. -/
def Preserves (Inv : ExecTrace → Prop) {α : Type} (m : Traceful α) : Prop :=
  ∀ tr, Inv tr → Inv (m.run tr).2.val

theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]; rcases x.run tr with ⟨_ | a, tr1⟩ <;> rfl

theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]; rcases x.run tr with ⟨_ | a, tr1⟩ <;> rfl

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
      ((f (mkRand tr.length n)).run (tr.append (RndE n))).2.val := by
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [run_bind_assoc_snd, run_bind_snd, Traceful.run_mk]
  dsimp only
  rw [run_pure_bind_snd]

theorem Preserves.of_id {Inv : ExecTrace → Prop} {α : Type} {x : Traceful α}
    (hx : ∀ tr, (x.run tr).2.val = tr) : Preserves Inv x := by
  intro tr h; rw [hx]; exact h

theorem Preserves.pure {Inv : ExecTrace → Prop} {α : Type} (a : α) :
    Preserves Inv (Pure.pure a : Traceful α) :=
  Preserves.of_id fun _ => by rw [Traceful.run_pure]

theorem Preserves.failure {Inv : ExecTrace → Prop} {α : Type} :
    Preserves Inv (failure : Traceful α) :=
  Preserves.of_id fun _ => by rw [Traceful.run_failure]

theorem Preserves.guardP {Inv : ExecTrace → Prop} (p : Prop) [Decidable p] :
    Preserves Inv (_root_.guard p : Traceful Unit) := by
  unfold _root_.guard; split
  · exact Preserves.pure _
  · exact Preserves.failure

theorem Preserves.requireTracePredicate {Inv : ExecTrace → Prop} (p : ExecTrace → Bool) :
    Preserves Inv (DY.Libsignal.PQXDH.guardTrace p) :=
  Preserves.of_id fun _ => by unfold DY.Libsignal.PQXDH.guardTrace; rw [Traceful.run_mk]

theorem Preserves.guardTrace {Inv : ExecTrace → Prop} (p : ExecTrace → Bool) :
    Preserves Inv (guardTrace p) :=
  Preserves.of_id fun _ => by unfold DY.Libsignal.TripleRatchet.guardTrace; rw [Traceful.run_mk]

theorem Preserves.monadLiftErr {Inv : ExecTrace → Prop} {α : Type} (x : Err α) :
    Preserves Inv (monadLift x : Traceful α) :=
  Preserves.of_id fun _ => by dsimp [MonadLiftT.monadLift, MonadLift.monadLift]; rw [Traceful.run_mk]

theorem Preserves.traceLength {Inv : ExecTrace → Prop} :
    Preserves Inv traceLength :=
  Preserves.of_id fun _ => by unfold DY.Libsignal.TripleRatchet.traceLength; rw [Traceful.run_mk]

theorem Preserves.getEntry {Inv : ExecTrace → Prop} {E : Type} [ExecTraceTypes.Has E] (h : Nat) :
    Preserves Inv (DY.getEntry h : Traceful E) :=
  Preserves.of_id fun _ => by simp only [Symbolic.DYBridge.DY.getEntry_eq_1]; rw [Traceful.run_mk]

theorem Preserves.bind {Inv : ExecTrace → Prop} {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : Preserves Inv x) (hf : ∀ a, Preserves Inv (f a)) : Preserves Inv (x >>= f) := by
  intro tr hInv; rw [Traceful.run_bind]; rcases h : x.run tr with ⟨o, trMid, _⟩
  have hMid : Inv trMid := by have := hx tr hInv; rw [h] at this; exact this
  cases o with
  | none => exact hMid
  | some a => exact hf a trMid hMid

theorem bind_guardP_at {Inv : ExecTrace → Prop} {α : Type}
    (p : Prop) [Decidable p] {f : Unit → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (hf : p → Inv ((f ()).run tr).2.val) :
    Inv (((_root_.guard p >>= f).run tr).2.val) := by
  unfold _root_.guard
  by_cases hp : p
  · rw [ite_eq_left_iff.mpr fun h => absurd hp h, run_pure_bind_snd]
    exact hf hp
  · rw [ite_eq_right_iff.mpr fun h => absurd h hp, run_bind_snd, Traceful.run_failure]
    exact hInv

theorem Preserves.receiveMessage {Inv : ExecTrace → Prop} (h : Nat) :
    Preserves Inv (Network.receiveMessage h) := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact Preserves.bind (Preserves.getEntry _) fun _ => Preserves.pure _

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

theorem bind_receiveMessage_at {Inv : ExecTrace → Prop} {α : Type}
    (h : Nat) {f : Bytes → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ msg, NetMsgAt msg h tr → msg.AttackerKnows tr → Inv ((f msg).run tr).2.val) :
    Inv (((Network.receiveMessage h >>= f).run tr).2.val) := by
  rw [run_bind_snd, receiveMessage_fst, receiveMessage_snd]
  rcases he : (tr.at? h : Option NetEntry) with _ | ⟨⟨msg⟩⟩
  · exact hInv
  · exact hf msg he (NetMsgAt.attackerKnows he)

theorem Preserves.getLocalState_tr {Inv : ExecTrace → Prop} (p : Participant) (h : Nat) :
    Preserves Inv (PersistentLocalState.getLocalState p h : Traceful TRState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine Preserves.bind (Preserves.bind (Preserves.getEntry _) fun _ => Preserves.pure _) fun _ => ?_
  exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

theorem Preserves.getLocalState_pq {Inv : ExecTrace → Prop} (p : Participant) (h : Nat) :
    Preserves Inv (PersistentLocalState.getLocalState p h : Traceful PQXDHState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine Preserves.bind (Preserves.bind (Preserves.getEntry _) fun _ => Preserves.pure _) fun _ => ?_
  exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

theorem getLocalState_tr_fst (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 =
      match (tr.at? stH : Option TRStEntry) with
      | some ⟨⟨p, st⟩⟩ => if p = me then some st else none
      | none => none := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1,
    Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [run_bind_fst, run_bind_fst, run_bind_snd, Traceful.run_mk]
  rcases (tr.at? stH : Option TRStEntry) with _ | ⟨⟨p, st⟩⟩
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

theorem getLocalState_tr_snd (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).2.val = tr :=
  Preserves.getLocalState_tr (Inv := fun t => t = tr) me stH tr rfl

theorem bind_getLocalState_tr_at {Inv : ExecTrace → Prop} {α : Type}
    (me : Participant) (stH : Nat) {f : TRState → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ st, TRStateStoredAt me st stH tr → Inv ((f st).run tr).2.val) :
    Inv (((PersistentLocalState.getLocalState me stH >>= f).run tr).2.val) := by
  rw [run_bind_snd, getLocalState_tr_fst, getLocalState_tr_snd]
  rcases he : (tr.at? stH : Option TRStEntry) with _ | ⟨⟨p, st⟩⟩
  · exact hInv
  · dsimp only
    by_cases hp : p = me
    · subst hp; simp only [↓reduceIte]; exact hf st he
    · simp only [hp, ↓reduceIte]; exact hInv

theorem Preserves.bind_getLocalState_tr {Inv : ExecTrace → Prop} {α : Type}
    (me : Participant) (stH : Nat) {f : TRState → Traceful α}
    (hf : ∀ st tr, Inv tr → TRStateStoredAt me st stH tr → Inv ((f st).run tr).2.val) :
    Preserves Inv (PersistentLocalState.getLocalState me stH >>= f) :=
  fun tr hInv => bind_getLocalState_tr_at me stH tr hInv (fun st hst => hf st tr hInv hst)

theorem getLocalState_pq_fst (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful PQXDHState).run tr).1 =
      match (tr.at? stH : Option PQXDHStEntry) with
      | some ⟨⟨p, st⟩⟩ => if p = me then some st else none
      | none => none := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1,
    Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [run_bind_fst, run_bind_fst, run_bind_snd, Traceful.run_mk]
  rcases (tr.at? stH : Option PQXDHStEntry) with _ | ⟨⟨p, st⟩⟩
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

theorem getLocalState_pq_snd (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful PQXDHState).run tr).2.val = tr :=
  Preserves.getLocalState_pq (Inv := fun t => t = tr) me stH tr rfl

theorem bind_getLocalState_pq_at {Inv : ExecTrace → Prop} {α : Type}
    (me : Participant) (stH : Nat) {f : PQXDHState → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ st, PQXDHStoredAt tr me st stH → Inv ((f st).run tr).2.val) :
    Inv (((PersistentLocalState.getLocalState me stH >>= f).run tr).2.val) := by
  rw [run_bind_snd, getLocalState_pq_fst, getLocalState_pq_snd]
  rcases he : (tr.at? stH : Option PQXDHStEntry) with _ | ⟨⟨p, st⟩⟩
  · exact hInv
  · dsimp only
    by_cases hp : p = me
    · subst hp; simp only [↓reduceIte]; exact hf st he
    · simp only [hp, ↓reduceIte]; exact hInv

theorem Preserves.receiveSignalMsg {Inv : ExecTrace → Prop} (msgH : Nat) :
    Preserves Inv (receiveSignalMsg msgH) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

theorem Preserves.verifyMacAndDecrypt {Inv : ExecTrace → Prop} (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : Bytes) :
    Preserves Inv (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.monadLiftErr _

theorem verifyMacAndDecrypt_trace (st : TRState) (msg : TRSignalMsg) (pqSalt seed : Bytes)
    (tr : ExecTrace) :
    ((verifyMacAndDecrypt st msg pqSalt seed).run tr).2.val = tr :=
  Preserves.verifyMacAndDecrypt (Inv := fun t => t = tr) st msg pqSalt seed tr rfl

theorem bind_getKey_at {Inv : ExecTrace → Prop} {α : Type}
    (p : Participant) (stateIdx : Nat) (kind : KeyKind) {f : Bytes → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ sk, PQXDHStoredAt tr p { kind, sk } stateIdx → Inv ((f sk).run tr).2.val) :
    Inv (((getKey p stateIdx kind >>= f).run tr).2.val) := by
  unfold DY.Libsignal.PQXDH.getKey
  rw [run_bind_assoc_snd]
  refine bind_getLocalState_pq_at p stateIdx tr hInv fun st hst => ?_
  rw [run_bind_assoc_snd]
  refine bind_guardP_at (st.kind = kind) tr hInv fun hk => ?_
  rcases st with ⟨k, sk⟩
  cases hk
  exact hf sk hst

theorem bind_lookupIdentity_at {Inv : ExecTrace → Prop} {α : Type}
    (p : Participant) (regIdx : Nat) {f : Bytes × Bytes → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ ikPk vkPk honest,
      tr.EventLoggedAt (PQXDHEvent.IdentityRegistered p ikPk vkPk honest) regIdx →
      Inv ((f (ikPk, vkPk)).run tr).2.val) :
    Inv (((lookupIdentity p regIdx >>= f).run tr).2.val) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  have hge2 : ((DY.getEntry regIdx : Traceful PQXDHEntry).run tr).2.val = tr := by
    simp only [Symbolic.DYBridge.DY.getEntry_eq_1]
    rw [Traceful.run_mk]
  rw [run_bind_assoc_snd, run_bind_snd, hge2]
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [Traceful.run_mk]
  dsimp only
  rcases he : (tr.at? regIdx : Option PQXDHEntry) with _ | ⟨⟨ev⟩⟩
  · exact hInv
  · dsimp only
    cases ev with
    | IdentityRegistered p' ikPk vkPk honest =>
      dsimp only
      rw [run_bind_assoc_snd]
      refine bind_guardP_at (p' = p) tr hInv fun hp => ?_
      subst hp
      rw [run_pure_bind_snd]
      exact hf ikPk vkPk honest ((Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr he)
    | _ =>
      dsimp only
      rw [run_bind_snd, Traceful.run_failure]
      exact hInv

/-- Output record of `aliceHandshake` starting at trace `tr` (draws `ek` at `tr.length` and KEM
randomness `e` at `tr.length + 1`). -/
def aliceOut (tr : ExecTrace) (ikA ikBPk spkPk pqPk : Bytes) (opk : Option Bytes) :
    AliceHandshakeOut :=
  let ek := mkRand tr.length 32
  let e := mkRand (tr.length + 1) 32
  { ikA := dhPk ikA, ikB := ikBPk, spk := spkPk, pqpk := pqPk, opk, ek := dhPk ek,
    ct := (aliceAgreement ikA ek ikBPk spkPk pqPk opk e).1,
    keys := (aliceAgreement ikA ek ikBPk spkPk pqPk opk e).2 }

def aliceHandshakeJp (ikA ikB spk pqpk : Bytes) (opk : Option Bytes) :
    Traceful AliceHandshakeOut := do
  let ek ← Random.genRand 32
  guard (!x25519LowOrder spk)
  guard (opk.all fun o => !x25519LowOrder o)
  let entropy ← Random.genRand 32
  let (ct, keys) := aliceAgreement ikA ek ikB spk pqpk opk entropy
  pure { ikA := dhPk ikA, ikB, spk, pqpk, opk, ek := dhPk ek, ct, keys }

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
  refine bind_guardP_at _ (tr.append (RndE 32)) habort fun hlo1 => ?_
  rw [run_bind_assoc_snd]
  refine bind_guardP_at _ (tr.append (RndE 32)) habort fun hlo2 => ?_
  rw [run_bind_assoc_snd, run_genRand_bind_snd, run_pure_bind_snd]
  have hlen : (tr.append (RndE 32)).length = tr.length + 1 := by
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rw [hlen]
  have hlow : x25519LowOrder spk = false := by revert hlo1; cases x25519LowOrder spk <;> decide
  exact hf hlow hlo2

theorem bind_aliceHandshake_at {Inv : ExecTrace → Prop} {α : Type}
    (a b : Participant) (idStateIdx regIdxB : Nat) (bh : BundleHandles)
    {f : AliceHandshakeOut → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (habort : Inv (tr.append (RndE 32)))
    (hf : ∀ (ikA ikB vkB spk spkSig pqpk pqpkSig : Bytes)
      (opk : Option Bytes) (honest : Bool),
      PQXDHStoredAt tr a { kind := .identity, sk := ikA } idStateIdx →
      tr.EventLoggedAt (PQXDHEvent.IdentityRegistered b ikB vkB honest) regIdxB →
      NetMsgAt spk bh.spk tr →
      NetMsgAt spkSig bh.spkSig tr →
      NetMsgAt pqpk bh.pqpk tr →
      NetMsgAt pqpkSig bh.pqpkSig tr →
      Signature.verify vkB (encodeEC spk) spkSig = true →
      Signature.verify vkB (encodeKEM pqpk) pqpkSig = true →
      (∀ o, opk = some o → ∃ idx, bh.opk = some idx ∧ NetMsgAt o idx tr) →
      x25519LowOrder spk = false →
      (opk.all fun o => !x25519LowOrder o) = true →
      Inv ((f (aliceOut tr ikA ikB spk pqpk opk)).run
        ((tr.append (RndE 32)).append (RndE 32))).2.val) :
    Inv (((aliceHandshake a b idStateIdx regIdxB bh >>= f).run tr).2.val) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  rw [run_bind_assoc_snd]
  apply bind_getKey_at a idStateIdx .identity tr hInv; intro ikA hstA
  rw [run_bind_assoc_snd]
  apply bind_lookupIdentity_at b regIdxB tr hInv; intro ikB vkB honest hregB
  rw [run_bind_assoc_snd]
  apply bind_receiveMessage_at bh.spk tr hInv; intro spk hspk _
  rw [run_bind_assoc_snd]
  apply bind_receiveMessage_at bh.spkSig tr hInv; intro spkSig hspkSig _
  rw [run_bind_assoc_snd]
  apply bind_receiveMessage_at bh.pqpk tr hInv; intro pqpk hpq _
  rw [run_bind_assoc_snd]
  apply bind_receiveMessage_at bh.pqpkSig tr hInv; intro pqpkSig hpqSig _
  rw [run_bind_assoc_snd]
  apply bind_guardP_at _ tr hInv; intro hv1
  rw [run_bind_assoc_snd]
  apply bind_guardP_at _ tr hInv; intro hv2
  rcases hbh : bh.opk with _ | opkIdx
  · change Inv ((((Pure.pure none : Traceful (Option Bytes)) >>=
      aliceHandshakeJp ikA ikB spk pqpk >>= f).run tr).2.val)
    rw [run_bind_assoc_snd, run_pure_bind_snd]
    exact bind_aliceHandshakeJp_at ikA ikB spk pqpk none tr habort fun hlow _ =>
      hf ikA ikB vkB spk spkSig pqpk pqpkSig none honest hstA hregB
        hspk hspkSig hpq hpqSig hv1 hv2 (fun _ h => nomatch h) hlow rfl
  · change Inv ((((Network.receiveMessage opkIdx >>= fun o =>
        (Pure.pure (some o) : Traceful (Option Bytes)) >>=
          aliceHandshakeJp ikA ikB spk pqpk) >>= f).run tr).2.val)
    rw [run_bind_assoc_snd]
    apply bind_receiveMessage_at opkIdx tr hInv; intro o hopk _
    rw [run_bind_assoc_snd, run_pure_bind_snd]
    exact bind_aliceHandshakeJp_at ikA ikB spk pqpk (some o) tr habort fun hlow hlo2 =>
      hf ikA ikB vkB spk spkSig pqpk pqpkSig (some o) honest hstA hregB
        hspk hspkSig hpq hpqSig hv1 hv2
        (fun o' ho' => ⟨opkIdx, hbh, Option.some.inj ho' ▸ hopk⟩) hlow hlo2

theorem bind_bobHandshake_at {Inv : ExecTrace → Prop} {α : Type}
    (b a : Participant) (kh : BobKeyHandles) (regIdxA ekIdx ctIdx : Nat)
    {f : BobHandshakeOut → Traceful α} (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ (ikB spkSk pqsk : Bytes) (opkSk : Option Bytes)
      (ikA vkA ek ct : Bytes) (honest : Bool) (keys : HandshakeKeys),
      PQXDHStoredAt tr b { kind := .identity, sk := ikB } kh.ik →
      PQXDHStoredAt tr b { kind := .signedPrekey, sk := spkSk } kh.spk →
      PQXDHStoredAt tr b { kind := .pqPrekey, sk := pqsk } kh.pqspk →
      (kh.opk = none ∧ opkSk = none ∨
        ∃ idx o, kh.opk = some idx ∧ opkSk = some o ∧
          PQXDHStoredAt tr b { kind := .oneTimePrekey, sk := o } idx) →
      tr.EventLoggedAt (PQXDHEvent.IdentityRegistered a ikA vkA honest) regIdxA →
      NetMsgAt ek ekIdx tr →
      NetMsgAt ct ctIdx tr →
      isCanonicalKey ek = true →
      bobAgreement ikB spkSk pqsk opkSk ikA ek ct = some keys →
      Inv ((f { ikB := dhPk ikB, ikA, spk := dhPk spkSk,
                pqpk := kemPk pqsk, opk := opkSk.map dhPk,
                ek, ct, spkSk, keys }).run tr).2.val) :
    Inv (((bobHandshake b a kh regIdxA ekIdx ctIdx >>= f).run tr).2.val) := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  rw [run_bind_assoc_snd]
  refine bind_getKey_at b kh.ik .identity tr hInv fun ikB hik => ?_
  rw [run_bind_assoc_snd]
  refine bind_getKey_at b kh.spk .signedPrekey tr hInv fun spkSk hspk => ?_
  rw [run_bind_assoc_snd]
  refine bind_getKey_at b kh.pqspk .pqPrekey tr hInv fun pqsk hpq => ?_
  rcases hopkH : kh.opk with _ | opkIdx
  · dsimp only
    rw [run_bind_assoc_snd, run_pure_bind_snd, run_bind_assoc_snd]
    refine bind_lookupIdentity_at a regIdxA tr hInv fun ikA vkA honest hregA => ?_
    rw [run_bind_assoc_snd]
    refine bind_receiveMessage_at ekIdx tr hInv fun ek hek _ => ?_
    rw [run_bind_assoc_snd]
    refine bind_receiveMessage_at ctIdx tr hInv fun ct hct _ => ?_
    rw [run_bind_assoc_snd]
    refine bind_guardP_at _ tr hInv fun hcan => ?_
    rcases hagree : bobAgreement ikB spkSk pqsk none ikA ek ct with _ | keys
    · dsimp only; rw [run_bind_snd, Traceful.run_failure]; exact hInv
    · dsimp only; rw [run_pure_bind_snd]
      exact hf ikB spkSk pqsk none ikA vkA ek ct honest keys
        hik hspk hpq (.inl ⟨hopkH, rfl⟩) hregA hek hct hcan hagree
  · dsimp only
    rw [run_bind_assoc_snd]
    refine bind_getKey_at b opkIdx .oneTimePrekey tr hInv fun o hopkSt => ?_
    rw [run_bind_assoc_snd, run_pure_bind_snd, run_bind_assoc_snd]
    refine bind_lookupIdentity_at a regIdxA tr hInv fun ikA vkA honest hregA => ?_
    rw [run_bind_assoc_snd]
    refine bind_receiveMessage_at ekIdx tr hInv fun ek hek _ => ?_
    rw [run_bind_assoc_snd]
    refine bind_receiveMessage_at ctIdx tr hInv fun ct hct _ => ?_
    rw [run_bind_assoc_snd]
    refine bind_guardP_at _ tr hInv fun hcan => ?_
    rcases hagree : bobAgreement ikB spkSk pqsk (some o) ikA ek ct with _ | keys
    · dsimp only; rw [run_bind_snd, Traceful.run_failure]; exact hInv
    · dsimp only; rw [run_pure_bind_snd]
      exact hf ikB spkSk pqsk (some o) ikA vkA ek ct honest keys
        hik hspk hpq (.inr ⟨opkIdx, o, hopkH, rfl, hopkSt⟩) hregA hek hct hcan hagree

/-! ## Composed Reachability Step and Induction Principle -/

theorem Preserves.composed_step {Inv : ExecTrace → Prop}
    (hNet : ∀ (msg : Bytes) (tr : ExecTrace), msg.AttackerKnows tr → Inv tr → Inv (tr.append (NetE msg)))
    (hRegId : ∀ p, Preserves Inv (registerIdentity p))
    (hRegCorrupt : ∀ p skIdx, Preserves Inv (registerCorruptIdentity p skIdx))
    (hGenSpk : ∀ b idStateIdx, Preserves Inv (genSignedPrekey b idStateIdx))
    (hGenPq : ∀ b idStateIdx, Preserves Inv (genPQPrekey b idStateIdx))
    (hGenOpk : ∀ b, Preserves Inv (genOneTimePrekey b))
    (hAliceStart : ∀ a b idStateIdx regIdxB bh, Preserves Inv (aliceStart a b idStateIdx regIdxB bh))
    (hBobStart : ∀ b a kh regIdxA mh pqIdx spqrMsgIdx,
      Preserves Inv (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx))
    (hMsgEnc : ∀ me stH coinsLen pqIdx, Preserves Inv (messageEncrypt me stH coinsLen pqIdx))
    (hMsgEncAbort : ∀ me stH, Preserves Inv (messageEncryptAbort me stH))
    (hMsgDec : ∀ me stH msgH pqIdx spqrMsgIdx,
      Preserves Inv (messageDecrypt me stH msgH pqIdx spqrMsgIdx))
    (hMsgDecSkip : ∀ me stH msgH evH pqIdx spqrMsgIdx,
      Preserves Inv (messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx))
    (hExpKey : ∀ me stH k, Preserves Inv (exposeKey me stH k))
    (hExpSpqr : ∀ me stH, Preserves Inv (exposeSpqr me stH))
    (hExpSkip : ∀ evH, Preserves Inv (exposeSkipped evH))
    (hCompIk : ∀ p stateIdx, Preserves Inv (compromiseIK p stateIdx))
    (hCompSpk : ∀ b stateIdx, Preserves Inv (compromiseSPK b stateIdx))
    (hCompPq : ∀ b stateIdx, Preserves Inv (compromisePQSPK b stateIdx))
    (hCompOpk : ∀ b stateIdx, Preserves Inv (compromiseOPK b stateIdx))
    (hBreakDh : Preserves Inv breakDH)
    (hBreakKem : Preserves Inv breakKEM)
    (hInvDh : ∀ msgIdx, Preserves Inv (invertDH msgIdx))
    (hInvKem : ∀ msgIdx, Preserves Inv (invertKEM msgIdx))
    (input : reachability.Input) (tr : ExecTrace)
    (hPre : reachability.PreCond input tr) (hInv : Inv tr) :
    Inv (((reachability.step input).snd).run tr).2.val := by
  rcases input with ⟨⟨i, hi⟩, inp⟩
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  · let msg : Bytes := inp
    have hstep : ((reachability.step ⟨⟨0, hi⟩, inp⟩).snd.run tr).2.val = tr.append (NetE msg) := by
      change ((Network.sendMessage msg).run tr).2.val = tr.append (NetE msg)
      simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
      rw [Traceful.run_mk]
    rw [hstep]
    exact hNet msg tr hPre hInv
  · exact hRegId inp tr hInv
  · rcases inp with ⟨p, skIdx⟩; exact hRegCorrupt p skIdx tr hInv
  · rcases inp with ⟨b, idStateIdx⟩; exact hGenSpk b idStateIdx tr hInv
  · rcases inp with ⟨b, idStateIdx⟩; exact hGenPq b idStateIdx tr hInv
  · exact hGenOpk inp tr hInv
  · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩
    exact hAliceStart a b idStateIdx regIdxB bh tr hInv
  · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩
    exact hBobStart b a kh regIdxA mh pqIdx spqrMsgIdx tr hInv
  · rcases inp with ⟨me, stH, coinsLen, pqIdx⟩
    exact hMsgEnc me stH coinsLen pqIdx tr hInv
  · rcases inp with ⟨me, stH⟩; exact hMsgEncAbort me stH tr hInv
  · rcases inp with ⟨me, stH, msgH, pqIdx, spqrMsgIdx⟩
    exact hMsgDec me stH msgH pqIdx spqrMsgIdx tr hInv
  · rcases inp with ⟨me, stH, msgH, evH, pqIdx, spqrMsgIdx⟩
    exact hMsgDecSkip me stH msgH evH pqIdx spqrMsgIdx tr hInv
  · rcases inp with ⟨me, stH, k⟩; exact hExpKey me stH k tr hInv
  · rcases inp with ⟨me, stH⟩; exact hExpSpqr me stH tr hInv
  · exact hExpSkip inp tr hInv
  · rcases inp with ⟨p, stateIdx⟩; exact hCompIk p stateIdx tr hInv
  · rcases inp with ⟨b, stateIdx⟩; exact hCompSpk b stateIdx tr hInv
  · rcases inp with ⟨b, stateIdx⟩; exact hCompPq b stateIdx tr hInv
  · rcases inp with ⟨b, stateIdx⟩; exact hCompOpk b stateIdx tr hInv
  · exact hBreakDh tr hInv
  · exact hBreakKem tr hInv
  · exact hInvDh inp tr hInv
  · exact hInvKem inp tr hInv
  · omega

/-- Induction principle for traces reachable under `Composed.reachability`. -/
theorem composed_reachable_induction {Inv : ExecTrace → Prop}
    (hBase : Inv Trace.nil)
    (hNet : ∀ (msg : Bytes) (tr : ExecTrace), msg.AttackerKnows tr → Inv tr → Inv (tr.append (NetE msg)))
    (hRegId : ∀ p, Preserves Inv (registerIdentity p))
    (hRegCorrupt : ∀ p skIdx, Preserves Inv (registerCorruptIdentity p skIdx))
    (hGenSpk : ∀ b idStateIdx, Preserves Inv (genSignedPrekey b idStateIdx))
    (hGenPq : ∀ b idStateIdx, Preserves Inv (genPQPrekey b idStateIdx))
    (hGenOpk : ∀ b, Preserves Inv (genOneTimePrekey b))
    (hAliceStart : ∀ a b idStateIdx regIdxB bh, Preserves Inv (aliceStart a b idStateIdx regIdxB bh))
    (hBobStart : ∀ b a kh regIdxA mh pqIdx spqrMsgIdx,
      Preserves Inv (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx))
    (hMsgEnc : ∀ me stH coinsLen pqIdx, Preserves Inv (messageEncrypt me stH coinsLen pqIdx))
    (hMsgEncAbort : ∀ me stH, Preserves Inv (messageEncryptAbort me stH))
    (hMsgDec : ∀ me stH msgH pqIdx spqrMsgIdx,
      Preserves Inv (messageDecrypt me stH msgH pqIdx spqrMsgIdx))
    (hMsgDecSkip : ∀ me stH msgH evH pqIdx spqrMsgIdx,
      Preserves Inv (messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx))
    (hExpKey : ∀ me stH k, Preserves Inv (exposeKey me stH k))
    (hExpSpqr : ∀ me stH, Preserves Inv (exposeSpqr me stH))
    (hExpSkip : ∀ evH, Preserves Inv (exposeSkipped evH))
    (hCompIk : ∀ p stateIdx, Preserves Inv (compromiseIK p stateIdx))
    (hCompSpk : ∀ b stateIdx, Preserves Inv (compromiseSPK b stateIdx))
    (hCompPq : ∀ b stateIdx, Preserves Inv (compromisePQSPK b stateIdx))
    (hCompOpk : ∀ b stateIdx, Preserves Inv (compromiseOPK b stateIdx))
    (hBreakDh : Preserves Inv breakDH)
    (hBreakKem : Preserves Inv breakKEM)
    (hInvDh : ∀ msgIdx, Preserves Inv (invertDH msgIdx))
    (hInvKem : ∀ msgIdx, Preserves Inv (invertKEM msgIdx))
    {tr : ExecTrace} (hReach : tr.Reachable reachability) :
    Inv tr := by
  induction hReach with
  | Base => exact hBase
  | Step input hPre _ ih =>
    exact Preserves.composed_step hNet hRegId hRegCorrupt hGenSpk hGenPq hGenOpk
      hAliceStart hBobStart hMsgEnc hMsgEncAbort hMsgDec hMsgDecSkip
      hExpKey hExpSpqr hExpSkip hCompIk hCompSpk hCompPq hCompOpk
      hBreakDh hBreakKem hInvDh hInvKem input _ hPre ih

end Symbolic.Swarm.COMPOSED.CompTrace
