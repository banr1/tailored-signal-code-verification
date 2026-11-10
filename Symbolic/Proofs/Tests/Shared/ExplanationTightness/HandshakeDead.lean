/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
public import Symbolic.Proofs.SpecLemmas.ModelProofDefs
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.ProtocolEvent
import DY.Trace.Basic
import DY.Trace.Monad
import Init.Data.String
import DY.Trace.Manipulation
import DY.Actions.PersistentGlobalState
import DY.Actions.Random
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Unreachability of Direct Handshake Root and Sending-Chain Key Exposure

Proves `exposedCKs_handshakeCk_dead_shared` and `exposedRK_handshakeRk_dead_shared`: on reachable
traces of `DY.Libsignal.Composed.reachability`, no `TREvent.ExposedCKs` or `TREvent.ExposedRK`
event ever exposes the initial PQXDH handshake keys `keys.ck` or `keys.rk` of any completed
handshake (`HandshakeKeysAt tr j keys`). Every stored `TRState` snapshot derives `st.rk` and
`st.cks` through `createChain` or `kdfCk`, which are domain-separated from `pqxdhKdf`.
-/

namespace Symbolic.Proofs.Tests.Shared.ExplanationTightness.HandshakeDead

open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.Comparse DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open DY.Libsignal.TripleRatchet (RecvChain SessionInfo KeyComponent KeyDir
  kdfRk createChain kdfCk hmac hkdfBlock1 hkdfBlock2 lit litByte
  x25519LowOrder findRecvChain setRecvChain recvChainFor consumeMessageKey
  TRState TREvent TRSignalMsg spqrA2B spqrB2A
  receiveSignalMsg ensureReceiverChain dhRatchetStep verifyMacAndDecrypt
  logSkippedKeys logMessageKeyAndStore traceLength guardTrace
  messageEncrypt messageEncryptAbort messageDecrypt messageDecryptSkipped
  exposeKey exposeSpqr exposeSkipped)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent KeyKind HandshakeKeys HandshakeKeysAt
  BundleHandles BobKeyHandles PreKeyMsgHandles AliceHandshakeOut BobHandshakeOut
  pqxdhKdf pqxdhLabel serializedIk guardTrace
  getKey lookupIdentity aliceAgreement bobAgreement aliceHandshake bobHandshake
  registerIdentity registerCorruptIdentity genSignedPrekey genPQPrekey genOneTimePrekey
  compromiseIK compromiseSPK compromisePQSPK compromiseOPK
  breakDH breakKEM invertDH invertKEM)

/-! ## KDF Domain Separation -/

private theorem concat_inj {a₁ b₁ a₂ b₂ : Bytes}
    (h : Concat.concat a₁ b₁ = Concat.concat a₂ b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have hv := congrArg (fun x : Bytes => x.view? Concat.Concat.SubF) h
  simp only [Concat.concat, Concat.CanConcat.concat, BytesView.view_pack,
    Option.some.injEq, Concat.Concat.SubF.mk.injEq] at hv
  exact hv

private theorem hmac_inj {k₁ m₁ k₂ m₂ : Bytes} (h : hmac k₁ m₁ = hmac k₂ m₂) :
    k₁ = k₂ ∧ m₁ = m₂ := by
  have hv := congrArg (fun b : Bytes => b.view? KdfExtract.KdfExtract.SubF) h
  dsimp only [hmac, KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hv
  rw [BytesView.view_pack, BytesView.view_pack] at hv
  injection hv with hv'
  cases hv'
  exact ⟨rfl, rfl⟩

private theorem hkdfBlock1_inj {p₁ i₁ p₂ i₂ : Bytes}
    (h : hkdfBlock1 p₁ i₁ = hkdfBlock1 p₂ i₂) : p₁ = p₂ ∧ i₁ = i₂ := by
  obtain ⟨hp, hi⟩ := hmac_inj h
  exact ⟨hp, (concat_inj hi).1⟩

private theorem hkdfBlock2_inj {p₁ i₁ p₂ i₂ : Bytes}
    (h : hkdfBlock2 p₁ i₁ = hkdfBlock2 p₂ i₂) : p₁ = p₂ ∧ i₁ = i₂ := by
  obtain ⟨hp, hi⟩ := hmac_inj h
  exact ⟨hp, (concat_inj (concat_inj hi).2).1⟩

private theorem pqxdhLabel_ne_whisperRatchet :
    (pqxdhLabel : Bytes) ≠ lit "WhisperRatchet" := by
  intro h
  have hm := congrArg bytesToLiteral h
  simp only [pqxdhLabel, lit, bytesToLiteral_literalToBytes, Option.some.injEq,
    String.toUTF8_eq_toByteArray, String.toByteArray_inj] at hm
  have hl := congrArg String.toList hm
  revert hl; decide

private theorem pqxdhKdf_rk_ne_createChain_fst (ikm rk pk sk : Bytes) :
    (pqxdhKdf ikm).rk ≠ (createChain rk pk sk).1 := by
  intro h
  exact pqxdhLabel_ne_whisperRatchet (hkdfBlock1_inj h).2

private theorem pqxdhKdf_ck_ne_createChain_snd (ikm rk pk sk : Bytes) :
    (pqxdhKdf ikm).ck ≠ (createChain rk pk sk).2 := by
  intro h
  exact pqxdhLabel_ne_whisperRatchet (hkdfBlock2_inj h).2

private theorem pqxdhKdf_ck_ne_kdfCk_fst (ikm ck : Bytes) :
    (pqxdhKdf ikm).ck ≠ (kdfCk ck).1 := by
  intro h
  obtain ⟨_, hikm⟩ := hmac_inj h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hikm

/-! ## Composed Trace Entry Helpers and Preservation Combinators -/

private abbrev NetEntry : Type := Network.ExecEntryT
private abbrev RndEntry : Type := Random.ExecEntryT
private abbrev TREntry : Type := ProtocolEvent.ExecEntryT TREvent
private abbrev PQXDHEntry : Type := ProtocolEvent.ExecEntryT PQXDHEvent
private abbrev CEntry : Type := ProtocolEvent.ExecEntryT ComposedEvent
 abbrev TRStEntry : Type :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
private abbrev PQXDHStEntry : Type :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState PQXDHState)

private abbrev NetE (msg : Bytes) : NetEntry := ⟨msg⟩
private abbrev RndE (n : Nat) : RndEntry := ⟨n⟩
private abbrev TREvE (ev : TREvent) : TREntry := ⟨ev⟩
private abbrev PQEvE (ev : PQXDHEvent) : PQXDHEntry := ⟨ev⟩
private abbrev CEvE (ev : ComposedEvent) : CEntry := ⟨ev⟩
 abbrev TRStE (me : Participant) (st : TRState) : TRStEntry :=
  ⟨({ participant := me, state := st } : PersistentLocalState.LocalState TRState)⟩
private abbrev PQStE (me : Participant) (st : PQXDHState) : PQXDHStEntry :=
  ⟨({ participant := me, state := st } : PersistentLocalState.LocalState PQXDHState)⟩

private theorem proj_inj_eq {E : Type} [ExecTraceTypes.Has E] (e : E) :
    (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by
  rw [TraceEntryHas.inj_proj_eq]

private theorem at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]

private theorem at?_append_cases {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    {tr : ExecTrace} {e : E1} {x : E2} {i : Nat}
    (h : ((tr.append e).at? i : Option E2) = some x) :
    (i < tr.length ∧ (tr.at? i : Option E2) = some x) ∨
    (i = tr.length ∧
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = some x) := by
  have hlt : i < (tr.append e).length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := E2) (tr.append e) i
    rw [h] at this; exact this
  have hlen : (tr.append e).length = tr.length + 1 := by
    rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rcases (show i < tr.length ∨ i = tr.length by omega) with hi | rfl
  · rw [at?_append_of_lt tr e hi] at h
    exact .inl ⟨hi, h⟩
  · simp only [Trace.at?, hlt, ↓reduceDIte] at h
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte] at h
    exact .inr ⟨rfl, h⟩

private theorem eventLoggedAt_append_same {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr : ExecTrace} {ev₀ ev : Ev} {i : Nat}
    (h : (tr.append (⟨ev₀⟩ : ProtocolEvent.ExecEntryT Ev)).EventLoggedAt ev i) :
    (i < tr.length ∧ tr.EventLoggedAt ev i) ∨ (i = tr.length ∧ ev₀ = ev) := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h
  rcases at?_append_cases h with ⟨hi, h⟩ | ⟨rfl, hp⟩
  · rw [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h
    exact .inl ⟨hi, h⟩
  · rw [proj_inj_eq] at hp; injection hp with hp; injection hp with hp
    exact .inr ⟨rfl, hp⟩

private theorem eventLoggedAt_append_other {E Ev : Type}
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

 abbrev TRStateStoredAt (p : Participant) (st : TRState) (i : Nat) (tr : ExecTrace) : Prop :=
  (tr.at? i : Option TRStEntry) = some (TRStE p st)

private theorem trStateStoredAt_append_same {tr : ExecTrace} {p₀ p : Participant}
    {st₀ st : TRState} {j : Nat}
    (h : TRStateStoredAt p st j (tr.append (TRStE p₀ st₀))) :
    (j < tr.length ∧ TRStateStoredAt p st j tr) ∨ (j = tr.length ∧ p₀ = p ∧ st₀ = st) := by
  rcases at?_append_cases h with ⟨hj, h⟩ | ⟨rfl, hp⟩
  · exact .inl ⟨hj, h⟩
  · rw [proj_inj_eq] at hp; injection hp with hp; injection hp with hp; injection hp with hp1 hp2
    exact .inr ⟨rfl, hp1, hp2⟩

private theorem trStateStoredAt_append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none)
    {p : Participant} {st : TRState} {j : Nat}
    (h : TRStateStoredAt p st j (tr.append e)) :
    TRStateStoredAt p st j tr := by
  rcases at?_append_cases h with ⟨_, h⟩ | ⟨_, hp⟩
  · exact h
  · rw [hnone] at hp; cases hp

private theorem handshakeKeysAt_append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHEntry) = none)
    {doneIdx : Nat} {keys : HandshakeKeys}
    (h : HandshakeKeysAt (tr.append e) doneIdx keys) :
    HandshakeKeysAt tr doneIdx keys := by
  rcases h with ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, hev⟩ | ⟨ek, ct, hev⟩⟩
  · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inl ⟨ek, ct, eventLoggedAt_append_other hnone hev⟩⟩
  · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inr ⟨ek, ct, eventLoggedAt_append_other hnone hev⟩⟩

private theorem handshakeKeysAt_append_nonDone {tr : ExecTrace} {ev : PQXDHEvent}
    (hne : ∀ a b ikA ikB spk pqpk opk ek ct keys,
      ev ≠ .AliceDone a b ikA ikB spk pqpk opk ek ct keys ∧
      ev ≠ .BobDone a b ikA ikB spk pqpk opk ek ct keys)
    {doneIdx : Nat} {keys : HandshakeKeys}
    (h : HandshakeKeysAt (tr.append (PQEvE ev)) doneIdx keys) :
    HandshakeKeysAt tr doneIdx keys := by
  rcases h with ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, hev⟩ | ⟨ek, ct, hev⟩⟩
  · rcases eventLoggedAt_append_same hev with ⟨_, hev⟩ | ⟨_, heq⟩
    · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inl ⟨ek, ct, hev⟩⟩
    · exact absurd heq (hne a b ikA ikB spk pqpk opk ek ct keys).1
  · rcases eventLoggedAt_append_same hev with ⟨_, hev⟩ | ⟨_, heq⟩
    · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inr ⟨ek, ct, hev⟩⟩
    · exact absurd heq (hne b a ikB ikA spk pqpk opk ek ct keys).2

private theorem handshakeKeysAt_append_done {tr : ExecTrace} {ev : PQXDHEvent}
    {doneIdx : Nat} {keys : HandshakeKeys}
    (h : HandshakeKeysAt (tr.append (PQEvE ev)) doneIdx keys) :
    HandshakeKeysAt tr doneIdx keys ∨
    (doneIdx = tr.length ∧
      ((∃ a b ikA ikB spk pqpk opk ek ct, ev = .AliceDone a b ikA ikB spk pqpk opk ek ct keys) ∨
       (∃ b a ikB ikA spk pqpk opk ek ct, ev = .BobDone b a ikB ikA spk pqpk opk ek ct keys))) := by
  rcases h with ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, hev⟩ | ⟨ek, ct, hev⟩⟩
  · rcases eventLoggedAt_append_same hev with ⟨_, hev⟩ | ⟨rfl, heq⟩
    · exact .inl ⟨a, b, ikA, ikB, spk, pqpk, opk, .inl ⟨ek, ct, hev⟩⟩
    · exact .inr ⟨rfl, .inl ⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, heq⟩⟩
  · rcases eventLoggedAt_append_same hev with ⟨_, hev⟩ | ⟨rfl, heq⟩
    · exact .inl ⟨a, b, ikA, ikB, spk, pqpk, opk, .inr ⟨ek, ct, hev⟩⟩
    · exact .inr ⟨rfl, .inr ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, heq⟩⟩

private def Preserves (Inv : ExecTrace → Prop) {α : Type} (m : Traceful α) : Prop :=
  ∀ tr, Inv tr → Inv (m.run tr).2.val

private def PreservesWith (Inv : ExecTrace → Prop) {α : Type} (Post : α → Prop)
    (m : Traceful α) : Prop :=
  ∀ tr, Inv tr → Inv (m.run tr).2.val ∧ ∀ a, (m.run tr).1 = some a → Post a

private theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]; rcases x.run tr with ⟨_ | a, tr1⟩ <;> rfl

private theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]; rcases x.run tr with ⟨_ | a, tr1⟩ <;> rfl

private theorem Preserves.of_id {Inv : ExecTrace → Prop} {α : Type} {x : Traceful α}
    (hx : ∀ tr, (x.run tr).2.val = tr) : Preserves Inv x := by
  intro tr h; rw [hx]; exact h

private theorem Preserves.pure {Inv : ExecTrace → Prop} {α : Type} (a : α) :
    Preserves Inv (Pure.pure a : Traceful α) :=
  Preserves.of_id fun _ => by rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; rfl

private theorem Preserves.failure {Inv : ExecTrace → Prop} {α : Type} :
    Preserves Inv (failure : Traceful α) :=
  Preserves.of_id fun _ => by rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; rfl

private theorem Preserves.guardP {Inv : ExecTrace → Prop} (p : Prop) [Decidable p] :
    Preserves Inv (_root_.guard p : Traceful Unit) := by
  unfold _root_.guard; split
  · exact Preserves.pure _
  · exact Preserves.failure

private theorem Preserves.requireTracePredicate {Inv : ExecTrace → Prop} (p : ExecTrace → Bool) :
    Preserves Inv (DY.Libsignal.PQXDH.guardTrace p) :=
  Preserves.of_id fun _ => by
    unfold DY.Libsignal.PQXDH.guardTrace
    rw [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1]

private theorem Preserves.guardTrace {Inv : ExecTrace → Prop} (p : ExecTrace → Bool) :
    Preserves Inv (guardTrace p) :=
  Preserves.of_id fun _ => by
    unfold DY.Libsignal.TripleRatchet.guardTrace
    rw [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1]

private theorem Preserves.monadLiftErr {Inv : ExecTrace → Prop} {α : Type} (x : Err α) :
    Preserves Inv (monadLift x : Traceful α) :=
  Preserves.of_id fun _ => by
    cases (x : Option α) <;>
      (dsimp only [monadLift, MonadLift.monadLift]
       rw [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1])

private theorem Preserves.traceLength {Inv : ExecTrace → Prop} :
    Preserves Inv traceLength :=
  Preserves.of_id fun _ => by
    unfold DY.Libsignal.TripleRatchet.traceLength
    rw [Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1]

private theorem Preserves.getEntry {Inv : ExecTrace → Prop} {E : Type} [ExecTraceTypes.Has E]
    (h : Nat) : Preserves Inv (DY.getEntry h : Traceful E) :=
  Preserves.of_id fun _ => by
    rw [Symbolic.DYBridge.DY.getEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
      Symbolic.DYBridge.DY.Traceful.mk_eq_1]

private theorem Preserves.bind {Inv : ExecTrace → Prop} {α β : Type}
    {x : Traceful α} {f : α → Traceful β}
    (hx : Preserves Inv x) (hf : ∀ a, Preserves Inv (f a)) : Preserves Inv (x >>= f) := by
  intro tr hInv; rw [Traceful.run_bind]; rcases h : x.run tr with ⟨o, trMid, _⟩
  have hMid : Inv trMid := by have := hx tr hInv; rw [h] at this; exact this
  cases o with
  | none => exact hMid
  | some a => exact hf a trMid hMid

private theorem PreservesWith.of_preserves {Inv : ExecTrace → Prop} {α : Type} {x : Traceful α}
    (hx : Preserves Inv x) : PreservesWith Inv (fun _ => True) x :=
  fun tr hInv => ⟨hx tr hInv, fun _ _ => trivial⟩

private theorem PreservesWith.pure {Inv : ExecTrace → Prop} {α : Type} {P : α → Prop}
    (a : α) (ha : P a) : PreservesWith Inv P (Pure.pure a : Traceful α) :=
  fun tr hInv => by
    rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
    exact ⟨hInv, fun _ h => Option.some.inj h ▸ ha⟩

private theorem PreservesWith.failure {Inv : ExecTrace → Prop} {α : Type} {P : α → Prop} :
    PreservesWith Inv P (failure : Traceful α) :=
  fun tr hInv => by
    rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
    exact ⟨hInv, fun _ h => nomatch h⟩

private theorem PreservesWith.bind {Inv : ExecTrace → Prop} {α β : Type}
    {P : α → Prop} {Q : β → Prop} {x : Traceful α} {f : α → Traceful β}
    (hx : PreservesWith Inv P x) (hf : ∀ a, P a → PreservesWith Inv Q (f a)) :
    PreservesWith Inv Q (x >>= f) := by
  intro tr hInv
  rw [Traceful.run_bind]
  obtain ⟨h1, h2⟩ := hx tr hInv
  rcases hrun : x.run tr with ⟨_ | a, trMid, _⟩
  · rw [hrun] at h1; exact ⟨h1, fun _ h => nomatch h⟩
  · rw [hrun] at h1
    exact hf a (h2 a (congrArg Prod.fst hrun)) trMid h1

private theorem PreservesWith.bind_preserves {Inv : ExecTrace → Prop} {α β : Type}
    {Q : β → Prop} {x : Traceful α} {f : α → Traceful β}
    (hx : Preserves Inv x) (hf : ∀ a, PreservesWith Inv Q (f a)) :
    PreservesWith Inv Q (x >>= f) :=
  PreservesWith.bind (PreservesWith.of_preserves hx) fun a _ => hf a

private theorem Preserves.bind_with {Inv : ExecTrace → Prop} {α β : Type}
    {P : α → Prop} {x : Traceful α} {f : α → Traceful β}
    (hx : PreservesWith Inv P x) (hf : ∀ a, P a → Preserves Inv (f a)) :
    Preserves Inv (x >>= f) := by
  intro tr hInv
  rw [Traceful.run_bind]
  obtain ⟨h1, h2⟩ := hx tr hInv
  rcases hrun : x.run tr with ⟨_ | a, trMid, _⟩
  · rw [hrun] at h1; exact h1
  · rw [hrun] at h1
    exact hf a (h2 a (congrArg Prod.fst hrun)) trMid h1

private theorem Preserves.receiveMessage {Inv : ExecTrace → Prop} (h : Nat) :
    Preserves Inv (Network.receiveMessage h) := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact Preserves.bind (Preserves.getEntry _) fun _ => Preserves.pure _

private theorem Preserves.getLocalState_tr {Inv : ExecTrace → Prop} (p : Participant) (h : Nat) :
    Preserves Inv (PersistentLocalState.getLocalState p h : Traceful TRState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine Preserves.bind (Preserves.bind (Preserves.getEntry _) fun _ => Preserves.pure _) fun _ => ?_
  exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem Preserves.getLocalState_pq {Inv : ExecTrace → Prop} (p : Participant) (h : Nat) :
    Preserves Inv (PersistentLocalState.getLocalState p h : Traceful PQXDHState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine Preserves.bind (Preserves.bind (Preserves.getEntry _) fun _ => Preserves.pure _) fun _ => ?_
  exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem getLocalState_tr_fst (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 =
      match (tr.at? stH : Option TRStEntry) with
      | some ⟨⟨p, st⟩⟩ => if p = me then some st else none
      | none => none := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  rw [run_bind_fst, run_bind_fst, run_bind_snd, Symbolic.DYBridge.DY.getEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  rcases (tr.at? stH : Option TRStEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · dsimp only
    rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
    change (((if p = me then pure () else failure : Traceful Unit) >>= fun _ => pure st).run tr).1 =
      if p = me then some st else none
    by_cases hp : p = me
    · simp only [hp, ↓reduceIte, run_bind_fst, Traceful.run_pure]
    · simp only [hp, ↓reduceIte, run_bind_fst, Traceful.run_failure]

private theorem getLocalState_tr_snd (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).2.val = tr :=
  Preserves.getLocalState_tr (Inv := fun t => t = tr) me stH tr rfl

private theorem Preserves.receiveSignalMsg {Inv : ExecTrace → Prop} (msgH : Nat) :
    Preserves Inv (receiveSignalMsg msgH) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem Preserves.verifyMacAndDecrypt {Inv : ExecTrace → Prop}
    (st : TRState) (msg : TRSignalMsg) (pqSalt seed : Bytes) :
    Preserves Inv (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.monadLiftErr _

private theorem Preserves.getKey {Inv : ExecTrace → Prop} (p : Participant) (stateIdx : Nat)
    (kind : KeyKind) : Preserves Inv (getKey p stateIdx kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p stateIdx) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem Preserves.lookupIdentity {Inv : ExecTrace → Prop} (p : Participant)
    (regIdx : Nat) : Preserves Inv (lookupIdentity p regIdx) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry _) fun e => ?_
  rcases e with ⟨ev⟩
  cases ev <;> try exact Preserves.failure
  exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

/-! ## Reachability Induction Principle -/

private theorem Preserves.composed_step {Inv : ExecTrace → Prop}
    (hNet : ∀ (msg : Bytes) (tr : ExecTrace),
      msg.AttackerKnows tr → Inv tr → Inv (tr.append (NetE msg)))
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
    change Inv ((Network.sendMessage msg).run tr).2.val
    rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1]
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

/-! ## Reachable-Trace Key-Shape Invariant -/

/-- A root key `rk` is a `createChain` first output (`hkdfBlock1 (hmac _ _) (lit "WhisperRatchet")`). -/
def IsRkShape (rk : Bytes) : Prop :=
  ∃ r₀ p₀ s₀, rk = (createChain r₀ p₀ s₀).1

/-- A sending chain key `ck` is either a `createChain` second output
(`hkdfBlock2 (hmac _ _) (lit "WhisperRatchet")`) or a symmetric-ratchet step `(kdfCk _).1`. -/
def IsCksShape (ck : Bytes) : Prop :=
  (∃ r₀ p₀ s₀, ck = (createChain r₀ p₀ s₀).2) ∨ ∃ ck₀, ck = (kdfCk ck₀).1

def StoredShape (st : TRState) : Prop :=
  IsRkShape st.rk ∧ IsCksShape st.cks

/-- Reachable-trace invariant separating `pqxdhKdf` outputs from stored and exposed ratchet keys. -/
structure DeadInv (tr : ExecTrace) : Prop where
  handshakeKdf : ∀ doneIdx keys, HandshakeKeysAt tr doneIdx keys → ∃ ikm, keys = pqxdhKdf ikm
  storedOK : ∀ p st j, TRStateStoredAt p st j tr → StoredShape st
  exposedRK : ∀ s rk r, tr.EventLogged (TREvent.ExposedRK s rk r) → IsRkShape rk
  exposedCKs : ∀ s ck n r, tr.EventLogged (TREvent.ExposedCKs s ck n r) → IsCksShape ck

private theorem DeadInv.nil : DeadInv Trace.nil where
  handshakeKdf _ _ h := by
    rcases h with ⟨_, _, _, _, _, _, _, ⟨_, _, hev⟩ | ⟨_, _, hev⟩⟩ <;>
      simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, Trace.at?,
        Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at hev
  storedOK _ _ _ hst := by
    simp only [TRStateStoredAt, Trace.at?, Symbolic.DYBridge.DY.Trace.nil_length_not_lt,
      ↓reduceDIte, reduceCtorEq] at hst
  exposedRK _ _ _ h := by
    obtain ⟨_, hev⟩ := h
    simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, Trace.at?,
      Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at hev
  exposedCKs _ _ _ _ h := by
    obtain ⟨_, hev⟩ := h
    simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, Trace.at?,
      Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at hev

private theorem DeadInv.append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone_pq : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHEntry) = none)
    (hnone_tr : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (hnone_st : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none)
    (h : DeadInv tr) : DeadInv (tr.append e) where
  handshakeKdf doneIdx keys hhk :=
    h.handshakeKdf doneIdx keys (handshakeKeysAt_append_other hnone_pq hhk)
  storedOK p st j hst :=
    h.storedOK p st j (trStateStoredAt_append_other hnone_st hst)
  exposedRK s rk r := fun ⟨k, hk⟩ =>
    h.exposedRK s rk r ⟨k, eventLoggedAt_append_other hnone_tr hk⟩
  exposedCKs s ck n r := fun ⟨k, hk⟩ =>
    h.exposedCKs s ck n r ⟨k, eventLoggedAt_append_other hnone_tr hk⟩

private theorem DeadInv.append_pqx_done {tr : ExecTrace} {ev : PQXDHEvent}
    (hdone : ∀ doneIdx keys,
      HandshakeKeysAt (tr.append (PQEvE ev)) doneIdx keys →
      HandshakeKeysAt tr doneIdx keys ∨ ∃ ikm, keys = pqxdhKdf ikm)
    (h : DeadInv tr) : DeadInv (tr.append (PQEvE ev)) where
  handshakeKdf doneIdx keys hhk := by
    rcases hdone doneIdx keys hhk with hhk' | hikm
    · exact h.handshakeKdf doneIdx keys hhk'
    · exact hikm
  storedOK p st j hst := h.storedOK p st j (trStateStoredAt_append_other rfl hst)
  exposedRK s rk r := fun ⟨k, hk⟩ =>
    h.exposedRK s rk r ⟨k, eventLoggedAt_append_other rfl hk⟩
  exposedCKs s ck n r := fun ⟨k, hk⟩ =>
    h.exposedCKs s ck n r ⟨k, eventLoggedAt_append_other rfl hk⟩

private theorem DeadInv.append_pqx_nonDone {tr : ExecTrace} {ev : PQXDHEvent}
    (hne : ∀ a b ikA ikB spk pqpk opk ek ct keys,
      ev ≠ .AliceDone a b ikA ikB spk pqpk opk ek ct keys ∧
      ev ≠ .BobDone a b ikA ikB spk pqpk opk ek ct keys)
    (h : DeadInv tr) : DeadInv (tr.append (PQEvE ev)) :=
  h.append_pqx_done fun _ _ hhk => .inl (handshakeKeysAt_append_nonDone hne hhk)

private theorem DeadInv.append_trEv {tr : ExecTrace} {ev : TREvent}
    (hrk : ∀ s rk r, ev = .ExposedRK s rk r → IsRkShape rk)
    (hcks : ∀ s ck n r, ev = .ExposedCKs s ck n r → IsCksShape ck)
    (h : DeadInv tr) : DeadInv (tr.append (TREvE ev)) where
  handshakeKdf doneIdx keys hhk :=
    h.handshakeKdf doneIdx keys (handshakeKeysAt_append_other rfl hhk)
  storedOK p st j hst := h.storedOK p st j (trStateStoredAt_append_other rfl hst)
  exposedRK s rk r := fun ⟨k, hk⟩ => by
    rcases eventLoggedAt_append_same hk with ⟨_, hk⟩ | ⟨_, heq⟩
    · exact h.exposedRK s rk r ⟨k, hk⟩
    · exact hrk s rk r heq
  exposedCKs s ck n r := fun ⟨k, hk⟩ => by
    rcases eventLoggedAt_append_same hk with ⟨_, hk⟩ | ⟨_, heq⟩
    · exact h.exposedCKs s ck n r ⟨k, hk⟩
    · exact hcks s ck n r heq

private theorem DeadInv.append_tr_inert {tr : ExecTrace} {ev : TREvent}
    (hne_rk : ∀ s rk r, ev ≠ .ExposedRK s rk r)
    (hne_cks : ∀ s ck n r, ev ≠ .ExposedCKs s ck n r)
    (h : DeadInv tr) : DeadInv (tr.append (TREvE ev)) :=
  h.append_trEv (fun s rk r he => absurd he (hne_rk s rk r))
    (fun s ck n r he => absurd he (hne_cks s ck n r))

private theorem DeadInv.append_storeTR {tr : ExecTrace} {p₀ : Participant} {st₀ : TRState}
    (hst₀ : StoredShape st₀) (h : DeadInv tr) : DeadInv (tr.append (TRStE p₀ st₀)) where
  handshakeKdf doneIdx keys hhk :=
    h.handshakeKdf doneIdx keys (handshakeKeysAt_append_other rfl hhk)
  storedOK p st j hst := by
    rcases trStateStoredAt_append_same hst with ⟨_, hst⟩ | ⟨_, rfl, rfl⟩
    · exact h.storedOK p st j hst
    · exact hst₀
  exposedRK s rk r := fun ⟨k, hk⟩ =>
    h.exposedRK s rk r ⟨k, eventLoggedAt_append_other rfl hk⟩
  exposedCKs s ck n r := fun ⟨k, hk⟩ =>
    h.exposedCKs s ck n r ⟨k, eventLoggedAt_append_other rfl hk⟩

/-! ### Step-level `Preserves DeadInv` combinators -/

private theorem preserves_sendMessage (m : Bytes) : Preserves DeadInv (Network.sendMessage m) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  exact h.append_other (e := NetE m) rfl rfl rfl

private theorem preserves_genRand (n : Nat) : Preserves DeadInv (Random.genRand n) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, run_bind_snd,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  dsimp only
  rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact h.append_other (e := RndE n) rfl rfl rfl

private theorem preserves_storePQX (p : Participant) (st : PQXDHState) :
    Preserves DeadInv (PersistentLocalState.storeLocalState p st) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  exact h.append_other (e := PQStE p st) rfl rfl rfl

private theorem preserves_logCEv (ev : ComposedEvent) : Preserves DeadInv (ProtocolEvent.logEvent ev) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, run_bind_snd,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  dsimp only
  rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact h.append_other (e := CEvE ev) rfl rfl rfl

private theorem preserves_logPQX_nonDone (ev : PQXDHEvent)
    (hne : ∀ a b ikA ikB spk pqpk opk ek ct keys,
      ev ≠ .AliceDone a b ikA ikB spk pqpk opk ek ct keys ∧
      ev ≠ .BobDone a b ikA ikB spk pqpk opk ek ct keys) :
    Preserves DeadInv (ProtocolEvent.logEvent ev) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, run_bind_snd,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  dsimp only
  rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact h.append_pqx_nonDone hne

private theorem preserves_logPQX_aliceDone (a b : Participant) (ikA ikB spk pqpk : Bytes)
    (opk : Option Bytes) (ek ct : Bytes) (keys : HandshakeKeys)
    (hkdf : ∃ ikm, keys = pqxdhKdf ikm) :
    Preserves DeadInv
      (ProtocolEvent.logEvent (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys)) := by
  intro tr hInv
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, run_bind_snd,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  dsimp only
  rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
  refine hInv.append_pqx_done fun j keys' hhk => ?_
  rcases handshakeKeysAt_append_done hhk with hhk' | ⟨_, heq⟩
  · exact .inl hhk'
  · rcases heq with ⟨_, _, _, _, _, _, _, _, _, hEq⟩ | ⟨_, _, _, _, _, _, _, _, _, hEq⟩
    · injection hEq with _ _ _ _ _ _ _ _ _ hkeys
      exact .inr (hkeys ▸ hkdf)
    · nomatch hEq

private theorem preserves_logPQX_bobDone (b a : Participant) (ikB ikA spk pqpk : Bytes)
    (opk : Option Bytes) (ek ct : Bytes) (keys : HandshakeKeys)
    (hkdf : ∃ ikm, keys = pqxdhKdf ikm) :
    Preserves DeadInv
      (ProtocolEvent.logEvent (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys)) := by
  intro tr hInv
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, run_bind_snd,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  dsimp only
  rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
  refine hInv.append_pqx_done fun j keys' hhk => ?_
  rcases handshakeKeysAt_append_done hhk with hhk' | ⟨_, heq⟩
  · exact .inl hhk'
  · rcases heq with ⟨_, _, _, _, _, _, _, _, _, hEq⟩ | ⟨_, _, _, _, _, _, _, _, _, hEq⟩
    · nomatch hEq
    · injection hEq with _ _ _ _ _ _ _ _ _ hkeys
      exact .inr (hkeys ▸ hkdf)

private theorem preserves_logTR_inert (ev : TREvent)
    (hne_rk : ∀ s rk r, ev ≠ .ExposedRK s rk r)
    (hne_cks : ∀ s ck n r, ev ≠ .ExposedCKs s ck n r) :
    Preserves DeadInv (ProtocolEvent.logEvent ev) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, run_bind_snd,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  dsimp only
  rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact h.append_tr_inert hne_rk hne_cks

private theorem preserves_storeTR (p : Participant) (st : TRState) (hst : StoredShape st) :
    Preserves DeadInv (PersistentLocalState.storeLocalState p st) := by
  intro tr h
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  exact h.append_storeTR hst

private theorem preserves_logSkippedKeys (s : SessionInfo) (pk : Bytes) (rIdx src : Nat) :
    ∀ (ck : Bytes) (n : UInt32) (k : Nat),
      Preserves DeadInv (logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0 => Preserves.pure ()
  | ck, n, k + 1 =>
    Preserves.bind
      (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
      fun _ => preserves_logSkippedKeys s pk rIdx src (kdfCk ck).1 (n + 1) k

private theorem preserves_logMessageKeyAndStore (me : Participant) (s : SessionInfo) (dir : KeyDir)
    (seed pqSalt : Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState)
    (hst : StoredShape st) :
    Preserves DeadInv (logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  refine Preserves.bind
    (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
    fun _ => ?_
  exact preserves_storeTR me st hst

private theorem preservesWith_getLocalState_tr (me : Participant) (stH : Nat) :
    PreservesWith DeadInv StoredShape
      (PersistentLocalState.getLocalState me stH : Traceful TRState) := by
  intro tr hInv
  rw [getLocalState_tr_fst, getLocalState_tr_snd]
  refine ⟨hInv, fun st h => ?_⟩
  rcases he : (tr.at? stH : Option TRStEntry) with _ | ⟨⟨p, st'⟩⟩
  · rw [he] at h; nomatch h
  · rw [he] at h; dsimp only at h
    split at h
    · next hp => subst hp; cases h; exact hInv.storedOK p st stH he
    · nomatch h

private theorem preservesWith_dhRatchetStep (st₀ : TRState) (theirPk : Bytes) :
    PreservesWith DeadInv (fun p : TRState × RecvChain => StoredShape p.1)
      (dhRatchetStep st₀ theirPk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine PreservesWith.bind_preserves (Preserves.guardP _) fun _ => ?_
  refine PreservesWith.bind_preserves (preserves_genRand 32) fun _ => ?_
  exact PreservesWith.pure _ ⟨⟨_, _, _, rfl⟩, .inl ⟨_, _, _, rfl⟩⟩

private theorem preservesWith_ensureReceiverChain (st₀ : TRState) (theirPk : Bytes)
    (h₀ : StoredShape st₀ ∨ st₀.recv = []) :
    PreservesWith DeadInv (fun p : TRState × RecvChain × Bool => StoredShape p.1)
      (ensureReceiverChain st₀ theirPk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  rcases hrec : recvChainFor st₀.toDRState theirPk with _ | ⟨c, _ | _⟩ <;> dsimp only
  · exact PreservesWith.failure
  · rcases h₀ with hst₀ | hnil
    · exact PreservesWith.pure (st₀, c, false) hst₀
    · unfold DY.Libsignal.TripleRatchet.recvChainFor
        DY.Libsignal.TripleRatchet.findRecvChain at hrec
      simp only [hnil, List.find?_nil] at hrec
      split at hrec <;> nomatch hrec
  · refine PreservesWith.bind (preservesWith_dhRatchetStep st₀ theirPk) fun p hst => ?_
    rcases p with ⟨st, c'⟩
    exact PreservesWith.pure (st, c', true) hst

private theorem bobAgreement_eq_pqxdhKdf {ikB spkSk pqsk : Bytes} {opkSk : Option Bytes}
    {ikA ek ct : Bytes} {keys : HandshakeKeys}
    (h : bobAgreement ikB spkSk pqsk opkSk ikA ek ct = some keys) :
    ∃ ikm, keys = pqxdhKdf ikm := by
  unfold DY.Libsignal.PQXDH.bobAgreement at h
  change some (pqxdhKdf _) = some keys at h
  injection h with h
  exact ⟨_, h.symm⟩

private def aliceHandshakeJp (ikA ikB spk pqpk : Bytes) (opk : Option Bytes) :
    Traceful AliceHandshakeOut := do
  let ek ← Random.genRand 32
  guard (!DY.Libsignal.PQXDH.x25519LowOrder spk)
  guard (opk.all fun o => !DY.Libsignal.PQXDH.x25519LowOrder o)
  let entropy ← Random.genRand 32
  let (ct, keys) := aliceAgreement ikA ek ikB spk pqpk opk entropy
  pure { ikA := DiffieHellman.dhPk ikA, ikB, spk, pqpk, opk, ek := DiffieHellman.dhPk ek, ct, keys }

private theorem PreservesWith.bind_guardP {Inv : ExecTrace → Prop} {β : Type}
    {Q : β → Prop} {p : Prop} {inst : Decidable p} {f : Unit → Traceful β}
    (hf : ∀ u : Unit, PreservesWith Inv Q (f u)) :
    PreservesWith Inv Q (@_root_.guard Traceful _ p inst >>= f) :=
  PreservesWith.bind_preserves (@Preserves.guardP Inv p inst) hf

private theorem preservesWith_aliceHandshakeJp (ikA ikB spk pqpk : Bytes) (opk : Option Bytes) :
    PreservesWith DeadInv (fun o : AliceHandshakeOut => ∃ ikm, o.keys = pqxdhKdf ikm)
      (aliceHandshakeJp ikA ikB spk pqpk opk) := by
  unfold aliceHandshakeJp
  refine PreservesWith.bind_preserves (preserves_genRand 32) fun ek => ?_
  refine PreservesWith.bind_guardP fun _ => ?_
  refine PreservesWith.bind_guardP fun _ => ?_
  refine PreservesWith.bind_preserves (preserves_genRand 32) fun entropy => ?_
  exact PreservesWith.pure _ ⟨_, rfl⟩

attribute [local irreducible] DY.instMonadTraceful in
private theorem preservesWith_aliceHandshake (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) :
    PreservesWith DeadInv (fun o : AliceHandshakeOut => ∃ ikm, o.keys = pqxdhKdf ikm)
      (aliceHandshake a b idStateIdx regIdxB bh) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  refine PreservesWith.bind_preserves (Preserves.getKey _ _ _) fun ikA => ?_
  refine PreservesWith.bind_preserves (Preserves.lookupIdentity _ _) fun p => ?_
  rcases p with ⟨ikB, vkB⟩
  dsimp only
  refine PreservesWith.bind_preserves (Preserves.receiveMessage _) fun spk => ?_
  refine PreservesWith.bind_preserves (Preserves.receiveMessage _) fun spkSig => ?_
  refine PreservesWith.bind_preserves (Preserves.receiveMessage _) fun pqpk => ?_
  refine PreservesWith.bind_preserves (Preserves.receiveMessage _) fun pqpkSig => ?_
  refine PreservesWith.bind_guardP fun _ => ?_
  refine PreservesWith.bind_guardP fun _ => ?_
  rcases bh.opk with _ | idx
  · exact PreservesWith.bind_preserves (Preserves.pure none)
      (preservesWith_aliceHandshakeJp ikA ikB spk pqpk)
  · exact PreservesWith.bind_preserves (Preserves.receiveMessage idx) fun o =>
      PreservesWith.bind_preserves (Preserves.pure (some o))
        (preservesWith_aliceHandshakeJp ikA ikB spk pqpk)

private theorem preservesWith_bobHandshake (b a : Participant) (kh : BobKeyHandles)
    (regIdxA ekIdx ctIdx : Nat) :
    PreservesWith DeadInv (fun o : BobHandshakeOut => ∃ ikm, o.keys = pqxdhKdf ikm)
      (bobHandshake b a kh regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  refine PreservesWith.bind_preserves (Preserves.getKey _ _ _) fun _ => ?_
  refine PreservesWith.bind_preserves (Preserves.getKey _ _ _) fun _ => ?_
  refine PreservesWith.bind_preserves (Preserves.getKey _ _ _) fun _ => ?_
  rcases kh.opk with _ | idx <;> dsimp only
  · refine PreservesWith.bind_preserves (Preserves.pure none) fun _ => ?_
    refine PreservesWith.bind_preserves (Preserves.lookupIdentity _ _) fun p => ?_
    rcases p with ⟨ikA, vkA⟩
    dsimp only
    refine PreservesWith.bind_preserves (Preserves.receiveMessage _) fun _ => ?_
    refine PreservesWith.bind_preserves (Preserves.receiveMessage _) fun _ => ?_
    refine PreservesWith.bind_preserves (Preserves.guardP _) fun _ => ?_
    split
    · next keys hagree => exact PreservesWith.pure _ (bobAgreement_eq_pqxdhKdf hagree)
    · exact PreservesWith.failure
  · refine PreservesWith.bind_preserves (Preserves.getKey _ _ _) fun _ => ?_
    refine PreservesWith.bind_preserves (Preserves.pure _) fun _ => ?_
    refine PreservesWith.bind_preserves (Preserves.lookupIdentity _ _) fun p => ?_
    rcases p with ⟨ikA, vkA⟩
    dsimp only
    refine PreservesWith.bind_preserves (Preserves.receiveMessage _) fun _ => ?_
    refine PreservesWith.bind_preserves (Preserves.receiveMessage _) fun _ => ?_
    refine PreservesWith.bind_preserves (Preserves.guardP _) fun _ => ?_
    split
    · next keys hagree => exact PreservesWith.pure _ (bobAgreement_eq_pqxdhKdf hagree)
    · exact PreservesWith.failure

/-! ### Preservation of `DeadInv` across all 23 transitions -/

private theorem preserves_registerIdentity (p : Participant) :
    Preserves DeadInv (registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (preserves_genRand 32) fun _ => ?_
  refine Preserves.bind (preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  exact preserves_storePQX p _

private theorem preserves_registerCorruptIdentity (p : Participant) (skIdx : Nat) :
    Preserves DeadInv (registerCorruptIdentity p skIdx) := by
  unfold DY.Libsignal.PQXDH.registerCorruptIdentity
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  refine Preserves.bind (preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  exact preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))

private theorem preserves_genSignedPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves DeadInv (genSignedPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (preserves_genRand 32) fun _ => ?_
  refine Preserves.bind (preserves_genRand 64) fun _ => ?_
  refine Preserves.bind (preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  refine Preserves.bind (preserves_storePQX b _) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  exact Preserves.pure _

private theorem preserves_genPQPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves DeadInv (genPQPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (preserves_genRand 64) fun _ => ?_
  refine Preserves.bind (preserves_genRand 64) fun _ => ?_
  refine Preserves.bind (preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  refine Preserves.bind (preserves_storePQX b _) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  exact Preserves.pure _

private theorem preserves_genOneTimePrekey (b : Participant) :
    Preserves DeadInv (genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  refine Preserves.bind (preserves_genRand 32) fun _ => ?_
  refine Preserves.bind (preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  refine Preserves.bind (preserves_storePQX b _) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  exact Preserves.pure _

private theorem preserves_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) : Preserves DeadInv (aliceStart a b idStateIdx regIdxB bh) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine Preserves.bind_with (preservesWith_aliceHandshake a b idStateIdx regIdxB bh)
    fun o hkdf => ?_
  refine Preserves.bind (preserves_genRand 32) fun dhsA => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind Preserves.traceLength fun _ => ?_
  refine Preserves.bind
    (preserves_logPQX_aliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys hkdf)
    fun _ => ?_
  refine Preserves.bind
    (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
    fun _ => ?_
  refine Preserves.bind (preserves_logCEv _) fun _ => ?_
  exact preserves_storeTR a _ ⟨⟨_, _, _, rfl⟩, .inl ⟨_, _, _, rfl⟩⟩

private theorem preserves_bobStart_afterOpk (b a : Participant) (o : BobHandshakeOut)
    (hkdf : ∃ ikm, o.keys = pqxdhKdf ikm) (st : TRState) (hst : StoredShape st)
    (msg : TRSignalMsg) (c c' : RecvChain) (ratcheted : Bool) (seed pqSalt m : Bytes)
    (spqr' : Bytes) :
    Preserves DeadInv (do
      let doneIdx ← traceLength
      ProtocolEvent.logEvent (PQXDHEvent.BobDone b a o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys)
      if ratcheted then
        ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs))
        ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
      ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
      let skipped := msg.counter.toNat - c.index.toNat
      let childIdx := (← traceLength) + skipped + 2
      logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
      ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }) := by
  refine Preserves.bind Preserves.traceLength fun _ => ?_
  refine Preserves.bind
    (preserves_logPQX_bobDone b a o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys hkdf)
    fun _ => ?_
  cases ratcheted <;> dsimp only
  · refine Preserves.bind (preserves_logCEv _) fun _ => ?_
    refine Preserves.bind Preserves.traceLength fun _ => ?_
    refine Preserves.bind (preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
    refine Preserves.bind
      (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
      fun _ => ?_
    exact preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _ ⟨hst.1, hst.2⟩
  · refine Preserves.bind
      (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
      fun _ => ?_
    refine Preserves.bind
      (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
      fun _ => ?_
    refine Preserves.bind (preserves_logCEv _) fun _ => ?_
    refine Preserves.bind Preserves.traceLength fun _ => ?_
    refine Preserves.bind (preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
    refine Preserves.bind
      (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
      fun _ => ?_
    exact preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _ ⟨hst.1, hst.2⟩

private theorem preserves_bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves DeadInv (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine Preserves.bind_with (preservesWith_bobHandshake b a kh regIdxA mh.ek mh.ct)
    fun o hkdf => ?_
  refine Preserves.bind (Preserves.receiveSignalMsg mh.msg) fun msg => ?_
  refine Preserves.bind_with
    (preservesWith_ensureReceiverChain _ msg.ratchetKey (.inr rfl))
    fun p hst => ?_
  rcases p with ⟨st, c, ratcheted⟩
  dsimp only
  rcases consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩ <;> dsimp only
  · exact Preserves.failure
  · rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩ <;> dsimp only
    · exact Preserves.failure
    · refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
      refine Preserves.bind (Preserves.receiveMessage _) fun pqSalt => ?_
      refine Preserves.bind (Preserves.verifyMacAndDecrypt _ _ _ _) fun m => ?_
      rcases hopk : o.opk with _ | opk <;> dsimp only
      · rw [← hopk]
        exact preserves_bobStart_afterOpk b a o hkdf st hst msg c c' ratcheted seed pqSalt m spqr'
      · refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
        refine Preserves.bind
          (preserves_logPQX_nonDone _
            (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h)))
          fun _ => ?_
        rw [← hopk]
        exact preserves_bobStart_afterOpk b a o hkdf st hst msg c c' ratcheted seed pqSalt m spqr'

private theorem preserves_messageEncrypt (me : Participant) (stH coinsLen pqIdx : Nat) :
    Preserves DeadInv (messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine Preserves.bind_with (preservesWith_getLocalState_tr me stH) fun st hst => ?_
  refine Preserves.bind (Preserves.guardP _) fun _ => ?_
  refine Preserves.bind (preserves_genRand 32) fun _ => ?_
  refine Preserves.bind (preserves_genRand coinsLen) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  refine Preserves.bind
    (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
    fun _ => ?_
  refine Preserves.bind
    (preserves_logMessageKeyAndStore me _ .sender _ _ _ _ _ _ ⟨hst.1, .inr ⟨_, rfl⟩⟩)
    fun _ => ?_
  exact preserves_sendMessage _

private theorem preserves_messageEncryptAbort (me : Participant) (stH : Nat) :
    Preserves DeadInv (messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  refine Preserves.bind (Preserves.getLocalState_tr _ _) fun _ => ?_
  exact Preserves.bind (preserves_genRand 32) fun _ => Preserves.failure

private theorem preserves_messageDecrypt (me : Participant) (stH msgH pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    Preserves DeadInv (messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine Preserves.bind_with (preservesWith_getLocalState_tr me stH) fun st₀ hst₀ => ?_
  refine Preserves.bind (Preserves.receiveSignalMsg msgH) fun msg => ?_
  refine Preserves.bind_with
    (preservesWith_ensureReceiverChain st₀ msg.ratchetKey (.inl hst₀))
    fun p hst => ?_
  rcases p with ⟨st, c, ratcheted⟩
  dsimp only
  rcases consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩ <;> dsimp only
  · exact Preserves.failure
  · rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩ <;> dsimp only
    · exact Preserves.failure
    · refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
      refine Preserves.bind (Preserves.receiveMessage _) fun pqSalt => ?_
      refine Preserves.bind (Preserves.verifyMacAndDecrypt _ _ _ _) fun m => ?_
      cases ratcheted
      · refine Preserves.bind (preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
        refine Preserves.bind
          (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
          fun _ => ?_
        exact preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _ ⟨hst.1, hst.2⟩
      · refine Preserves.bind
          (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
          fun _ => ?_
        refine Preserves.bind
          (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
          fun _ => ?_
        refine Preserves.bind (preserves_logSkippedKeys _ _ _ _ _ _ _) fun _ => ?_
        refine Preserves.bind
          (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
          fun _ => ?_
        exact preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _ ⟨hst.1, hst.2⟩

private theorem preserves_messageDecryptSkipped (me : Participant) (stH msgH evH pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    Preserves DeadInv (messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine Preserves.bind_with (preservesWith_getLocalState_tr me stH) fun st hst => ?_
  refine Preserves.bind (Preserves.receiveSignalMsg msgH) fun msg => ?_
  refine Preserves.bind (Preserves.getEntry evH) fun e => ?_
  rcases e with ⟨ev⟩
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    dsimp only
    refine Preserves.bind (Preserves.guardP _) fun _ => ?_
    refine Preserves.bind (Preserves.guardTrace _) fun _ => ?_
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩ <;> dsimp only
    · exact Preserves.failure
    · refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
      refine Preserves.bind (Preserves.receiveMessage _) fun pqSalt => ?_
      refine Preserves.bind (Preserves.verifyMacAndDecrypt _ _ _ _) fun m => ?_
      refine Preserves.bind
        (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
        fun _ => ?_
      refine Preserves.bind
        (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
        fun _ => ?_
      exact preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _ ⟨hst.1, hst.2⟩
  | _ => exact Preserves.failure

private theorem preserves_exposeKey (me : Participant) (stH : Nat) (k : KeyComponent) :
    Preserves DeadInv (exposeKey me stH k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine Preserves.bind_with (preservesWith_getLocalState_tr me stH) fun st hst => ?_
  cases k <;> dsimp only
  case rk =>
    refine Preserves.bind ?_ fun _ => preserves_sendMessage _
    intro tr hInv
    rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, run_bind_snd,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
      Symbolic.DYBridge.DY.Traceful.mk_eq_1]
    dsimp only
    rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
    exact hInv.append_trEv (fun _ _ _ he => by cases he; exact hst.1) (fun _ _ _ _ he => by cases he)
  case dhs =>
    refine Preserves.bind
      (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
      fun _ => preserves_sendMessage _
  case cks =>
    refine Preserves.bind ?_ fun _ => preserves_sendMessage _
    intro tr hInv
    rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, run_bind_snd,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
      Symbolic.DYBridge.DY.Traceful.mk_eq_1]
    dsimp only
    rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
    exact hInv.append_trEv (fun _ _ _ he => by cases he) (fun _ _ _ _ he => by cases he; exact hst.2)
  case ckr pk =>
    rcases findRecvChain st.recv pk with _ | c <;> dsimp only
    · exact Preserves.failure
    · refine Preserves.bind
        (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
        fun _ => preserves_sendMessage _

private theorem preserves_exposeSpqr (me : Participant) (stH : Nat) :
    Preserves DeadInv (exposeSpqr me stH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  refine Preserves.bind (Preserves.getLocalState_tr _ _) fun _ => ?_
  refine Preserves.bind
    (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
    fun _ => preserves_sendMessage _

private theorem preserves_exposeSkipped (evH : Nat) :
    Preserves DeadInv (exposeSkipped evH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine Preserves.bind (Preserves.getEntry evH) fun e => ?_
  rcases e with ⟨ev⟩
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    refine Preserves.bind (Preserves.guardTrace _) fun _ => ?_
    refine Preserves.bind
      (preserves_logTR_inert _ (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))
      fun _ => preserves_sendMessage _
  | _ => exact Preserves.failure

private theorem preserves_compromiseIK (p : Participant) (stateIdx : Nat) :
    Preserves DeadInv (compromiseIK p stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseIK
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  exact preserves_sendMessage _

private theorem preserves_compromiseSPK (b : Participant) (stateIdx : Nat) :
    Preserves DeadInv (compromiseSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  exact preserves_sendMessage _

private theorem preserves_compromisePQSPK (b : Participant) (stateIdx : Nat) :
    Preserves DeadInv (compromisePQSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  exact preserves_sendMessage _

private theorem preserves_compromiseOPK (b : Participant) (stateIdx : Nat) :
    Preserves DeadInv (compromiseOPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))) fun _ => ?_
  exact preserves_sendMessage _

private theorem preserves_breakDH : Preserves DeadInv breakDH :=
  preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))

private theorem preserves_breakKEM : Preserves DeadInv breakKEM :=
  preserves_logPQX_nonDone _
    (fun _ _ _ _ _ _ _ _ _ _ => And.intro (fun h => by cases h) (fun h => by cases h))

private theorem preserves_invertDH (pkIdx : Nat) : Preserves DeadInv (invertDH pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertDH
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  split
  · exact preserves_sendMessage _
  · exact Preserves.failure

private theorem preserves_invertKEM (pkIdx : Nat) : Preserves DeadInv (invertKEM pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertKEM
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  refine Preserves.bind (Preserves.monadLiftErr _) fun _ => ?_
  exact preserves_sendMessage _

theorem deadInv_reachable {tr : ExecTrace} (hReach : tr.Reachable reachability) : DeadInv tr := by
  induction hReach with
  | Base => exact DeadInv.nil
  | Step input hPre _ ih =>
    exact Preserves.composed_step
      (fun msg _ _ hInv => hInv.append_other rfl rfl rfl)
      preserves_registerIdentity
      preserves_registerCorruptIdentity
      preserves_genSignedPrekey
      preserves_genPQPrekey
      preserves_genOneTimePrekey
      preserves_aliceStart
      preserves_bobStart
      preserves_messageEncrypt
      preserves_messageEncryptAbort
      preserves_messageDecrypt
      preserves_messageDecryptSkipped
      preserves_exposeKey
      preserves_exposeSpqr
      preserves_exposeSkipped
      preserves_compromiseIK
      preserves_compromiseSPK
      preserves_compromisePQSPK
      preserves_compromiseOPK
      preserves_breakDH
      preserves_breakKEM
      preserves_invertDH
      preserves_invertKEM
      input _ hPre ih

/-! ## Main Deadness Theorems -/

/-- No reachable trace logs `ExposedCKs s keys.ck n r` for any completed handshake's `keys`. -/
theorem exposedCKs_handshakeCk_dead_shared : ∀ tr : ExecTrace, tr.Reachable reachability →
    ¬ ∃ s j keys n r, tr.EventLogged (ComposedEvent.HandshakeSession s j) ∧ HandshakeKeysAt tr j keys ∧
      tr.EventLogged (TREvent.ExposedCKs s keys.ck n r) := by
  intro tr hR ⟨s, j, keys, n, r, _, hK, hE⟩
  have hInv := deadInv_reachable hR
  obtain ⟨ikm, rfl⟩ := hInv.handshakeKdf j keys hK
  rcases hInv.exposedCKs s (pqxdhKdf ikm).ck n r hE with ⟨r₀, p₀, s₀, hcc⟩ | ⟨ck₀, hck⟩
  · exact pqxdhKdf_ck_ne_createChain_snd ikm r₀ p₀ s₀ hcc
  · exact pqxdhKdf_ck_ne_kdfCk_fst ikm ck₀ hck

/-- No reachable trace logs `ExposedRK s keys.rk r` for any completed handshake's `keys`. -/
theorem exposedRK_handshakeRk_dead_shared : ∀ tr : ExecTrace, tr.Reachable reachability →
    ¬ ∃ s j keys r, tr.EventLogged (ComposedEvent.HandshakeSession s j) ∧ HandshakeKeysAt tr j keys ∧
      tr.EventLogged (TREvent.ExposedRK s keys.rk r) := by
  intro tr hR ⟨s, j, keys, r, _, hK, hE⟩
  have hInv := deadInv_reachable hR
  obtain ⟨ikm, rfl⟩ := hInv.handshakeKdf j keys hK
  obtain ⟨r₀, p₀, s₀, hrk⟩ := hInv.exposedRK s (pqxdhKdf ikm).rk r hE
  exact pqxdhKdf_rk_ne_createChain_fst ikm r₀ p₀ s₀ hrk

end Symbolic.Proofs.Tests.Shared.ExplanationTightness.HandshakeDead
