/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.ModelProofDefs
import DY.Bytes.Basic
import DY.Trace.Manipulation
import DY.EquationalTheory.KdfExtract
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Trace.Basic
import DY.Trace.Monad
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import DY.ALaCarte.Basic
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.PersistentGlobalState
public import Symbolic.Specifications.Model.Instance
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.SymEnc
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Trunc
import Symbolic.Tests.ModelNonVacuity -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState

/-!
# Shared `Runs` Combinators and Reachability Helpers for `DY.Libsignal.Composed`

Defines symbolic step-execution (`Runs`) combinators, reachability preservation lemmas, and
key-schedule agreement lemmas for `DY.Libsignal.Composed`, covering handshakes with and without
a one-time prekey.
-/

@[expose] public section

set_option autoImplicit false

/-! ## Generic PQXDH Handshake `Runs` Combinators -/

namespace Symbolic.Proofs.Tests.Shared.Composed.Runs

namespace ComposedRuns

open DY DY.Libsignal DY.Libsignal.PQXDH

open DY DY.Comparse DY.DiffieHellman DY.PQKem DY.Libsignal.PQXDH

variable [DY.Libsignal.PQXDH.HasExecTrace]

def rnd (t n : Nat) : Bytes :=
  BytesView.pack (SubF := Random.Random) { timestamp := t, size := n }

def Runs {α : Type} (x : Traceful α) (tr : ExecTrace) (a : α) (tr' : ExecTrace) : Prop :=
  (x.run tr).1 = some a ∧ (x.run tr).2.val = tr'

theorem Runs.bind {α β : Type} {x : Traceful α} {f : α → Traceful β} {tr tr1 tr2 : ExecTrace}
    {a : α} {b : β} (h1 : Runs x tr a tr1) (h2 : Runs (f a) tr1 b tr2) :
    Runs (x >>= f) tr b tr2 := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  rcases hx : x.run tr with ⟨o, t, _⟩
  rw [hx] at h1a h1b
  cases h1a
  cases h1b
  rcases hf : (f a).run t with ⟨o', t', _⟩
  rw [hf] at h2a h2b
  cases h2a
  cases h2b
  refine ⟨?_, ?_⟩ <;> rw [Traceful.run_bind, hx] <;> dsimp only <;> rw [hf]

private theorem append_len_loc {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem Runs.pure {α : Type} (a : α) (tr : ExecTrace) : Runs (pure a : Traceful α) tr a tr := by
  unfold Runs; rw [Traceful.run_pure]; exact ⟨rfl, rfl⟩

theorem Runs.getEntry {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {i : Nat} {e : E}
    (h : tr.at? i = some e) : Runs (DY.getEntry i : Traceful E) tr e tr := by
  unfold Runs; rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]; exact ⟨h, rfl⟩

theorem Runs.appendEntry {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    Runs (DY.appendEntry e) tr tr.length (tr.append e) := by
  unfold Runs; rw [Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]; exact ⟨rfl, rfl⟩

theorem Runs.guard {p : Prop} [Decidable p] (tr : ExecTrace) (h : p) :
    Runs (_root_.guard p : Traceful Unit) tr () tr := by
  simp only [_root_.guard, h, ↓reduceIte]; exact Runs.pure _ _

theorem Runs.genRand (tr : ExecTrace) (n : Nat) :
    Runs (Random.genRand n) tr (rnd tr.length n) (tr.append (Random.ExecEntryT.mk n)) := by
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1]
  exact Runs.bind (Runs.appendEntry tr _) (Runs.pure _ _)

abbrev EvE (ev : PQXDHEvent) : ProtocolEvent.ExecEntryT PQXDHEvent := ProtocolEvent.ExecEntryT.mk ev
abbrev NetE (b : Bytes) : Network.ExecEntryT := Network.ExecEntryT.mk b
abbrev StE (me : Participant) (st : PQXDHState) :=
  PersistentGlobalState.State.ExecEntryT.mk
    ({ participant := me, state := st } : PersistentLocalState.LocalState PQXDHState)

theorem Runs.receiveMessage {tr : ExecTrace} {i : Nat} {b : Bytes}
    (h : tr.at? i = some (NetE b)) : Runs (Network.receiveMessage i) tr b tr := by
  rw [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact Runs.bind (Runs.getEntry h) (Runs.pure _ _)

theorem Runs.getKey {tr : ExecTrace} {me : Participant} {h : Nat} {kind : KeyKind} {sk : Bytes}
    (hst : tr.at? h = some (StE me { kind, sk })) :
    Runs (DY.Libsignal.PQXDH.getKey me h kind) tr sk tr := by
  unfold DY.Libsignal.PQXDH.getKey
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine Runs.bind (Runs.bind (Runs.bind (Runs.getEntry hst) (Runs.pure _ _))
    (Runs.bind (Runs.guard _ rfl) (Runs.pure _ _))) ?_
  exact Runs.bind (Runs.guard _ rfl) (Runs.pure _ _)

theorem Runs.lookupIdentity {tr : ExecTrace} {p : Participant} {i : Nat} {ikPk vkPk : Bytes}
    {honest : Bool} (h : tr.at? i = some (EvE (.IdentityRegistered p ikPk vkPk honest))) :
    Runs (DY.Libsignal.PQXDH.lookupIdentity p i) tr (ikPk, vkPk) tr := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Runs.bind (Runs.getEntry h) ?_
  exact Runs.bind (Runs.guard _ rfl) (Runs.pure _ _)

def aliceOutOpt (tr : ExecTrace) (ikA ikBPk spkPk pqPk : Bytes) (opkPk : Option Bytes) :
    AliceHandshakeOut :=
  let ek := rnd tr.length 32
  let e := rnd (tr.length + 1) 32
  { ikA := dhPk ikA, ikB := ikBPk, spk := spkPk, pqpk := pqPk, opk := opkPk, ek := dhPk ek,
    ct := (aliceAgreement ikA ek ikBPk spkPk pqPk opkPk e).1,
    keys := (aliceAgreement ikA ek ikBPk spkPk pqPk opkPk e).2 }

abbrev aliceOut (tr : ExecTrace) (ikA ikBPk spkPk pqPk : Bytes) : AliceHandshakeOut :=
  aliceOutOpt tr ikA ikBPk spkPk pqPk none

theorem Runs.aliceHandshake {tr : ExecTrace} {a b : Participant} {idH regB : Nat}
    {h : BundleHandles} {ikA ikBPk vkB spkPk spkSig pqPk pqSig : Bytes} {honest : Bool}
    (hid : tr.at? idH = some (StE a { kind := .identity, sk := ikA }))
    (hreg : tr.at? regB = some (EvE (.IdentityRegistered b ikBPk vkB honest)))
    (hspk : tr.at? h.spk = some (NetE spkPk)) (hspkSig : tr.at? h.spkSig = some (NetE spkSig))
    (hpq : tr.at? h.pqpk = some (NetE pqPk)) (hpqSig : tr.at? h.pqpkSig = some (NetE pqSig))
    (hv1 : Signature.verify vkB (encodeEC spkPk) spkSig = true)
    (hv2 : Signature.verify vkB (encodeKEM pqPk) pqSig = true)
    (hopk : h.opk = none) (hlowSpk : x25519LowOrder spkPk = false) :
    Runs (DY.Libsignal.PQXDH.aliceHandshake a b idH regB h) tr
      (aliceOutOpt tr ikA ikBPk spkPk pqPk none)
      ((tr.append (Random.ExecEntryT.mk 32)).append (Random.ExecEntryT.mk 32)) := by
  rcases h with ⟨_, _, _, _, oi⟩
  cases hopk
  unfold DY.Libsignal.PQXDH.aliceHandshake
  refine Runs.bind (Runs.getKey hid) ?_
  refine Runs.bind (Runs.lookupIdentity hreg) ?_
  refine Runs.bind (Runs.receiveMessage hspk) ?_
  refine Runs.bind (Runs.receiveMessage hspkSig) ?_
  refine Runs.bind (Runs.receiveMessage hpq) ?_
  refine Runs.bind (Runs.receiveMessage hpqSig) ?_
  refine Runs.bind (Runs.guard _ hv1) ?_
  refine Runs.bind (Runs.guard _ hv2) ?_
  dsimp only
  refine Runs.bind (Runs.pure _ _) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.guard _ (by simp [hlowSpk])) ?_
  refine Runs.bind (Runs.guard _ rfl) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  simpa only [aliceOutOpt, append_len_loc] using Runs.pure _ _

theorem Runs.aliceHandshakeOpk {tr : ExecTrace} {a b : Participant} {idH regB oi : Nat}
    {h : BundleHandles} {ikA ikBPk vkB spkPk spkSig pqPk pqSig opkPk : Bytes} {honest : Bool}
    (hid : tr.at? idH = some (StE a { kind := .identity, sk := ikA }))
    (hreg : tr.at? regB = some (EvE (.IdentityRegistered b ikBPk vkB honest)))
    (hspk : tr.at? h.spk = some (NetE spkPk)) (hspkSig : tr.at? h.spkSig = some (NetE spkSig))
    (hpq : tr.at? h.pqpk = some (NetE pqPk)) (hpqSig : tr.at? h.pqpkSig = some (NetE pqSig))
    (hv1 : Signature.verify vkB (encodeEC spkPk) spkSig = true)
    (hv2 : Signature.verify vkB (encodeKEM pqPk) pqSig = true)
    (hopkEq : h.opk = some oi) (hopk : tr.at? oi = some (NetE opkPk))
    (hlowSpk : x25519LowOrder spkPk = false)
    (hlowOpk : ((some opkPk).all (!x25519LowOrder ·)) = true) :
    Runs (DY.Libsignal.PQXDH.aliceHandshake a b idH regB h) tr
      (aliceOutOpt tr ikA ikBPk spkPk pqPk (some opkPk))
      ((tr.append (Random.ExecEntryT.mk 32)).append (Random.ExecEntryT.mk 32)) := by
  rcases h with ⟨_, _, _, _, _⟩
  cases hopkEq
  unfold DY.Libsignal.PQXDH.aliceHandshake
  refine Runs.bind (Runs.getKey hid) ?_
  refine Runs.bind (Runs.lookupIdentity hreg) ?_
  refine Runs.bind (Runs.receiveMessage hspk) ?_
  refine Runs.bind (Runs.receiveMessage hspkSig) ?_
  refine Runs.bind (Runs.receiveMessage hpq) ?_
  refine Runs.bind (Runs.receiveMessage hpqSig) ?_
  refine Runs.bind (Runs.guard _ hv1) ?_
  refine Runs.bind (Runs.guard _ hv2) ?_
  refine Runs.bind (Runs.receiveMessage hopk) ?_
  refine Runs.bind (Runs.pure _ _) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.guard _ (by simp [hlowSpk])) ?_
  refine Runs.bind (Runs.guard _ hlowOpk) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  dsimp only
  simpa only [aliceOutOpt, append_len_loc] using Runs.pure _ _

def bobOutOpt (ikB spk pqsk : Bytes) (opkSk : Option Bytes) (ikAPk ek ct : Bytes)
    (keys : HandshakeKeys) : BobHandshakeOut :=
  { ikB := dhPk ikB, ikA := ikAPk, spk := dhPk spk, pqpk := kemPk pqsk,
    opk := opkSk.map dhPk, ek, ct, spkSk := spk, keys }

abbrev bobOut (ikB spk pqsk ikAPk ek ct : Bytes) (keys : HandshakeKeys) : BobHandshakeOut :=
  bobOutOpt ikB spk pqsk none ikAPk ek ct keys

theorem Runs.bobHandshakeOpt {tr : ExecTrace} {b a : Participant} {h : BobKeyHandles}
    {regA ekH ctH : Nat} {ikB spk pqsk ikAPk vkA ek ct : Bytes}
    {opkSk : Option Bytes} {honest : Bool} {keys : HandshakeKeys}
    (hik : tr.at? h.ik = some (StE b { kind := .identity, sk := ikB }))
    (hspk : tr.at? h.spk = some (StE b { kind := .signedPrekey, sk := spk }))
    (hpq : tr.at? h.pqspk = some (StE b { kind := .pqPrekey, sk := pqsk }))
    (hopk : match h.opk, opkSk with
      | none, none => True
      | some oi, some sk => tr.at? oi = some (StE b { kind := .oneTimePrekey, sk })
      | _, _ => False)
    (hreg : tr.at? regA = some (EvE (.IdentityRegistered a ikAPk vkA honest)))
    (hek : tr.at? ekH = some (NetE ek)) (hct : tr.at? ctH = some (NetE ct))
    (hcan : isCanonicalKey ek = true)
    (hagree : bobAgreement ikB spk pqsk opkSk ikAPk ek ct = some keys) :
    Runs (DY.Libsignal.PQXDH.bobHandshake b a h regA ekH ctH) tr
      (bobOutOpt ikB spk pqsk opkSk ikAPk ek ct keys) tr := by
  rcases h with ⟨_, _, _, oi⟩
  unfold DY.Libsignal.PQXDH.bobHandshake
  refine Runs.bind (Runs.getKey hik) ?_
  refine Runs.bind (Runs.getKey hspk) ?_
  refine Runs.bind (Runs.getKey hpq) ?_
  cases oi <;> cases opkSk
  · dsimp only
    refine Runs.bind (Runs.pure _ _) ?_
    refine Runs.bind (Runs.lookupIdentity hreg) ?_
    refine Runs.bind (Runs.receiveMessage hek) ?_
    refine Runs.bind (Runs.receiveMessage hct) ?_
    refine Runs.bind (Runs.guard _ hcan) ?_
    dsimp only
    rw [hagree]
    exact Runs.pure _ _
  · cases hopk
  · cases hopk
  · dsimp only at hopk
    refine Runs.bind (Runs.getKey hopk) ?_
    refine Runs.bind (Runs.pure _ _) ?_
    refine Runs.bind (Runs.lookupIdentity hreg) ?_
    refine Runs.bind (Runs.receiveMessage hek) ?_
    refine Runs.bind (Runs.receiveMessage hct) ?_
    refine Runs.bind (Runs.guard _ hcan) ?_
    rw [hagree]
    exact Runs.pure _ _

theorem Runs.bobHandshake {tr : ExecTrace} {b a : Participant} {h : BobKeyHandles}
    {regA ekH ctH : Nat} {ikB spk pqsk ikAPk vkA ek ct : Bytes} {honest : Bool}
    {keys : HandshakeKeys}
    (hik : tr.at? h.ik = some (StE b { kind := .identity, sk := ikB }))
    (hspk : tr.at? h.spk = some (StE b { kind := .signedPrekey, sk := spk }))
    (hpq : tr.at? h.pqspk = some (StE b { kind := .pqPrekey, sk := pqsk }))
    (hopk : h.opk = none)
    (hreg : tr.at? regA = some (EvE (.IdentityRegistered a ikAPk vkA honest)))
    (hek : tr.at? ekH = some (NetE ek)) (hct : tr.at? ctH = some (NetE ct))
    (hcan : isCanonicalKey ek = true)
    (hagree : bobAgreement ikB spk pqsk none ikAPk ek ct = some keys) :
    Runs (DY.Libsignal.PQXDH.bobHandshake b a h regA ekH ctH) tr
      (bobOut ikB spk pqsk ikAPk ek ct keys) tr :=
  Runs.bobHandshakeOpt (opkSk := none) hik hspk hpq (by simp [hopk]) hreg hek hct hcan hagree

end ComposedRuns

section

open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.Comparse DY.DiffieHellman DY.PQKem
open DY.Libsignal.Composed
open TripleRatchet (RecvChain SessionInfo KeyDir KeyComponent SignalMsg hmac kdfCk chainKeyAt
  createChain x25519LowOrder computeMac messageVersion maxReceiverChains maxForwardJumps u32Max
  lit litByte hkdfBlock1 hkdfBlock2 hkdfBlock3 zeroSalt consumeMessageKey
  findRecvChain setRecvChain recvChainFor TRState TREvent TRSignalMsg spqrA2B spqrB2A trMsgKeys
  trHonestWireMsg parseTrSignalMsg)
open PQXDH (PQXDHState PQXDHEvent KeyKind HandshakeKeys BundleHandles BobKeyHandles
  PreKeyMsgHandles serializedIk AliceHandshakeOut BobHandshakeOut aliceAgreement bobAgreement
  pqxdhKdf pqxdhIkm pqxdhLabel discontinuity agree isCanonicalKey encodeEC encodeKEM errToOption)
open PQXDH (NoCompromise HonestRun KeyKnown)

/-! ## Running transitions step by step -/

/-- A random value (defeq to DyLean's `makeRand`). -/
def rnd (t n : Nat) : Bytes :=
  BytesView.pack (SubF := Random.Random) { timestamp := t, size := n }

/-- Dynamic trace-index lookup (first matching entry). -/
def findEntryIdx (tr : ExecTrace) (p : ExecTrace.Entry → Bool) : Nat :=
  (List.range tr.length).findIdx fun i => match tr.at? i with | some e => p e | none => false

/-- Dynamic trace-index lookup (last matching entry). -/
def findLastEntryIdx (tr : ExecTrace) (p : ExecTrace.Entry → Bool) : Nat :=
  tr.length - 1 - (List.range tr.length).findIdx fun i =>
    match tr.at? (tr.length - 1 - i) with | some e => p e | none => false

/-- `x` run on `tr` returns `a` and leaves `tr'`. -/
def Runs {α : Type} (x : Traceful α) (tr : ExecTrace) (a : α) (tr' : ExecTrace) : Prop :=
  (x.run tr).1 = some a ∧ (x.run tr).2.val = tr'

theorem Runs.bind {α β : Type} {x : Traceful α} {f : α → Traceful β} {tr tr1 tr2 : ExecTrace}
    {a : α} {b : β} (h1 : Runs x tr a tr1) (h2 : Runs (f a) tr1 b tr2) :
    Runs (x >>= f) tr b tr2 := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  rcases hx : x.run tr with ⟨o, t, _⟩
  rw [hx] at h1a h1b
  cases h1a
  cases h1b
  rcases hf : (f a).run t with ⟨o', t', _⟩
  rw [hf] at h2a h2b
  cases h2a
  cases h2b
  refine ⟨?_, ?_⟩ <;> rw [Traceful.run_bind, hx] <;> dsimp only <;> rw [hf]

private theorem append_len_loc {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem runs_cast_loc {α : Type} {x : Traceful α} {tr : ExecTrace} {a₁ a₂ : α}
    {tr₁ tr₂ : ExecTrace} (h : Runs x tr a₁ tr₁) (ha : a₁ = a₂) (htr : tr₁ = tr₂) :
    Runs x tr a₂ tr₂ :=
  ha ▸ htr ▸ h

theorem Runs.pure {α : Type} (a : α) (tr : ExecTrace) : Runs (pure a : Traceful α) tr a tr := by
  unfold Runs; rw [Traceful.run_pure]; exact ⟨rfl, rfl⟩

theorem Runs.getEntry {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {i : Nat} {e : E}
    (h : tr.at? i = some e) : Runs (DY.getEntry i : Traceful E) tr e tr := by
  unfold Runs; rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]; exact ⟨h, rfl⟩

theorem Runs.appendEntry {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    Runs (DY.appendEntry e) tr tr.length (tr.append e) := by
  unfold Runs; rw [Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]; exact ⟨rfl, rfl⟩

theorem Runs.guard {p : Prop} [Decidable p] (tr : ExecTrace) (h : p) :
    Runs (_root_.guard p : Traceful Unit) tr () tr := by
  simp only [_root_.guard, h, ↓reduceIte]; exact Runs.pure _ _

theorem Runs.requireTracePredicate {tr : ExecTrace} {p : ExecTrace → Bool} (h : p tr = true) :
    Runs (PQXDH.guardTrace p) tr () tr := by
  unfold Runs PQXDH.guardTrace
  simp only [Traceful.run_mk, h, ↓reduceIte]
  exact ⟨trivial, trivial⟩

theorem Runs.guardTrace {tr : ExecTrace} {p : ExecTrace → Bool} (h : p tr = true) :
    Runs (TripleRatchet.guardTrace p) tr () tr := by
  unfold Runs TripleRatchet.guardTrace
  simp only [Traceful.run_mk, h, ↓reduceIte]
  exact ⟨trivial, trivial⟩

theorem Runs.logEvent {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    (tr : ExecTrace) (ev : Ev) :
    Runs (ProtocolEvent.logEvent ev) tr () (tr.append (ProtocolEvent.ExecEntryT.mk ev)) := by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
  exact Runs.bind (Runs.appendEntry tr _) (Runs.pure _ _)

theorem Runs.genRand (tr : ExecTrace) (n : Nat) :
    Runs (Random.genRand n) tr (rnd tr.length n) (tr.append (Random.ExecEntryT.mk n)) := by
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1]
  exact Runs.bind (Runs.appendEntry tr _) (Runs.pure _ _)

abbrev RndE (n : Nat) : Random.ExecEntryT := Random.ExecEntryT.mk n
abbrev NetE (b : Bytes) : Network.ExecEntryT := Network.ExecEntryT.mk b
abbrev EvT (ev : TREvent) : ProtocolEvent.ExecEntryT TREvent := ProtocolEvent.ExecEntryT.mk ev
abbrev TrEvE (ev : TREvent) : ProtocolEvent.ExecEntryT TREvent := EvT ev
abbrev EvP (ev : PQXDHEvent) : ProtocolEvent.ExecEntryT PQXDHEvent := ProtocolEvent.ExecEntryT.mk ev
abbrev EvE (ev : PQXDHEvent) : ProtocolEvent.ExecEntryT PQXDHEvent := EvP ev
abbrev EvC (ev : ComposedEvent) : ProtocolEvent.ExecEntryT ComposedEvent := ProtocolEvent.ExecEntryT.mk ev

abbrev StT (me : Participant) (st : TRState) :=
  PersistentGlobalState.State.ExecEntryT.mk
    ({ participant := me, state := st } : PersistentLocalState.LocalState TRState)
abbrev TrStE (me : Participant) (st : TRState) := StT me st

abbrev StP (me : Participant) (st : PQXDHState) :=
  PersistentGlobalState.State.ExecEntryT.mk
    ({ participant := me, state := st } : PersistentLocalState.LocalState PQXDHState)
abbrev StE (me : Participant) (st : PQXDHState) := StP me st

theorem Runs.sendMessage (tr : ExecTrace) (b : Bytes) :
    Runs (Network.sendMessage b) tr tr.length (tr.append (NetE b)) := by
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1]
  exact Runs.appendEntry _ _

theorem Runs.receiveMessage {tr : ExecTrace} {h : Nat} {b : Bytes}
    (hb : tr.at? h = some (NetE b)) : Runs (Network.receiveMessage h) tr b tr := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact Runs.bind (Runs.getEntry hb) (Runs.pure _ _)

theorem Runs.traceLength (tr : ExecTrace) :
    Runs TripleRatchet.traceLength tr tr.length tr := by
  unfold Runs TripleRatchet.traceLength
  rw [Traceful.run_mk]
  exact ⟨rfl, rfl⟩

theorem Runs.getLocalState {tr : ExecTrace} {me : Participant} {h : Nat} {st : TRState}
    (hst : tr.at? h = some (StT me st)) :
    Runs (PersistentLocalState.getLocalState me h : Traceful TRState) tr st tr := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact Runs.bind (Runs.bind (Runs.getEntry hst) (Runs.pure _ _))
    (Runs.bind (Runs.guard _ rfl) (Runs.pure _ _))

theorem Runs.storeLocalState (tr : ExecTrace) (me : Participant) (st : TRState) :
    Runs (PersistentLocalState.storeLocalState me st) tr tr.length (tr.append (StT me st)) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1]
  exact Runs.bind (Runs.pure _ _) (Runs.appendEntry _ _)

theorem Runs.storePQXDHState (tr : ExecTrace) (me : Participant) (st : PQXDHState) :
    Runs (PersistentLocalState.storeLocalState me st) tr tr.length (tr.append (StP me st)) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1]
  exact Runs.bind (Runs.pure _ _) (Runs.appendEntry _ _)

theorem Runs.getKey {tr : ExecTrace} {me : Participant} {h : Nat} {kind : KeyKind} {sk : Bytes}
    (hst : tr.at? h = some (StP me { kind, sk })) :
    Runs (PQXDH.getKey me h kind) tr sk tr :=
  ComposedRuns.Runs.getKey hst

theorem Runs.lookupIdentity {tr : ExecTrace} {p : Participant} {i : Nat} {ikPk vkPk : Bytes}
    {honest : Bool} (h : tr.at? i = some (EvP (.IdentityRegistered p ikPk vkPk honest))) :
    Runs (PQXDH.lookupIdentity p i) tr (ikPk, vkPk) tr :=
  ComposedRuns.Runs.lookupIdentity h

/-! ## Triple Ratchet steps -/

theorem Runs.receiveSignalMsg {tr : ExecTrace} {msgH : Nat} {t : Bytes} {msg : TRSignalMsg}
    (hmsg : tr.at? msgH = some (NetE t))
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion) :
    Runs (TripleRatchet.receiveSignalMsg msgH) tr msg tr := by
  unfold TripleRatchet.receiveSignalMsg
  refine Runs.bind (Runs.receiveMessage hmsg) ?_
  rw [hparse]
  exact Runs.bind (Runs.guard _ hver) (Runs.pure _ _)

theorem Runs.verifyMacAndDecrypt {tr : ExecTrace} {st : TRState} {msg : TRSignalMsg}
    {pq seed m : Bytes}
    (hmac : msg.mac = computeMac (trMsgKeys pq seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : SymEnc.symDec (trMsgKeys pq seed).cipherKey (trMsgKeys pq seed).iv msg.ciphertext =
      some m) :
    Runs (TripleRatchet.verifyMacAndDecrypt st msg pq seed) tr m tr := by
  unfold TripleRatchet.verifyMacAndDecrypt
  refine Runs.bind (Runs.guard _ hmac) ?_
  unfold Runs
  rw [hdec]
  dsimp only [liftM, monadLift, MonadLift.monadLift]
  rw [Traceful.run_mk]
  exact ⟨rfl, rfl⟩

theorem Runs.logSkippedKeys (s : SessionInfo) (pk : Bytes) (r sourceStateIdx : Nat) :
    ∀ (ck : Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace),
      Runs (TripleRatchet.logSkippedKeys s pk r sourceStateIdx ck n k) tr ()
        ((TripleRatchet.logSkippedKeys s pk r sourceStateIdx ck n k).run tr).2.val
  | _, _, 0, _ => by unfold TripleRatchet.logSkippedKeys Runs; rw [Traceful.run_pure]; exact ⟨rfl, rfl⟩
  | ck, n, k + 1, tr => by
    unfold TripleRatchet.logSkippedKeys
    have h2 := Runs.logSkippedKeys s pk r sourceStateIdx (kdfCk ck).1 (n + 1) k
      (tr.append (EvT (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 r sourceStateIdx)))
    have := Runs.bind
      (f := fun _ =>
        TripleRatchet.logSkippedKeys s pk r sourceStateIdx (kdfCk ck).1 (n + 1) k)
      (Runs.logEvent tr (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 r sourceStateIdx)) h2
    exact ⟨this.1, rfl⟩

theorem Runs.ensureReceiverChain_found {tr : ExecTrace} {st : TRState} {pk : Bytes}
    {c : RecvChain} (hfind : findRecvChain st.recv pk = some c) :
    Runs (TripleRatchet.ensureReceiverChain st pk) tr (st, c, false) tr := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor
  rw [hfind]
  exact Runs.pure _ _

/-- The state and new receiver chain of `dhRatchetStep st pk` with fresh secret `dhs`. -/
def ratchetState (st : TRState) (pk dhs : Bytes) : TRState × RecvChain :=
  let (rk1, ckr) := createChain st.rk pk st.dhs
  let (rk2, cks) := createChain rk1 pk dhs
  let c : RecvChain := { ratchetKey := pk, chainKey := ckr, index := 0, rIdx := st.rIdx + 2 }
  let recv := (st.recv ++ [c]).drop ((st.recv.length + 1) - maxReceiverChains)
  let pn := if st.ns = 0 then 0 else st.ns - 1
  ({ st with rk := rk2, dhs, cks, ns := 0, pn, rIdx := st.rIdx + 2, recv }, c)

theorem Runs.ensureReceiverChain_ratchet {tr : ExecTrace} {st : TRState} {pk : Bytes}
    (hfind : findRecvChain st.recv pk = none) (hlow : x25519LowOrder pk = false) :
    Runs (TripleRatchet.ensureReceiverChain st pk) tr
      ((ratchetState st pk (rnd tr.length 32)).1, (ratchetState st pk (rnd tr.length 32)).2, true)
      (tr.append (RndE 32)) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  rw [hfind, hlow]
  dsimp only [ite_false]
  exact Runs.bind (Runs.bind (Runs.guard _ (by simp))
    (Runs.bind (Runs.genRand _ _) (Runs.pure _ _))) (Runs.pure _ _)

theorem Runs.logMessageKeyAndStore (tr : ExecTrace) (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (mk pq : Bytes) (n : UInt32)
    (rIdx parentStateIdx : Nat) (st : TRState) :
    Runs (TripleRatchet.logMessageKeyAndStore me s dir mk pq n rIdx
      parentStateIdx st) tr (tr.length + 1)
      ((tr.append (EvT (.MessageKey s dir mk pq n rIdx parentStateIdx))).append (StT me st)) := by
  unfold TripleRatchet.logMessageKeyAndStore
  exact Runs.bind (Runs.logEvent _ _) (runs_cast_loc (Runs.storeLocalState _ _ _) (append_len_loc _ _) rfl)

/-- A non-fresh SPQR state (not an `InitState`), from a kernel-decided `isNone`. -/
theorem notInit {st : Bytes} (h : (st.view? Spqr.InitState.SubF).isNone = true) :
    st.view? Spqr.InitState.SubF = none :=
  Option.isNone_iff_eq_none.mp h

/-- The SPQR state after an accepting `spqrRecv st msg _`: `RecvState{st, msg}`. -/
abbrev recvSt (st msg : Bytes) : Bytes := ({st, msg} : Spqr.RecvState.SubF Bytes).pack

/-- The opaque key of an accepting `spqrRecv st msg _` on a non-fresh state. -/
abbrev recvKey (st msg : Bytes) : Bytes := ({st, msg} : Spqr.RecvKey.SubF Bytes).pack

theorem notInit_send (st coins : Bytes) :
    (Spqr.spqrSend st coins).1.view? Spqr.InitState.SubF = none := by
  dsimp only [Spqr.spqrSend]
  exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Spqr.InitState.SubF _

theorem notInit_recv (st msg : Bytes) :
    (recvSt st msg).view? Spqr.InitState.SubF = none := by
  dsimp only [recvSt]
  exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Spqr.InitState.SubF _

/-- The trace after the skipped-key bookkeeping of a decrypt. -/
abbrev skipTr (tr : ExecTrace) (s : SessionInfo) (pk : Bytes) (c : RecvChain)
    (sourceStateIdx : Nat) (n : UInt32) : ExecTrace :=
  ((TripleRatchet.logSkippedKeys s pk c.rIdx sourceStateIdx c.chainKey c.index
    (n.toNat - c.index.toNat)).run tr).2.val

theorem Runs.messageDecrypt_noRatchet {tr : ExecTrace} {me : Participant} {stH msgH pqH : Nat}
    {idx : UInt32} {st : TRState} {t : Bytes} {msg : TRSignalMsg} {c c' : RecvChain}
    {pq seed m spqr' key : Bytes}
    (hst : tr.at? stH = some (StT me st))
    (hmsg : tr.at? msgH = some (NetE t))
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hfind : findRecvChain st.recv msg.ratchetKey = some c)
    (hcons : consumeMessageKey c msg.counter = some (seed, c'))
    (hrecv : Spqr.spqrRecv st.spqr msg.pqRatchet idx = some (spqr', key))
    (hpq : (tr.append (NetE key)).at? pqH = some (NetE pq))
    (hmac : msg.mac = computeMac (trMsgKeys pq seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : SymEnc.symDec (trMsgKeys pq seed).cipherKey (trMsgKeys pq seed).iv msg.ciphertext =
      some m)
    {stOut : TRState}
    (hout : { st with recv := setRecvChain st.recv c', spqr := spqr' } = stOut) :
    let tr0 := tr.append (NetE key)
    let trS := skipTr tr0 (st.sessionInfo me) msg.ratchetKey c stH msg.counter
    Runs (TripleRatchet.messageDecrypt me stH msgH pqH idx) tr (trS.length + 2)
      (((trS.append (EvT (.Received me st.peer msg.ratchetKey msg.counter m))).append
        (EvT (.MessageKey (st.sessionInfo me) .receiver seed pq msg.counter c.rIdx
          stH))).append
        (StT me stOut)) := by
  subst hout
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine Runs.bind (Runs.getLocalState hst) ?_
  refine Runs.bind (Runs.receiveSignalMsg hmsg hparse hver) ?_
  refine Runs.bind (Runs.ensureReceiverChain_found hfind) ?_
  dsimp only
  rw [hcons]
  dsimp only
  rw [hrecv]
  dsimp only
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.receiveMessage hpq) ?_
  refine Runs.bind (Runs.verifyMacAndDecrypt hmac hdec) ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Runs.bind (Runs.logSkippedKeys _ _ _ _ _ _ _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  exact runs_cast_loc (Runs.logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _)
    (by rw [append_len_loc, Nat.add_assoc]) rfl

theorem Runs.messageDecrypt_ratchet {tr : ExecTrace} {me : Participant} {stH msgH pqH : Nat}
    {idx : UInt32} {st st' : TRState} {t : Bytes} {msg : TRSignalMsg} {c c' : RecvChain}
    {pq seed m spqr' key : Bytes}
    (hst : tr.at? stH = some (StT me st))
    (hmsg : tr.at? msgH = some (NetE t))
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hfind : findRecvChain st.recv msg.ratchetKey = none)
    (hlow : x25519LowOrder msg.ratchetKey = false)
    (hrs : ratchetState st msg.ratchetKey (rnd tr.length 32) = (st', c))
    (hcons : consumeMessageKey c msg.counter = some (seed, c'))
    (hrecv : Spqr.spqrRecv st'.spqr msg.pqRatchet idx = some (spqr', key))
    (hpq : ((tr.append (RndE 32)).append (NetE key)).at? pqH = some (NetE pq))
    (hmac : msg.mac = computeMac (trMsgKeys pq seed).macKey st'.peerIk st'.myIk msg.wire)
    (hdec : SymEnc.symDec (trMsgKeys pq seed).cipherKey (trMsgKeys pq seed).iv msg.ciphertext =
      some m)
    {stOut : TRState}
    (hout : { st' with recv := setRecvChain st'.recv c', spqr := spqr' } = stOut) :
    let tr1 := (((tr.append (RndE 32)).append (NetE key)).append
        (EvT (.DHRatchet me st'.peer msg.ratchetKey (dhPk st'.dhs)))).append
        (EvT (.HonestDH (st'.sessionInfo me) st'.dhs (st'.rIdx - 2)))
    let trS := skipTr tr1 (st'.sessionInfo me) msg.ratchetKey c stH msg.counter
    Runs (TripleRatchet.messageDecrypt me stH msgH pqH idx) tr (trS.length + 2)
      (((trS.append (EvT (.Received me st'.peer msg.ratchetKey msg.counter m))).append
        (EvT (.MessageKey (st'.sessionInfo me) .receiver seed pq msg.counter c.rIdx
          stH))).append
        (StT me stOut)) := by
  subst hout
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine Runs.bind (Runs.getLocalState hst) ?_
  refine Runs.bind (Runs.receiveSignalMsg hmsg hparse hver) ?_
  have he := Runs.ensureReceiverChain_ratchet (tr := tr) hfind hlow
  rw [hrs] at he
  refine Runs.bind he ?_
  dsimp only
  rw [hcons]
  dsimp only
  rw [hrecv]
  dsimp only
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.receiveMessage hpq) ?_
  refine Runs.bind (Runs.verifyMacAndDecrypt hmac hdec) ?_
  simp only [↓reduceIte]
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.logSkippedKeys _ _ _ _ _ _ _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  exact runs_cast_loc (Runs.logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _)
    (by rw [append_len_loc, Nat.add_assoc]) rfl

theorem Runs.messageDecryptSkipped {tr : ExecTrace} {me : Participant}
    {stH msgH skH pqH : Nat} {idx : UInt32} {st : TRState} {t : Bytes} {msg : TRSignalMsg}
    {s : SessionInfo} {pk : Bytes} {n : UInt32} {seed pq m spqr' key : Bytes}
    {rIdx srcIdx : Nat}
    (hst : tr.at? stH = some (StT me st))
    (hmsg : tr.at? msgH = some (NetE t))
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hsk : tr.at? skH = some (EvT (.SkippedKeyStored s pk n seed rIdx srcIdx)))
    (heq : s = st.sessionInfo me ∧ pk = msg.ratchetKey ∧ n = msg.counter ∧
      (TripleRatchet.findRecvChain st.recv pk).isSome = true)
    (hunused : (!TripleRatchet.skippedKeyUsedB tr skH) = true)
    (hrecv : Spqr.spqrRecv st.spqr msg.pqRatchet idx = some (spqr', key))
    (hpq : (tr.append (NetE key)).at? pqH = some (NetE pq))
    (hmac : msg.mac = computeMac (trMsgKeys pq seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : SymEnc.symDec (trMsgKeys pq seed).cipherKey (trMsgKeys pq seed).iv msg.ciphertext =
      some m)
    {stOut : TRState} (hout : { st with spqr := spqr' } = stOut) :
    let tr0 := ((tr.append (NetE key)).append (EvT (.SkippedKeyUsed s skH))).append
      (EvT (.Received me st.peer pk n m))
    Runs (TripleRatchet.messageDecryptSkipped me stH msgH skH pqH idx) tr (tr0.length + 1)
      ((tr0.append (EvT (.MessageKey s .receiver seed pq n rIdx stH))).append (StT me stOut)) := by
  subst hout
  unfold TripleRatchet.messageDecryptSkipped
  refine Runs.bind (Runs.getLocalState hst) ?_
  refine Runs.bind (Runs.receiveSignalMsg hmsg hparse hver) ?_
  refine Runs.bind (Runs.getEntry hsk) ?_
  dsimp only
  refine Runs.bind (Runs.guard _ heq) ?_
  refine Runs.bind (Runs.guardTrace hunused) ?_
  rw [hrecv]
  dsimp only
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.receiveMessage hpq) ?_
  refine Runs.bind (Runs.verifyMacAndDecrypt hmac hdec) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  exact Runs.logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _

/-- The wire message (with MAC) `messageEncrypt` sends from state `st` with SPQR coins `coins`,
salt `pq` and plaintext `m`. -/
def encMsg (st : TRState) (coins pq m : Bytes) : Bytes :=
  let keys := trMsgKeys pq (kdfCk st.cks).2
  let wire := trHonestWireMsg (dhPk st.dhs) st.ns st.pn
    (SymEnc.symEnc keys.cipherKey keys.iv m) (Spqr.spqrSend st.spqr coins).2.2
  Concat.concat wire (computeMac keys.macKey st.myIk st.peerIk wire)

/-- The state `messageEncrypt` stores after sending from `st` with SPQR coins `coins`. -/
def encSt (st : TRState) (coins : Bytes) : TRState :=
  { st with cks := (kdfCk st.cks).1, ns := st.ns + 1, spqr := (Spqr.spqrSend st.spqr coins).1 }

/-- The trace after `messageEncrypt me stH 32 pqH` on `tr` reading `st` and salt `pq`: plaintext
at `tr.length`, coins at `tr.length + 1`, the published SPQR key at `tr.length + 2`. -/
def encTr (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState) (pq : Bytes) :
    ExecTrace :=
  let m := rnd tr.length 32
  let coins := rnd (tr.length + 1) 32
  ((((((tr.append (RndE 32)).append (RndE 32)).append
    (NetE (Spqr.spqrSend st.spqr coins).2.1)).append
    (EvT (.Sent me st.peer (dhPk st.dhs) st.ns m))).append
    (EvT (.MessageKey (st.sessionInfo me) .sender (kdfCk st.cks).2 pq st.ns
      st.rIdx stH))).append
    (StT me (encSt st coins))).append
    (NetE (encMsg st coins pq m))

theorem Runs.messageEncrypt {tr : ExecTrace} {me : Participant} {stH pqH : Nat} {st : TRState}
    {pq : Bytes} (hst : tr.at? stH = some (StT me st)) (hns : st.ns ≠ u32Max)
    (hpq : (((tr.append (RndE 32)).append (RndE 32)).append
      (NetE (Spqr.spqrSend st.spqr (rnd (tr.length + 1) 32)).2.1)).at? pqH = some (NetE pq)) :
    Runs (TripleRatchet.messageEncrypt me stH 32 pqH) tr (tr.length + 6)
      (encTr tr me stH st pq) := by
  unfold TripleRatchet.messageEncrypt
  refine Runs.bind (Runs.getLocalState hst) ?_
  refine Runs.bind (Runs.guard _ hns) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  have hpq' :
      (((tr.append (RndE 32)).append (RndE 32)).append
        (NetE (Spqr.spqrSend st.spqr
          (rnd (tr.append (RndE 32)).length 32)).2.1)).at? pqH = some (NetE pq) := by
    rw [append_len_loc]; exact hpq
  refine Runs.bind (Runs.receiveMessage hpq') ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _) ?_
  refine runs_cast_loc (Runs.sendMessage _ _) ?_ ?_
  · simp only [NetE, EvT, StT, append_len_loc, Nat.add_assoc]
  · simp only [encTr, encSt, encMsg, RndE, NetE, EvT, StT, append_len_loc]
    dsimp only [kdfCk, Spqr.spqrSend]

/-! ## Session-State and Skipped-Key Exposure Transitions -/

def exposeRkTr (tr : ExecTrace) (me : Participant) (st : TRState) : ExecTrace :=
  (tr.append (EvT (.ExposedRK (st.sessionInfo me) st.rk st.rIdx))).append (NetE st.rk)

theorem Runs.exposeRk {tr : ExecTrace} {me : Participant} {stH : Nat} {st : TRState}
    (hst : tr.at? stH = some (StT me st)) :
    Runs (TripleRatchet.exposeKey me stH .rk) tr (tr.length + 1) (exposeRkTr tr me st) := by
  unfold TripleRatchet.exposeKey
  refine Runs.bind (Runs.getLocalState hst) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  exact runs_cast_loc (Runs.sendMessage _ _) (append_len_loc _ _) rfl

def exposeDhsTr (tr : ExecTrace) (me : Participant) (st : TRState) : ExecTrace :=
  (tr.append (EvT (.ExposedDHs (st.sessionInfo me) st.dhs st.rIdx))).append (NetE st.dhs)

theorem Runs.exposeDhs {tr : ExecTrace} {me : Participant} {stH : Nat} {st : TRState}
    (hst : tr.at? stH = some (StT me st)) :
    Runs (TripleRatchet.exposeKey me stH .dhs) tr (tr.length + 1) (exposeDhsTr tr me st) := by
  unfold TripleRatchet.exposeKey
  refine Runs.bind (Runs.getLocalState hst) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  exact runs_cast_loc (Runs.sendMessage _ _) (append_len_loc _ _) rfl

def exposeCksTr (tr : ExecTrace) (me : Participant) (st : TRState) : ExecTrace :=
  (tr.append (EvT (.ExposedCKs (st.sessionInfo me) st.cks st.ns st.rIdx))).append (NetE st.cks)

theorem Runs.exposeCks {tr : ExecTrace} {me : Participant} {stH : Nat} {st : TRState}
    (hst : tr.at? stH = some (StT me st)) :
    Runs (TripleRatchet.exposeKey me stH .cks) tr (tr.length + 1) (exposeCksTr tr me st) := by
  unfold TripleRatchet.exposeKey
  refine Runs.bind (Runs.getLocalState hst) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  exact runs_cast_loc (Runs.sendMessage _ _) (append_len_loc _ _) rfl

def exposeCkrTr (tr : ExecTrace) (me : Participant) (st : TRState) (c : RecvChain) :
    ExecTrace :=
  (tr.append (EvT (.ExposedCKr (st.sessionInfo me) c.chainKey c.index c.rIdx))).append
    (NetE c.chainKey)

theorem Runs.exposeCkr {tr : ExecTrace} {me : Participant} {stH : Nat} {st : TRState}
    {pk : Bytes} {c : RecvChain} (hst : tr.at? stH = some (StT me st))
    (hfind : findRecvChain st.recv pk = some c) :
    Runs (TripleRatchet.exposeKey me stH (.ckr pk)) tr (tr.length + 1)
      (exposeCkrTr tr me st c) := by
  unfold TripleRatchet.exposeKey
  refine Runs.bind (Runs.getLocalState hst) ?_
  dsimp only
  rw [hfind]
  refine Runs.bind (Runs.logEvent _ _) ?_
  exact runs_cast_loc (Runs.sendMessage _ _) (append_len_loc _ _) rfl

def exposeSpqrTr (tr : ExecTrace) (me : Participant) (st : TRState) : ExecTrace :=
  (tr.append (EvT (.ExposedSpqr (st.sessionInfo me) st.spqr st.rIdx))).append (NetE st.spqr)

theorem Runs.exposeSpqr {tr : ExecTrace} {me : Participant} {stH : Nat} {st : TRState}
    (hst : tr.at? stH = some (StT me st)) :
    Runs (TripleRatchet.exposeSpqr me stH) tr (tr.length + 1) (exposeSpqrTr tr me st) := by
  unfold TripleRatchet.exposeSpqr
  refine Runs.bind (Runs.getLocalState hst) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  exact runs_cast_loc (Runs.sendMessage _ _) (append_len_loc _ _) rfl

def exposeSkippedTr (tr : ExecTrace) (s : SessionInfo) (seed : Bytes) (n : UInt32)
    (rIdx : Nat) : ExecTrace :=
  (tr.append (EvT (.ExposedMK s seed n rIdx))).append (NetE seed)

abbrev exposeMkTr := exposeSkippedTr

theorem Runs.exposeSkipped {tr : ExecTrace} {skH : Nat} {s : SessionInfo} {pk : Bytes}
    {n : UInt32} {seed : Bytes} {rIdx srcIdx : Nat}
    (hsk : tr.at? skH = some (EvT (.SkippedKeyStored s pk n seed rIdx srcIdx)))
    (hunused : (!TripleRatchet.receiverKeyUsedB tr s seed n rIdx) = true) :
    Runs (TripleRatchet.exposeSkipped skH) tr (tr.length + 1)
      (exposeSkippedTr tr s seed n rIdx) := by
  unfold TripleRatchet.exposeSkipped
  refine Runs.bind (Runs.getEntry hsk) ?_
  dsimp only
  refine Runs.bind (Runs.guardTrace hunused) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  exact runs_cast_loc (Runs.sendMessage _ _) (append_len_loc _ _) rfl

abbrev Runs.exposeMk := @Runs.exposeSkipped

/-! ## Equational theory, wire-format, and key-schedule agreement helpers -/

theorem length_hmac (k m : Bytes) : (hmac k m).length = 32 := by
  simp only [hmac, KdfExtract.kdfExtract]
  simp [Bytes.length.eq, Symbolic.DYBridge.DY.KdfExtract.KdfExtract.SubF.length_eq_1]

theorem parse_honest (rk ct pqm mk ikS ikR : Bytes) (n pn : UInt32) :
    parseTrSignalMsg (Concat.concat (trHonestWireMsg rk n pn ct pqm)
      (computeMac mk ikS ikR (trHonestWireMsg rk n pn ct pqm))) =
    some { wire := trHonestWireMsg rk n pn ct pqm,
           mac := computeMac mk ikS ikR (trHonestWireMsg rk n pn ct pqm),
           version := 4, ratchetKey := rk, counter := n, ciphertext := ct, pqRatchet := pqm } := by
  have hl : (Concat.concat (trHonestWireMsg rk n pn ct pqm)
      (computeMac mk ikS ikR (trHonestWireMsg rk n pn ct pqm))).length - Trunc.trunc8Length =
      (trHonestWireMsg rk n pn ct pqm).length := by
    simp [computeMac, Trunc.length_trunc8, length_hmac, Trunc.trunc8Length]
  simp only [parseTrSignalMsg, hl, Concat.split_concat]
  simp only [trHonestWireMsg, bind, Option.bind, TrWire.trWireMsgFields?_trWireMsg]
  rfl

/-- The parsed form of `encMsg st coins pq m`. -/
def encSig (st : TRState) (coins pq m : Bytes) : TRSignalMsg :=
  let keys := trMsgKeys pq (kdfCk st.cks).2
  let wire := trHonestWireMsg (dhPk st.dhs) st.ns st.pn
    (SymEnc.symEnc keys.cipherKey keys.iv m) (Spqr.spqrSend st.spqr coins).2.2
  { wire, mac := computeMac keys.macKey st.myIk st.peerIk wire, version := 4,
    ratchetKey := dhPk st.dhs, counter := st.ns,
    ciphertext := SymEnc.symEnc keys.cipherKey keys.iv m,
    pqRatchet := (Spqr.spqrSend st.spqr coins).2.2 }

theorem parse_encMsg (st : TRState) (coins pq m : Bytes) :
    parseTrSignalMsg (encMsg st coins pq m) = some (encSig st coins pq m) :=
  parse_honest _ _ _ _ _ _ _ _

/-- The receiver's MAC check passes on `encMsg stS coins pq m` if it derives the sender's seed and
uses the sender's salt. -/
theorem mac_ok {stS stR : TRState} {coins pq m seed : Bytes} (hseed : (kdfCk stS.cks).2 = seed)
    (h1 : stR.peerIk = stS.myIk) (h2 : stR.myIk = stS.peerIk) :
    (encSig stS coins pq m).mac =
      computeMac (trMsgKeys pq seed).macKey stR.peerIk stR.myIk
        (encSig stS coins pq m).wire := by
  subst hseed; rw [h1, h2]; rfl

theorem dec_ok {stS : TRState} {coins pq m seed : Bytes} (hseed : (kdfCk stS.cks).2 = seed) :
    SymEnc.symDec (trMsgKeys pq seed).cipherKey (trMsgKeys pq seed).iv
      (encSig stS coins pq m).ciphertext = some m := by
  subst hseed; exact SymEnc.symDec_symEnc _ _ _

private theorem norm_dhPk_loc (a : Bytes) :
    X25519.normalizeX25519Key (dhPk a) = dhPk a := by
  dsimp only [X25519.normalizeX25519Key, DiffieHellman.dhPk, DiffieHellman.instCanDHBytes]
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none X25519.Variant.SubF]

theorem createChain_comm (rk a b : Bytes) :
    createChain rk (dhPk a) b = createChain rk (dhPk b) a := by
  simp only [createChain, DY.X25519.agree]
  rw [norm_dhPk_loc a, norm_dhPk_loc b, DiffieHellman.dh_commutes]

theorem rnd_inj {t t' n n' : Nat} (h : rnd t n = rnd t' n') : t = t' := by
  have := congrArg (fun b => Bytes.view? b Random.Random) h
  simp only [rnd, BytesView.view_pack, Option.some.injEq, Random.Random.mk.injEq] at this
  exact this.1

theorem dhPk_inj {a b : Bytes} (h : dhPk a = dhPk b) : a = b := by
  have := congrArg (fun x => Bytes.view? x DiffieHellman.DhPk.SubF) h
  simp only [dhPk, BytesView.view_pack, Option.some.injEq,
    DiffieHellman.DhPk.SubF.mk.injEq] at this
  exact this

theorem dhPk_rnd_ne {t t' : Nat} (h : t ≠ t') :
    dhPk (rnd t 32) ≠ dhPk (rnd t' 32) :=
  fun e => h (rnd_inj (dhPk_inj e))

theorem kemDecap_kemEncap (sk e : Bytes) :
    kemDecap sk (kemEncap (kemPk sk) e).1 = some (kemEncap (kemPk sk) e).2 := by
  simp only [kemDecap, kemEncap, kemPk, BytesView.view_pack, ↓reduceIte]

theorem agree_comm (a b : Bytes) : agree (dhPk a) b = agree (dhPk b) a := by
  simp only [agree]
  rw [norm_dhPk_loc a, norm_dhPk_loc b, DiffieHellman.dh_commutes]

/-- Key-schedule agreement between `bobAgreement` and `aliceAgreement` (with optional OPK). -/
theorem bobAgreement_honest_opt (ikA ek ikB spk pqsk e : Bytes) (opk : Option Bytes) :
    bobAgreement ikB spk pqsk opk (dhPk ikA) (dhPk ek)
      (aliceAgreement ikA ek (dhPk ikB) (dhPk spk) (kemPk pqsk) (opk.map dhPk) e).1 =
    some (aliceAgreement ikA ek (dhPk ikB) (dhPk spk) (kemPk pqsk) (opk.map dhPk) e).2 := by
  have hct : (aliceAgreement ikA ek (dhPk ikB) (dhPk spk) (kemPk pqsk) (opk.map dhPk) e).1 =
      (kemEncap (kemPk pqsk) e).1 := rfl
  have hk : (aliceAgreement ikA ek (dhPk ikB) (dhPk spk) (kemPk pqsk) (opk.map dhPk) e).2 =
      pqxdhKdf (pqxdhIkm (agree (dhPk spk) ikA) (agree (dhPk ikB) ek) (agree (dhPk spk) ek)
        ((opk.map dhPk).map (agree · ek)) (kemEncap (kemPk pqsk) e).2) := rfl
  rw [hct, hk]
  simp only [bobAgreement, errToOption, kemDecap_kemEncap, Option.getD_some]
  rw [agree_comm ikA spk, agree_comm ek ikB, agree_comm ek spk]
  cases opk with
  | none => rfl
  | some o =>
    show some (pqxdhKdf (pqxdhIkm _ _ _ (some (agree (dhPk ek) o)) _)) =
      some (pqxdhKdf (pqxdhIkm _ _ _ (some (agree (dhPk o) ek)) _))
    rw [agree_comm ek o]

theorem bobAgreement_honest (ikA ek ikB spk pqsk e : Bytes) :
    bobAgreement ikB spk pqsk none (dhPk ikA) (dhPk ek)
      (aliceAgreement ikA ek (dhPk ikB) (dhPk spk) (kemPk pqsk) none e).1 =
    some (aliceAgreement ikA ek (dhPk ikB) (dhPk spk) (kemPk pqsk) none e).2 :=
  bobAgreement_honest_opt ikA ek ikB spk pqsk e none

theorem bobAgreement_honest_opk (ikA ek ikB spk pqsk opk e : Bytes) :
    bobAgreement ikB spk pqsk (some opk) (dhPk ikA) (dhPk ek)
      (aliceAgreement ikA ek (dhPk ikB) (dhPk spk) (kemPk pqsk) (some (dhPk opk)) e).1 =
    some (aliceAgreement ikA ek (dhPk ikB) (dhPk spk) (kemPk pqsk) (some (dhPk opk)) e).2 :=
  bobAgreement_honest_opt ikA ek ikB spk pqsk e (some opk)

/-! ## Session Starts (`aliceStart`, `bobStart`), with and without OPK -/

abbrev aliceOutOpt (tr : ExecTrace) (ikA ikBPk spkPk pqPk : Bytes) (opkPk : Option Bytes) :
    AliceHandshakeOut :=
  ComposedRuns.aliceOutOpt tr ikA ikBPk spkPk pqPk opkPk

abbrev aliceOut (tr : ExecTrace) (ikA ikBPk spkPk pqPk : Bytes) : AliceHandshakeOut :=
  ComposedRuns.aliceOut tr ikA ikBPk spkPk pqPk

abbrev aliceOutOpk (tr : ExecTrace) (ikA ikBPk spkPk pqPk opkPk : Bytes) : AliceHandshakeOut :=
  ComposedRuns.aliceOutOpt tr ikA ikBPk spkPk pqPk (some opkPk)

theorem Runs.aliceHandshake {tr : ExecTrace} {a b : Participant} {idH regB : Nat}
    {h : BundleHandles} {ikA ikBPk vkB spkPk spkSig pqPk pqSig : Bytes} {honest : Bool}
    (hid : tr.at? idH = some (StP a { kind := .identity, sk := ikA }))
    (hreg : tr.at? regB = some (EvP (.IdentityRegistered b ikBPk vkB honest)))
    (hspk : tr.at? h.spk = some (NetE spkPk)) (hspkSig : tr.at? h.spkSig = some (NetE spkSig))
    (hpq : tr.at? h.pqpk = some (NetE pqPk)) (hpqSig : tr.at? h.pqpkSig = some (NetE pqSig))
    (hv1 : Signature.verify vkB (encodeEC spkPk) spkSig = true)
    (hv2 : Signature.verify vkB (encodeKEM pqPk) pqSig = true)
    (hopk : h.opk = none) (hlow : x25519LowOrder spkPk = false) :
    Runs (PQXDH.aliceHandshake a b idH regB h) tr (aliceOut tr ikA ikBPk spkPk pqPk)
      ((tr.append (RndE 32)).append (RndE 32)) :=
  ComposedRuns.Runs.aliceHandshake hid hreg hspk hspkSig hpq hpqSig hv1 hv2 hopk hlow

theorem Runs.aliceHandshakeOpk {tr : ExecTrace} {a b : Participant} {idH regB oi : Nat}
    {h : BundleHandles} {ikA ikBPk vkB spkPk spkSig pqPk pqSig opkPk : Bytes} {honest : Bool}
    (hid : tr.at? idH = some (StP a { kind := .identity, sk := ikA }))
    (hreg : tr.at? regB = some (EvP (.IdentityRegistered b ikBPk vkB honest)))
    (hspk : tr.at? h.spk = some (NetE spkPk)) (hspkSig : tr.at? h.spkSig = some (NetE spkSig))
    (hpq : tr.at? h.pqpk = some (NetE pqPk)) (hpqSig : tr.at? h.pqpkSig = some (NetE pqSig))
    (hv1 : Signature.verify vkB (encodeEC spkPk) spkSig = true)
    (hv2 : Signature.verify vkB (encodeKEM pqPk) pqSig = true)
    (hopkEq : h.opk = some oi) (hopk : tr.at? oi = some (NetE opkPk))
    (hlowSpk : x25519LowOrder spkPk = false)
    (hlowOpk : ((some opkPk).all (!x25519LowOrder ·)) = true) :
    Runs (PQXDH.aliceHandshake a b idH regB h) tr (aliceOutOpk tr ikA ikBPk spkPk pqPk opkPk)
      ((tr.append (RndE 32)).append (RndE 32)) :=
  ComposedRuns.Runs.aliceHandshakeOpk hid hreg hspk hspkSig hpq hpqSig hv1 hv2 hopkEq
    hopk hlowSpk hlowOpk

/-- The session state `aliceStart` stores, from the handshake output `o` and the ratchet secret
`dhsA`. -/
def aliceSt (b : Participant) (o : AliceHandshakeOut) (dhsA : Bytes) : TRState :=
  { peer := b, myIk := serializedIk o.ikA, peerIk := serializedIk o.ikB,
    rk := (createChain o.keys.rk o.spk dhsA).1, dhs := dhsA,
    cks := (createChain o.keys.rk o.spk dhsA).2, ns := 0, pn := 0,
    sid := Concat.concat (dhPk dhsA) o.keys.rk,
    initiator := true, rIdx := 1,
    recv := [{ ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }],
    spqr := Spqr.spqrInit o.keys.pqr spqrA2B }

/-- The trace `aliceStart` leaves on `tr` with optional one-time prekey `opkPk`: base key, KEM
entropy and ratchet secret (randomness at `tr.length` to `tr.length + 2`), base key and KEM
ciphertext (network), `AliceDone` at `tr.length + 5`, `InitSession`, `HandshakeSession`, and the
state at `tr.length + 8`. -/
def aliceTrOpt (tr : ExecTrace) (a b : Participant) (ikA ikBPk spkPk pqPk : Bytes)
    (opkPk : Option Bytes) : ExecTrace :=
  let o := aliceOutOpt tr ikA ikBPk spkPk pqPk opkPk
  let dhsA := rnd (tr.length + 2) 32
  ((((((((tr.append (RndE 32)).append (RndE 32)).append (RndE 32)).append
    (NetE o.ek)).append (NetE o.ct)).append
    (EvP (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys))).append
    (EvT (.InitSession a b (dhPk dhsA) o.spk))).append
    (EvC (.HandshakeSession ((aliceSt b o dhsA).sessionInfo a) (tr.length + 5)))).append
    (StT a (aliceSt b o dhsA))

abbrev aliceTr (tr : ExecTrace) (a b : Participant) (ikA ikBPk spkPk pqPk : Bytes) : ExecTrace :=
  aliceTrOpt tr a b ikA ikBPk spkPk pqPk none

abbrev aliceTrOpk (tr : ExecTrace) (a b : Participant) (ikA ikBPk spkPk pqPk opkPk : Bytes) :
    ExecTrace :=
  aliceTrOpt tr a b ikA ikBPk spkPk pqPk (some opkPk)

theorem Runs.aliceStart {tr : ExecTrace} {a b : Participant} {idH regB : Nat}
    {h : BundleHandles} {ikA ikBPk vkB spkPk spkSig pqPk pqSig : Bytes} {honest : Bool}
    (hid : tr.at? idH = some (StP a { kind := .identity, sk := ikA }))
    (hreg : tr.at? regB = some (EvP (.IdentityRegistered b ikBPk vkB honest)))
    (hspk : tr.at? h.spk = some (NetE spkPk)) (hspkSig : tr.at? h.spkSig = some (NetE spkSig))
    (hpq : tr.at? h.pqpk = some (NetE pqPk)) (hpqSig : tr.at? h.pqpkSig = some (NetE pqSig))
    (hv1 : Signature.verify vkB (encodeEC spkPk) spkSig = true)
    (hv2 : Signature.verify vkB (encodeKEM pqPk) pqSig = true)
    (hopk : h.opk = none) (hlow : x25519LowOrder spkPk = false) :
    Runs (Composed.aliceStart a b idH regB h) tr (tr.length + 8)
      (aliceTr tr a b ikA ikBPk spkPk pqPk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine Runs.bind (Runs.aliceHandshake hid hreg hspk hspkSig hpq hpqSig hv1 hv2 hopk hlow) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  dsimp only
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.traceLength _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine runs_cast_loc (Runs.storeLocalState _ _ _) ?_ ?_
  · simp only [RndE, NetE, append_len_loc, Nat.add_assoc]
  · simp only [aliceTr, aliceTrOpt, aliceSt, aliceOut, RndE, NetE, EvP, EvT, EvC, StT,
      append_len_loc, Nat.add_assoc]

theorem Runs.aliceStartOpk {tr : ExecTrace} {a b : Participant} {idH regB oi : Nat}
    {h : BundleHandles} {ikA ikBPk vkB spkPk spkSig pqPk pqSig opkPk : Bytes} {honest : Bool}
    (hid : tr.at? idH = some (StP a { kind := .identity, sk := ikA }))
    (hreg : tr.at? regB = some (EvP (.IdentityRegistered b ikBPk vkB honest)))
    (hspk : tr.at? h.spk = some (NetE spkPk)) (hspkSig : tr.at? h.spkSig = some (NetE spkSig))
    (hpq : tr.at? h.pqpk = some (NetE pqPk)) (hpqSig : tr.at? h.pqpkSig = some (NetE pqSig))
    (hv1 : Signature.verify vkB (encodeEC spkPk) spkSig = true)
    (hv2 : Signature.verify vkB (encodeKEM pqPk) pqSig = true)
    (hopkEq : h.opk = some oi) (hopk : tr.at? oi = some (NetE opkPk))
    (hlowSpk : x25519LowOrder spkPk = false)
    (hlowOpk : ((some opkPk).all (!x25519LowOrder ·)) = true) :
    Runs (Composed.aliceStart a b idH regB h) tr (tr.length + 8)
      (aliceTrOpk tr a b ikA ikBPk spkPk pqPk opkPk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine Runs.bind
    (Runs.aliceHandshakeOpk hid hreg hspk hspkSig hpq hpqSig hv1 hv2 hopkEq hopk hlowSpk hlowOpk)
    ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  dsimp only
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.traceLength _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine runs_cast_loc (Runs.storeLocalState _ _ _) ?_ ?_
  · simp only [RndE, NetE, append_len_loc, Nat.add_assoc]
  · simp only [aliceTrOpk, aliceTrOpt, aliceSt, aliceOutOpk, RndE, NetE, EvP, EvT, EvC, StT,
      append_len_loc, Nat.add_assoc]

abbrev bobOutOpt (ikB spk pqsk : Bytes) (opkSk : Option Bytes) (ikAPk ek ct : Bytes)
    (keys : HandshakeKeys) : BobHandshakeOut :=
  ComposedRuns.bobOutOpt ikB spk pqsk opkSk ikAPk ek ct keys

abbrev bobOut (ikB spk pqsk ikAPk ek ct : Bytes) (keys : HandshakeKeys) : BobHandshakeOut :=
  ComposedRuns.bobOut ikB spk pqsk ikAPk ek ct keys

abbrev bobOutOpk (ikB spk pqsk opkSk ikAPk ek ct : Bytes) (keys : HandshakeKeys) :
    BobHandshakeOut :=
  ComposedRuns.bobOutOpt ikB spk pqsk (some opkSk) ikAPk ek ct keys

theorem Runs.bobHandshakeOpt {tr : ExecTrace} {b a : Participant} {h : BobKeyHandles}
    {regA ekH ctH : Nat} {ikB spk pqsk ikAPk vkA ek ct : Bytes}
    {opkSk : Option Bytes} {honest : Bool} {keys : HandshakeKeys}
    (hik : tr.at? h.ik = some (StP b { kind := .identity, sk := ikB }))
    (hspk : tr.at? h.spk = some (StP b { kind := .signedPrekey, sk := spk }))
    (hpq : tr.at? h.pqspk = some (StP b { kind := .pqPrekey, sk := pqsk }))
    (hopk : match h.opk, opkSk with
      | none, none => True
      | some oi, some sk => tr.at? oi = some (StP b { kind := .oneTimePrekey, sk })
      | _, _ => False)
    (hreg : tr.at? regA = some (EvP (.IdentityRegistered a ikAPk vkA honest)))
    (hek : tr.at? ekH = some (NetE ek)) (hct : tr.at? ctH = some (NetE ct))
    (hcan : isCanonicalKey ek = true)
    (hagree : bobAgreement ikB spk pqsk opkSk ikAPk ek ct = some keys) :
    Runs (PQXDH.bobHandshake b a h regA ekH ctH) tr
      (bobOutOpt ikB spk pqsk opkSk ikAPk ek ct keys) tr :=
  ComposedRuns.Runs.bobHandshakeOpt hik hspk hpq
    (by rcases h with ⟨_, _, _, _ | _⟩ <;> rcases opkSk with _ | _ <;> exact hopk)
    hreg hek hct hcan hagree

theorem Runs.bobHandshake {tr : ExecTrace} {b a : Participant} {h : BobKeyHandles}
    {regA ekH ctH : Nat} {ikB spk pqsk ikAPk vkA ek ct : Bytes} {honest : Bool}
    {keys : HandshakeKeys}
    (hik : tr.at? h.ik = some (StP b { kind := .identity, sk := ikB }))
    (hspk : tr.at? h.spk = some (StP b { kind := .signedPrekey, sk := spk }))
    (hpq : tr.at? h.pqspk = some (StP b { kind := .pqPrekey, sk := pqsk }))
    (hopk : h.opk = none)
    (hreg : tr.at? regA = some (EvP (.IdentityRegistered a ikAPk vkA honest)))
    (hek : tr.at? ekH = some (NetE ek)) (hct : tr.at? ctH = some (NetE ct))
    (hcan : isCanonicalKey ek = true)
    (hagree : bobAgreement ikB spk pqsk none ikAPk ek ct = some keys) :
    Runs (PQXDH.bobHandshake b a h regA ekH ctH) tr
      (bobOut ikB spk pqsk ikAPk ek ct keys) tr :=
  ComposedRuns.Runs.bobHandshake hik hspk hpq hopk hreg hek hct hcan hagree

theorem Runs.bobHandshakeOpk {tr : ExecTrace} {b a : Participant} {h : BobKeyHandles}
    {regA ekH ctH oi : Nat} {ikB spk pqsk opkSk ikAPk vkA ek ct : Bytes} {honest : Bool}
    {keys : HandshakeKeys}
    (hik : tr.at? h.ik = some (StP b { kind := .identity, sk := ikB }))
    (hspk : tr.at? h.spk = some (StP b { kind := .signedPrekey, sk := spk }))
    (hpq : tr.at? h.pqspk = some (StP b { kind := .pqPrekey, sk := pqsk }))
    (hopkEq : h.opk = some oi)
    (hopk : tr.at? oi = some (StP b { kind := .oneTimePrekey, sk := opkSk }))
    (hreg : tr.at? regA = some (EvP (.IdentityRegistered a ikAPk vkA honest)))
    (hek : tr.at? ekH = some (NetE ek)) (hct : tr.at? ctH = some (NetE ct))
    (hcan : isCanonicalKey ek = true)
    (hagree : bobAgreement ikB spk pqsk (some opkSk) ikAPk ek ct = some keys) :
    Runs (PQXDH.bobHandshake b a h regA ekH ctH) tr
      (bobOutOpk ikB spk pqsk opkSk ikAPk ek ct keys) tr :=
  ComposedRuns.Runs.bobHandshakeOpt (opkSk := some opkSk) hik hspk hpq
    (by rw [hopkEq]; exact hopk) hreg hek hct hcan hagree

/-- Bob's in-memory session state of `bobStart` (`initialize_bob_session`), before the decrypt of
the opening message `msg`. -/
def bobSt0 (a : Participant) (ikB spk ikAPk : Bytes) (keys : HandshakeKeys) (msg : TRSignalMsg) :
    TRState :=
  { peer := a, myIk := serializedIk (dhPk ikB), peerIk := serializedIk ikAPk, rk := keys.rk,
    dhs := spk, cks := keys.ck, ns := 0, pn := 0,
    sid := Concat.concat (X25519.normalizeX25519Key msg.ratchetKey) keys.rk,
    initiator := false, rIdx := 0, recv := [], spqr := Spqr.spqrInit keys.pqr spqrB2A }

theorem Runs.bobStart {tr : ExecTrace} {b a : Participant} {kh : BobKeyHandles} {regA : Nat}
    {mh : PreKeyMsgHandles} {pqH : Nat} {spqrIdx : UInt32}
    {ikB spk pqsk ikAPk vkA ek ct t pq m seed spqr' key : Bytes} {honest : Bool}
    {keys : HandshakeKeys} {msg : TRSignalMsg} {st' : TRState} {c c' : RecvChain}
    (hik : tr.at? kh.ik = some (StP b { kind := .identity, sk := ikB }))
    (hspk : tr.at? kh.spk = some (StP b { kind := .signedPrekey, sk := spk }))
    (hpqk : tr.at? kh.pqspk = some (StP b { kind := .pqPrekey, sk := pqsk }))
    (hopk : kh.opk = none)
    (hreg : tr.at? regA = some (EvP (.IdentityRegistered a ikAPk vkA honest)))
    (hek : tr.at? mh.ek = some (NetE ek)) (hct : tr.at? mh.ct = some (NetE ct))
    (hcan : isCanonicalKey ek = true)
    (hagree : bobAgreement ikB spk pqsk none ikAPk ek ct = some keys)
    (hmsg : tr.at? mh.msg = some (NetE t))
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hlow : x25519LowOrder msg.ratchetKey = false)
    (hrs : ratchetState (bobSt0 a ikB spk ikAPk keys msg) msg.ratchetKey (rnd tr.length 32) =
      (st', c))
    (hcons : consumeMessageKey c msg.counter = some (seed, c'))
    (hrecv : Spqr.spqrRecv st'.spqr msg.pqRatchet spqrIdx = some (spqr', key))
    (hpq : ((tr.append (RndE 32)).append (NetE key)).at? pqH = some (NetE pq))
    (hmac : msg.mac = computeMac (trMsgKeys pq seed).macKey st'.peerIk st'.myIk msg.wire)
    (hdec : SymEnc.symDec (trMsgKeys pq seed).cipherKey (trMsgKeys pq seed).iv msg.ciphertext =
      some m)
    {stOut : TRState}
    (hout : { st' with recv := setRecvChain st'.recv c', spqr := spqr' } = stOut) :
    let o := bobOut ikB spk pqsk ikAPk ek ct keys
    let tr1 := (tr.append (RndE 32)).append (NetE key)
    let tr5 := (((tr1.append
        (EvP (.BobDone b a o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys))).append
        (EvT (.DHRatchet b st'.peer msg.ratchetKey (dhPk st'.dhs)))).append
        (EvT (.HonestDH (st'.sessionInfo b) st'.dhs (st'.rIdx - 2)))).append
        (EvC (.HandshakeSession (st'.sessionInfo b) tr1.length))
    let child := tr5.length + (msg.counter.toNat - c.index.toNat) + 2
    let trS := skipTr tr5 (st'.sessionInfo b) msg.ratchetKey c child msg.counter
    Runs (Composed.bobStart b a kh regA mh pqH spqrIdx) tr (trS.length + 2)
      (((trS.append (EvT (.Received b st'.peer msg.ratchetKey msg.counter m))).append
        (EvT (.MessageKey (st'.sessionInfo b) .receiver seed pq msg.counter c.rIdx
          child))).append
        (StT b stOut)) := by
  subst hout
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine Runs.bind (Runs.bobHandshake hik hspk hpqk hopk hreg hek hct hcan hagree) ?_
  refine Runs.bind (Runs.receiveSignalMsg hmsg hparse hver) ?_
  have he := Runs.ensureReceiverChain_ratchet (tr := tr)
    (st := bobSt0 a ikB spk ikAPk keys msg) (pk := msg.ratchetKey) rfl hlow
  rw [hrs] at he
  refine Runs.bind he ?_
  dsimp only
  rw [hcons]
  dsimp only
  rw [hrecv]
  dsimp only
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.receiveMessage hpq) ?_
  refine Runs.bind (Runs.verifyMacAndDecrypt hmac hdec) ?_
  dsimp only [bobOut, bobOutOpt, ComposedRuns.bobOut,
    ComposedRuns.bobOutOpt, Option.map]
  refine Runs.bind (Runs.traceLength _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  simp only [↓reduceIte]
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.traceLength _) ?_
  refine Runs.bind (Runs.logSkippedKeys _ _ _ _ _ _ _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  exact runs_cast_loc (Runs.logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _)
    (by rw [append_len_loc (skipTr _ _ _ _ _ _) _, Nat.add_assoc]) rfl

theorem Runs.bobStartOpk {tr : ExecTrace} {b a : Participant} {kh : BobKeyHandles} {regA oi : Nat}
    {mh : PreKeyMsgHandles} {pqH : Nat} {spqrIdx : UInt32}
    {ikB spk pqsk opkSk ikAPk vkA ek ct t pq m seed spqr' key : Bytes} {honest : Bool}
    {keys : HandshakeKeys} {msg : TRSignalMsg} {st' : TRState} {c c' : RecvChain}
    (hik : tr.at? kh.ik = some (StP b { kind := .identity, sk := ikB }))
    (hspk : tr.at? kh.spk = some (StP b { kind := .signedPrekey, sk := spk }))
    (hpqk : tr.at? kh.pqspk = some (StP b { kind := .pqPrekey, sk := pqsk }))
    (hopkEq : kh.opk = some oi)
    (hopk : tr.at? oi = some (StP b { kind := .oneTimePrekey, sk := opkSk }))
    (hreg : tr.at? regA = some (EvP (.IdentityRegistered a ikAPk vkA honest)))
    (hek : tr.at? mh.ek = some (NetE ek)) (hct : tr.at? mh.ct = some (NetE ct))
    (hcan : isCanonicalKey ek = true)
    (hagree : bobAgreement ikB spk pqsk (some opkSk) ikAPk ek ct = some keys)
    (hmsg : tr.at? mh.msg = some (NetE t))
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hlow : x25519LowOrder msg.ratchetKey = false)
    (hrs : ratchetState (bobSt0 a ikB spk ikAPk keys msg) msg.ratchetKey (rnd tr.length 32) =
      (st', c))
    (hcons : consumeMessageKey c msg.counter = some (seed, c'))
    (hrecv : Spqr.spqrRecv st'.spqr msg.pqRatchet spqrIdx = some (spqr', key))
    (hpq : ((tr.append (RndE 32)).append (NetE key)).at? pqH = some (NetE pq))
    (hmac : msg.mac = computeMac (trMsgKeys pq seed).macKey st'.peerIk st'.myIk msg.wire)
    (hdec : SymEnc.symDec (trMsgKeys pq seed).cipherKey (trMsgKeys pq seed).iv msg.ciphertext =
      some m)
    (hopkUnused : (!PQXDH.opkUsedB ((tr.append (RndE 32)).append (NetE key)) b (dhPk opkSk)) =
      true)
    {stOut : TRState}
    (hout : { st' with recv := setRecvChain st'.recv c', spqr := spqr' } = stOut) :
    let o := bobOutOpk ikB spk pqsk opkSk ikAPk ek ct keys
    let tr1 := ((tr.append (RndE 32)).append (NetE key)).append
      (EvP (.OPKUsed b (dhPk opkSk)))
    let tr5 := (((tr1.append
        (EvP (.BobDone b a o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys))).append
        (EvT (.DHRatchet b st'.peer msg.ratchetKey (dhPk st'.dhs)))).append
        (EvT (.HonestDH (st'.sessionInfo b) st'.dhs (st'.rIdx - 2)))).append
        (EvC (.HandshakeSession (st'.sessionInfo b) tr1.length))
    let child := tr5.length + (msg.counter.toNat - c.index.toNat) + 2
    let trS := skipTr tr5 (st'.sessionInfo b) msg.ratchetKey c child msg.counter
    Runs (Composed.bobStart b a kh regA mh pqH spqrIdx) tr (trS.length + 2)
      (((trS.append (EvT (.Received b st'.peer msg.ratchetKey msg.counter m))).append
        (EvT (.MessageKey (st'.sessionInfo b) .receiver seed pq msg.counter c.rIdx
          child))).append
        (StT b stOut)) := by
  subst hout
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine Runs.bind
    (Runs.bobHandshakeOpk hik hspk hpqk hopkEq hopk hreg hek hct hcan hagree) ?_
  refine Runs.bind (Runs.receiveSignalMsg hmsg hparse hver) ?_
  have he := Runs.ensureReceiverChain_ratchet (tr := tr)
    (st := bobSt0 a ikB spk ikAPk keys msg) (pk := msg.ratchetKey) rfl hlow
  rw [hrs] at he
  refine Runs.bind he ?_
  dsimp only
  rw [hcons]
  dsimp only
  rw [hrecv]
  dsimp only
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.receiveMessage hpq) ?_
  refine Runs.bind (Runs.verifyMacAndDecrypt hmac hdec) ?_
  dsimp only [bobOutOpk, bobOutOpt, ComposedRuns.bobOutOpt, Option.map]
  refine Runs.bind (Runs.requireTracePredicate hopkUnused) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.traceLength _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  simp only [↓reduceIte]
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.traceLength _) ?_
  refine Runs.bind (Runs.logSkippedKeys _ _ _ _ _ _ _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  exact runs_cast_loc (Runs.logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _)
    (by rw [append_len_loc (skipTr _ _ _ _ _ _) _, Nat.add_assoc]) rfl

/-! ## PKI and Prekey Upload `Runs` Combinators -/

def registerIdentityTr (tr : ExecTrace) (p : Participant) : ExecTrace :=
  let ik := rnd tr.length 32
  ((((tr.append (RndE 32)).append
    (EvP (.IdentityRegistered p (dhPk ik) (Signature.vk ik) true))).append
    (NetE (dhPk ik))).append (NetE (Signature.vk ik))).append
    (StP p { kind := .identity, sk := ik })

theorem Runs.registerIdentity {tr : ExecTrace} {p : Participant}
    (hunreg : (!PQXDH.isRegisteredB tr p) = true) :
    Runs (PQXDH.registerIdentity p) tr (tr.length + 4) (registerIdentityTr tr p) := by
  unfold PQXDH.registerIdentity
  refine Runs.bind (Runs.requireTracePredicate hunreg) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine runs_cast_loc (Runs.storePQXDHState _ _ _) ?_ rfl
  simp only [NetE, append_len_loc, Nat.add_assoc]

def genSignedPrekeyTr (tr : ExecTrace) (b : Participant) (ik : Bytes) : ExecTrace :=
  let spk := rnd tr.length 32
  let nonce := rnd (tr.length + 1) 64
  (((((tr.append (RndE 32)).append (RndE 64)).append
    (EvP (.SignedPrekeyPublished b (dhPk spk)))).append
    (StP b { kind := .signedPrekey, sk := spk })).append
    (NetE (dhPk spk))).append
    (NetE (Signature.sign ik nonce (encodeEC (dhPk spk))))

theorem Runs.genSignedPrekey {tr : ExecTrace} {b : Participant} {idH : Nat} {ik : Bytes}
    (hik : tr.at? idH = some (StP b { kind := .identity, sk := ik })) :
    Runs (PQXDH.genSignedPrekey b idH) tr (tr.length + 3) (genSignedPrekeyTr tr b ik) := by
  unfold PQXDH.genSignedPrekey
  refine Runs.bind (Runs.getKey hik) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.storePQXDHState _ _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  simpa only [genSignedPrekeyTr, RndE, EvP, NetE, StP, append_len_loc, Nat.add_assoc] using
    Runs.pure _ _

def genPQPrekeyTr (tr : ExecTrace) (b : Participant) (ik : Bytes) : ExecTrace :=
  let pqsk := rnd tr.length 64
  let nonce := rnd (tr.length + 1) 64
  (((((tr.append (RndE 64)).append (RndE 64)).append
    (EvP (.PQPrekeyPublished b (kemPk pqsk)))).append
    (StP b { kind := .pqPrekey, sk := pqsk })).append
    (NetE (kemPk pqsk))).append
    (NetE (Signature.sign ik nonce (encodeKEM (kemPk pqsk))))

theorem Runs.genPQPrekey {tr : ExecTrace} {b : Participant} {idH : Nat} {ik : Bytes}
    (hik : tr.at? idH = some (StP b { kind := .identity, sk := ik })) :
    Runs (PQXDH.genPQPrekey b idH) tr (tr.length + 3) (genPQPrekeyTr tr b ik) := by
  unfold PQXDH.genPQPrekey
  refine Runs.bind (Runs.getKey hik) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.storePQXDHState _ _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  simpa only [genPQPrekeyTr, RndE, EvP, NetE, StP, append_len_loc, Nat.add_assoc] using
    Runs.pure _ _

def genOneTimePrekeyTr (tr : ExecTrace) (b : Participant) : ExecTrace :=
  let opk := rnd tr.length 32
  (((tr.append (RndE 32)).append
    (EvP (.OneTimePrekeyPublished b (dhPk opk)))).append
    (StP b { kind := .oneTimePrekey, sk := opk })).append
    (NetE (dhPk opk))

theorem Runs.genOneTimePrekey (tr : ExecTrace) (b : Participant) :
    Runs (PQXDH.genOneTimePrekey b) tr (tr.length + 2) (genOneTimePrekeyTr tr b) := by
  unfold PQXDH.genOneTimePrekey
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.storePQXDHState _ _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  simpa only [genOneTimePrekeyTr, RndE, EvP, NetE, StP, append_len_loc, Nat.add_assoc] using
    Runs.pure _ _

/-! ## Reachability of single steps -/

theorem reach_of_runs {α : Type} {x : Traceful α} {tr tr' : ExecTrace} {a : α}
    (h : Runs x tr a tr') (hr : ((x.run tr).2.val).Reachable reachability) :
    tr'.Reachable reachability := h.2 ▸ hr

theorem sendMessage_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {m : Bytes} (hm : m.AttackerKnows tr) :
    (tr.append (NetE m)).Reachable reachability := by
  have hr := (Traceful.PreservesReachability_base Network.reachability reachability m tr h hm).1
  dsimp only [Network.reachability] at hr
  rwa [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_mk] at hr

theorem registerIdentity_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {p : Participant} : ((PQXDH.registerIdentity p).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base PQXDH.registerIdentity.reachability reachability p tr h
    trivial).1

theorem registerCorruptIdentity_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {p : Participant} {skIdx : Nat} :
    ((PQXDH.registerCorruptIdentity p skIdx).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base PQXDH.registerCorruptIdentity.reachability reachability
    (p, skIdx) tr h trivial).1

theorem genSignedPrekey_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {b : Participant} {i : Nat} :
    ((PQXDH.genSignedPrekey b i).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base PQXDH.genSignedPrekey.reachability reachability (b, i)
    tr h trivial).1

theorem genPQPrekey_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {b : Participant} {i : Nat} :
    ((PQXDH.genPQPrekey b i).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base PQXDH.genPQPrekey.reachability reachability (b, i) tr
    h trivial).1

theorem genOneTimePrekey_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {b : Participant} :
    ((PQXDH.genOneTimePrekey b).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base PQXDH.genOneTimePrekey.reachability reachability b tr
    h trivial).1

theorem aliceStart_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {a b : Participant} {i r : Nat} {bh : BundleHandles} :
    ((Composed.aliceStart a b i r bh).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base aliceStart.reachability reachability (a, b, i, r, bh) tr h
    trivial).1

theorem bobStart_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {b a : Participant} {kh : BobKeyHandles} {r : Nat} {mh : PreKeyMsgHandles} {pqIdx : Nat}
    {i : UInt32} :
    ((Composed.bobStart b a kh r mh pqIdx i).run tr).2.val.Reachable
      reachability :=
  (Traceful.PreservesReachability_base bobStart.reachability reachability
    (b, a, kh, r, mh, pqIdx, i) tr h trivial).1

theorem messageEncrypt_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {me : Participant} {stateIdx coinsLen pqIdx : Nat}
    (hcur : TripleRatchet.isCurrentSnapshot tr stateIdx = true := by decide) :
    ((TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx).run tr).2.val.Reachable
      reachability :=
  (Traceful.PreservesReachability_base TripleRatchet.messageEncrypt.reachability reachability
    (me, stateIdx, coinsLen, pqIdx) tr h hcur).1

theorem messageEncryptAbort_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {me : Participant} {stateIdx : Nat}
    (hcur : TripleRatchet.isCurrentSnapshot tr stateIdx = true := by decide) :
    ((TripleRatchet.messageEncryptAbort me stateIdx).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base TripleRatchet.messageEncryptAbort.reachability reachability
    (me, stateIdx) tr h hcur).1

theorem messageDecrypt_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {me : Participant} {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32}
    (hcur : TripleRatchet.isCurrentSnapshot tr stateIdx = true := by decide) :
    ((TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val.Reachable
      reachability :=
  (Traceful.PreservesReachability_base TripleRatchet.messageDecrypt.reachability reachability
    (me, stateIdx, msgIdx, pqIdx, spqrMsgIdx) tr h hcur).1

theorem messageDecryptSkipped_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {me : Participant} {stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat} {spqrMsgIdx : UInt32}
    (hcur : TripleRatchet.isCurrentSnapshot tr stateIdx = true := by decide) :
    ((TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx
      spqrMsgIdx).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base TripleRatchet.messageDecryptSkipped.reachability reachability
    (me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx) tr h hcur).1

theorem exposeKey_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {me : Participant} {stateIdx : Nat} {k : KeyComponent} :
    ((TripleRatchet.exposeKey me stateIdx k).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base TripleRatchet.exposeKey.reachability reachability
    (me, stateIdx, k) tr h trivial).1

theorem exposeSpqr_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {me : Participant} {stateIdx : Nat} :
    ((TripleRatchet.exposeSpqr me stateIdx).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base TripleRatchet.exposeSpqr.reachability reachability
    (me, stateIdx) tr h trivial).1

theorem exposeSkipped_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {skippedKeyEventIdx : Nat} :
    ((TripleRatchet.exposeSkipped skippedKeyEventIdx).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base TripleRatchet.exposeSkipped.reachability reachability
    skippedKeyEventIdx tr h trivial).1

theorem compromiseIK_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {p : Participant} {stateIdx : Nat} :
    ((PQXDH.compromiseIK p stateIdx).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base PQXDH.compromiseIK.reachability reachability
    (p, stateIdx) tr h trivial).1

theorem compromiseSPK_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {b : Participant} {stateIdx : Nat} :
    ((PQXDH.compromiseSPK b stateIdx).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base PQXDH.compromiseSPK.reachability reachability
    (b, stateIdx) tr h trivial).1

theorem compromisePQSPK_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {b : Participant} {stateIdx : Nat} :
    ((PQXDH.compromisePQSPK b stateIdx).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base PQXDH.compromisePQSPK.reachability reachability
    (b, stateIdx) tr h trivial).1

theorem compromiseOPK_reachable {tr : ExecTrace} (h : tr.Reachable reachability)
    {b : Participant} {stateIdx : Nat} :
    ((PQXDH.compromiseOPK b stateIdx).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base PQXDH.compromiseOPK.reachability reachability
    (b, stateIdx) tr h trivial).1

theorem breakDH_reachable {tr : ExecTrace} (h : tr.Reachable reachability) :
    (PQXDH.breakDH.run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base PQXDH.breakDH.reachability reachability () tr h
    trivial).1

theorem breakKEM_reachable {tr : ExecTrace} (h : tr.Reachable reachability) :
    (PQXDH.breakKEM.run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base PQXDH.breakKEM.reachability reachability () tr h
    trivial).1

theorem invertDH_reachable {tr : ExecTrace} (h : tr.Reachable reachability) {pkIdx : Nat} :
    ((PQXDH.invertDH pkIdx).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base PQXDH.invertDH.reachability reachability pkIdx tr h
    trivial).1

theorem invertKEM_reachable {tr : ExecTrace} (h : tr.Reachable reachability) {pkIdx : Nat} :
    ((PQXDH.invertKEM pkIdx).run tr).2.val.Reachable reachability :=
  (Traceful.PreservesReachability_base PQXDH.invertKEM.reachability reachability pkIdx tr h
    trivial).1

/-- A message-key seed `(kdfCk ck).2` is derivable once `ck` is on the network. -/
theorem knows_seed {tr : ExecTrace} {ck : Bytes} {i : Nat} (h : tr.MessageSentAt ck i) :
    (kdfCk ck).2.AttackerKnows tr :=
  KdfExtract.attacker_knows_kdfExtract _ _ _ (Trace.MessageSentAt_implies_AttackerKnows _ _ _ h)
    (Literal.attacker_knows_literalToBytes _ _)

end

end Symbolic.Proofs.Tests.Shared.Composed.Runs
