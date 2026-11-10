/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.ModelProofDefs
public import Symbolic.Proofs.Swarm.COMPOSED.CompKeyInversion
import DY.Actions.ProtocolEvent
import DY.Trace.Basic
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.Random
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Composed Secrecy and Authentication Invariant Definitions

Defines trace-entry abbreviations, positional secret classes, `CompExposure`, the attacker-knowledge
over-approximation `Pub`, monotonicity lemmas, stored-state and handshake predicates, the composed
invariant `SpqrInv`, and its empty-trace base case `spqrInv_nil`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompInv

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.PQKem DY.Signature DY.X25519
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding x25519LowOrder
open DY.Libsignal.Composed
open Symbolic.Swarm.COMPOSED.CompKeyInversion

/-! ## Trace Entry Abbreviations and Positions -/

abbrev NetEntry : Type := Network.ExecEntryT
abbrev RndEntry : Type := Random.ExecEntryT
abbrev TREvEntry : Type := ProtocolEvent.ExecEntryT TREvent
abbrev EvEntry : Type := ProtocolEvent.ExecEntryT PQXDHEvent
abbrev CEvEntry : Type := ProtocolEvent.ExecEntryT ComposedEvent
abbrev TRStEntry : Type :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
abbrev StEntry : Type :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState PQXDHState)

abbrev NetE (msg : Bytes) : NetEntry := ⟨msg⟩
abbrev RndE (n : Nat) : RndEntry := ⟨n⟩
abbrev TREvE (ev : TREvent) : TREvEntry := ⟨ev⟩
abbrev EvE (ev : PQXDHEvent) : EvEntry := ⟨ev⟩
abbrev CEvE (ev : ComposedEvent) : CEvEntry := ⟨ev⟩
abbrev TRStE (me : Participant) (st : TRState) : TRStEntry :=
  ⟨({ participant := me, state := st } : PersistentLocalState.LocalState TRState)⟩
abbrev StE (me : Participant) (st : PQXDHState) : StEntry :=
  ⟨({ participant := me, state := st } : PersistentLocalState.LocalState PQXDHState)⟩

/-- A `genRand n` entry is at trace index `t`. -/
def RandAt (tr : ExecTrace) (t n : Nat) : Prop :=
  (tr.at? t : Option RndEntry) = some (RndE n)

/-- `st : PQXDHState` is stored by `me` at trace index `idx`. -/
def StoredAt (tr : ExecTrace) (me : Participant) (st : PQXDHState) (idx : Nat) : Prop :=
  (tr.at? idx : Option StEntry) = some (StE me st)

/-- `st : TRState` is stored by `me` at trace index `idx`. -/
def TRStoredAt (tr : ExecTrace) (me : Participant) (st : TRState) (idx : Nat) : Prop :=
  (tr.at? idx : Option TRStEntry) = some (TRStE me st)

/-- `msg : Bytes` is sent on the network at trace index `idx`. -/
def NetAt (tr : ExecTrace) (msg : Bytes) (idx : Nat) : Prop :=
  (tr.at? idx : Option NetEntry) = some (NetE msg)

theorem rnd_inj {t t' n n' : Nat} (h : rnd t n = rnd t' n') : t = t' ∧ n = n' := by
  have hv := congrArg (fun b : Bytes => b.view? Random.Random) h
  simp only [rnd, BytesView.view_pack, Option.some.injEq, Random.Random.mk.injEq] at hv
  exact hv

theorem RandAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {t n : Nat} (h : RandAt tr t n) :
    RandAt tr' t n := by
  have hat := Trace.at?_le (EntryT := RndEntry) tr tr' t hle
  unfold RandAt at h ⊢
  rw [h] at hat
  exact hat

theorem StoredAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {me : Participant} {st : PQXDHState}
    {idx : Nat} (h : StoredAt tr me st idx) : StoredAt tr' me st idx := by
  have hat := Trace.at?_le (EntryT := StEntry) tr tr' idx hle
  unfold StoredAt at h ⊢
  rw [h] at hat
  exact hat

theorem TRStoredAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {me : Participant} {st : TRState}
    {idx : Nat} (h : TRStoredAt tr me st idx) : TRStoredAt tr' me st idx := by
  have hat := Trace.at?_le (EntryT := TRStEntry) tr tr' idx hle
  unfold TRStoredAt at h ⊢
  rw [h] at hat
  exact hat

theorem NetAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {msg : Bytes} {idx : Nat}
    (h : NetAt tr msg idx) : NetAt tr' msg idx := by
  have hat := Trace.at?_le (EntryT := NetEntry) tr tr' idx hle
  unfold NetAt at h ⊢
  rw [h] at hat
  exact hat

theorem evAt_mono {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr tr' : ExecTrace} (hle : tr ≤ tr') {ev : Ev} {i : Nat}
    (h : tr.EventLoggedAt ev i) : tr'.EventLoggedAt ev i := by
  have hat := Trace.at?_le (EntryT := ProtocolEvent.ExecEntryT Ev) tr tr' i hle
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  rw [h] at hat
  exact hat

theorem ev_mono {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr tr' : ExecTrace} (hle : tr ≤ tr') {ev : Ev}
    (h : tr.EventLogged ev) : tr'.EventLogged ev :=
  Trace.EventLogged_le ev tr tr' hle h

theorem loggedBefore_mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {ev : PQXDHEvent} {i : Nat}
    (h : LoggedBefore ev i tr) : LoggedBefore ev i tr' := by
  obtain ⟨j, hj, hlt⟩ := h
  exact ⟨j, evAt_mono hle hj, hlt⟩

theorem handshakeKeysAt_mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {j : Nat} {keys : HandshakeKeys}
    (h : HandshakeKeysAt tr j keys) : HandshakeKeysAt tr' j keys := by
  rcases h with ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, hA⟩ | ⟨ek, ct, hB⟩⟩
  · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inl ⟨ek, ct, evAt_mono hle hA⟩⟩
  · exact ⟨a, b, ikA, ikB, spk, pqpk, opk, .inr ⟨ek, ct, evAt_mono hle hB⟩⟩

theorem sessionStateExposed_mono {tr tr' : ExecTrace} (hle : tr ≤ tr')
    {keys : HandshakeKeys} {k : Bytes}
    (h : SessionStateExposed tr keys k) : SessionStateExposed tr' keys k := by
  obtain ⟨s, j, hhs, hkeys, hcases⟩ := h
  refine ⟨s, j, ev_mono hle hhs, handshakeKeysAt_mono hle hkeys, ?_⟩
  rcases hcases with ⟨rfl, sp, r, hev⟩ | ⟨rfl, n, r, hev⟩ | ⟨rfl, n, r, hev⟩ | ⟨rfl, r, hev⟩
  · exact .inl ⟨rfl, sp, r, ev_mono hle hev⟩
  · exact .inr (.inl ⟨rfl, n, r, ev_mono hle hev⟩)
  · exact .inr (.inr (.inl ⟨rfl, n, r, ev_mono hle hev⟩))
  · exact .inr (.inr (.inr ⟨rfl, r, ev_mono hle hev⟩))

/-! ## Positional Secret Classes -/

/-- `r` is `p`'s honest identity secret: `genRand 32 @t`, then `IdentityRegistered p ... true @t+1`
(`registerIdentity`). -/
def IKAt (tr : ExecTrace) (p : Participant) (r : Bytes) : Prop :=
  ∃ t, r = rnd t 32 ∧ RandAt tr t 32 ∧
    tr.EventLoggedAt
      (PQXDHEvent.IdentityRegistered p (DiffieHellman.dhPk r) (Signature.vk r) true) (t + 1)

/-- `r` is a signed prekey secret of `b`: `genRand 32 @t`, nonce `genRand 64 @t+1`,
`SignedPrekeyPublished b (dhPk r) @t+2` (`genSignedPrekey`). -/
def SPKAt (tr : ExecTrace) (b : Participant) (r : Bytes) : Prop :=
  ∃ t, r = rnd t 32 ∧ RandAt tr t 32 ∧ RandAt tr (t + 1) 64 ∧
    tr.EventLoggedAt (PQXDHEvent.SignedPrekeyPublished b (DiffieHellman.dhPk r)) (t + 2)

/-- `r` is a Kyber prekey secret of `b`: `genRand 64 @t`, nonce `genRand 64 @t+1`,
`PQPrekeyPublished b (kemPk r) @t+2` (`genPQPrekey`). -/
def PQAt (tr : ExecTrace) (b : Participant) (r : Bytes) : Prop :=
  ∃ t, r = rnd t 64 ∧ RandAt tr t 64 ∧ RandAt tr (t + 1) 64 ∧
    tr.EventLoggedAt (PQXDHEvent.PQPrekeyPublished b (PQKem.kemPk r)) (t + 2)

/-- `r` is a one-time prekey secret of `b`: `genRand 32 @t`,
`OneTimePrekeyPublished b (dhPk r) @t+1` (`genOneTimePrekey`). -/
def OPKAt (tr : ExecTrace) (b : Participant) (r : Bytes) : Prop :=
  ∃ t, r = rnd t 32 ∧ RandAt tr t 32 ∧
    tr.EventLoggedAt (PQXDHEvent.OneTimePrekeyPublished b (DiffieHellman.dhPk r)) (t + 1)

/-- `t` starts an `aliceStart` execution: base key `32 @t`, KEM coins `32 @t+1`, ratchet secret
`32 @t+2`, `NetE ek @t+3`, `NetE ct @t+4`, `AliceDone @t+5`. -/
def AliceSlot (tr : ExecTrace) (t : Nat) : Prop :=
  RandAt tr t 32 ∧ RandAt tr (t + 1) 32 ∧ RandAt tr (t + 2) 32 ∧
    ∃ a b ikA ikB spk pqpk opk ek ct keys,
      NetAt tr ek (t + 3) ∧ NetAt tr ct (t + 4) ∧
      tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) (t + 5)

/-- `r` is an `aliceStart` base-key secret (`ek`). -/
def EKAt (tr : ExecTrace) (r : Bytes) : Prop := ∃ t, r = rnd t 32 ∧ AliceSlot tr t
/-- `r` is an `aliceStart` sending-ratchet secret (`dhsA`). -/
def RatchetAt (tr : ExecTrace) (r : Bytes) : Prop := ∃ t, r = rnd (t + 2) 32 ∧ AliceSlot tr t

/-- `r` is a `TripleRatchet` ratchet DH secret (`dhs'` in `bobStart` / `messageDecrypt`):
`genRand 32 @t` followed by `sendMessage key` (`NetAt tr msg (t + 1)`). -/
def TRRatchetAt (tr : ExecTrace) (r : Bytes) : Prop :=
  ∃ t msg, r = rnd t 32 ∧ RandAt tr t 32 ∧ NetAt tr msg (t + 1)

/-- `r` is a `messageEncrypt` plaintext (`rnd t 32` followed by `RandAt tr (t+1) n`, `NetE` at `t+2`,
and `TREvent` at `t+3`) or `messageEncrypt` SPQR coins (`rnd (t+1) n` after `RandAt tr t 32` and
before `NetE` at `t+2` and `TREvent` at `t+3`). -/
def MsgEncRandAt (tr : ExecTrace) (r : Bytes) : Prop :=
  (∃ t n msg, r = rnd t 32 ∧ RandAt tr t 32 ∧ RandAt tr (t + 1) n ∧ NetAt tr msg (t + 2) ∧
    ∃ ev : TREvent, tr.EventLoggedAt ev (t + 3)) ∨
  (∃ t n msg, r = rnd (t + 1) n ∧ RandAt tr t 32 ∧ RandAt tr (t + 1) n ∧ NetAt tr msg (t + 2) ∧
    ∃ ev : TREvent, tr.EventLoggedAt ev (t + 3))

/-- DH secrets: their public key `dhPk r` is (or may be) sent, and `invertDH` recovers `r` after
`BrokenDH`. -/
def DhClass (tr : ExecTrace) (r : Bytes) : Prop :=
  (∃ p, IKAt tr p r) ∨ (∃ b, SPKAt tr b r) ∨ (∃ b, OPKAt tr b r) ∨
  EKAt tr r ∨ RatchetAt tr r ∨ TRRatchetAt tr r

/-- KEM secrets: `kemPk r` is sent, and `invertKEM` recovers `r` after `BrokenKEM`. -/
def PQClass (tr : ExecTrace) (r : Bytes) : Prop := ∃ b, PQAt tr b r

/-- The random terms the attacker may know: compromised stored secrets, DH secrets after
`BrokenDH`, KEM secrets after `BrokenKEM`, exposed TR ratchet secrets, and `messageEncrypt`
plaintexts/coins. -/
def RandExposed (tr : ExecTrace) (r : Bytes) : Prop :=
  (∃ p, IKAt tr p r ∧ tr.EventLogged (PQXDHEvent.CompromisedIK p (DiffieHellman.dhPk r))) ∨
  (∃ b, SPKAt tr b r ∧ tr.EventLogged (PQXDHEvent.CompromisedSPK b (DiffieHellman.dhPk r))) ∨
  (∃ b, PQAt tr b r ∧ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b (PQKem.kemPk r))) ∨
  (∃ b, OPKAt tr b r ∧ tr.EventLogged (PQXDHEvent.CompromisedOPK b (DiffieHellman.dhPk r))) ∨
  (DhClass tr r ∧ tr.EventLogged PQXDHEvent.BrokenDH) ∨
  (PQClass tr r ∧ tr.EventLogged PQXDHEvent.BrokenKEM) ∨
  ((RatchetAt tr r ∨ TRRatchetAt tr r) ∧ ∃ s rIdx, tr.EventLogged (TREvent.ExposedDHs s r rIdx)) ∨
  MsgEncRandAt tr r

/-- `x` is the HMAC input of a `messageEncrypt` MAC on a session rooted at an honest handshake
(`HandshakeKeysAt tr j keys` at `j < tr.length`). -/
def HonestMac (tr : ExecTrace) (x : Bytes) : Prop :=
  ∃ j keys rkChain pk sk counter pqSalt ikA ikB wire,
    j < tr.length ∧ HandshakeKeysAt tr j keys ∧
    (rkChain = keys.rk ∨ ∃ r₀ p₀ s₀, rkChain = (createChain r₀ p₀ s₀).1) ∧
    let seed := (kdfCk (chainKeyAt (createChain rkChain pk sk).2 counter)).2
    let mk := DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed
    x = hmac mk.macKey
      (Concat.concat ikA (Concat.concat ikB wire))

/-- `(sk, msg)` is an honest prekey signature: `sk` is `b`'s identity secret and `msg` is the
encoding of one of `b`'s signed prekeys (`genSignedPrekey`) or Kyber prekeys (`genPQPrekey`). -/
def HonestSig (tr : ExecTrace) (sk msg : Bytes) : Prop :=
  ∃ b, IKAt tr b sk ∧
    ((∃ s, SPKAt tr b s ∧ msg = encodeEC (DiffieHellman.dhPk s)) ∨
     (∃ q, PQAt tr b q ∧ msg = encodeKEM (PQKem.kemPk q)))

/-- Session-state KDF terms exposed via `exposeSpqr`, `exposeKey` (`.rk`, `.cks`, `.ckr`), or
`exposeSkipped` on a stored `TRState` / `SkippedKeyStored` rooted at `HandshakeKeysAt tr j keys`. -/
inductive CompExposure (tr : ExecTrace) : Bytes → Prop where
  | pqr {keys : HandshakeKeys}
      (hexp : SessionStateExposed tr keys keys.pqr) :
      CompExposure tr keys.pqr
  | ck0 {keys : HandshakeKeys}
      (hexp : SessionStateExposed tr keys keys.ck) :
      CompExposure tr keys.ck
  | ckStep {keys : HandshakeKeys} {j n : Nat}
      (hj : j < tr.length) (hkeys : HandshakeKeysAt tr j keys) :
      CompExposure tr (chainKeyAt keys.ck (n + 1))
  | rkRatchet (rk pk sk : Bytes) :
      CompExposure tr (createChain rk pk sk).1
  | chainRatchet {keys : HandshakeKeys} {j n : Nat} {rkChain pk sk : Bytes}
      (hj : j < tr.length) (hkeys : HandshakeKeysAt tr j keys)
      (hrk : rkChain = keys.rk ∨ ∃ r₀ p₀ s₀, rkChain = (createChain r₀ p₀ s₀).1) :
      CompExposure tr (chainKeyAt (createChain rkChain pk sk).2 n)
  | seedCk {keys : HandshakeKeys} {j n : Nat}
      (hj : j < tr.length) (hkeys : HandshakeKeysAt tr j keys) :
      CompExposure tr (kdfCk (chainKeyAt keys.ck n)).2
  | seedRatchet {keys : HandshakeKeys} {j n : Nat} {rkChain pk sk : Bytes}
      (hj : j < tr.length) (hkeys : HandshakeKeysAt tr j keys)
      (hrk : rkChain = keys.rk ∨ ∃ r₀ p₀ s₀, rkChain = (createChain r₀ p₀ s₀).1) :
      CompExposure tr (kdfCk (chainKeyAt (createChain rkChain pk sk).2 n)).2

/-! ## Over-Approximation of Composed Attacker Knowledge -/

inductive Pub (tr : ExecTrace) : Bytes → Prop where
  | rand {t n : Nat} (h : RandExposed tr (rnd t n)) : Pub tr (rnd t n)
  | exp {b : Bytes} (h : CompExposure tr b) : Pub tr b
  | literal (bs : ByteArray) : Pub tr (Literal.literalToBytes bs)
  | cat {l r : Bytes} (hl : Pub tr l) (hr : Pub tr r) : Pub tr (Concat.concat l r)
  | kdf {s m : Bytes} (hs : Pub tr s) (hm : Pub tr m) : Pub tr (KdfExtract.kdfExtract s m)
  | trunc {m : Bytes} (hm : Pub tr m) : Pub tr (Trunc.trunc8 m)
  | truncHonest {m : Bytes} (hm : HonestMac tr m) : Pub tr (Trunc.trunc8 m)
  | trWire {v : UInt8} {rk : Bytes} {c pc : UInt32} {ct pq : Bytes} {ev : TrWire.EncodingVariation}
      (hrk : Pub tr rk) (hct : Pub tr ct) (hpq : Pub tr pq) :
      Pub tr (TrWire.trWireMsg v rk c pc ct pq ev)
  | enc {k iv m : Bytes} (hm : Pub tr m) : Pub tr (SymEnc.symEnc k iv m)
  | var {key : Bytes} (v : Fin 4) {t : Fin 8} (hkey : Pub tr key) :
      Pub tr ((({ key := key, variation := v, torsion := t } : X25519.Variant.SubF Bytes)).pack)
  | dhPub {sk : Bytes} (h : DhClass tr sk) : Pub tr (DiffieHellman.dhPk sk)
  | dhPubK {sk : Bytes} (h : Pub tr sk) : Pub tr (DiffieHellman.dhPk sk)
  | dhSk (sk pk : Bytes) (h : Pub tr sk) :
      Pub tr ((({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes)).pack)
  | dhPeer (sk s : Bytes) (h : Pub tr s) :
      Pub tr ((({ sk := sk, pk := DiffieHellman.dhPk s } : DiffieHellman.Dh.SubF Bytes)).pack)
  | kemPub {sk : Bytes} (h : PQClass tr sk) : Pub tr (PQKem.kemPk sk)
  | kemPubK {sk : Bytes} (h : Pub tr sk) : Pub tr (PQKem.kemPk sk)
  | encap (pk e : Bytes) : Pub tr (PQKem.kemEncap pk e).1
  | ss {pk e : Bytes} (hpk : Pub tr pk) (he : Pub tr e) : Pub tr (PQKem.kemEncap pk e).2
  | ssKey {sk : Bytes} (e : Bytes) (h : Pub tr sk) : Pub tr (PQKem.kemEncap (PQKem.kemPk sk) e).2
  | rejKey {sk ct : Bytes} (hsk : Pub tr sk) (hct : Pub tr ct) :
      Pub tr ((({ sk := sk, cipher := ct } : PQKem.RejKey.SubF Bytes)).pack)
  | vkPub {p : Participant} {sk : Bytes} (h : IKAt tr p sk) : Pub tr (Signature.vk sk)
  | vkPubK {sk : Bytes} (h : Pub tr sk) : Pub tr (Signature.vk sk)
  | sig {sk : Bytes} (nonce msg : Bytes) (h : Pub tr sk) : Pub tr (Signature.sign sk nonce msg)
  | sigHonest {sk : Bytes} (nonce msg : Bytes) (h : HonestSig tr sk msg) :
      Pub tr (Signature.sign sk nonce msg)
  | spqrInit {authKey params : Bytes} (hk : Pub tr authKey) (hp : Pub tr params) :
      Pub tr (Spqr.spqrInit authKey params)
  | spqrChainKey (authKey params idx : Bytes) :
      Pub tr (Spqr.spqrChainKey authKey params idx)
  | spqrSendState {st coins : Bytes} (hst : Pub tr st) (hc : Pub tr coins) :
      Pub tr ((({ st := st, coins := coins } : Spqr.SendState.SubF Bytes)).pack)
  | spqrSendKey (st coins : Bytes) :
      Pub tr ((({ st := st, coins := coins } : Spqr.SendKey.SubF Bytes)).pack)
  | spqrSendMsg (st coins : Bytes) :
      Pub tr ((({ st := st, coins := coins } : Spqr.SendMsg.SubF Bytes)).pack)
  | spqrRecvState {st msg : Bytes} (hst : Pub tr st) (hm : Pub tr msg) :
      Pub tr ((({ st := st, msg := msg } : Spqr.RecvState.SubF Bytes)).pack)
  | spqrRecvKey (st msg : Bytes) :
      Pub tr ((({ st := st, msg := msg } : Spqr.RecvKey.SubF Bytes)).pack)

/-! ## Monotonicity -/

theorem IKAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {p : Participant} {r : Bytes}
    (h : IKAt tr p r) : IKAt tr' p r := by
  obtain ⟨t, rfl, h1, h2⟩ := h
  exact ⟨t, rfl, h1.mono hle, evAt_mono hle h2⟩

theorem SPKAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : Participant} {r : Bytes}
    (h : SPKAt tr b r) : SPKAt tr' b r := by
  obtain ⟨t, rfl, h1, h2, h3⟩ := h
  exact ⟨t, rfl, h1.mono hle, h2.mono hle, evAt_mono hle h3⟩

theorem PQAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : Participant} {r : Bytes}
    (h : PQAt tr b r) : PQAt tr' b r := by
  obtain ⟨t, rfl, h1, h2, h3⟩ := h
  exact ⟨t, rfl, h1.mono hle, h2.mono hle, evAt_mono hle h3⟩

theorem OPKAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : Participant} {r : Bytes}
    (h : OPKAt tr b r) : OPKAt tr' b r := by
  obtain ⟨t, rfl, h1, h2⟩ := h
  exact ⟨t, rfl, h1.mono hle, evAt_mono hle h2⟩

theorem AliceSlot.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {t : Nat}
    (h : AliceSlot tr t) : AliceSlot tr' t := by
  obtain ⟨h0, h1, h2, a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, h3, h4, h5⟩ := h
  exact ⟨h0.mono hle, h1.mono hle, h2.mono hle,
    a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, h3.mono hle, h4.mono hle, evAt_mono hle h5⟩

theorem EKAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {r : Bytes} (h : EKAt tr r) :
    EKAt tr' r := by
  obtain ⟨t, rfl, h⟩ := h
  exact ⟨t, rfl, h.mono hle⟩

theorem RatchetAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {r : Bytes} (h : RatchetAt tr r) :
    RatchetAt tr' r := by
  obtain ⟨t, rfl, h⟩ := h
  exact ⟨t, rfl, h.mono hle⟩

theorem TRRatchetAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {r : Bytes} (h : TRRatchetAt tr r) :
    TRRatchetAt tr' r := by
  obtain ⟨t, msg, rfl, hr, hn⟩ := h
  exact ⟨t, msg, rfl, hr.mono hle, hn.mono hle⟩

theorem MsgEncRandAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {r : Bytes}
    (h : MsgEncRandAt tr r) : MsgEncRandAt tr' r := by
  rcases h with ⟨t, n, msg, rfl, h1, h2, h3, ev, h4⟩ | ⟨t, n, msg, rfl, h1, h2, h3, ev, h4⟩
  · exact .inl ⟨t, n, msg, rfl, h1.mono hle, h2.mono hle, h3.mono hle, ev, evAt_mono hle h4⟩
  · exact .inr ⟨t, n, msg, rfl, h1.mono hle, h2.mono hle, h3.mono hle, ev, evAt_mono hle h4⟩

theorem DhClass.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {r : Bytes} (h : DhClass tr r) :
    DhClass tr' r := by
  rcases h with ⟨p, h⟩ | ⟨b, h⟩ | ⟨b, h⟩ | h | h | h
  · exact .inl ⟨p, h.mono hle⟩
  · exact .inr (.inl ⟨b, h.mono hle⟩)
  · exact .inr (.inr (.inl ⟨b, h.mono hle⟩))
  · exact .inr (.inr (.inr (.inl (h.mono hle))))
  · exact .inr (.inr (.inr (.inr (.inl (h.mono hle)))))
  · exact .inr (.inr (.inr (.inr (.inr (h.mono hle)))))

theorem PQClass.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {r : Bytes} (h : PQClass tr r) :
    PQClass tr' r := by
  obtain ⟨b, h⟩ := h
  exact ⟨b, h.mono hle⟩

theorem RandExposed.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {r : Bytes}
    (h : RandExposed tr r) : RandExposed tr' r := by
  rcases h with ⟨p, h, he⟩ | ⟨b, h, he⟩ | ⟨b, h, he⟩ | ⟨b, h, he⟩ |
    ⟨h, he⟩ | ⟨h, he⟩ | ⟨hrat, s, rIdx, he⟩ | h
  · exact .inl ⟨p, h.mono hle, ev_mono hle he⟩
  · exact .inr (.inl ⟨b, h.mono hle, ev_mono hle he⟩)
  · exact .inr (.inr (.inl ⟨b, h.mono hle, ev_mono hle he⟩))
  · exact .inr (.inr (.inr (.inl ⟨b, h.mono hle, ev_mono hle he⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨DhClass.mono hle h, ev_mono hle he⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨PQClass.mono hle h, ev_mono hle he⟩)))))
  · refine .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨?_, s, rIdx, ev_mono hle he⟩))))))
    rcases hrat with h | h
    · exact .inl (h.mono hle)
    · exact .inr (h.mono hle)
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (h.mono hle)))))))

theorem HonestMac.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {x : Bytes} (h : HonestMac tr x) :
    HonestMac tr' x := by
  obtain ⟨j, keys, rkChain, pk, sk, counter, pqSalt, ikA, ikB, wire, hj, hkeys, hrk, hx⟩ := h
  have hlen : tr.length ≤ tr'.length := Trace.length_le tr tr' hle
  exact ⟨j, keys, rkChain, pk, sk, counter, pqSalt, ikA, ikB, wire,
    Nat.lt_of_lt_of_le hj hlen, handshakeKeysAt_mono hle hkeys, hrk, hx⟩

theorem HonestSig.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {sk msg : Bytes}
    (h : HonestSig tr sk msg) : HonestSig tr' sk msg := by
  obtain ⟨b, hik, ⟨s, hs, hm⟩ | ⟨q, hq, hm⟩⟩ := h
  · exact ⟨b, hik.mono hle, .inl ⟨s, hs.mono hle, hm⟩⟩
  · exact ⟨b, hik.mono hle, .inr ⟨q, hq.mono hle, hm⟩⟩

theorem CompExposure.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : Bytes}
    (h : CompExposure tr b) : CompExposure tr' b := by
  have hlen : tr.length ≤ tr'.length := Trace.length_le tr tr' hle
  cases h with
  | pqr hexp => exact .pqr (sessionStateExposed_mono hle hexp)
  | ck0 hexp => exact .ck0 (sessionStateExposed_mono hle hexp)
  | ckStep hj hkeys =>
    exact .ckStep (Nat.lt_of_lt_of_le hj hlen) (handshakeKeysAt_mono hle hkeys)
  | rkRatchet rk pk sk => exact .rkRatchet rk pk sk
  | chainRatchet hj hkeys hrk =>
    exact .chainRatchet (Nat.lt_of_lt_of_le hj hlen) (handshakeKeysAt_mono hle hkeys) hrk
  | seedCk hj hkeys =>
    exact .seedCk (Nat.lt_of_lt_of_le hj hlen) (handshakeKeysAt_mono hle hkeys)
  | seedRatchet hj hkeys hrk =>
    exact .seedRatchet (Nat.lt_of_lt_of_le hj hlen) (handshakeKeysAt_mono hle hkeys) hrk

theorem Pub.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {x : Bytes} (h : Pub tr x) : Pub tr' x := by
  induction h with
  | rand h => exact .rand (RandExposed.mono hle h)
  | exp h => exact .exp (CompExposure.mono hle h)
  | literal bs => exact .literal bs
  | cat _ _ ih1 ih2 => exact .cat ih1 ih2
  | kdf _ _ ih1 ih2 => exact .kdf ih1 ih2
  | trunc _ ih => exact .trunc ih
  | truncHonest h => exact .truncHonest (HonestMac.mono hle h)
  | trWire _ _ _ ih1 ih2 ih3 =>
    exact .trWire ih1 ih2 ih3
  | enc _ ih => exact .enc ih
  | var v _ ih => exact .var v ih
  | dhPub h => exact .dhPub (DhClass.mono hle h)
  | dhPubK _ ih => exact .dhPubK ih
  | dhSk sk pk _ ih => exact .dhSk sk pk ih
  | dhPeer sk s _ ih => exact .dhPeer sk s ih
  | kemPub h => exact .kemPub (PQClass.mono hle h)
  | kemPubK _ ih => exact .kemPubK ih
  | encap pk e => exact .encap pk e
  | ss _ _ ih1 ih2 => exact .ss ih1 ih2
  | ssKey e _ ih => exact .ssKey e ih
  | rejKey _ _ ih1 ih2 => exact .rejKey ih1 ih2
  | vkPub h => exact .vkPub (IKAt.mono hle h)
  | vkPubK _ ih => exact .vkPubK ih
  | sig nonce msg _ ih => exact .sig nonce msg ih
  | sigHonest nonce msg h => exact .sigHonest nonce msg (HonestSig.mono hle h)
  | spqrInit _ _ ih1 ih2 => exact .spqrInit ih1 ih2
  | spqrChainKey k p i => exact .spqrChainKey k p i
  | spqrSendState _ _ ih1 ih2 => exact .spqrSendState ih1 ih2
  | spqrSendKey st coins => exact .spqrSendKey st coins
  | spqrSendMsg st coins => exact .spqrSendMsg st coins
  | spqrRecvState _ _ ih1 ih2 => exact .spqrRecvState ih1 ih2
  | spqrRecvKey st msg => exact .spqrRecvKey st msg

/-! ## Stored State and Handshake Predicates -/

/-- A stored `PQXDHState` has the role its kind says, for its owner. -/
def KindOK (tr : ExecTrace) (me : Participant) (st : PQXDHState) : Prop :=
  match st.kind with
  | .identity => IKAt tr me st.sk
  | .signedPrekey => SPKAt tr me st.sk
  | .pqPrekey => PQAt tr me st.sk
  | .oneTimePrekey => OPKAt tr me st.sk

/-- Bob's bundle as Alice used it: honest (`ikB`, `spk`, `pqpk` are `b`'s keys), or `ikB` was
compromised before, or DH was broken before. -/
def BundleOK (tr : ExecTrace) (b : Participant) (ikB spk pqpk : Bytes) (i : Nat) : Prop :=
  (∃ sB sS sQ, IKAt tr b sB ∧ ikB = DiffieHellman.dhPk sB ∧
    SPKAt tr b sS ∧ spk = DiffieHellman.dhPk sS ∧ PQAt tr b sQ ∧ pqpk = PQKem.kemPk sQ) ∨
  LoggedBefore (PQXDHEvent.CompromisedIK b ikB) i tr ∨
  LoggedBefore PQXDHEvent.BrokenDH i tr

/-- What an `AliceDone` at `i` records: `i = t + 5` for an `AliceSlot t` (so `ek` is the base key
`rnd t 32` and the KEM coins are `rnd (t+1) 32`), `ikA` is `a`'s identity key, the key schedule
is `aliceAgreement`, and Bob's bundle is `BundleOK`. -/
def AliceDoneFacts (tr : ExecTrace) (a b : Participant) (ikA ikB spk pqpk : Bytes)
    (opk : Option Bytes) (ek ct : Bytes) (keys : HandshakeKeys) (i : Nat) : Prop :=
  ∃ t sA, i = t + 5 ∧ AliceSlot tr t ∧ IKAt tr a sA ∧ ikA = DiffieHellman.dhPk sA ∧
    ek = DiffieHellman.dhPk (rnd t 32) ∧
    (ct, keys) = aliceAgreement sA (rnd t 32) ikB spk pqpk opk (rnd (t + 1) 32) ∧
    BundleOK tr b ikB spk pqpk i

/-- An honest Alice completed, before `i`, the exchange Bob completed. -/
def AliceMatch (tr : ExecTrace) (ikA ikB pqpk ek ct : Bytes) (keys : HandshakeKeys) (i : Nat) :
    Prop :=
  ∃ j a' b' spk' opk', j < i ∧
    tr.EventLoggedAt (PQXDHEvent.AliceDone a' b' ikA ikB spk' pqpk opk' ek ct keys) j

/-- What a `BobDone` at `i` records. -/
def BobDoneFacts (tr : ExecTrace) (b a : Participant) (ikB ikA spk pqpk : Bytes)
    (opk : Option Bytes) (ek ct : Bytes) (keys : HandshakeKeys) (i : Nat) : Prop :=
  ∃ (sB sS sQ : Bytes) (o : Option Bytes) (e : Bytes),
    IKAt tr b sB ∧ ikB = DiffieHellman.dhPk sB ∧
    SPKAt tr b sS ∧ spk = DiffieHellman.dhPk sS ∧
    PQAt tr b sQ ∧ pqpk = PQKem.kemPk sQ ∧
    (∀ x, o = some x → OPKAt tr b x) ∧ opk = o.map DiffieHellman.dhPk ∧
    isCanonicalKey ek = true ∧
    e = (DY.Libsignal.PQXDH.errToOption (PQKem.kemDecap sQ ct)).getD (PQKem.kemRejKey sQ ct) ∧
    keys = pqxdhKdf (pqxdhIkm (agree ikA sS) (agree ek sB) (agree ek sS) (o.map (agree ek ·)) e) ∧
    (∃ r vkA hon, r < i ∧
      tr.EventLoggedAt (PQXDHEvent.IdentityRegistered a ikA vkA hon) r) ∧
    (AliceMatch tr ikA ikB pqpk ek ct keys i ∨
      LoggedBefore (PQXDHEvent.CompromisedIK a ikA) i tr ∨
      LoggedBefore (PQXDHEvent.CompromisedSPK b spk) i tr ∨
      LoggedBefore PQXDHEvent.BrokenDH i tr)

/-- SPQR state `spqr` is rooted at `pqr` with `Pub tr`-closed parameters, coins, and messages. -/
inductive SpqrStateFrom (tr : ExecTrace) (pqr : Bytes) : Bytes → Prop where
  | init {params : Bytes} (hp : Pub tr params) :
      SpqrStateFrom tr pqr (Spqr.spqrInit pqr params)
  | send {st coins : Bytes} (hst : SpqrStateFrom tr pqr st) (hc : Pub tr coins) :
      SpqrStateFrom tr pqr ((({ st := st, coins := coins } : Spqr.SendState.SubF Bytes)).pack)
  | recv {st msg : Bytes} (hst : SpqrStateFrom tr pqr st) (hm : Pub tr msg) :
      SpqrStateFrom tr pqr ((({ st := st, msg := msg } : Spqr.RecvState.SubF Bytes)).pack)

theorem SpqrStateFrom.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {pqr spqr : Bytes}
    (h : SpqrStateFrom tr pqr spqr) : SpqrStateFrom tr' pqr spqr := by
  induction h with
  | init hp => exact .init (Pub.mono hle hp)
  | send _ hc ih => exact .send ih (Pub.mono hle hc)
  | recv _ hm ih => exact .recv ih (Pub.mono hle hm)

/-- Structural invariant for every stored `st : TRState` of participant `me`. -/
def TRStateOK (tr : ExecTrace) (me : Participant) (st : TRState) : Prop :=
  ∃ j keys,
    j < tr.length ∧
    HandshakeKeysAt tr j keys ∧
    tr.EventLogged (ComposedEvent.HandshakeSession (st.sessionInfo me) j) ∧
    (RatchetAt tr st.dhs ∨ TRRatchetAt tr st.dhs) ∧
    SpqrStateFrom tr keys.pqr st.spqr ∧
    (∃ r p s, st.rk = (createChain r p s).1) ∧
    (∃ rkChain pk sk n,
      (rkChain = keys.rk ∨ ∃ r₀ p₀ s₀, rkChain = (createChain r₀ p₀ s₀).1) ∧
      st.cks = chainKeyAt (createChain rkChain pk sk).2 n) ∧
    (∀ c ∈ st.recv,
      (c.index = 0 ∧ c.rIdx = 1 ∧ c.chainKey = keys.ck) ∨
      (∃ n, c.index.toNat = n + 1 ∧ c.rIdx = 1 ∧ c.chainKey = chainKeyAt keys.ck (n + 1)) ∨
      (∃ rkChain pk sk n,
        (rkChain = keys.rk ∨ ∃ r₀ p₀ s₀, rkChain = (createChain r₀ p₀ s₀).1) ∧
        c.chainKey = chainKeyAt (createChain rkChain pk sk).2 n))

theorem TRStateOK.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {me : Participant} {st : TRState}
    (h : TRStateOK tr me st) : TRStateOK tr' me st := by
  obtain ⟨j, keys, hj, hkeys, hhs, hdhs, hspqr, hrk, hcks, hrecv⟩ := h
  have hlen : tr.length ≤ tr'.length := Trace.length_le tr tr' hle
  refine ⟨j, keys, Nat.lt_of_lt_of_le hj hlen, handshakeKeysAt_mono hle hkeys,
    ev_mono hle hhs, ?_, hspqr.mono hle, hrk, hcks, hrecv⟩
  rcases hdhs with h | h
  · exact .inl (h.mono hle)
  · exact .inr (h.mono hle)

/-- Structural invariant for every `TREvent.SkippedKeyStored s rPk ctr seed rIdx src` on `tr`. -/
def SkippedKeyOK (tr : ExecTrace) (seed : Bytes) : Prop :=
  ∃ j keys,
    j < tr.length ∧
    HandshakeKeysAt tr j keys ∧
    ((∃ n, seed = (kdfCk (chainKeyAt keys.ck n)).2) ∨
     (∃ rkChain pk sk n,
       (rkChain = keys.rk ∨ ∃ r₀ p₀ s₀, rkChain = (createChain r₀ p₀ s₀).1) ∧
       seed = (kdfCk (chainKeyAt (createChain rkChain pk sk).2 n)).2))

theorem SkippedKeyOK.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {seed : Bytes}
    (h : SkippedKeyOK tr seed) : SkippedKeyOK tr' seed := by
  obtain ⟨j, keys, hj, hkeys, hseed⟩ := h
  have hlen : tr.length ≤ tr'.length := Trace.length_le tr tr' hle
  exact ⟨j, keys, Nat.lt_of_lt_of_le hj hlen, handshakeKeysAt_mono hle hkeys, hseed⟩

/-- Ordering and `!opkUsedB` guard for one-time prekeys: every `BobDone` carrying `some o` has
`OPKUsed b o` logged strictly before it, and no `CompromisedOPK b o` occurs after `OPKUsed b o`. -/
def BobDoneOpkInv (tr : ExecTrace) : Prop :=
  (∀ b a ikB ikA spk pqpk o ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk (some o) ek ct keys) i →
    LoggedBefore (PQXDHEvent.OPKUsed b o) i tr) ∧
  (∀ b o k,
    tr.EventLoggedAt (PQXDHEvent.CompromisedOPK b o) k →
    ¬ LoggedBefore (PQXDHEvent.OPKUsed b o) k tr)

/-- Composed secrecy and authentication invariant on an execution trace. -/
structure SpqrInv (tr : ExecTrace) : Prop where
  /-- Everything on the network is `Pub`. -/
  netPub : ∀ x, Trace.BaseAttackerKnows tr x → Pub tr x
  /-- Every stored `PQXDHState` has its kind's role, for its owner. -/
  stOK : ∀ me st idx, StoredAt tr me st idx → KindOK tr me st
  /-- Every stored `TRState` satisfies `TRStateOK`. -/
  trStOK : ∀ me st idx, TRStoredAt tr me st idx → TRStateOK tr me st
  /-- Every `SkippedKeyStored` event has a seed satisfying `SkippedKeyOK`. -/
  skipOK : ∀ s rPk ctr seed rIdx src idx,
    tr.EventLoggedAt (TREvent.SkippedKeyStored s rPk ctr seed rIdx src) idx →
    SkippedKeyOK tr seed
  /-- Honest PKI entries are `registerIdentity`'s: an honest identity secret. -/
  irHonest : ∀ p ik vkp r,
    tr.EventLoggedAt (PQXDHEvent.IdentityRegistered p ik vkp true) r →
    ∃ s, IKAt tr p s ∧ ik = DiffieHellman.dhPk s ∧ vkp = Signature.vk s
  /-- Dishonest PKI entries are followed by `CompromisedIK` (`registerCorruptIdentity`). -/
  irCorrupt : ∀ p ik vkp r,
    tr.EventLoggedAt (PQXDHEvent.IdentityRegistered p ik vkp false) r →
    tr.EventLoggedAt (PQXDHEvent.CompromisedIK p ik) (r + 1)
  /-- Facts of every `AliceDone`. -/
  aliceDone : ∀ a b ikA ikB spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i →
    AliceDoneFacts tr a b ikA ikB spk pqpk opk ek ct keys i
  /-- Facts of every `BobDone`. -/
  bobDone : ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    BobDoneFacts tr b a ikB ikA spk pqpk opk ek ct keys i
  /-- Ordering of `OPKUsed`, `BobDone`, and `!opkUsedB`-guarded `CompromisedOPK`. -/
  opkOrder : BobDoneOpkInv tr

theorem KindOK.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {me : Participant} {st : PQXDHState}
    (h : KindOK tr me st) : KindOK tr' me st := by
  obtain ⟨kind, sk⟩ := st
  cases kind
  · exact IKAt.mono hle h
  · exact SPKAt.mono hle h
  · exact PQAt.mono hle h
  · exact OPKAt.mono hle h

theorem BundleOK.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : Participant}
    {ikB spk pqpk : Bytes} {i : Nat} (h : BundleOK tr b ikB spk pqpk i) :
    BundleOK tr' b ikB spk pqpk i := by
  rcases h with ⟨sB, sS, sQ, h1, h2, h3, h4, h5, h6⟩ | h | h
  · exact .inl ⟨sB, sS, sQ, h1.mono hle, h2, h3.mono hle, h4, h5.mono hle, h6⟩
  · exact .inr (.inl (loggedBefore_mono hle h))
  · exact .inr (.inr (loggedBefore_mono hle h))

theorem AliceDoneFacts.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {a b : Participant}
    {ikA ikB spk pqpk : Bytes} {opk : Option Bytes} {ek ct : Bytes} {keys : HandshakeKeys}
    {i : Nat} (h : AliceDoneFacts tr a b ikA ikB spk pqpk opk ek ct keys i) :
    AliceDoneFacts tr' a b ikA ikB spk pqpk opk ek ct keys i := by
  obtain ⟨t, sA, hi, hs, hik, h1, h2, h3, hb⟩ := h
  exact ⟨t, sA, hi, hs.mono hle, hik.mono hle, h1, h2, h3, hb.mono hle⟩

theorem AliceMatch.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {ikA ikB pqpk ek ct : Bytes}
    {keys : HandshakeKeys} {i : Nat} (h : AliceMatch tr ikA ikB pqpk ek ct keys i) :
    AliceMatch tr' ikA ikB pqpk ek ct keys i := by
  obtain ⟨j, a', b', spk', opk', hj, hev⟩ := h
  exact ⟨j, a', b', spk', opk', hj, evAt_mono hle hev⟩

theorem BobDoneFacts.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {b a : Participant}
    {ikB ikA spk pqpk : Bytes} {opk : Option Bytes} {ek ct : Bytes} {keys : HandshakeKeys}
    {i : Nat} (h : BobDoneFacts tr b a ikB ikA spk pqpk opk ek ct keys i) :
    BobDoneFacts tr' b a ikB ikA spk pqpk opk ek ct keys i := by
  obtain ⟨sB, sS, sQ, o, e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    ⟨r, vkA, hon, hr, hir⟩, hm⟩ := h
  refine ⟨sB, sS, sQ, o, e, h1.mono hle, h2, h3.mono hle, h4, h5.mono hle, h6,
    fun x hx => (h7 x hx).mono hle, h8, h9, h10, h11, ⟨r, vkA, hon, hr, evAt_mono hle hir⟩, ?_⟩
  rcases hm with h | h | h | h
  · exact .inl (AliceMatch.mono hle h)
  · exact .inr (.inl (loggedBefore_mono hle h))
  · exact .inr (.inr (.inl (loggedBefore_mono hle h)))
  · exact .inr (.inr (.inr (loggedBefore_mono hle h)))

/-! ## Base Case and Owner Uniqueness -/

theorem eventLoggedAt_nil {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {ev : Ev} {i : Nat} :
    ¬ (Trace.nil : ExecTrace).EventLoggedAt ev i := by
  intro h
  (simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h; unfold Trace.at? at h)
  simp [Symbolic.DYBridge.DY.Trace.length_eq_1] at h

theorem storedAt_nil {me : Participant} {st : PQXDHState} {idx : Nat} :
    ¬ StoredAt (Trace.nil : ExecTrace) me st idx := by
  intro h
  unfold StoredAt Trace.at? at h
  simp [Symbolic.DYBridge.DY.Trace.length_eq_1] at h

theorem trStoredAt_nil {me : Participant} {st : TRState} {idx : Nat} :
    ¬ TRStoredAt (Trace.nil : ExecTrace) me st idx := by
  intro h
  unfold TRStoredAt Trace.at? at h
  simp [Symbolic.DYBridge.DY.Trace.length_eq_1] at h

theorem BobDoneOpkInv.nil : BobDoneOpkInv (Trace.nil : ExecTrace) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ h => (eventLoggedAt_nil h).elim,
   fun _ _ _ h => (eventLoggedAt_nil h).elim⟩

private theorem at?_append_of_lt_opk {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte, ← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]

private theorem at?_append_cases_opk {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
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
  · rw [at?_append_of_lt_opk tr e hi] at h
    exact .inl ⟨hi, h⟩
  · simp only [Trace.at?, hlt, ↓reduceDIte] at h
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte] at h
    exact .inr ⟨rfl, h⟩

theorem BobDoneOpkInv.append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option EvEntry) = none)
    (h : BobDoneOpkInv tr) : BobDoneOpkInv (tr.append e) := by
  have hle : tr ≤ tr.append e := Trace.append_le tr e
  refine ⟨?_, ?_⟩
  · intro b a ikB ikA spk pqpk o ek ct keys i hi
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
    rcases at?_append_cases_opk hi with ⟨_, hi'⟩ | ⟨_, hp⟩
    · rw [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi'
      exact loggedBefore_mono hle (h.1 b a ikB ikA spk pqpk o ek ct keys i hi')
    · rw [hnone] at hp; cases hp
  · intro b o k hk ⟨j, hj, hjk⟩
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hk hj
    rcases at?_append_cases_opk hk with ⟨_, hk'⟩ | ⟨_, hp⟩
    · rcases at?_append_cases_opk hj with ⟨_, hj'⟩ | ⟨rfl, _⟩
      · rw [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hk' hj'
        exact h.2 b o k hk' ⟨j, hj', hjk⟩
      · omega
    · rw [hnone] at hp; cases hp

theorem BobDoneOpkInv.append_ev {tr : ExecTrace} {ev : PQXDHEvent} (h : BobDoneOpkInv tr)
    (hbd : ∀ b a ikB ikA spk pqpk o ek ct keys,
      ev = PQXDHEvent.BobDone b a ikB ikA spk pqpk (some o) ek ct keys →
      LoggedBefore (PQXDHEvent.OPKUsed b o) tr.length tr)
    (hco : ∀ b o,
      ev = PQXDHEvent.CompromisedOPK b o →
      ¬ LoggedBefore (PQXDHEvent.OPKUsed b o) tr.length tr) :
    BobDoneOpkInv (tr.append (EvE ev)) := by
  have hle : tr ≤ tr.append (EvE ev) := Trace.append_le tr (EvE ev)
  refine ⟨?_, ?_⟩
  · intro b a ikB ikA spk pqpk o ek ct keys i hi
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
    rcases at?_append_cases_opk hi with ⟨_, hi'⟩ | ⟨rfl, hp⟩
    · rw [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi'
      exact loggedBefore_mono hle (h.1 b a ikB ikA spk pqpk o ek ct keys i hi')
    · rw [TraceEntryHas.inj_proj_eq] at hp
      cases hp
      exact loggedBefore_mono hle (hbd b a ikB ikA spk pqpk o ek ct keys rfl)
  · intro b o k hk ⟨j, hj, hjk⟩
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hk hj
    rcases at?_append_cases_opk hk with ⟨_, hk'⟩ | ⟨rfl, hp⟩
    · rcases at?_append_cases_opk hj with ⟨_, hj'⟩ | ⟨rfl, _⟩
      · rw [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hk' hj'
        exact h.2 b o k hk' ⟨j, hj', hjk⟩
      · omega
    · rw [TraceEntryHas.inj_proj_eq] at hp
      cases hp
      rcases at?_append_cases_opk hj with ⟨_, hj'⟩ | ⟨rfl, _⟩
      · rw [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hj'
        exact hco b o rfl ⟨j, hj', hjk⟩
      · omega

theorem opkUsedB_eq_true_of_eventLoggedAt {tr : ExecTrace} {b : Participant} {o : Bytes} {j : Nat}
    (hAt : tr.EventLoggedAt (PQXDHEvent.OPKUsed b o) j) : opkUsedB tr b o = true := by
  have hAt' : (tr.at? j : Option EvEntry) = some ⟨PQXDHEvent.OPKUsed b o⟩ := by
    rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hAt
  have hj : j < tr.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := EvEntry) tr j
    rw [hAt'] at this; exact this
  unfold opkUsedB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [List.any_eq_true]
  refine ⟨j, List.mem_range.mpr hj, ?_⟩
  rw [hAt']
  simp

theorem not_loggedBefore_opkUsed_of_opkUsedB_eq_false {tr : ExecTrace} {b : Participant} {o : Bytes}
    (h : opkUsedB tr b o = false) {k : Nat} :
    ¬ LoggedBefore (PQXDHEvent.OPKUsed b o) k tr := by
  rintro ⟨j, hj, _⟩
  have hTrue := opkUsedB_eq_true_of_eventLoggedAt hj
  rw [h] at hTrue; cases hTrue

theorem SpqrInv.compOpk_loggedBefore {tr : ExecTrace} (hinv : SpqrInv tr)
    {b a : Participant} {ikB ikA spk pqpk o ek ct : Bytes} {keys : HandshakeKeys} {i : Nat}
    (hDone : tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk (some o) ek ct keys) i)
    (hEv : tr.EventLogged (PQXDHEvent.CompromisedOPK b o)) :
    LoggedBefore (PQXDHEvent.CompromisedOPK b o) i tr := by
  obtain ⟨k, hk⟩ := hEv
  obtain ⟨u, hu, hui⟩ := hinv.opkOrder.1 b a ikB ikA spk pqpk o ek ct keys i hDone
  have hNotBefore := hinv.opkOrder.2 b o k hk
  exact ⟨k, hk, Nat.lt_of_not_ge fun hge => hNotBefore ⟨u, hu, by omega⟩⟩

/-- `SpqrInv` holds on the empty execution trace. -/
theorem spqrInv_nil : SpqrInv (Trace.nil : ExecTrace) where
  netPub b h := (Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1 b ▸ h).elim
  stOK _ _ _ h := (storedAt_nil h).elim
  trStOK _ _ _ h := (trStoredAt_nil h).elim
  skipOK _ _ _ _ _ _ _ h := (eventLoggedAt_nil h).elim
  irHonest _ _ _ _ h := (eventLoggedAt_nil h).elim
  irCorrupt _ _ _ _ h := (eventLoggedAt_nil h).elim
  aliceDone _ _ _ _ _ _ _ _ _ _ _ h := (eventLoggedAt_nil h).elim
  bobDone _ _ _ _ _ _ _ _ _ _ _ h := (eventLoggedAt_nil h).elim
  opkOrder := BobDoneOpkInv.nil

/-- `Inv` is preserved by running `x` on any trace. -/
def Preserves (Inv : ExecTrace → Prop) {α : Type} (x : Traceful α) : Prop :=
  ∀ tr, Inv tr → Inv (x.run tr).2.val

theorem ikAt_owner_unique {tr : ExecTrace} {p₁ p₂ : Participant} {r : Bytes}
    (h₁ : IKAt tr p₁ r) (h₂ : IKAt tr p₂ r) : p₁ = p₂ := by
  obtain ⟨t₁, hr₁, _, hev₁⟩ := h₁
  obtain ⟨t₂, hr₂, _, hev₂⟩ := h₂
  have ht : t₁ = t₂ := (rnd_inj (hr₁.symm.trans hr₂)).1
  subst ht
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev₁ hev₂
  have hEq :
      (some (EvE (PQXDHEvent.IdentityRegistered p₁ (DiffieHellman.dhPk r) (Signature.vk r) true)) : Option EvEntry) =
      some (EvE (PQXDHEvent.IdentityRegistered p₂ (DiffieHellman.dhPk r) (Signature.vk r) true)) :=
    hev₁.symm.trans hev₂
  cases hEq
  rfl

end Symbolic.Swarm.COMPOSED.CompInv
