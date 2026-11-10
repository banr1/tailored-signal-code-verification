/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.EquationalTheory.DiffieHellman
public import DY.Actions.Random
public import DY.Actions.PersistentLocalState
public import Symbolic.Specifications.Model.EquationalTheory.X25519
public import Symbolic.Specifications.Model.EquationalTheory.Kem
public import DY.EquationalTheory.Sign
public import Symbolic.Specifications.Model.MsgKeys

/-!
# Symbolic PQXDH Handshake, PKI, Prekeys, and Threat Model

DyLean model of libsignal's PQXDH key schedule, authentic PKI registration, prekey publication,
trace-silent handshake subroutines (`aliceHandshake`, `bobHandshake`), and key-compromise /
primitive-break transitions. Role names follow libsignal (`AliceDone` fetches a bundle; `BobDone`
publishes prekeys).
-/

namespace DY.Libsignal.PQXDH

open DY.Comparse

export DY.X25519 (x25519LowOrder isCanonicalKey agree)
export DY.Libsignal.TripleRatchet (MessageKeys SignalMsg lit litByte hmac hkdfBlock1 hkdfBlock2
  hkdfBlock3 zeroSalt messageVersion maxForwardJumps u32Max
  anyEventOnTrace guardTrace getStoredLocalStateAt?)

public section ExecBytesConfig

class HasExecBytes where
  [bytesFunc: BytesFunctor]
  [bytesFunc0: BytesFunctor.Has Random.SubF]
  [bytesFunc1: BytesFunctor.Has Literal.SubF]
  [bytesFunc2: BytesFunctor.Has Concat.SubF]
  [bytesFunc3: BytesFunctor.Has DiffieHellman.SubF]
  [bytesFunc4: BytesFunctor.Has KdfExtract.SubF]
  [bytesFunc8: BytesFunctor.Has X25519.SubF]
  [bytesFuncKem: BytesFunctor.Has PQKem.SubF]
  [bytesFuncSig: BytesFunctor.Has Signature.SubF]
  [bytesLen: BytesLength]
  [bytesLen0: BytesLength.Has Random.SubF.length]
  [bytesLen1: BytesLength.Has Literal.SubF.length]
  [bytesLen2: BytesLength.Has Concat.SubF.length]
  [bytesLen3: BytesLength.Has DiffieHellman.SubF.length]
  [bytesLen4: BytesLength.Has KdfExtract.SubF.length]
  [bytesLen8: BytesLength.Has X25519.SubF.length]
  [bytesLenKem: BytesLength.Has PQKem.SubF.length]
  [bytesLenSig: BytesLength.Has Signature.SubF.length]
  [att: AttackerKnowledge]
  [att0: AttackerKnowledge.Has Random.attackerKnowledge]
  [att1: AttackerKnowledge.Has Literal.attackerKnowledge]
  [att2: AttackerKnowledge.Has Concat.attackerKnowledge]
  [att3: AttackerKnowledge.Has DiffieHellman.attackerKnowledge]
  [att4: AttackerKnowledge.Has KdfExtract.attackerKnowledge]
  [att8: AttackerKnowledge.Has X25519.attackerKnowledge]
  [attKem: AttackerKnowledge.Has PQKem.attackerKnowledge]
  [attSig: AttackerKnowledge.Has Signature.attackerKnowledge]

attribute [reducible, scoped instance] HasExecBytes.bytesFunc HasExecBytes.bytesFunc0
  HasExecBytes.bytesFunc1 HasExecBytes.bytesFunc2 HasExecBytes.bytesFunc3 HasExecBytes.bytesFunc4
  HasExecBytes.bytesFunc8 HasExecBytes.bytesFuncKem HasExecBytes.bytesFuncSig
  HasExecBytes.bytesLen HasExecBytes.att
attribute [scoped instance] HasExecBytes.bytesLen0 HasExecBytes.bytesLen1 HasExecBytes.bytesLen2
  HasExecBytes.bytesLen3 HasExecBytes.bytesLen4 HasExecBytes.bytesLen8
  HasExecBytes.bytesLenKem HasExecBytes.bytesLenSig
attribute [scoped instance] HasExecBytes.att0 HasExecBytes.att1 HasExecBytes.att2 HasExecBytes.att3
  HasExecBytes.att4 HasExecBytes.att8
  HasExecBytes.attKem HasExecBytes.attSig

end ExecBytesConfig

public section Structures

variable [HasExecBytes]

/-- Tag distinguishing stored long-term and prekey secrets in `PQXDHState`. -/
inductive KeyKind where
  | identity
  | signedPrekey
  | pqPrekey
  | oneTimePrekey
deriving DecidableEq

/-- Stored secret key of a participant (identity, signed prekey, Kyber prekey, or one-time prekey).
Alice's ephemeral base key is dropped after `pqxdh_initiate` and never stored. -/
structure PQXDHState where
  kind: KeyKind
  sk: Bytes

/-- Output of `HandshakeKeys::derive`: 32-byte root key, initial chain key, and initial SPQR key. -/
structure HandshakeKeys where
  rk: Bytes
  ck: Bytes
  pqr: Bytes

/-- Protocol and threat events logged by PQXDH transitions (carrying public keys so events do not
reveal secrets). -/
inductive PQXDHEvent where
  | IdentityRegistered (p: Participant) (ikPk vk: Bytes) (honest: Bool)
  | SignedPrekeyPublished (b: Participant) (spkPk: Bytes)
  | PQPrekeyPublished (b: Participant) (pqPk: Bytes)
  | OneTimePrekeyPublished (b: Participant) (opkPk: Bytes)
  | AliceDone (a b: Participant) (ikA ikB spk pqpk: Bytes) (opk: Option Bytes) (ek ct: Bytes)
      (keys: HandshakeKeys)
  | BobDone (b a: Participant) (ikB ikA spk pqpk: Bytes) (opk: Option Bytes) (ek ct: Bytes)
      (keys: HandshakeKeys)
  | CompromisedIK (p: Participant) (ikPk: Bytes)
  | CompromisedSPK (b: Participant) (spkPk: Bytes)
  | CompromisedPQSPK (b: Participant) (pqPk: Bytes)
  | CompromisedOPK (b: Participant) (opkPk: Bytes)
  | BrokenDH
  | BrokenKEM
  /-- Ghost event recording single-use consumption of one-time prekey `opkPk` by `b`. -/
  | OPKUsed (b: Participant) (opkPk: Bytes)

end Structures

public section Formats

variable [HasExecBytes]

def KeyKind.ofBits: Bool × Bool → KeyKind
  | (false, false) => .identity
  | (false, true) => .signedPrekey
  | (true, false) => .pqPrekey
  | (true, true) => .oneTimePrekey

@[expose] def KeyKind.toBits: KeyKind → Bool × Bool
  | .identity => (false, false)
  | .signedPrekey => (false, true)
  | .pqPrekey => (true, false)
  | .oneTimePrekey => (true, true)

public
instance: ParseableSerializeable PQXDHState := .make <|
  .triviallyIsomorphic
    (.prod .bool (.prod .bool .bytes))
    (fun (b1, b2, sk) => { kind := KeyKind.ofBits (b1, b2), sk })
    (fun { kind, sk } => (kind.toBits.1, kind.toBits.2, sk))
    (by intro (b1, b2, sk); cases b1 <;> cases b2 <;> rfl)
    (by intro { kind, sk }; cases kind <;> rfl)

end Formats

public section ExecTraceConfig

class HasExecTrace extends toPQXDHExecBytes : HasExecBytes where
  [traceExec: ExecTraceTypes]
  [traceExec0: ExecTraceTypes.Has Network.ExecEntryT]
  [traceExec1: ExecTraceTypes.Has Random.ExecEntryT]
  [traceExec2: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT PQXDHEvent)]
  [traceExec3: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT PQXDHState)]
  [attBase: BaseAttackerKnowledge]

attribute [reducible, scoped instance] HasExecTrace.traceExec HasExecTrace.traceExec0
  HasExecTrace.traceExec1 HasExecTrace.traceExec2 HasExecTrace.traceExec3 HasExecTrace.attBase

end ExecTraceConfig

@[expose] public section KeySchedule

variable [HasExecBytes]

open Literal Concat DiffieHellman KdfExtract PQKem

/-- HKDF info string of `HandshakeKeys::derive`. -/
def pqxdhLabel: Bytes := lit "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"

/-- 32-byte `0xFF` domain-separation prefix of the PQXDH input key material. -/
def discontinuity: Bytes := literalToBytes ⟨Array.replicate 32 0xFF⟩

/-- `KeyType::Djb` (`0x05`) prefix byte for serialized X25519 public keys. -/
def ecKeyType: UInt8 := 0x05

/-- `kem::KeyType::Kyber1024` (`0x08`) prefix byte for serialized Kyber-1024 public keys. -/
def kemKeyType: UInt8 := 0x08

/-- `PublicKey::serialize` for X25519 (`0x05 || pk`). -/
def encodeEC (pk: Bytes): Bytes := concat (litByte ecKeyType) pk

/-- `kem::PublicKey::serialize` for Kyber-1024 (`0x08 || pk`). -/
def encodeKEM (pk: Bytes): Bytes := concat (litByte kemKeyType) pk

/-- `IdentityKey::serialize` (`encodeEC ikPk`). -/
def serializedIk (ikPk: Bytes): Bytes := encodeEC ikPk

/-- Concatenated PQXDH secret input: `discontinuity || dh1 || dh2 || dh3 [|| dh4] || ss`. -/
def pqxdhIkm (dh1 dh2 dh3: Bytes) (dh4: Option Bytes) (ss: Bytes): Bytes :=
  concat discontinuity (concat dh1 (concat dh2 (concat dh3
    (match dh4 with
     | some d => concat d ss
     | none => ss))))

/-- `HandshakeKeys::derive`: HKDF-SHA256 with `zeroSalt` and `pqxdhLabel` into `(rk, ck, pqr)`. -/
def pqxdhKdf (ikm: Bytes): HandshakeKeys :=
  let prk := hmac zeroSalt ikm
  { rk := hkdfBlock1 prk pqxdhLabel
    ck := hkdfBlock2 prk pqxdhLabel
    pqr := hkdfBlock3 prk pqxdhLabel }

/-- `pqxdh_initiate`: encapsulates to `pqPk` under `entropy` and derives `(ct, HandshakeKeys)`. -/
def aliceAgreement (ikA ek ikBPk spkPk pqPk: Bytes) (opkPk: Option Bytes) (entropy: Bytes):
    Bytes × HandshakeKeys :=
  let (ct, ss) := kemEncap pqPk entropy
  (ct, pqxdhKdf (pqxdhIkm (agree spkPk ikA) (agree ikBPk ek) (agree spkPk ek)
    (opkPk.map (agree · ek)) ss))

def errToOption {α: Type} (x: Err α): Option α := x

/-- `pqxdh_accept`: decapsulates `ct` under `pqsk` (with implicit rejection `kemRejKey pqsk ct` on
decapsulation failure) and derives `HandshakeKeys`. -/
def bobAgreement (ikB spk pqsk: Bytes) (opk: Option Bytes) (ikAPk ekPk ct: Bytes):
    Option HandshakeKeys := do
  let ss := (errToOption (kemDecap pqsk ct)).getD (kemRejKey pqsk ct)
  pure (pqxdhKdf (pqxdhIkm (agree ikAPk spk) (agree ekPk ikB) (agree ekPk spk)
    (opk.map (agree ekPk ·)) ss))

/-- Discrete-log extraction of `sk` from `dhPk sk`. -/
def extractDhSecretKey (pk: Bytes): Option Bytes :=
  match pk.view? DiffieHellman.DhPk.SubF with
  | some { sk } => some sk
  | none => none

end KeySchedule

@[expose] public section Specification

variable [HasExecTrace]

open DiffieHellman Signature PQKem
open PersistentLocalState (getLocalState storeLocalState)
open Network (sendMessage receiveMessage)
open Random (genRand)
open ProtocolEvent (logEvent)

def isRegisteredB (tr: ExecTrace) (p: Participant) : Bool :=
  anyEventOnTrace PQXDHEvent tr fun
    | .IdentityRegistered p' _ _ _ => p' == p
    | _ => false

def opkUsedB (tr: ExecTrace) (b: Participant) (opkPk: Bytes) : Bool :=
  anyEventOnTrace PQXDHEvent tr fun
    | .OPKUsed b' o => b' == b && o == opkPk
    | _ => false

def brokenDHB (tr: ExecTrace) : Bool :=
  anyEventOnTrace PQXDHEvent tr fun | .BrokenDH => true | _ => false

def brokenKEMB (tr: ExecTrace) : Bool :=
  anyEventOnTrace PQXDHEvent tr fun | .BrokenKEM => true | _ => false

def getKey (p: Participant) (stateIdx: Nat) (kind: KeyKind) : Traceful Bytes := do
  let st: PQXDHState ← getLocalState p stateIdx
  guard (st.kind = kind)
  pure st.sk

/-- Register an honest identity for `p` (at most once per participant): draws `ik`, publishes
`dhPk ik` and its XEdDSA verification key `vk ik`, logs `IdentityRegistered p (dhPk ik) (vk ik) true`,
and stores `ik` in the modeled authentic PKI. -/
def registerIdentity (p: Participant) : Traceful Nat := do
  guardTrace fun tr => !isRegisteredB tr p
  let ik ← genRand 32
  logEvent (PQXDHEvent.IdentityRegistered p (dhPk ik) (vk ik) true)
  let _ ← sendMessage (dhPk ik)
  let _ ← sendMessage (vk ik)
  storeLocalState p { kind := .identity, sk := ik : PQXDHState }

/-- Register an attacker-controlled identity for `p` from network handle `skIdx` (at most once per
participant), logging `IdentityRegistered ... false` and `CompromisedIK`. -/
def registerCorruptIdentity (p: Participant) (skIdx: Nat) : Traceful Unit := do
  guardTrace fun tr => !isRegisteredB tr p
  let ik ← receiveMessage skIdx
  logEvent (PQXDHEvent.IdentityRegistered p (dhPk ik) (vk ik) false)
  logEvent (PQXDHEvent.CompromisedIK p (dhPk ik))

/-- Look up `(ikPk, vkPk)` for `p` from the `IdentityRegistered` event at `regIdx`. -/
def lookupIdentity (p: Participant) (regIdx: Nat) : Traceful (Bytes × Bytes) := do
  let e: ProtocolEvent.ExecEntryT PQXDHEvent ← getEntry regIdx
  let .IdentityRegistered p' ikPk vkPk _ := e.ev | failure
  guard (p' = p)
  pure (ikPk, vkPk)

/-- Generate, sign (`encodeEC`), store, and publish an X25519 signed prekey for `b`. -/
def genSignedPrekey (b: Participant) (idStateIdx: Nat) : Traceful Nat := do
  let ik ← getKey b idStateIdx .identity
  let spk ← genRand 32
  let nonce ← genRand 64
  logEvent (PQXDHEvent.SignedPrekeyPublished b (dhPk spk))
  let h ← storeLocalState b { kind := .signedPrekey, sk := spk : PQXDHState }
  let _ ← sendMessage (dhPk spk)
  let _ ← sendMessage (sign ik nonce (encodeEC (dhPk spk)))
  pure h

/-- Generate, sign (`encodeKEM`), store, and publish a reusable Kyber-1024 prekey for `b`. -/
def genPQPrekey (b: Participant) (idStateIdx: Nat) : Traceful Nat := do
  let ik ← getKey b idStateIdx .identity
  let pqsk ← genRand 64
  let nonce ← genRand 64
  logEvent (PQXDHEvent.PQPrekeyPublished b (kemPk pqsk))
  let h ← storeLocalState b { kind := .pqPrekey, sk := pqsk : PQXDHState }
  let _ ← sendMessage (kemPk pqsk)
  let _ ← sendMessage (sign ik nonce (encodeKEM (kemPk pqsk)))
  pure h

/-- Generate, store, and publish an unsigned X25519 one-time prekey for `b`. -/
def genOneTimePrekey (b: Participant) : Traceful Nat := do
  let opk ← genRand 32
  logEvent (PQXDHEvent.OneTimePrekeyPublished b (dhPk opk))
  let h ← storeLocalState b { kind := .oneTimePrekey, sk := opk : PQXDHState }
  let _ ← sendMessage (dhPk opk)
  pure h

/-- Network handles for a received prekey bundle. -/
structure BundleHandles where
  spk: Nat
  spkSig: Nat
  pqpk: Nat
  pqpkSig: Nat
  opk: Option Nat

structure AliceHandshakeOut where
  ikA: Bytes
  ikB: Bytes
  spk: Bytes
  pqpk: Bytes
  opk: Option Bytes
  ek: Bytes
  ct: Bytes
  keys: HandshakeKeys

/-- Alice's handshake subroutine (`process_prekey_bundle` / `pqxdh_initiate`): verifies both prekey
signatures under `b`'s PKI verification key, draws ephemeral secret `ek`, rejects low-order
prekeys, encapsulates, and derives `HandshakeKeys` without logging events or storing state. -/
def aliceHandshake (a b: Participant) (idStateIdx regIdxB: Nat) (h: BundleHandles) :
    Traceful AliceHandshakeOut := do
  let ikA ← getKey a idStateIdx .identity
  let (ikB, vkB) ← lookupIdentity b regIdxB
  let spk ← receiveMessage h.spk
  let spkSig ← receiveMessage h.spkSig
  let pqpk ← receiveMessage h.pqpk
  let pqpkSig ← receiveMessage h.pqpkSig
  guard (verify vkB (encodeEC spk) spkSig)
  guard (verify vkB (encodeKEM pqpk) pqpkSig)
  let opk ← match h.opk with
    | some i => do pure (some (← receiveMessage i))
    | none => pure none
  let ek ← genRand 32
  guard (!x25519LowOrder spk)
  guard (opk.all fun o => !x25519LowOrder o)
  let entropy ← genRand 32
  let (ct, keys) := aliceAgreement ikA ek ikB spk pqpk opk entropy
  pure { ikA := dhPk ikA, ikB, spk, pqpk, opk, ek := dhPk ek, ct, keys }

/-- Local state handles for Bob's secrets in `bobHandshake`. -/
structure BobKeyHandles where
  ik: Nat
  spk: Nat
  pqspk: Nat
  opk: Option Nat

structure BobHandshakeOut where
  ikB: Bytes
  ikA: Bytes
  spk: Bytes
  pqpk: Bytes
  opk: Option Bytes
  ek: Bytes
  ct: Bytes
  spkSk: Bytes
  keys: HandshakeKeys

/-- Bob's handshake subroutine (`process_prekey_impl` / `pqxdh_accept`): loads Bob's secrets and
Alice's PKI identity key, checks `isCanonicalKey ek`, and derives `HandshakeKeys` without logging
events or storing state. -/
def bobHandshake (b a: Participant) (h: BobKeyHandles) (regIdxA ekIdx ctIdx: Nat) :
    Traceful BobHandshakeOut := do
  let ikB ← getKey b h.ik .identity
  let spkSk ← getKey b h.spk .signedPrekey
  let pqsk ← getKey b h.pqspk .pqPrekey
  let opkSk ← match h.opk with
    | some i => do pure (some (← getKey b i .oneTimePrekey))
    | none => pure none
  let (ikA, _) ← lookupIdentity a regIdxA
  let ek ← receiveMessage ekIdx
  let ct ← receiveMessage ctIdx
  guard (isCanonicalKey ek)
  let some keys := bobAgreement ikB spkSk pqsk opkSk ikA ek ct | failure
  pure { ikB := dhPk ikB, ikA, spk := dhPk spkSk, pqpk := kemPk pqsk, opk := opkSk.map dhPk,
         ek, ct, spkSk, keys }

/-- Network handles for an incoming `PreKeySignalMessage` (`ek`, `ct`, and inner `SignalMessage`). -/
structure PreKeyMsgHandles where
  ek: Nat
  ct: Nat
  msg: Nat

def compromiseIK (p: Participant) (stateIdx: Nat) : Traceful Nat := do
  let ik ← getKey p stateIdx .identity
  logEvent (PQXDHEvent.CompromisedIK p (dhPk ik))
  sendMessage ik

def compromiseSPK (b: Participant) (stateIdx: Nat) : Traceful Nat := do
  let spk ← getKey b stateIdx .signedPrekey
  logEvent (PQXDHEvent.CompromisedSPK b (dhPk spk))
  sendMessage spk

def compromisePQSPK (b: Participant) (stateIdx: Nat) : Traceful Nat := do
  let pqsk ← getKey b stateIdx .pqPrekey
  logEvent (PQXDHEvent.CompromisedPQSPK b (kemPk pqsk))
  sendMessage pqsk

/-- Leak an unconsumed one-time prekey secret of `b`. -/
def compromiseOPK (b: Participant) (stateIdx: Nat) : Traceful Nat := do
  let opk ← getKey b stateIdx .oneTimePrekey
  guardTrace fun tr => !opkUsedB tr b (dhPk opk)
  logEvent (PQXDHEvent.CompromisedOPK b (dhPk opk))
  sendMessage opk

def breakDH : Traceful Unit := logEvent PQXDHEvent.BrokenDH

def breakKEM : Traceful Unit := logEvent PQXDHEvent.BrokenKEM

/-- Discrete-log oracle enabled after `BrokenDH`. -/
def invertDH (pkIdx: Nat) : Traceful Nat := do
  guardTrace brokenDHB
  let pk ← receiveMessage pkIdx
  let some sk := extractDhSecretKey (X25519.normalizeX25519Key pk) | failure
  sendMessage sk

/-- KEM public-key inversion oracle enabled after `BrokenKEM`. -/
def invertKEM (pkIdx: Nat) : Traceful Nat := do
  guardTrace brokenKEMB
  let pk ← receiveMessage pkIdx
  let sk ← invertKemPublicKey pk
  sendMessage sk

end Specification

public section Reachability

variable [HasExecTrace]

@[expose] public section
def registerIdentity.reachability: ReachabilityConfig :=
  .make (fun p => registerIdentity p)
def registerCorruptIdentity.reachability: ReachabilityConfig :=
  .make (fun ((p, skIdx): Participant × Nat) => registerCorruptIdentity p skIdx)
def genSignedPrekey.reachability: ReachabilityConfig :=
  .make (fun ((b, idStateIdx): Participant × Nat) => genSignedPrekey b idStateIdx)
def genPQPrekey.reachability: ReachabilityConfig :=
  .make (fun ((b, idStateIdx): Participant × Nat) => genPQPrekey b idStateIdx)
def genOneTimePrekey.reachability: ReachabilityConfig :=
  .make (fun b => genOneTimePrekey b)
def compromiseIK.reachability: ReachabilityConfig :=
  .make (fun ((p, stateIdx): Participant × Nat) => compromiseIK p stateIdx)
def compromiseSPK.reachability: ReachabilityConfig :=
  .make (fun ((b, stateIdx): Participant × Nat) => compromiseSPK b stateIdx)
def compromisePQSPK.reachability: ReachabilityConfig :=
  .make (fun ((b, stateIdx): Participant × Nat) => compromisePQSPK b stateIdx)
def compromiseOPK.reachability: ReachabilityConfig :=
  .make (fun ((b, stateIdx): Participant × Nat) => compromiseOPK b stateIdx)
def breakDH.reachability: ReachabilityConfig :=
  .make (fun (_: Unit) => breakDH)
def breakKEM.reachability: ReachabilityConfig :=
  .make (fun (_: Unit) => breakKEM)
def invertDH.reachability: ReachabilityConfig :=
  .make (fun pkIdx => invertDH pkIdx)
def invertKEM.reachability: ReachabilityConfig :=
  .make (fun pkIdx => invertKEM pkIdx)
end

end Reachability

end DY.Libsignal.PQXDH
