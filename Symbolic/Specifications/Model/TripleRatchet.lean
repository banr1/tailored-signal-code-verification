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
public import Symbolic.Specifications.Model.EquationalTheory.SymEnc
public import Symbolic.Specifications.Model.EquationalTheory.Trunc
public import Symbolic.Specifications.Model.EquationalTheory.X25519
public import Symbolic.Specifications.Model.EquationalTheory.Spqr
public import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
public import Symbolic.Specifications.Model.MsgKeys

/-!
# Symbolic Triple Ratchet (Double Ratchet + SPQR V1)

DyLean model of libsignal's Triple Ratchet session state, symmetric and DH ratchet KDFs, wire
codec, encryption/decryption transitions, and per-component state exposure. Each `TRState` carries
an opaque `Spqr` state whose per-message keys are published and mixed into `trMsgKeys` via an
attacker-supplied network handle.
-/

namespace DY.Libsignal.TripleRatchet

open DY.Comparse

export DY.X25519 (x25519LowOrder agree)

public section ExecBytesConfig

class HasExecBytes where
  [bytesFunc: BytesFunctor]
  [bytesFunc0: BytesFunctor.Has Random.SubF]
  [bytesFunc1: BytesFunctor.Has Literal.SubF]
  [bytesFunc2: BytesFunctor.Has Concat.SubF]
  [bytesFunc3: BytesFunctor.Has DiffieHellman.SubF]
  [bytesFunc4: BytesFunctor.Has KdfExtract.SubF]
  [bytesFunc5: BytesFunctor.Has SymEnc.SubF]
  [bytesFunc6: BytesFunctor.Has Trunc.SubF]
  [bytesFunc8: BytesFunctor.Has X25519.SubF]
  [bytesFuncSpqr: BytesFunctor.Has Spqr.SubF]
  [bytesFuncTrWire: BytesFunctor.Has TrWire.SubF]
  [bytesLen: BytesLength]
  [bytesLen0: BytesLength.Has Random.SubF.length]
  [bytesLen1: BytesLength.Has Literal.SubF.length]
  [bytesLen2: BytesLength.Has Concat.SubF.length]
  [bytesLen3: BytesLength.Has DiffieHellman.SubF.length]
  [bytesLen4: BytesLength.Has KdfExtract.SubF.length]
  [bytesLen5: BytesLength.Has SymEnc.SubF.length]
  [bytesLen6: BytesLength.Has Trunc.SubF.length]
  [bytesLen8: BytesLength.Has X25519.SubF.length]
  [bytesLenSpqr: BytesLength.Has Spqr.SubF.length]
  [bytesLenTrWire: BytesLength.Has TrWire.SubF.length]
  [att: AttackerKnowledge]
  [att0: AttackerKnowledge.Has Random.attackerKnowledge]
  [att1: AttackerKnowledge.Has Literal.attackerKnowledge]
  [att2: AttackerKnowledge.Has Concat.attackerKnowledge]
  [att3: AttackerKnowledge.Has DiffieHellman.attackerKnowledge]
  [att4: AttackerKnowledge.Has KdfExtract.attackerKnowledge]
  [att5: AttackerKnowledge.Has SymEnc.attackerKnowledge]
  [att6: AttackerKnowledge.Has Trunc.attackerKnowledge]
  [att8: AttackerKnowledge.Has X25519.attackerKnowledge]
  [attSpqr: AttackerKnowledge.Has Spqr.attackerKnowledge]
  [attTrWire: AttackerKnowledge.Has TrWire.attackerKnowledge]

attribute [reducible, scoped instance] HasExecBytes.bytesFunc HasExecBytes.bytesFunc0
  HasExecBytes.bytesFunc1 HasExecBytes.bytesFunc2 HasExecBytes.bytesFunc3 HasExecBytes.bytesFunc4
  HasExecBytes.bytesFunc5 HasExecBytes.bytesFunc6 HasExecBytes.bytesFunc8
  HasExecBytes.bytesFuncSpqr HasExecBytes.bytesFuncTrWire
  HasExecBytes.bytesLen HasExecBytes.att
attribute [scoped instance] HasExecBytes.bytesLen0 HasExecBytes.bytesLen1 HasExecBytes.bytesLen2
  HasExecBytes.bytesLen3 HasExecBytes.bytesLen4 HasExecBytes.bytesLen5 HasExecBytes.bytesLen6
  HasExecBytes.bytesLen8
  HasExecBytes.bytesLenSpqr HasExecBytes.bytesLenTrWire
attribute [scoped instance] HasExecBytes.att0 HasExecBytes.att1 HasExecBytes.att2 HasExecBytes.att3
  HasExecBytes.att4 HasExecBytes.att5 HasExecBytes.att6 HasExecBytes.att8
  HasExecBytes.attSpqr HasExecBytes.attTrWire

end ExecBytesConfig

public section Structures

variable [HasExecBytes]

/-- Receiver chain entry: peer ratchet public key, chain key at `index`, and ghost ratchet index
`rIdx` at which the chain was created. -/
structure RecvChain where
  ratchetKey: Bytes
  chainKey: Bytes
  index: UInt32
  rIdx: Nat := 0

/-- Base Double Ratchet session state (version 4, without SPQR or cached skipped message keys). -/
structure DRState where
  peer: Participant
  myIk: Bytes
  peerIk: Bytes
  rk: Bytes
  /-- Current sending ratchet private key (`dhPk dhs` is sent on the wire). -/
  dhs: Bytes
  cks: Bytes
  ns: UInt32
  pn: UInt32
  /-- Ghost session identifier (`concat firstRatchetPk handshakeRk`). -/
  sid: Bytes
  /-- Ghost initiator flag (`true` for Alice). -/
  initiator: Bool
  /-- Ghost ratchet epoch index of this snapshot. -/
  rIdx: Nat
  /-- Active receiver chains, oldest first (at most `maxReceiverChains`). -/
  recv: List RecvChain

@[expose] section
/-- Ghost session descriptor `(sid, initiator, me, peer)`. -/
structure SessionInfo where
  sid: Bytes
  initiator: Bool
  me: Participant
  peer: Participant
deriving DecidableEq
end

inductive KeyDir where
  | sender
  | receiver

/-- Session state component selected by `exposeKey` (`ckr pk` selects the receiver chain for `pk`). -/
inductive KeyComponent where
  | rk
  | dhs
  | cks
  | ckr (pk: Bytes)

/-- Triple Ratchet session snapshot: `DRState` paired with the opaque `spqr` state term. -/
structure TRState extends DRState where
  spqr: Bytes

/-- Decoded Triple Ratchet `SignalMessage` (`SignalMsg` plus `pqRatchet`). -/
structure TRSignalMsg extends SignalMsg where
  pqRatchet: Bytes

/-- Functional and ghost events logged by Triple Ratchet transitions. Logging an event does not
reveal terms to the attacker (`ProtocolEvent.baseAttackerKnowledge` is `False`). -/
inductive TREvent where
  | InitSession (alice bob: Participant) (pkA pkB: Bytes)
  | Sent (me peer: Participant) (pk: Bytes) (n: UInt32) (m: Bytes)
  | Received (me peer: Participant) (pk: Bytes) (n: UInt32) (m: Bytes)
  | DHRatchet (me peer: Participant) (theirPk myPk: Bytes)
  | ExposedRK (s: SessionInfo) (rk: Bytes) (rIdx: Nat)
  | ExposedDHs (s: SessionInfo) (dhs: Bytes) (rIdx: Nat)
  | ExposedCKs (s: SessionInfo) (ck: Bytes) (n: UInt32) (rIdx: Nat)
  | ExposedCKr (s: SessionInfo) (ck: Bytes) (n: UInt32) (rIdx: Nat)
  | ExposedMK (s: SessionInfo) (seed: Bytes) (n: UInt32) (rIdx: Nat)
  | ExposedSpqr (s: SessionInfo) (spqr: Bytes) (rIdx: Nat)
  /-- Fresh DH ratchet key `dhs` generated at pre-step ratchet index `rIdx`. -/
  | HonestDH (s: SessionInfo) (dhs: Bytes) (rIdx: Nat)
  /-- Derived hybrid message keys `trMsgKeys pqSalt seed` for counter `n` at `rIdx` from snapshot
  `parentStateIdx`. -/
  | MessageKey (s: SessionInfo) (dir: KeyDir) (seed pqSalt: Bytes) (n: UInt32)
      (rIdx parentStateIdx: Nat)
  /-- Cached skipped message-key `seed` at counter `n` on `pk`'s receive chain. -/
  | SkippedKeyStored (s: SessionInfo) (pk: Bytes) (n: UInt32) (seed: Bytes) (rIdx: Nat)
      (sourceStateIdx: Nat)
  /-- Consumed and deleted the skipped key logged at `skippedKeyEventIdx`. -/
  | SkippedKeyUsed (s: SessionInfo) (skippedKeyEventIdx: Nat)

end Structures

public section Formats

variable [HasExecBytes]

public
instance RecvChain.ps: ParseableSerializeableNE RecvChain := .make <|
  .triviallyIsomorphic
    (.prod .slowBytes (.prod .slowBytes (.prod .uint32 .slowNat)))
    (fun (ratchetKey, chainKey, index, rIdx) => { ratchetKey, chainKey, index, rIdx })
    (fun { ratchetKey, chainKey, index, rIdx } => (ratchetKey, chainKey, index, rIdx))

instance: RecvChain.ps.mf.ParseConsumes := by
  dsimp only [ParseableSerializeableNE.mf]
  infer_instance

public
instance: ParseableSerializeable TRState := .make <|
  .triviallyIsomorphic
    (.prod .slowString (.prod .slowBytes (.prod .slowBytes (.prod .slowBytes (.prod .slowBytes
      (.prod .slowBytes (.prod .uint32 (.prod .uint32 (.prod .slowBytes (.prod .bool
      (.prod .slowNat (.prod .slowBytes (.list RecvChain.ps.mf)))))))))))))
    (fun (peer, myIk, peerIk, rk, dhs, cks, ns, pn, sid, initiator, rIdx, spqr, recv) =>
      { peer, myIk, peerIk, rk, dhs, cks, ns, pn, sid, initiator, rIdx, recv, spqr })
    (fun st => (st.peer, st.myIk, st.peerIk, st.rk, st.dhs, st.cks, st.ns, st.pn, st.sid,
      st.initiator, st.rIdx, st.spqr, st.recv))

end Formats

public section ExecTraceConfig

class HasExecTrace extends HasExecBytes where
  [traceExec: ExecTraceTypes]
  [traceExec0: ExecTraceTypes.Has Network.ExecEntryT]
  [traceExec1: ExecTraceTypes.Has Random.ExecEntryT]
  [traceExec2: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT TREvent)]
  [traceExec3: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TRState)]
  [attBase: BaseAttackerKnowledge]

attribute [reducible, scoped instance] HasExecTrace.traceExec HasExecTrace.traceExec0
  HasExecTrace.traceExec1 HasExecTrace.traceExec2 HasExecTrace.traceExec3 HasExecTrace.attBase

end ExecTraceConfig

@[expose] public section KeySchedule

variable [HasExecBytes]

open Literal Concat DiffieHellman KdfExtract

/-- `RootKey::create_chain` on a DH shared secret: expands `"WhisperRatchet"` from `hmac rk dhOut`
into `(newRk, newCk)`. -/
def kdfRk (rk dhOut: Bytes): Bytes × Bytes :=
  let prk := hmac rk dhOut
  (hkdfBlock1 prk (lit "WhisperRatchet"), hkdfBlock2 prk (lit "WhisperRatchet"))

/-- `RootKey::create_chain`: `kdfRk rk (agree theirPk ourSk)` (normalizing `theirPk`). -/
def createChain (rk theirPk ourSk: Bytes): Bytes × Bytes :=
  kdfRk rk (agree theirPk ourSk)

/-- Symmetric-ratchet step `(nextCk = hmac ck [0x02], seed = hmac ck [0x01])`. -/
def kdfCk (ck: Bytes): Bytes × Bytes :=
  (hmac ck (litByte 0x02), hmac ck (litByte 0x01))

/-- Advance symmetric chain key `ck` by `n` steps. -/
def chainKeyAt (ck: Bytes): Nat → Bytes
  | 0 => ck
  | n + 1 => chainKeyAt (kdfCk ck).1 n

/-- `seed` is derived from `ck` after `steps ≥ 0` symmetric-ratchet steps. -/
def DerivesMsgKey (ck seed: Bytes): Prop :=
  ∃ steps : Nat, seed = (kdfCk (chainKeyAt ck steps)).2

/-- Reflexive-transitive closure of DH-ratchet root-key updates `(createChain _ theirPk ourSk).1`. -/
inductive RootDescends (rk: Bytes): Bytes → Prop where
  | refl : RootDescends rk rk
  | step {rk' theirPk ourSk} :
      RootDescends rk rk' → RootDescends rk (createChain rk' theirPk ourSk).1

/-- `ck` is the chain-key output `(createChain rk' theirPk ourSk).2` of some root key `rk'`
descending from `rk`. -/
def DerivesChain (rk ck: Bytes): Prop :=
  ∃ rk' theirPk ourSk, RootDescends rk rk' ∧ ck = (createChain rk' theirPk ourSk).2

/-- `SignalMessage::compute_mac`: 8-byte truncated `HMAC(macKey, senderIk || receiverIk || wire)`. -/
def computeMac (macKey senderIk receiverIk wire: Bytes): Bytes :=
  Trunc.trunc8 (hmac macKey (concat senderIk (concat receiverIk wire)))

/-- `consts::MAX_RECEIVER_CHAINS`. -/
def maxReceiverChains: Nat := 5

/-- `consume_message_key`: rejects duplicate counters (`< c.index`), jumps exceeding
`maxForwardJumps`, and `u32Max`; otherwise returns `(seed, advancedChain)`. -/
def consumeMessageKey (c: RecvChain) (counter: UInt32): Option (Bytes × RecvChain) :=
  if counter < c.index then none
  else if counter.toNat - c.index.toNat > maxForwardJumps then none
  else if counter = u32Max then none
  else
    let ck := chainKeyAt c.chainKey (counter.toNat - c.index.toNat)
    some ((kdfCk ck).2, { c with chainKey := (kdfCk ck).1, index := counter + 1 })

def findRecvChain (recv: List RecvChain) (theirPk: Bytes): Option RecvChain :=
  recv.find? (·.ratchetKey == theirPk)

def setRecvChain (recv: List RecvChain) (c: RecvChain): List RecvChain :=
  recv.map fun c' => if c'.ratchetKey == c.ratchetKey then c else c'

/-- Append `c` and drop the oldest chain if the list exceeds `maxReceiverChains`. -/
def pushRecvChain (recv: List RecvChain) (c: RecvChain): List RecvChain :=
  (recv ++ [c]).drop ((recv.length + 1) - maxReceiverChains)

/-- Receiving half of `dh_ratchet_step`: rejects low-order `theirPk`, otherwise computes
`createChain st.rk theirPk st.dhs` at `rIdx := st.rIdx + 2`. -/
def recvHalfStep (st: DRState) (theirPk: Bytes): Option (Bytes × RecvChain) :=
  if x25519LowOrder theirPk then none
  else
    let (rk1, ckr) := createChain st.rk theirPk st.dhs
    some (rk1, { ratchetKey := theirPk, chainKey := ckr, index := 0, rIdx := st.rIdx + 2 })

/-- Message-key seeds skipped when `c` advances to `counter`. -/
def skippedSeeds (c: RecvChain) (counter: UInt32): List Bytes :=
  (List.range (counter.toNat - c.index.toNat)).map fun j =>
    (kdfCk (chainKeyAt c.chainKey j)).2

def DRState.sessionInfo (st: DRState) (me: Participant): SessionInfo :=
  { sid := st.sid, initiator := st.initiator, me, peer := st.peer }

abbrev spqrA2B: Bytes := Spqr.encodeSpqrDirectionParams .a2b

abbrev spqrB2A: Bytes := Spqr.encodeSpqrDirectionParams .b2a

/-- `initialize_alice_session`: Alice's initial `TRState` from sending ratchet secret `dhsA`, Bob's
signed prekey `theirSpk`, and handshake outputs `(rk, ck, pqr)`. -/
def initAliceState (peer: Participant) (myIk peerIk dhsA theirSpk rk ck pqr: Bytes): TRState :=
  let (rkA, cksA) := createChain rk theirSpk dhsA
  { peer, myIk, peerIk, rk := rkA, dhs := dhsA, cks := cksA, ns := 0, pn := 0,
    sid := concat (dhPk dhsA) rk, initiator := true, rIdx := 1,
    recv := [{ ratchetKey := theirSpk, chainKey := ck, index := 0, rIdx := 1 }],
    spqr := Spqr.spqrInit pqr spqrA2B }

/-- `initialize_bob_session`: Bob's initial in-memory `TRState` before decrypting the opening
message. -/
def initBobState (peer: Participant) (myIk peerIk spkSk ratchetKey rk ck pqr: Bytes): TRState :=
  { peer, myIk, peerIk, rk, dhs := spkSk, cks := ck, ns := 0, pn := 0,
    sid := concat (X25519.normalizeX25519Key ratchetKey) rk, initiator := false, rIdx := 0,
    recv := [], spqr := Spqr.spqrInit pqr spqrB2A }

end KeySchedule

@[expose] public section TrWireFormat

variable [HasExecBytes]

/-- Canonical `SignalMessage::new` body (without trailing MAC). -/
def trHonestWireMsg (ratchetKey: Bytes) (counter previousCounter: UInt32)
    (ciphertext pqRatchet: Bytes) : Bytes :=
  TrWire.trWireMsg messageVersion ratchetKey counter previousCounter ciphertext pqRatchet
    TrWire.canonicalVariation

end TrWireFormat

@[expose] public section TrWireParse

variable [HasExecBytes]

open Concat

/-- `SignalMessage::try_from`: splits off the 8-byte MAC and decodes the `trWireMsg` header. -/
def parseTrSignalMsg (t: Bytes): Option TRSignalMsg := do
  let (wire, mac) ← split t (t.length - Trunc.trunc8Length)
  let x ← TrWire.trWireMsgFields? wire
  pure { wire, mac, version := x.version % 16, ratchetKey := x.senderRatchetKey,
         counter := x.counter, ciphertext := x.ciphertext, pqRatchet := x.pqRatchet }

end TrWireParse

@[expose] public section Specification

variable [HasExecTrace]

open DiffieHellman SymEnc
open PersistentLocalState (getLocalState storeLocalState)
open Network (sendMessage receiveMessage)
open Random (genRand)
open ProtocolEvent (logEvent)

/-- `dh_ratchet_step`: runs `recvHalfStep`, draws a fresh sending ratchet secret `dhs`, derives the
new sending chain, and pushes the new receiver chain (leaving `spqr` unchanged). -/
def dhRatchetStep (st: TRState) (theirPk: Bytes): Traceful (TRState × RecvChain) := do
  let some (rk1, c) := recvHalfStep st.toDRState theirPk | failure
  let dhs ← genRand 32
  let (rk2, cks) := createChain rk1 theirPk dhs
  let pn := if st.ns = 0 then 0 else st.ns - 1
  pure ({ st with rk := rk2, dhs, cks, ns := 0, pn, rIdx := st.rIdx + 2,
                  recv := pushRecvChain st.recv c }, c)

/-- `ensure_receiver_chain`: looks up `theirPk` in `st.recv`, or runs `dhRatchetStep` if absent. -/
def ensureReceiverChain (st: TRState) (theirPk: Bytes): Traceful (TRState × RecvChain × Bool) := do
  match findRecvChain st.recv theirPk with
  | some c => pure (st, c, false)
  | none =>
    let (st', c) ← dhRatchetStep st theirPk
    pure (st', c, true)

/-- Current trace length (index of the next appended entry). -/
def traceLength : Traceful Nat :=
  Traceful.mk fun tr => (some tr.length, ⟨tr, by grind⟩)

def logMessageKeyAndStore (me: Participant) (s: SessionInfo) (dir: KeyDir) (seed pqSalt: Bytes)
    (n: UInt32) (rIdx parentStateIdx: Nat) (st: TRState) : Traceful Nat := do
  logEvent (TREvent.MessageKey s dir seed pqSalt n rIdx parentStateIdx)
  storeLocalState me st

/-- `OutgoingTripleRatchet::encrypt`: draws a fresh 32-byte plaintext and `coinsLen` SPQR coins,
runs `spqrSend` and publishes its SPQR key, mixes `seed` with network term `pqIdx` via `trMsgKeys`,
stores the updated `TRState`, and sends `wire || mac`. -/
def messageEncrypt (me: Participant) (stateIdx coinsLen pqIdx: Nat) : Traceful Nat := do
  let st: TRState ← getLocalState me stateIdx
  guard (st.ns ≠ u32Max)
  let m ← genRand 32
  let coins ← genRand coinsLen
  let (spqr', key, pqMsg) := Spqr.spqrSend st.spqr coins
  let _ ← sendMessage key
  let (ck', seed) := kdfCk st.cks
  let pqSalt ← receiveMessage pqIdx
  let keys := trMsgKeys pqSalt seed
  let wire := trHonestWireMsg (dhPk st.dhs) st.ns st.pn (symEnc keys.cipherKey keys.iv m) pqMsg
  let mac := computeMac keys.macKey st.myIk st.peerIk wire
  logEvent (TREvent.Sent me st.peer (dhPk st.dhs) st.ns m)
  let _ ← logMessageKeyAndStore me (st.sessionInfo me) .sender seed pqSalt st.ns st.rIdx stateIdx { st with cks := ck', ns := st.ns + 1, spqr := spqr' }
  sendMessage (Concat.concat wire mac)

/-- Aborted `message_encrypt` that draws its plaintext randomness before failing. -/
def messageEncryptAbort (me: Participant) (stateIdx: Nat) : Traceful Nat := do
  let _st: TRState ← getLocalState me stateIdx
  let _ ← genRand 32
  failure

def logSkippedKeys (s: SessionInfo) (pk: Bytes) (rIdx sourceStateIdx: Nat) :
    Bytes → UInt32 → Nat → Traceful Unit
  | _, _, 0 => pure ()
  | ck, n, k + 1 => do
    logEvent (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx)
    logSkippedKeys s pk rIdx sourceStateIdx (kdfCk ck).1 (n + 1) k

def receiveSignalMsg (msgIdx: Nat) : Traceful TRSignalMsg := do
  let some msg := parseTrSignalMsg (← receiveMessage msgIdx) | failure
  guard (msg.version = messageVersion)
  pure msg

def verifyMacAndDecrypt (st: TRState) (msg: TRSignalMsg) (pqSalt seed: Bytes) :
    Traceful Bytes := do
  let keys := trMsgKeys pqSalt seed
  guard (msg.mac = computeMac keys.macKey st.peerIk st.myIk msg.wire)
  symDec keys.cipherKey keys.iv msg.ciphertext

/-- Uncommitted output of `decryptInMemory`, shared by `messageDecrypt` and `Composed.bobStart`. -/
structure PendingDecrypt where
  st: TRState
  msg: TRSignalMsg
  c: RecvChain
  c': RecvChain
  ratcheted: Bool
  spqr': Bytes
  pqSalt: Bytes
  seed: Bytes
  plaintext: Bytes

/-- In-memory decryption (`try_decrypt_from_record`): runs `ensureReceiverChain`,
`consumeMessageKey`, `spqrRecv` (publishing its SPQR key), and `verifyMacAndDecrypt` under salt
`pqIdx`, without logging events or storing state. -/
def decryptInMemory (st0: TRState) (msg: TRSignalMsg) (pqIdx: Nat) (spqrMsgIdx: UInt32) :
    Traceful PendingDecrypt := do
  let (st, c, ratcheted) ← ensureReceiverChain st0 msg.ratchetKey
  let some (seed, c') := consumeMessageKey c msg.counter | failure
  let some (spqr', key) := Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx | failure
  let _ ← sendMessage key
  let pqSalt ← receiveMessage pqIdx
  let plaintext ← verifyMacAndDecrypt st msg pqSalt seed
  pure { st, msg, c, c', ratcheted, spqr', pqSalt, seed, plaintext }

def PendingDecrypt.logRatchet (p: PendingDecrypt) (me: Participant) : Traceful Unit := do
  if p.ratcheted then
    logEvent (TREvent.DHRatchet me p.st.peer p.msg.ratchetKey (dhPk p.st.dhs))
    logEvent (TREvent.HonestDH (p.st.sessionInfo me) p.st.dhs (p.st.rIdx - 2))

/-- Commit skipped-key events, `Received`, `MessageKey (.receiver)`, and the updated `TRState` for
`p`. When `parentStateIdx = none` (`Composed.bobStart`), lineage points to the newly stored snapshot
itself. -/
def PendingDecrypt.commit (p: PendingDecrypt) (me: Participant)
    (parentStateIdx: Option Nat := none) : Traceful Nat := do
  let s := p.st.sessionInfo me
  let skipped := p.msg.counter.toNat - p.c.index.toNat
  let commitTail (lineageIdx: Nat) : Traceful Nat := do
    logSkippedKeys s p.msg.ratchetKey p.c.rIdx lineageIdx p.c.chainKey p.c.index skipped
    logEvent (TREvent.Received me p.st.peer p.msg.ratchetKey p.msg.counter p.plaintext)
    logMessageKeyAndStore me s .receiver p.seed p.pqSalt p.msg.counter p.c.rIdx
      lineageIdx { p.st with recv := setRecvChain p.st.recv p.c', spqr := p.spqr' }
  match parentStateIdx with
  | some idx => commitTail idx
  | none => do commitTail ((← traceLength) + skipped + 2)

/-- `TripleRatchet::decrypt` on a stored session snapshot. -/
def messageDecrypt (me: Participant) (stateIdx msgIdx pqIdx: Nat) (spqrMsgIdx: UInt32) :
    Traceful Nat := do
  let st: TRState ← getLocalState me stateIdx
  let msg ← receiveSignalMsg msgIdx
  let pending ← decryptInMemory st msg pqIdx spqrMsgIdx
  pending.logRatchet me
  pending.commit me (some stateIdx)

/-- Leak a single key component (`rk`, `dhs`, `cks`, or `ckr pk`) from snapshot `stateIdx`. -/
def exposeKey (me: Participant) (stateIdx: Nat) (k: KeyComponent) : Traceful Nat := do
  let st: TRState ← getLocalState me stateIdx
  match k with
  | .rk =>
    logEvent (TREvent.ExposedRK (st.sessionInfo me) st.rk st.rIdx)
    sendMessage st.rk
  | .dhs =>
    logEvent (TREvent.ExposedDHs (st.sessionInfo me) st.dhs st.rIdx)
    sendMessage st.dhs
  | .cks =>
    logEvent (TREvent.ExposedCKs (st.sessionInfo me) st.cks st.ns st.rIdx)
    sendMessage st.cks
  | .ckr pk =>
    let some c := findRecvChain st.recv pk | failure
    logEvent (TREvent.ExposedCKr (st.sessionInfo me) c.chainKey c.index c.rIdx)
    sendMessage c.chainKey

/-- Leak the serialized SPQR state `st.spqr` from snapshot `stateIdx`. -/
def exposeSpqr (me: Participant) (stateIdx: Nat) : Traceful Nat := do
  let st: TRState ← getLocalState me stateIdx
  logEvent (TREvent.ExposedSpqr (st.sessionInfo me) st.spqr st.rIdx)
  sendMessage st.spqr

def skippedKeyUsedB (tr: ExecTrace) (skippedKeyEventIdx: Nat) : Bool :=
  anyEventOnTrace TREvent tr fun
    | .SkippedKeyUsed _ skippedKeyEventIdx' => skippedKeyEventIdx' == skippedKeyEventIdx
    | _ => false

def receiverKeyUsedB (tr: ExecTrace) (s: SessionInfo) (seed: Bytes) (n: UInt32) (rIdx: Nat) :
    Bool :=
  anyEventOnTrace TREvent tr fun
    | .MessageKey s' .receiver seed' _ n' rIdx' _ =>
      decide (s' = s ∧ seed' = seed ∧ n' = n ∧ rIdx' = rIdx)
    | _ => false

/-- Leak an unconsumed cached skipped message-key seed logged at `skippedKeyEventIdx`. -/
def exposeSkipped (skippedKeyEventIdx: Nat) : Traceful Nat := do
  let e: ProtocolEvent.ExecEntryT TREvent ← getEntry skippedKeyEventIdx
  let .SkippedKeyStored s _ n seed rIdx _ := e.ev | failure
  guardTrace fun tr => !receiverKeyUsedB tr s seed n rIdx
  logEvent (TREvent.ExposedMK s seed n rIdx)
  sendMessage seed

/-- Decrypt an out-of-order message using the unconsumed skipped seed at `skippedKeyEventIdx`
(while `pk` remains in `st.recv`), advancing `st.spqr` via `spqrRecv`. -/
def messageDecryptSkipped (me: Participant) (stateIdx msgIdx skippedKeyEventIdx pqIdx: Nat)
    (spqrMsgIdx: UInt32) : Traceful Nat := do
  let st: TRState ← getLocalState me stateIdx
  let msg ← receiveSignalMsg msgIdx
  let e: ProtocolEvent.ExecEntryT TREvent ← getEntry skippedKeyEventIdx
  let .SkippedKeyStored s pk n seed rIdx _sourceStateIdx := e.ev | failure
  guard (s = st.sessionInfo me ∧ pk = msg.ratchetKey ∧ n = msg.counter ∧
    (findRecvChain st.toDRState.recv pk).isSome)
  guardTrace fun tr => !skippedKeyUsedB tr skippedKeyEventIdx
  let some (spqr', key) := Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx | failure
  let _ ← sendMessage key
  let pqSalt ← receiveMessage pqIdx
  let m ← verifyMacAndDecrypt st msg pqSalt seed
  logEvent (TREvent.SkippedKeyUsed s skippedKeyEventIdx)
  logEvent (TREvent.Received me st.peer pk n m)
  logMessageKeyAndStore me s .receiver seed pqSalt n rIdx stateIdx { st with spqr := spqr' }

/-- Whether `stateIdx` holds the latest stored `TRState` snapshot for its `(participant, initiator)`
pair on `tr`. -/
def isCurrentSnapshot (tr : ExecTrace) (stateIdx : Nat) : Bool :=
  match getStoredLocalStateAt? TRState tr stateIdx with
  | some st =>
    (List.range' (stateIdx + 1) (tr.length - (stateIdx + 1))).all fun j =>
      match getStoredLocalStateAt? TRState tr j with
      | some st' => st'.participant != st.participant ||
          st'.state.initiator != st.state.initiator
      | none => true
  | none => false

/-- Whether `skIdx` logs a `SkippedKeyStored s pk ..` event whose chain `pk` still resides in a
current snapshot of session `s`. -/
def isSkippedChainCurrent (tr : ExecTrace) (skIdx : Nat) : Bool :=
  match tr.getEventAt TREvent skIdx with
  | some (.SkippedKeyStored s pk ..) =>
    (List.range tr.length).any fun stateIdx =>
      isCurrentSnapshot tr stateIdx &&
      match (tr.at? stateIdx : Option (PersistentGlobalState.State.ExecEntryT
          (PersistentLocalState.LocalState TRState))) with
      | some e =>
        decide (e.st.participant = s.me ∧ e.st.state.sessionInfo s.me = s) &&
          (findRecvChain e.st.state.toDRState.recv pk).isSome
      | none => false
  | _ => false

end Specification

public section Reachability

variable [HasExecTrace]

@[expose] public section
def messageEncrypt.reachability: ReachabilityConfig where
  Input := Participant × Nat × Nat × Nat
  PreCond := fun (_, stateIdx, _, _) tr => isCurrentSnapshot tr stateIdx = true
  step := fun (me, stateIdx, coinsLen, pqIdx) => ⟨_, messageEncrypt me stateIdx coinsLen pqIdx⟩
def messageEncryptAbort.reachability: ReachabilityConfig where
  Input := Participant × Nat
  PreCond := fun (_, stateIdx) tr => isCurrentSnapshot tr stateIdx = true
  step := fun (me, stateIdx) => ⟨_, messageEncryptAbort me stateIdx⟩
def messageDecrypt.reachability: ReachabilityConfig where
  Input := Participant × Nat × Nat × Nat × UInt32
  PreCond := fun (_, stateIdx, _, _, _) tr => isCurrentSnapshot tr stateIdx = true
  step := fun (me, stateIdx, msgIdx, pqIdx, spqrMsgIdx) =>
    ⟨_, messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx⟩
def messageDecryptSkipped.reachability: ReachabilityConfig where
  Input := Participant × Nat × Nat × Nat × Nat × UInt32
  PreCond := fun (_, stateIdx, _, _, _, _) tr => isCurrentSnapshot tr stateIdx = true
  step := fun (me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx) =>
    ⟨_, messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx⟩
def exposeKey.reachability: ReachabilityConfig :=
  .make (fun (me, stateIdx, k) => exposeKey me stateIdx k)
def exposeSpqr.reachability: ReachabilityConfig :=
  .make (fun (me, stateIdx) => exposeSpqr me stateIdx)
def exposeSkipped.reachability: ReachabilityConfig :=
  .make (fun skippedKeyEventIdx => exposeSkipped skippedKeyEventIdx)
end

end Reachability

end DY.Libsignal.TripleRatchet
