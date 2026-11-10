/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi

/-!
# Whole-message AES session encrypt and decrypt model

Parameterizes the Triple Ratchet and `SessionState` encrypt and decrypt operations over an
abstract whole-message AES-256-CBC interface `AesW`, matching the binary's extern contracts, and
proves definitional agreement with the block-cipher CBC instance `cbcW`.
-/

@[expose] public section

namespace Proofs.libsignal.SR

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoGames.HMAC CryptoGames.HKDF CryptoGames.CBC CryptoGames.LibsignalAead

/-- Whole-message AES-256-CBC interface (`dec` returns `none` on bad ciphertext). -/
structure AesW where
  enc : AesKey → Block → List (BitVec 8) → List (BitVec 8)
  dec : AesKey → Block → List (BitVec 8) → Option (List (BitVec 8))

/-- Block-cipher CBC instance reproducing the `CryptoGames.LibsignalSession` operations. -/
def cbcW (C : Crypto) : AesW where
  enc := aesCbcEncrypt C.E
  dec := aesCbcDecrypt C.D

def TripleRatchet.decryptW {PQ PQC : Type} (C : Crypto) (W : AesW) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) : Mut (TripleRatchet PQ) (List (BitVec 8)) := do
  let their := ciphertext.senderRatchetKey
  let counter := ciphertext.counter
  let chainKey ← TripleRatchet.onRatchet (RatchetState.ensureReceiverChain C their coins)
  let messageKeyGen ←
    TripleRatchet.onRatchet (RatchetState.consumeMessageKey C.F their chainKey counter msgType)
  let t ← get
  if spqr.recvPanics t.pqrState ciphertext.pqRatchet then throw .panic
  let (newPqrState, pqrKey) ← match spqr.recv t.pqrState ciphertext.pqRatchet with
    | .ok r => pure r
    | .error true => throw .invalidState
    | .error false => throw (.invalidMessage msgType .pqRatchet)
  let messageKeys := messageKeyGen.generateKeys C.F pqrKey
  let macValid := ciphertext.verifyMacWithAddresses C.F expected t.remoteIdentityKey
    t.localIdentityKey messageKeys.macKey
  if !macValid then throw (.invalidMessage msgType .macFailed)
  let some ptext := W.dec messageKeys.cipherKey messageKeys.iv ciphertext.ciphertext
    | throw (.invalidMessage msgType .badCiphertext)
  modify fun t => { t with pqrState := newPqrState }
  return ptext

namespace SessionState

def tryDecryptWithStateW {PQ PQC : Type} [Inhabited PQ] (C : Crypto) (W : AesW)
    (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) : Mut (SessionState PQ) (List (BitVec 8)) := do
  let session ← TripleRatchet.fromSessionState
  let (r, session) :=
    Mut.exec (TripleRatchet.decryptW C W spqr expected ciphertext msgType coins) session
  let ptext ← liftE r
  modify fun s => (session.applyToSessionState s).clearUnacknowledgedPreKeyMessage
  return ptext

def tryDecryptFromRecordW {PQ PQC : Type} [Inhabited PQ] (C : Crypto) (W : AesW)
    (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (record : SessionState PQ) :
    Except SignalProtocolError (List (BitVec 8)) × SessionState PQ :=
  if record.version.toNat ≠ ciphertext.messageVersion.toNat then
    (.error (.invalidMessage msgType .decryptionFailed), record)
  else
    match Mut.exec (tryDecryptWithStateW C W spqr expected ciphertext msgType coins) record with
    | (.ok ptext, updated) => (.ok ptext, updated)
    | (.error e, _) => (.error (LibsignalSession.SessionState.recordError msgType e), record)

theorem tryDecryptFromRecordW_cbcW {PQ PQC : Type} [Inhabited PQ] (C : Crypto)
    (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (record : SessionState PQ) :
    tryDecryptFromRecordW C (cbcW C) spqr expected ciphertext msgType coins record =
      SessionState.tryDecryptFromRecord C spqr expected ciphertext msgType coins record := rfl

end SessionState

def OutgoingTripleRatchet.encryptW {PQ PQC : Type} (C : Crypto) (W : AesW) (codec : SignalMessageProtoCodec)
    (spqr : Spqr PQ PQC)
    (ptext : List (BitVec 8)) (addresses : Option (List (BitVec 8))) (coins : PQC) :
    Mut (OutgoingTripleRatchet PQ) SignalMessage := do
  let o ← get
  if spqr.sendPanics o.pqrState coins then throw .panic
  let some (newPqrState, pqrKey, pqrMsg) := spqr.send o.pqrState coins | throw .invalidState
  let messageKeys := (o.senderChainKey.messageKeys C.F).generateKeys C.F pqrKey
  let ctext := W.enc messageKeys.cipherKey messageKeys.iv ptext
  let message := SignalMessage.new C.F codec o.sessionVersion messageKeys.macKey addresses
    o.senderRatchetKey.publicKey o.senderChainKey.index o.previousCounter ctext
    o.localIdentityKey o.remoteIdentityKey pqrMsg
  let next ← liftE (o.senderChainKey.nextChainKey C.F)
  set { o with senderChainKey := next, pqrState := newPqrState }
  return message

namespace SessionState

def messageEncryptW {PQ PQC : Type} [Inhabited PQ] (C : Crypto) (W : AesW) (codec : SignalMessageProtoCodec)
    (spqr : Spqr PQ PQC)
    (addresses : Option (List (BitVec 8))) (ptext : List (BitVec 8)) (coins : PQC)
    (record : SessionState PQ) : Except SignalProtocolError SignalMessage × SessionState PQ :=
  match Mut.exec OutgoingTripleRatchet.fromSessionState record with
  | (.error e, _) => (.error e, record)
  | (.ok session, taken) =>
    match Mut.exec (OutgoingTripleRatchet.encryptW C W codec spqr ptext
        (record.encryptAddresses addresses) coins) session with
    | (.error e, _) => (.error e, record)
    | (.ok message, session) => (.ok message, session.applyToSessionState taken)

theorem messageEncryptW_cbcW {PQ PQC : Type} [Inhabited PQ] (C : Crypto) (codec : SignalMessageProtoCodec)
    (spqr : Spqr PQ PQC)
    (addresses : Option (List (BitVec 8))) (ptext : List (BitVec 8)) (coins : PQC)
    (record : SessionState PQ) :
    messageEncryptW C (cbcW C) codec spqr addresses ptext coins record =
      SessionState.messageEncrypt C codec spqr addresses ptext coins record := rfl

end SessionState

end Proofs.libsignal.SR
