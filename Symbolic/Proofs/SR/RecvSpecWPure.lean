/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SR.ModelW
import Symbolic.Proofs.Refinement.RngFree.SpecsPure -- shake: keep

/-!
# Record- and API-level whole-message AES decryption

Lifts `SessionState.tryDecryptFromRecordW` to `SessionRecord` (`SessionRecord.tryDecryptFromRecordW`)
and the store-backed public API (`messageDecryptSignalW`).
-/

@[expose] public section

set_option autoImplicit false

namespace Proofs.libsignal.SR

open CryptoVerification
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Proofs.libsignal.Refinement.RngFree

def SessionRecord.tryDecryptFromRecordW {PQ PQC : Type} [Inhabited PQ] (C : Crypto) (W : AesW)
    (spqr : Spqr PQ PQC) (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage)
    (coins : BitVec 256) (record : SessionRecord PQ) :
    Except SignalProtocolError (List (BitVec 8) × SessionRecord PQ) :=
  match record.currentSession with
  | none => .error (.invalidMessage .whisper .decryptionFailed)
  | some session =>
    match SessionState.tryDecryptFromRecordW C W spqr expected ciphertext .whisper coins
        session.state with
    | (.ok ptext, state) =>
      let updated : Session PQ :=
        { session with state := state, pendingPreKey := none, pendingKyberPreKey := none }
      .ok (ptext, { currentSession := some updated })
    | (.error e, _) => .error e

def messageDecryptSignalW {Addr PQ PQC E : Type} [Inhabited PQ] (C : Crypto) (W : AesW)
    (spqr : Spqr PQ PQC)
    (serializeAddresses : Addr → Addr → Option (List (BitVec 8)))
    (answers : StoreAnswers PQ E) (ciphertext : SignalMessage) (remoteAddress localAddress : Addr)
    (coins : BitVec 256) :
    Except (ApiError Addr E) (List (BitVec 8)) × List (StoreCall Addr PQ) := Api.run do
  let some record ← storeCall (.loadSession remoteAddress) answers.loadSession
    | throw (.sessionNotFound remoteAddress "message_decrypt_signal")
  let (ptext, record) ← liftProtocol (SessionRecord.tryDecryptFromRecordW C W spqr
    (serializeAddresses remoteAddress localAddress) ciphertext coins record)
  let some session := record.currentSession | throw .panic
  let some theirIdentityKey := session.state.remoteIdentity | throw .panic
  let trusted ← storeCall (.isTrustedIdentity remoteAddress theirIdentityKey .receiving)
    answers.isTrustedIdentity
  if !trusted then throw (.untrustedIdentity remoteAddress)
  let _ ← storeCall (.saveIdentity remoteAddress theirIdentityKey) answers.saveIdentity
  storeCall (.storeSession remoteAddress record) answers.storeSession
  return ptext

end Proofs.libsignal.SR
