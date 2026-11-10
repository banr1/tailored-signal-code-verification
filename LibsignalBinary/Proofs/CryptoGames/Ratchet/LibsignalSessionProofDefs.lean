/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.LibsignalSignalMessage

/-!
# Proof-Side Definitions and Lemmas for `LibsignalSession`

All-or-nothing error preservation lemmas, raw-wire `messageDecrypt`, and wire `(ser, tag)` splitting.
-/

@[expose] public section

namespace CryptoGames
namespace LibsignalSession
open HMAC HKDF CBC LibsignalAead
namespace SessionState

/-- A failed `try_decrypt_from_record` leaves the session record unchanged. -/
theorem tryDecryptFromRecord_error {PQ PQC : Type} [Inhabited PQ] (C : Crypto)
    (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (record : SessionState PQ) (e : SignalProtocolError)
    (h : (tryDecryptFromRecord C spqr expected ciphertext msgType coins record).1 = .error e) :
    (tryDecryptFromRecord C spqr expected ciphertext msgType coins record).2 = record := by
  unfold tryDecryptFromRecord at h ⊢
  split
  · rfl
  · split <;> simp_all

/-- `message_decrypt_signal` decryption on raw wire bytes (`SignalMessage::try_from` followed by
`try_decrypt_from_record` with `msg_type = Whisper`, omitting identity-trust and store steps). -/
def messageDecrypt {PQ PQC : Type} [Inhabited PQ] (C : Crypto) (codec : SignalMessageProtoCodec)
    (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (wire : List (BitVec 8)) (coins : BitVec 256)
    (record : SessionState PQ) :
    Except SignalProtocolError (List (BitVec 8)) × SessionState PQ :=
  match SignalMessage.tryFrom codec wire with
  | .error e => (.error e, record)
  | .ok m => tryDecryptFromRecord C spqr expected m .whisper coins record

/-- A failed `message_encrypt` leaves the session record unchanged. -/
theorem messageEncrypt_error {PQ PQC : Type} [Inhabited PQ] (C : Crypto) (codec : SignalMessageProtoCodec)
    (spqr : Spqr PQ PQC)
    (addresses : Option (List (BitVec 8))) (ptext : List (BitVec 8)) (coins : PQC)
    (record : SessionState PQ) (e : SignalProtocolError)
    (h : (messageEncrypt C codec spqr addresses ptext coins record).1 = .error e) :
    (messageEncrypt C codec spqr addresses ptext coins record).2 = record := by
  unfold messageEncrypt at h ⊢
  split
  · rfl
  · split <;> simp_all

end SessionState

/-- Splits a serialized `SignalMessage` into the prefix before the MAC and the 8-byte MAC as a
little-endian `BitVec 64`. -/
def SignalMessage.wire (m : SignalMessage) : List (BitVec 8) × BitVec 64 :=
  (m.serialized.take (m.serialized.length - macLength),
    bytesToWord64LE (m.serialized.drop (m.serialized.length - macLength)))

end LibsignalSession
end CryptoGames
