/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.StateXModel
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi

/-!
# Proof-Side `RecordExtras` Scope Definitions

Defines `seedRecordExtras` and `FixedIdRecordExtras` over `RecordExtras` from
`LibsignalBinary/Specifications/LibsignalE2E/StateXModel.lean`.
-/

@[expose] public section

namespace CryptoVerification.E2E
open CryptoGames CryptoGames.LibsignalSession CryptoVerification.LibsignalProtoCodec

/-- The constant extras that `encodeRecord` (`State.lean`) writes, the same for both parties:
pending pre-key `{pre_key_id: none, signed_pre_key_id: 0, base_key: 0x05 ‖ 0^32, timestamp: 0}`,
no Kyber pre-key, registration ids 0, empty `alice_base_key`. -/
def seedRecordExtras : Party → RecordExtras := fun _ =>
  { pending := { preKeyId := none, signedPreKeyId := 0#32, baseKey := placeholderBaseKey,
                 timestamp := 0#64 }
    kyber := none
    remoteRegistrationId := 0#32
    localRegistrationId := 0#32
    aliceBaseKey := [] }

/-- A restricted scope of one party's extras (fixed ids, bounded lengths): registration ids 0,
no one-time pre-key, signed pre-key id 0, timestamp 0, a Kyber pre-key (if any) with id 0 and a
ciphertext shorter than `2^16` bytes, and an `alice_base_key` shorter than `2^16` bytes. The base
key is arbitrary. -/
def FixedIdRecordExtras (x : RecordExtras) : Prop :=
  x.remoteRegistrationId = 0 ∧ x.localRegistrationId = 0 ∧
  x.pending.preKeyId = none ∧ x.pending.signedPreKeyId = 0 ∧ x.pending.timestamp = 0 ∧
  (∀ k, x.kyber = some k → k.preKeyId = 0 ∧ k.ciphertext.length < 2 ^ 16) ∧
  x.aliceBaseKey.length < 2 ^ 16

end CryptoVerification.E2E
