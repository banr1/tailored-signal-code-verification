/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhCorrectModel
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
public import LibsignalBinary.Specifications.LibsignalE2E.StateXModel
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Init

/-!
# Proof-Side PQXDH End-to-End Model Definitions

Helper definitions (`pqxdhSpqrModel`, `preKeyStoreEventsBytes`, `recvPrekeyModel`) extending
`LibsignalBinary/Specifications/LibsignalE2E/PqxdhCorrectModel.lean`.
-/

@[expose] public section

set_option autoImplicit false
namespace CryptoVerification.E2E
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalAesCbc (toLEBytes)

/-- The V1 SPQR model (`LibsignalSpqrV1.spqrV1`) at `W`'s SHA-256 compression function `W.C.F`
and ML-KEM-768 primitives `W.Q.K`. -/
def pqxdhSpqrModel (W : PEParams) : LibsignalTripleRatchet.SpqrModel :=
  LibsignalSpqrV1.spqrV1 W.C.F W.Q.K

/-- The 47-byte events header that `recvPrekeyModel` puts before the plaintext after a
successful `message_decrypt_prekey` on `m`. It records one
`mark_kyber_pre_key_used(kpk_id, spk_id, base_key)` call, then `remove_pre_key(opk_id)` if a
one-time pre-key was used. -/
def preKeyStoreEventsBytes (m : PreKeyMessageFields) : List (BitVec 8) :=
  1#8 :: toLEBytes 4 m.kpkId ++ toLEBytes 4 m.spkId ++ djbKey m.baseKey ++
    (match m.opkId with
     | some i => 1#8 :: toLEBytes 4 i
     | none => 0#8 :: toLEBytes 4 (0#32))

/-- Bob's pre-key `recv` outcome as bytes: `recvPrekeyState`'s, with the record
`encodeRecordUnderExtras` of its state under its extras and the message part `preKeyStoreEventsBytes m ‖ plaintext`. -/
def recvPrekeyModel (X : UnreachedPqxdhPrimitives) (W : PEParams) (P : Party) (me : LocalIdentity) (k : ResponderPreKeySecrets)
    (m : PreKeyMessageFields) (rc : BitVec 256) : Option (Option (Bytes × Bytes)) :=
  (recvPrekeyState X W P me k m rc).map
    (Option.map fun (x, g, pt) => (encodeRecordUnderExtras (fun _ => x) g, preKeyStoreEventsBytes m ++ pt))

end CryptoVerification.E2E
