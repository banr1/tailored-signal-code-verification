/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.RecordCodecs.Proto
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession

/-!
# Key and Identity-Key-Pair Codecs for `libsignal-cli` File Stores

**Checked by Lean.** Machine-free models of libsignal v0.105.4's `PrivateKey` (`deserializePrivateKey`,
`serializePrivateKey`), `IdentityKey::decode` (`decodeIdentityKey`), and `IdentityKeyPair`
(`IdentityKeyPair.tryFrom`, `IdentityKeyPair.serialize`), extending the protobuf codecs in
`RecordCodecs/Proto.lean`.
-/

@[expose] public section

namespace CryptoVerification.RecordCodecs

open CryptoGames CryptoGames.LibsignalSession CryptoVerification.LibsignalProtoCodec

/-! ## Keys (`L/core/src/curve.rs`, `L/protocol/src/identity_key.rs`) -/

/-- `PrivateKey::deserialize` (`L/core/src/curve.rs:242–250`): exactly 32 bytes
(`BadKeyLength(Djb, len)` otherwise), then `scalar::clamp_integer`. -/
def deserializePrivateKey (bs : List (BitVec 8)) : Except SignalProtocolError PrivateKey :=
  if h : bs.length = 32 then .ok ⟨Ratchet.clampScalar ⟨bs, h⟩⟩
  else .error (.badKeyLength bs.length)

/-- `PrivateKey::serialize` (`L/core/src/curve.rs:253–257`): the 32 stored bytes. -/
def serializePrivateKey (k : PrivateKey) : List (BitVec 8) := k.bytes.toList

/-- `IdentityKey::decode` (`L/protocol/src/identity_key.rs:52–55`) = `PublicKey::try_from`
= `PublicKey::deserialize`: type byte `0x05` and at least 32 key bytes, trailing bytes ignored. -/
def decodeIdentityKey (bs : List (BitVec 8)) : Except SignalProtocolError IdentityKey :=
  (PublicKey.deserialize bs).map IdentityKey.mk

/-- `IdentityKeyPair { identity_key, private_key }` (`L/protocol/src/identity_key.rs:111–114`). -/
structure IdentityKeyPair where
  /-- The public identity key. -/
  identityKey : IdentityKey
  /-- The private key. -/
  privateKey : PrivateKey
  deriving DecidableEq

/-- `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` (`L/protocol/src/identity_key.rs:181–192`):
decode (`InvalidProtobufEncoding` on any decode error), then the public key, then the private
key, in this order. -/
def IdentityKeyPair.tryFrom (bs : List (BitVec 8)) :
    Except SignalProtocolError IdentityKeyPair :=
  match IdentityKeyPairStructure.decode bs with
  | none => .error .invalidProtobufEncoding
  | some s => do
    let ik ← decodeIdentityKey s.publicKey
    let sk ← deserializePrivateKey s.privateKey
    pure ⟨ik, sk⟩

/-- `IdentityKeyPair::serialize` (`L/protocol/src/identity_key.rs:154–162`). -/
def IdentityKeyPair.serialize (kp : IdentityKeyPair) : List (BitVec 8) :=
  IdentityKeyPairStructure.encode
    ⟨kp.identityKey.serialize, serializePrivateKey kp.privateKey⟩

end CryptoVerification.RecordCodecs
