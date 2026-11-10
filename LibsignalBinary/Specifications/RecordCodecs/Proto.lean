/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSignalMessage

/-!
# Protobuf Record Codecs for Identity and Pre-Key Stores

**Trusted in part.** `SignalSession/PqDir.lean` (`encodeDir`) encodes identity and pre-key store
files with `IdentityKeyPairStructure`, `SignedPreKeyRecordStructure`, and `PreKeyRecordStructure`
(`encode`) via `encodeProto3BytesField`, `encodeProto3Uint32Field`, `encodeProto3Fixed64Field`, and
`le64Bytes`; the decoders (`empty`, `mergeField`, `decode`, `decodeFieldsLoop`, `skipUnknown`,
`mergeFixed64`, `le64`) and record wrappers (`PreKeyRecord`, `SignedPreKeyRecord`,
`KyberPreKeyRecord`, `deserialize`, `serialize`) are checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Models `prost` 0.14.4's proto3 encoders (tag-ordered fields, omitting default `0` / empty values)
and decoders (`Message::merge` from default with last-write-wins field merging and unknown-field
skipping up to recursion limit 100) for `storage.proto` messages.
-/

@[expose] public section

namespace CryptoVerification.RecordCodecs

open CryptoGames.LibsignalSession CryptoVerification.LibsignalProtoCodec

/-! ## The decode loop for proto3 messages -/

/-- The `while buf.has_remaining()` loop of `Message::merge` (`P/message.rs:126–136`) for a
message type with fields `M` and generated `merge_field` `mergeField`: decode a key, merge the
field, repeat. `fuel` = the input length suffices (each round consumes at least the key byte). -/
def decodeFieldsLoop {M : Type} (mergeField : M → ℕ → WireType → List (BitVec 8) →
    Option (M × List (BitVec 8))) : ℕ → M → List (BitVec 8) → Option M
  | _, m, [] => some m
  | 0, _, _ :: _ => none                                     -- unreachable with fuel = length
  | fuel + 1, m, bs@(_ :: _) =>
    match decodeKey bs with
    | none => none
    | some ((tag, wt), rest) =>
      match mergeField m tag wt rest with
      | none => none
      | some (m', rest') => decodeFieldsLoop mergeField fuel m' rest'

/-- An unknown field: `skip_field(wire_type, tag, buf, ctx)` with the default context
(`P/encoding.rs:166–199`), the message unchanged. -/
def skipUnknown {M : Type} (m : M) (tag : ℕ) (wt : WireType) (bs : List (BitVec 8)) :
    Option (M × List (BitVec 8)) :=
  (skipField (2 * bs.length + 2) recursionLimit tag wt bs).map fun r => (m, r)

/-! ## `fixed64` (`fixed_width!`, `P/encoding.rs:376–403, 497–504`) -/

/-- `Buf::get_u64_le` on the first 8 bytes `b₀ … b₇` (`b₀` least significant). -/
def le64 (b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : BitVec 8) : BitVec 64 :=
  BitVec.ofNat 64 (b₀.toNat + 2 ^ 8 * b₁.toNat + 2 ^ 16 * b₂.toNat + 2 ^ 24 * b₃.toNat +
    2 ^ 32 * b₄.toNat + 2 ^ 40 * b₅.toNat + 2 ^ 48 * b₆.toNat + 2 ^ 56 * b₇.toNat)

/-- `BufMut::put_u64_le`: the 8 little-endian bytes of `v`. -/
def le64Bytes (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
    v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8]

/-- `fixed64::merge` (`P/encoding.rs:391–403`): wire type `SixtyFourBit`, at least 8 bytes
(`BufferUnderflow` otherwise), then `get_u64_le`. -/
def mergeFixed64 (wt : WireType) (bs : List (BitVec 8)) : Option (BitVec 64 × List (BitVec 8)) :=
  if wt ≠ .sixtyFourBit then none                            -- UnexpectedWireType
  else match bs with
    | b₀ :: b₁ :: b₂ :: b₃ :: b₄ :: b₅ :: b₆ :: b₇ :: rest =>
      some (le64 b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇, rest)
    | _ => none                                              -- BufferUnderflow

/-! ## proto3 field encoders (omit the default value, `D/field/scalar.rs:119–126`) -/

/-- A proto3 `bytes` field: nothing when empty, else `bytes::encode(tag, value)`
(`P/encoding.rs:691–695`). -/
def encodeProto3BytesField (tag : ℕ) (v : List (BitVec 8)) : List (BitVec 8) :=
  if v = [] then [] else encodeBytesField tag (some v)

/-- A proto3 `uint32` field: nothing when `0`, else `uint32::encode(tag, value)`. -/
def encodeProto3Uint32Field (tag : ℕ) (v : BitVec 32) : List (BitVec 8) :=
  if v = 0 then [] else encodeUint32Field tag (some v)

/-- A proto3 `fixed64` field: nothing when `0`, else the key and `put_u64_le(value)`. -/
def encodeProto3Fixed64Field (tag : ℕ) (v : BitVec 64) : List (BitVec 8) :=
  if v = 0 then [] else encodeKey tag .sixtyFourBit ++ le64Bytes v

/-! ## `PreKeyRecordStructure` (`storage.proto:76–80`) -/

/-- `message PreKeyRecordStructure { uint32 id = 1; bytes public_key = 2; bytes private_key = 3; }`
(prost struct `proto::storage::PreKeyRecordStructure`). -/
structure PreKeyRecordStructure where
  /-- `uint32 id = 1`. -/
  id : BitVec 32
  /-- `bytes public_key = 2` (libsignal writes `PublicKey::serialize`, 33 bytes). -/
  publicKey : List (BitVec 8)
  /-- `bytes private_key = 3` (libsignal writes `PrivateKey::serialize`, 32 bytes). -/
  privateKey : List (BitVec 8)
  deriving DecidableEq, Repr

namespace PreKeyRecordStructure

/-- `PreKeyRecordStructure::default()`. -/
def empty : PreKeyRecordStructure := ⟨0, [], []⟩

/-- The derived `merge_field`. -/
def mergeField (m : PreKeyRecordStructure) (tag : ℕ) (wt : WireType) (bs : List (BitVec 8)) :
    Option (PreKeyRecordStructure × List (BitVec 8)) :=
  match tag with
  | 1 => (mergeUint32 wt bs).map fun (v, r) => ({ m with id := v }, r)
  | 2 => (mergeBytes wt bs).map fun (v, r) => ({ m with publicKey := v }, r)
  | 3 => (mergeBytes wt bs).map fun (v, r) => ({ m with privateKey := v }, r)
  | _ => skipUnknown m tag wt bs

/-- `<PreKeyRecordStructure as Message>::decode(&[u8])`; `none` = `Err(DecodeError)`. -/
def decode (bs : List (BitVec 8)) : Option PreKeyRecordStructure :=
  decodeFieldsLoop mergeField bs.length empty bs

/-- `<PreKeyRecordStructure as Message>::encode_to_vec`. -/
def encode (m : PreKeyRecordStructure) : List (BitVec 8) :=
  encodeProto3Uint32Field 1 m.id ++ encodeProto3BytesField 2 m.publicKey ++ encodeProto3BytesField 3 m.privateKey

end PreKeyRecordStructure

/-! ## `SignedPreKeyRecordStructure` (`storage.proto:82–88`) -/

/-- `message SignedPreKeyRecordStructure { uint32 id = 1; bytes public_key = 2;
bytes private_key = 3; bytes signature = 4; fixed64 timestamp = 5; }`. Both
`SignedPreKeyRecord` (X25519 keys) and `KyberPreKeyRecord` (KEM keys) store one. -/
structure SignedPreKeyRecordStructure where
  /-- `uint32 id = 1`. -/
  id : BitVec 32
  /-- `bytes public_key = 2`. -/
  publicKey : List (BitVec 8)
  /-- `bytes private_key = 3`. -/
  privateKey : List (BitVec 8)
  /-- `bytes signature = 4`. -/
  signature : List (BitVec 8)
  /-- `fixed64 timestamp = 5` (milliseconds since the epoch). -/
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace SignedPreKeyRecordStructure

/-- `SignedPreKeyRecordStructure::default()`. -/
def empty : SignedPreKeyRecordStructure := ⟨0, [], [], [], 0⟩

/-- The derived `merge_field`. -/
def mergeField (m : SignedPreKeyRecordStructure) (tag : ℕ) (wt : WireType)
    (bs : List (BitVec 8)) : Option (SignedPreKeyRecordStructure × List (BitVec 8)) :=
  match tag with
  | 1 => (mergeUint32 wt bs).map fun (v, r) => ({ m with id := v }, r)
  | 2 => (mergeBytes wt bs).map fun (v, r) => ({ m with publicKey := v }, r)
  | 3 => (mergeBytes wt bs).map fun (v, r) => ({ m with privateKey := v }, r)
  | 4 => (mergeBytes wt bs).map fun (v, r) => ({ m with signature := v }, r)
  | 5 => (mergeFixed64 wt bs).map fun (v, r) => ({ m with timestamp := v }, r)
  | _ => skipUnknown m tag wt bs

/-- `<SignedPreKeyRecordStructure as Message>::decode(&[u8])`; `none` = `Err(DecodeError)`. -/
def decode (bs : List (BitVec 8)) : Option SignedPreKeyRecordStructure :=
  decodeFieldsLoop mergeField bs.length empty bs

/-- `<SignedPreKeyRecordStructure as Message>::encode_to_vec`. -/
def encode (m : SignedPreKeyRecordStructure) : List (BitVec 8) :=
  encodeProto3Uint32Field 1 m.id ++ encodeProto3BytesField 2 m.publicKey ++ encodeProto3BytesField 3 m.privateKey ++
    encodeProto3BytesField 4 m.signature ++ encodeProto3Fixed64Field 5 m.timestamp

end SignedPreKeyRecordStructure

/-! ## `IdentityKeyPairStructure` (`storage.proto:90–93`) -/

/-- `message IdentityKeyPairStructure { bytes public_key = 1; bytes private_key = 2; }`. -/
structure IdentityKeyPairStructure where
  /-- `bytes public_key = 1`. -/
  publicKey : List (BitVec 8)
  /-- `bytes private_key = 2`. -/
  privateKey : List (BitVec 8)
  deriving DecidableEq, Repr

namespace IdentityKeyPairStructure

/-- `IdentityKeyPairStructure::default()`. -/
def empty : IdentityKeyPairStructure := ⟨[], []⟩

/-- The derived `merge_field`. -/
def mergeField (m : IdentityKeyPairStructure) (tag : ℕ) (wt : WireType) (bs : List (BitVec 8)) :
    Option (IdentityKeyPairStructure × List (BitVec 8)) :=
  match tag with
  | 1 => (mergeBytes wt bs).map fun (v, r) => ({ m with publicKey := v }, r)
  | 2 => (mergeBytes wt bs).map fun (v, r) => ({ m with privateKey := v }, r)
  | _ => skipUnknown m tag wt bs

/-- `<IdentityKeyPairStructure as Message>::decode(&[u8])`; `none` = `Err(DecodeError)`. -/
def decode (bs : List (BitVec 8)) : Option IdentityKeyPairStructure :=
  decodeFieldsLoop mergeField bs.length empty bs

/-- `<IdentityKeyPairStructure as Message>::encode_to_vec`. -/
def encode (m : IdentityKeyPairStructure) : List (BitVec 8) :=
  encodeProto3BytesField 1 m.publicKey ++ encodeProto3BytesField 2 m.privateKey

end IdentityKeyPairStructure

/-! ## The record types (`L/protocol/src/state/{prekey,signed_prekey,kyber_prekey}.rs`) -/

/-- `PreKeyRecord { pre_key: PreKeyRecordStructure }` (`L/protocol/src/state/prekey.rs:27–30`). -/
structure PreKeyRecord where
  /-- The stored protobuf structure. -/
  preKey : PreKeyRecordStructure
  deriving DecidableEq, Repr

/-- `PreKeyRecord::deserialize` (`L/protocol/src/state/prekey.rs:44–49`): any decode error is
`InvalidProtobufEncoding`; no field is checked. -/
def PreKeyRecord.deserialize (bs : List (BitVec 8)) : Except SignalProtocolError PreKeyRecord :=
  match PreKeyRecordStructure.decode bs with
  | none => .error .invalidProtobufEncoding
  | some s => .ok ⟨s⟩

/-- `PreKeyRecord::serialize` (`L/protocol/src/state/prekey.rs:70–72`, always `Ok`). -/
def PreKeyRecord.serialize (r : PreKeyRecord) : List (BitVec 8) := r.preKey.encode

/-- `SignedPreKeyRecord { signed_pre_key: SignedPreKeyRecordStructure }`
(`L/protocol/src/state/signed_prekey.rs:26–29`). -/
structure SignedPreKeyRecord where
  /-- The stored protobuf structure. -/
  signedPreKey : SignedPreKeyRecordStructure
  deriving DecidableEq, Repr

/-- `<SignedPreKeyRecord as GenericSignedPreKey>::deserialize`
(`L/protocol/src/state/signed_prekey.rs:80–88`). -/
def SignedPreKeyRecord.deserialize (bs : List (BitVec 8)) :
    Except SignalProtocolError SignedPreKeyRecord :=
  match SignedPreKeyRecordStructure.decode bs with
  | none => .error .invalidProtobufEncoding
  | some s => .ok ⟨s⟩

/-- `<SignedPreKeyRecord as GenericSignedPreKey>::serialize`
(`L/protocol/src/state/signed_prekey.rs:76–78`, always `Ok`). -/
def SignedPreKeyRecord.serialize (r : SignedPreKeyRecord) : List (BitVec 8) :=
  r.signedPreKey.encode

/-- `KyberPreKeyRecord { signed_pre_key: SignedPreKeyRecordStructure }`
(`L/protocol/src/state/kyber_prekey.rs:26–29`): the same structure as `SignedPreKeyRecord`, with
KEM keys in `public_key` / `private_key`. -/
structure KyberPreKeyRecord where
  /-- The stored protobuf structure. -/
  signedPreKey : SignedPreKeyRecordStructure
  deriving DecidableEq, Repr

/-- `<KyberPreKeyRecord as GenericSignedPreKey>::deserialize` (the provided method,
`L/protocol/src/state/signed_prekey.rs:80–88`). -/
def KyberPreKeyRecord.deserialize (bs : List (BitVec 8)) :
    Except SignalProtocolError KyberPreKeyRecord :=
  match SignedPreKeyRecordStructure.decode bs with
  | none => .error .invalidProtobufEncoding
  | some s => .ok ⟨s⟩

/-- `<KyberPreKeyRecord as GenericSignedPreKey>::serialize` (the provided method). -/
def KyberPreKeyRecord.serialize (r : KyberPreKeyRecord) : List (BitVec 8) :=
  r.signedPreKey.encode

end CryptoVerification.RecordCodecs
