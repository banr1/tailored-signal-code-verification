/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Data.Vector.Defs

/-!
# `SignalMessage` Wire Format and `prost` Protobuf Codec

**Trusted in part.** `Computational/Theorems/` uses every definition in this file except
`skipGroup`: wire parsing uses `SignalMessage` (`SignalMessage.tryFrom`), `SignalProtocolError`,
`PublicKey` (`PublicKey.deserialize`), `ProtoSignalMessage`, `SignalMessageProtoCodec`, and the
concrete `prost` 0.14.4 codec `protoSignalCodec` (`decodeVarint`, `decodeKey`, `skipField`,
`mergeField`, `decode`, `encodeVarint`, `encodeKey`, `encode`; DEV-LS21). See
`Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

namespace CryptoGames
namespace LibsignalSession

/-! ### Constants (`protocol.rs`) -/

/-- `CIPHERTEXT_MESSAGE_CURRENT_VERSION = 4` (`protocol.rs:19`). -/
def currentVersion : BitVec 8 := 4

/-- `CIPHERTEXT_MESSAGE_PRE_KYBER_VERSION = 3` (`protocol.rs:21`). -/
def preKyberVersion : BitVec 8 := 3

/-- `SignalMessage::MAC_LENGTH = 8` (`protocol.rs:76`). -/
def macLength : ℕ := 8

/-! ### Errors (`error.rs`, restricted to what this model produces) -/

/-- `CiphertextMessageType` (`protocol.rs:32–40`), restricted to the two double-ratchet types; it
is carried by `InvalidMessage` errors only. -/
inductive MessageType where
  | whisper
  | preKey
  deriving DecidableEq, Repr

/-- The reason of an `InvalidMessage` error (upstream: a `String`). -/
inductive InvalidMessageReason where
  /-- "message from too far into the future" (`double_ratchet.rs:232–235`). -/
  | tooFarInFuture
  /-- "post-quantum ratchet error" from `spqr::recv` (`triple_ratchet.rs:247–250`). -/
  | pqRatchet
  /-- "MAC verification failed" (`triple_ratchet.rs:264–269`). -/
  | macFailed
  /-- "failed to decrypt" (`BadCiphertext`, `triple_ratchet.rs:286–291`). -/
  | badCiphertext
  /-- "decryption failed": every session of the record failed (`session_management.rs:451–454,
  551–554`). -/
  | decryptionFailed
  deriving DecidableEq, Repr

/-- The reason of an `InvalidSessionStructure` error that the typed model can still produce. -/
inductive InvalidSessionReason where
  /-- "missing sender chain" (`double_ratchet.rs:279`, `state/session.rs:244, 256, 398`). -/
  | missingSenderChain
  /-- "missing receiver chain key" (`double_ratchet.rs:267`). -/
  | missingReceiverChainKey
  /-- "missing remote identity key" (`triple_ratchet.rs:66–68, 183–185`). -/
  | missingRemoteIdentity
  /-- "version does not fit in u8" (`triple_ratchet.rs:59–61`). -/
  | versionTooLarge
  deriving DecidableEq, Repr

/-- `SignalProtocolError` (`error.rs`), restricted to the variants this model produces. -/
inductive SignalProtocolError where
  /-- `InvalidSessionStructure` / `InvalidSessionError` (session state lacks a field). -/
  | invalidSessionStructure (r : InvalidSessionReason)
  /-- `InvalidKeyAgreement` (from `CurveError::InvalidKeyAgreement`, `error.rs:154`): the X25519
  shared secret is all zero (`core/curve.rs:302–305`). -/
  | invalidKeyAgreement
  /-- `DuplicatedMessage(chain_index, counter)` (`double_ratchet.rs:222`). -/
  | duplicatedMessage (chainIndex counter : BitVec 32)
  /-- `InvalidMessage(original_message_type, reason)`. -/
  | invalidMessage (t : MessageType) (r : InvalidMessageReason)
  /-- `InvalidState(…, "post-quantum ratchet …")`: `spqr::send` failed (`triple_ratchet.rs:97–102`)
  or `spqr::recv` failed to decode the state (`:243–246`). -/
  | invalidState
  /-- `CiphertextMessageTooShort(len)` (`protocol.rs:265–267`). -/
  | ciphertextMessageTooShort (len : ℕ)
  /-- `LegacyCiphertextVersion(v)` (`protocol.rs:269–273`). -/
  | legacyCiphertextVersion (v : BitVec 8)
  /-- `UnrecognizedCiphertextVersion(v)` (`protocol.rs:274–278`). -/
  | unrecognizedCiphertextVersion (v : BitVec 8)
  /-- `InvalidProtobufEncoding` (`protocol.rs:280–295`). -/
  | invalidProtobufEncoding
  /-- `NoKeyTypeIdentifier` (`core/curve.rs:85`, `error.rs:151`). -/
  | noKeyTypeIdentifier
  /-- `BadKeyType(t)` (`core/curve.rs:53`, `error.rs:152`). -/
  | badKeyType (t : BitVec 8)
  /-- `BadKeyLength(Djb, len)` (`core/curve.rs:91–92`, `error.rs:153`). -/
  | badKeyLength (len : ℕ)
  /-- A Rust panic (`expect`, index out of bounds, `u32` overflow): unwinds before any store. -/
  | panic
  deriving DecidableEq, Repr

/-! ### Keys (`core/curve.rs`, `core/curve/curve25519.rs`, `identity_key.rs`) -/

/-- A Curve25519 public key (`PublicKey { key: DjbPublicKey([u8; 32]) }`, `core/curve.rs:57–66`).
Equality is byte equality (`ct_eq` of the key data, `core/curve.rs:206–218`). -/
structure PublicKey where
  /-- The 32 key bytes. -/
  bytes : List.Vector (BitVec 8) 32
  deriving DecidableEq

/-- `KeyType::Djb`'s type byte `0x05` (`core/curve.rs:49–53`). -/
def djbType : BitVec 8 := 0x05

/-- `PublicKey::deserialize` (`core/curve.rs:84–105`): a type byte `0x05` and at least 32 key
bytes; **trailing bytes are accepted** (and ignored). -/
def PublicKey.deserialize (v : List (BitVec 8)) : Except SignalProtocolError PublicKey :=
  match v with
  | [] => .error .noKeyTypeIdentifier
  | t :: rest =>
    if t ≠ djbType then .error (.badKeyType t)
    else if h : 32 ≤ rest.length then
      .ok ⟨⟨rest.take 32, by simp [List.length_take, Nat.min_eq_left h]⟩⟩
    else .error (.badKeyLength (rest.length + 1))

/-! ### `SignalMessage` (`protocol.rs:62–308`) -/

/-- prost's `proto::wire::SignalMessage` (`proto/wire.proto:10–17`, proto2: every field is
optional). -/
structure ProtoSignalMessage where
  /-- Field 1. -/
  ratchetKey : Option (List (BitVec 8))
  /-- Field 2. -/
  counter : Option (BitVec 32)
  /-- Field 3. -/
  previousCounter : Option (BitVec 32)
  /-- Field 4. -/
  ciphertext : Option (List (BitVec 8))
  /-- Field 5. -/
  pqRatchet : Option (List (BitVec 8))
  /-- Field 6. -/
  addresses : Option (List (BitVec 8))
  deriving DecidableEq

/-- **prost's protobuf codec for `SignalMessage`** (abstract): `encode` = `Message::encode`,
`decode` = `Message::decode` (`none` = `Err`). No property is assumed by the model; a round-trip
property is needed for correctness only. -/
structure SignalMessageProtoCodec where
  /-- `Message::encode`. -/
  encode : ProtoSignalMessage → List (BitVec 8)
  /-- `Message::decode`. -/
  decode : List (BitVec 8) → Option ProtoSignalMessage

/-- `SignalMessage` (`protocol.rs:62–73`). `serialized` is the full wire bytes
`version byte ‖ protobuf ‖ 8-byte MAC`. -/
structure SignalMessage where
  /-- `message_version` (`u8`). -/
  messageVersion : BitVec 8
  /-- `sender_ratchet_key`. -/
  senderRatchetKey : PublicKey
  /-- `counter`. -/
  counter : BitVec 32
  /-- `previous_counter` (sent, never used by the receiver). -/
  previousCounter : BitVec 32
  /-- `ciphertext` (the AES-CBC body, any length). -/
  ciphertext : List (BitVec 8)
  /-- `pq_ratchet` (empty if absent). -/
  pqRatchet : List (BitVec 8)
  /-- `addresses` (the serialized sender/recipient addresses, if present). -/
  addresses : Option (List (BitVec 8))
  /-- `serialized`: the raw wire bytes. -/
  serialized : List (BitVec 8)
  deriving DecidableEq

/-- `SignalMessage::try_from(&[u8])` (`protocol.rs:261–307`): length ≥ 9, version
`3 ≤ value[0] >> 4 ≤ 4`, protobuf decode of the bytes between the version byte and the MAC,
required `ratchet_key` (then `PublicKey::deserialize`), `counter` and `ciphertext`; an absent
`previous_counter` is 0 and an absent `pq_ratchet` is empty. -/
def SignalMessage.tryFrom (codec : SignalMessageProtoCodec) (value : List (BitVec 8)) :
    Except SignalProtocolError SignalMessage := do
  if value.length < macLength + 1 then throw (.ciphertextMessageTooShort value.length)
  let v := (value.headD 0) >>> 4
  if v < preKyberVersion then throw (.legacyCiphertextVersion v)
  if currentVersion < v then throw (.unrecognizedCiphertextVersion v)
  let some p := codec.decode ((value.take (value.length - macLength)).drop 1)
    | throw .invalidProtobufEncoding
  let some rk := p.ratchetKey | throw .invalidProtobufEncoding
  let senderRatchetKey ← PublicKey.deserialize rk
  let some counter := p.counter | throw .invalidProtobufEncoding
  let some ciphertext := p.ciphertext | throw .invalidProtobufEncoding
  return { messageVersion := v, senderRatchetKey, counter,
           previousCounter := p.previousCounter.getD 0, ciphertext,
           pqRatchet := p.pqRatchet.getD [], addresses := p.addresses, serialized := value }

end LibsignalSession
end CryptoGames

/-!
## `prost` 0.14.4 Protobuf Codec for `signal.proto.wire.SignalMessage`

Concrete instance `protoSignalCodec : SignalMessageProtoCodec` (DEV-LS21) modeling `prost` 0.14.4's
`Message::encode` (fields emitted in tag order `1..6`) and `Message::decode(&[u8])` (LEB128
varints up to 10 bytes with `u64` overflow check, last-write-wins field merging, and unknown-field
skipping with `RECURSION_LIMIT = 100` for nested groups).
-/

namespace CryptoVerification.LibsignalProtoCodec

open CryptoGames.LibsignalSession

/-! ## Varints (`P/encoding/varint.rs`) -/

/-- `decode_varint_slow` (`P/encoding/varint.rs:157–174`), the loop body at `count = i`
(`i ≤ 9`): `acc` holds the bits decoded so far. `none` = `InvalidVarint`. Returns the value and the
rest of the input. -/
def decodeVarintAux : ℕ → BitVec 64 → List (BitVec 8) → Option (BitVec 64 × List (BitVec 8))
  | _, _, [] => none                                         -- truncated (or empty)
  | i, acc, b :: rest =>
    let acc := acc ||| ((b &&& 0x7F).zeroExtend 64 <<< (7 * i))
    if b.toNat ≤ 0x7F then
      if i = 9 ∧ 0x02 ≤ b.toNat then none else some (acc, rest)  -- u64 overflow at byte 10
    else if i = 9 then none                                  -- 10 bytes, no terminator
    else decodeVarintAux (i + 1) acc rest

/-- `decode_varint` (`P/encoding/varint.rs:37–55`; all three paths agree, module docstring). -/
def decodeVarint (bs : List (BitVec 8)) : Option (BitVec 64 × List (BitVec 8)) :=
  decodeVarintAux 0 0 bs

/-- `encode_varint` (`P/encoding/varint.rs:11–22`): `fuel` = the remaining rounds of the
`for _ in 0..10` loop. -/
def encodeVarintAux : ℕ → BitVec 64 → List (BitVec 8)
  | 0, _ => []
  | k + 1, v =>
    if v.toNat < 0x80 then [v.setWidth 8]
    else ((v &&& 0x7F) ||| 0x80).setWidth 8 :: encodeVarintAux k (v >>> 7)

/-- `encode_varint(value)` (10 rounds always suffice for a `u64`). -/
def encodeVarint (v : BitVec 64) : List (BitVec 8) := encodeVarintAux 10 v

/-! ## Keys and wire types (`P/encoding/wire_type.rs`, `P/encoding.rs:100–128`) -/

/-- `WireType` (`P/encoding/wire_type.rs:8–15`). -/
inductive WireType where
  | varint | sixtyFourBit | lengthDelimited | startGroup | endGroup | thirtyTwoBit
  deriving DecidableEq, Repr

/-- `WireType::try_from(u64)` (`P/encoding/wire_type.rs:17–32`): `none` = `InvalidWireType`. -/
def WireType.ofNat? : ℕ → Option WireType
  | 0 => some .varint
  | 1 => some .sixtyFourBit
  | 2 => some .lengthDelimited
  | 3 => some .startGroup
  | 4 => some .endGroup
  | 5 => some .thirtyTwoBit
  | _ => none

/-- `wire_type as u32` (the `#[repr(u8)]` discriminant). -/
def WireType.toNat : WireType → ℕ
  | .varint => 0
  | .sixtyFourBit => 1
  | .lengthDelimited => 2
  | .startGroup => 3
  | .endGroup => 4
  | .thirtyTwoBit => 5

/-- `decode_key` (`P/encoding.rs:115–128`): `(tag, wire_type)` and the rest of the input. -/
def decodeKey (bs : List (BitVec 8)) : Option ((ℕ × WireType) × List (BitVec 8)) :=
  match decodeVarint bs with
  | none => none
  | some (key, rest) =>
    if 2 ^ 32 ≤ key.toNat then none                          -- InvalidKey
    else match WireType.ofNat? (key.toNat % 8) with
      | none => none                                        -- InvalidWireType (6, 7)
      | some wt =>
        let tag := key.toNat / 8
        if tag < 1 then none else some ((tag, wt), rest)     -- InvalidTag

/-- `encode_key(tag, wire_type)` (`P/encoding.rs:106–110`). -/
def encodeKey (tag : ℕ) (wt : WireType) : List (BitVec 8) :=
  encodeVarint (BitVec.ofNat 64 (tag * 8 + wt.toNat))

/-! ## Skipping unknown fields (`skip_field`, `P/encoding.rs:166–199`) -/

/-- `buf.advance(len)` after the check `len > buf.remaining() ⇒ BufferUnderflow`
(`P/encoding.rs:193–197`). -/
def skipBytes (n : ℕ) (bs : List (BitVec 8)) : Option (List (BitVec 8)) :=
  if bs.length < n then none else some (bs.drop n)

/-- `skip_field` on the four non-group wire types (`P/encoding.rs:173–177, 193–197`), after the
`limit_reached` check. -/
def skipScalar (wt : WireType) (bs : List (BitVec 8)) : Option (List (BitVec 8)) :=
  match wt with
  | .varint => (decodeVarint bs).map (·.2)
  | .thirtyTwoBit => skipBytes 4 bs
  | .sixtyFourBit => skipBytes 8 bs
  | .lengthDelimited =>
    match decodeVarint bs with
    | none => none
    | some (len, rest) => skipBytes len.toNat rest
  | .startGroup | .endGroup => none                         -- not called on these

mutual

/-- `skip_field(wire_type, tag, buf, ctx)` (`P/encoding.rs:166–199`) with
`ctx.recurse_count = depth`. `fuel` bounds the recursion; `2 * |bs| + 2` always suffices
(each `skipGroup` round consumes a key byte before recursing, `skipField` → `skipGroup` costs one
unit). -/
def skipField (fuel depth tag : ℕ) (wt : WireType) (bs : List (BitVec 8)) :
    Option (List (BitVec 8)) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if depth = 0 then none                                   -- RecursionLimitReached
    else match wt with
      | .endGroup => none                                    -- UnexpectedEndGroupTag
      | .startGroup => skipGroup fuel depth tag bs
      | wt => skipScalar wt bs

/-- The `WireType::StartGroup` loop of `skip_field` (`P/encoding.rs:178–189`) for a group with tag
`tag`, entered with `ctx.recurse_count = depth`: inner fields are skipped with `depth - 1`. -/
def skipGroup (fuel depth tag : ℕ) (bs : List (BitVec 8)) : Option (List (BitVec 8)) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match decodeKey bs with
    | none => none
    | some ((itag, .endGroup), rest) =>
      if itag = tag then some rest else none                 -- UnexpectedEndGroupTag
    | some ((itag, iwt), rest) =>
      match skipField fuel (depth - 1) itag iwt rest with
      | none => none
      | some rest' => skipGroup fuel depth tag rest'

end

/-- `RECURSION_LIMIT` (`P/lib.rs:30`; `DecodeContext::default`, `P/encoding.rs:49–56`). -/
def recursionLimit : ℕ := 100

/-! ## Known fields (`merge_field`, generated by `D/lib.rs:111–125, 180–193`) -/

/-- `bytes::merge` into an `Option<Vec<u8>>` field (`P/encoding.rs:697–724`): the new value and the
rest of the input. -/
def mergeBytes (wt : WireType) (bs : List (BitVec 8)) :
    Option (List (BitVec 8) × List (BitVec 8)) :=
  if wt ≠ .lengthDelimited then none                        -- UnexpectedWireType
  else match decodeVarint bs with
    | none => none
    | some (len, rest) =>
      if rest.length < len.toNat then none                   -- BufferUnderflow
      else some (rest.take len.toNat, rest.drop len.toNat)

/-- `uint32::merge` into an `Option<u32>` field (`P/encoding.rs:268–273`): `value as u32`. -/
def mergeUint32 (wt : WireType) (bs : List (BitVec 8)) : Option (BitVec 32 × List (BitVec 8)) :=
  if wt ≠ .varint then none                                 -- UnexpectedWireType
  else match decodeVarint bs with
    | none => none
    | some (v, rest) => some (v.setWidth 32, rest)

/-- `SignalMessage::merge_field(tag, wire_type, buf, DecodeContext::default())`: the updated
message and the rest of the input. -/
def mergeField (m : ProtoSignalMessage) (tag : ℕ) (wt : WireType) (bs : List (BitVec 8)) :
    Option (ProtoSignalMessage × List (BitVec 8)) :=
  match tag with
  | 1 => (mergeBytes wt bs).map fun (v, r) => ({ m with ratchetKey := some v }, r)
  | 2 => (mergeUint32 wt bs).map fun (v, r) => ({ m with counter := some v }, r)
  | 3 => (mergeUint32 wt bs).map fun (v, r) => ({ m with previousCounter := some v }, r)
  | 4 => (mergeBytes wt bs).map fun (v, r) => ({ m with ciphertext := some v }, r)
  | 5 => (mergeBytes wt bs).map fun (v, r) => ({ m with pqRatchet := some v }, r)
  | 6 => (mergeBytes wt bs).map fun (v, r) => ({ m with addresses := some v }, r)
  | _ => (skipField (2 * bs.length + 2) recursionLimit tag wt bs).map fun r => (m, r)

/-- The `while buf.has_remaining()` loop of `Message::merge` (`P/message.rs:126–136`). `fuel` =
the input length suffices: each round consumes at least the key byte. -/
def decodeLoop : ℕ → ProtoSignalMessage → List (BitVec 8) → Option ProtoSignalMessage
  | _, m, [] => some m
  | 0, _, _ :: _ => none                                     -- unreachable with fuel = length
  | fuel + 1, m, bs@(_ :: _) =>
    match decodeKey bs with
    | none => none
    | some ((tag, wt), rest) =>
      match mergeField m tag wt rest with
      | none => none
      | some (m', rest') => decodeLoop fuel m' rest'

/-- `SignalMessage::default()`: every field `None`. -/
def emptyProtoSignalMessage : ProtoSignalMessage :=
  { ratchetKey := none, counter := none, previousCounter := none, ciphertext := none,
    pqRatchet := none, addresses := none }

/-- `<SignalMessage as Message>::decode(&[u8])` (`P/message.rs:105–111`); `none` = `Err`. -/
def decode (bs : List (BitVec 8)) : Option ProtoSignalMessage :=
  decodeLoop bs.length emptyProtoSignalMessage bs

/-! ## Encoding (`encode_raw`, generated by `D/lib.rs:107–109, 175–177`) -/

/-- `bytes::encode(tag, value)` (`P/encoding.rs:691–695`) for a `Some` field, nothing for `None`. -/
def encodeBytesField (tag : ℕ) : Option (List (BitVec 8)) → List (BitVec 8)
  | none => []
  | some v => encodeKey tag .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 v.length) ++ v

/-- `uint32::encode(tag, value)` (`P/encoding.rs:263–266`, `*value as u64`) for a `Some` field. -/
def encodeUint32Field (tag : ℕ) : Option (BitVec 32) → List (BitVec 8)
  | none => []
  | some v => encodeKey tag .varint ++ encodeVarint (v.zeroExtend 64)

/-- `<SignalMessage as Message>::encode` into a `Vec<u8>` = `encode_raw`: the fields in tag order. -/
def encode (m : ProtoSignalMessage) : List (BitVec 8) :=
  encodeBytesField 1 m.ratchetKey ++ encodeUint32Field 2 m.counter ++
    encodeUint32Field 3 m.previousCounter ++ encodeBytesField 4 m.ciphertext ++
    encodeBytesField 5 m.pqRatchet ++ encodeBytesField 6 m.addresses

/-- **prost 0.14.4's codec for `signal.proto.wire.SignalMessage`** (DEV-LS21). -/
def protoSignalCodec : SignalMessageProtoCodec where
  encode := encode
  decode := decode

end CryptoVerification.LibsignalProtoCodec
