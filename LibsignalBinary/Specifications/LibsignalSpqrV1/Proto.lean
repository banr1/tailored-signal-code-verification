/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
public import Batteries.Lean.Except

/-!
# SPQR V1: Protobuf types and `prost` 0.14.4 codec for `pq_ratchet.proto`

**Trusted in part.** The theorems of `Computational/Theorems/` use only part of this file (see
`Computational/docs/TRUSTED_BASE.md`): the message types (`PolynomialEncoder`, `PolynomialDecoder`,
`ProtoChunk`, `V1State`, `InnerState`, `PqRatchetState`) and the `encodeRaw` / `mergeField` codec
functions (`WireType`, `DecodeErr`, `decodeVarint`, `encodeVarint`, `decodeKey`, `encodeKey`,
`skipField`, `mergeFieldsLoop`, `mergeMessage`, `mergeTopLevelMessage`, `decodeTopLevelMessage`,
`encodeMessage`, `decodeState`, `encodeState`) that the SPQR V1 state goes through. The remaining
definitions (`encode`, `decode`, `encodedLen`, `merge`, `V1Msg`, `decodeV1Msg`, `encodeV1Msg`, and
`spqrDecodeState`) are checked by Lean.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

/-! ## 1. Enums and message structures (`src/proto/pq_ratchet.proto`) -/

namespace Version
end Version

namespace Direction
end Direction

abbrev ProtoChainParams := ChainParamsPB
abbrev ProtoEpochDirection := EpochDirectionPB
abbrev ProtoChainEpoch := ChainEpochPB
abbrev ProtoChain := ChainPB
abbrev ProtoVersionNegotiation := VersionNegotiationPB
abbrev AuthenticatorPB := ProtoAuthenticator

/-- `message PolynomialEncoder` (`src/proto/pq_ratchet.proto:8–16`). -/
structure PolynomialEncoder where
  idx : BitVec 32 := 0#32
  pts : List Bytes := []
  polys : List Bytes := []
  deriving DecidableEq, Repr, Inhabited

abbrev PolynomialEncoderPB := PolynomialEncoder

/-- `message PolynomialDecoder` (`src/proto/pq_ratchet.proto:18–23`). -/
structure PolynomialDecoder where
  ptsNeeded : BitVec 32 := 0#32
  polys : BitVec 32 := 0#32
  pts : List Bytes := []
  isComplete : Bool := false
  deriving DecidableEq, Repr, Inhabited

abbrev PolynomialDecoderPB := PolynomialDecoder

/-- `message Chunk` (`src/proto/pq_ratchet.proto:40–43`). -/
structure ProtoChunk where
  index : BitVec 32 := 0#32
  data : Bytes := []
  deriving DecidableEq, Repr, Inhabited

/-- `oneof V1Msg.inner_msg` (`src/proto/pq_ratchet.proto:48–58`). -/
inductive V1Msg.InnerMsg where
  | hdr (v : ProtoChunk)
  | ek (v : ProtoChunk)
  | ekCt1Ack (v : ProtoChunk)
  | ct1Ack (v : Bool)
  | ct1 (v : ProtoChunk)
  | ct2 (v : ProtoChunk)
  deriving DecidableEq, Repr

/-- `message V1Msg` (`src/proto/pq_ratchet.proto:45–59`). -/
structure V1Msg where
  epoch : Epoch := 0#64
  index : BitVec 32 := 0#32
  innerMsg : Option V1Msg.InnerMsg := none
  deriving DecidableEq, Repr, Inhabited

/-- `message V1State.Unchunked` (`src/proto/pq_ratchet.proto:67–125`). -/
structure V1State.Unchunked where
  deriving DecidableEq, Repr, Inhabited

namespace V1State.Unchunked
structure KeysUnsampled where
  epoch : Epoch := 0#64
  auth : Option ProtoAuthenticator := none
  deriving DecidableEq, Repr, Inhabited
structure HeaderSent where
  epoch : Epoch := 0#64
  auth : Option ProtoAuthenticator := none
  ek : Bytes := []
  dk : Bytes := []
  deriving DecidableEq, Repr, Inhabited
structure EkSent where
  epoch : Epoch := 0#64
  auth : Option ProtoAuthenticator := none
  dk : Bytes := []
  deriving DecidableEq, Repr, Inhabited
structure EkSentCt1Received where
  epoch : Epoch := 0#64
  auth : Option ProtoAuthenticator := none
  dk : Bytes := []
  ct1 : Bytes := []
  deriving DecidableEq, Repr, Inhabited
structure NoHeaderReceived where
  epoch : Epoch := 0#64
  auth : Option ProtoAuthenticator := none
  deriving DecidableEq, Repr, Inhabited
structure HeaderReceived where
  epoch : Epoch := 0#64
  auth : Option ProtoAuthenticator := none
  hdr : Bytes := []
  deriving DecidableEq, Repr, Inhabited
structure EkReceived where
  epoch : Epoch := 0#64
  auth : Option ProtoAuthenticator := none
  hdr : Bytes := []
  ek : Bytes := []
  deriving DecidableEq, Repr, Inhabited
structure Ct1Sent where
  epoch : Epoch := 0#64
  auth : Option ProtoAuthenticator := none
  hdr : Bytes := []
  es : Bytes := []
  ct1 : Bytes := []
  deriving DecidableEq, Repr, Inhabited
structure Ct1SentEkReceived where
  epoch : Epoch := 0#64
  auth : Option ProtoAuthenticator := none
  es : Bytes := []
  ek : Bytes := []
  ct1 : Bytes := []
  deriving DecidableEq, Repr, Inhabited
structure Ct2Sent where
  epoch : Epoch := 0#64
  auth : Option ProtoAuthenticator := none
  deriving DecidableEq, Repr, Inhabited
end V1State.Unchunked

/-- `message V1State.Chunked` (`src/proto/pq_ratchet.proto:126–175`). -/
structure V1State.Chunked where
  deriving DecidableEq, Repr, Inhabited

namespace V1State.Chunked
structure KeysUnsampled where
  uc : Option V1State.Unchunked.KeysUnsampled := none
  deriving DecidableEq, Repr, Inhabited
structure KeysSampled where
  uc : Option V1State.Unchunked.HeaderSent := none
  sendingHdr : Option PolynomialEncoder := none
  deriving DecidableEq, Repr, Inhabited
structure HeaderSent where
  uc : Option V1State.Unchunked.EkSent := none
  sendingEk : Option PolynomialEncoder := none
  receivingCt1 : Option PolynomialDecoder := none
  deriving DecidableEq, Repr, Inhabited
structure Ct1Received where
  uc : Option V1State.Unchunked.EkSentCt1Received := none
  sendingEk : Option PolynomialEncoder := none
  deriving DecidableEq, Repr, Inhabited
/-- `V1State.Chunked.EkSentCt1Received` (`pq_ratchet.proto:144–147`): tags `uc = 1`, `receiving_ct2 = 3`. -/
structure EkSentCt1Received where
  uc : Option V1State.Unchunked.EkSentCt1Received := none
  receivingCt2 : Option PolynomialDecoder := none
  deriving DecidableEq, Repr, Inhabited
structure NoHeaderReceived where
  uc : Option V1State.Unchunked.NoHeaderReceived := none
  receivingHdr : Option PolynomialDecoder := none
  deriving DecidableEq, Repr, Inhabited
structure HeaderReceived where
  uc : Option V1State.Unchunked.HeaderReceived := none
  receivingEk : Option PolynomialDecoder := none
  deriving DecidableEq, Repr, Inhabited
structure Ct1Sampled where
  uc : Option V1State.Unchunked.Ct1Sent := none
  sendingCt1 : Option PolynomialEncoder := none
  receivingEk : Option PolynomialDecoder := none
  deriving DecidableEq, Repr, Inhabited
structure EkReceivedCt1Sampled where
  uc : Option V1State.Unchunked.Ct1SentEkReceived := none
  sendingCt1 : Option PolynomialEncoder := none
  deriving DecidableEq, Repr, Inhabited
structure Ct1Acknowledged where
  uc : Option V1State.Unchunked.Ct1Sent := none
  receivingEk : Option PolynomialDecoder := none
  deriving DecidableEq, Repr, Inhabited
structure Ct2Sampled where
  uc : Option V1State.Unchunked.Ct2Sent := none
  sendingCt2 : Option PolynomialEncoder := none
  deriving DecidableEq, Repr, Inhabited
end V1State.Chunked

namespace V1State
/-- `oneof V1State.inner_state` (`src/proto/pq_ratchet.proto:177–192`). -/
inductive InnerState where
  | keysUnsampled (v : Chunked.KeysUnsampled)
  | keysSampled (v : Chunked.KeysSampled)
  | headerSent (v : Chunked.HeaderSent)
  | ct1Received (v : Chunked.Ct1Received)
  | ekSentCt1Received (v : Chunked.EkSentCt1Received)
  | noHeaderReceived (v : Chunked.NoHeaderReceived)
  | headerReceived (v : Chunked.HeaderReceived)
  | ct1Sampled (v : Chunked.Ct1Sampled)
  | ekReceivedCt1Sampled (v : Chunked.EkReceivedCt1Sampled)
  | ct1Acknowledged (v : Chunked.Ct1Acknowledged)
  | ct2Sampled (v : Chunked.Ct2Sampled)
  deriving DecidableEq, Repr
end V1State

/-- `message V1State` (`src/proto/pq_ratchet.proto:66–193`). -/
structure V1State where
  innerState : Option V1State.InnerState := none
  deriving DecidableEq, Repr, Inhabited

abbrev V1StatePB := V1State

/-- `oneof PqRatchetState.inner` (`src/proto/pq_ratchet.proto:35–37`). -/
inductive PqRatchetState.Inner where
  | v1 (v : V1State)
  deriving DecidableEq, Repr

/-- `message PqRatchetState` (`src/proto/pq_ratchet.proto:25–38`). -/
structure PqRatchetState where
  versionNegotiation : Option VersionNegotiationPB := none
  chain : Option ChainPB := none
  inner : Option PqRatchetState.Inner := none
  deriving DecidableEq, Repr, Inhabited

/-! ## 2. `prost` 0.14.4 wire format, varint, tag/wire-type, and field codecs (`namespace Proto`) -/

namespace Proto

abbrev ChainParams := ChainParamsPB
abbrev EpochDirection := EpochDirectionPB
abbrev Chain := ChainPB
abbrev VersionNegotiation := VersionNegotiationPB
abbrev Chunk := ProtoChunk
abbrev Authenticator := ProtoAuthenticator

/-- `prost::encoding::WireType`. -/
inductive WireType where
  | varint | SixtyFourBit | lengthDelimited | startGroup | endGroup | ThirtyTwoBit
  deriving DecidableEq, Repr, Inhabited

namespace WireType
def ofU64? (v : BitVec 64) : Option WireType :=
  if v == 0#64 then some .varint else if v == 1#64 then some .SixtyFourBit
  else if v == 2#64 then some .lengthDelimited else if v == 3#64 then some .startGroup
  else if v == 4#64 then some .endGroup else if v == 5#64 then some .ThirtyTwoBit else none
def toU32 : WireType → BitVec 32
  | .varint => 0#32 | .SixtyFourBit => 1#32 | .lengthDelimited => 2#32
  | .startGroup => 3#32 | .endGroup => 4#32 | .ThirtyTwoBit => 5#32
end WireType

/-- `prost::DecodeError` kinds. -/
inductive DecodeErr where
  | invalidVarint | bufferUnderflow | invalidWireType (v : BitVec 64)
  | invalidKey (key : BitVec 64) | invalidTag (tag : BitVec 32)
  | unexpectedWireType (expected actual : WireType) | unexpectedEndGroupTag | recursionLimitExceeded
  deriving DecidableEq, Repr, Inhabited

def RECURSION_LIMIT : Nat := 100
def MIN_TAG : BitVec 32 := 1#32

/-- LEB128 varint decoder (`prost::encoding::varint::decode_varint_slow`): 1 to 10 bytes, with the
10th byte required to be `< 0x02`. -/
def decodeVarintAux : Nat → Nat → BitVec 64 → Bytes → Except DecodeErr (BitVec 64 × Bytes)
  | 0, _, _, _ => .error .invalidVarint
  | fuel + 1, idx, acc, bs =>
    match bs with
    | [] => .error .bufferUnderflow
    | b :: rest =>
      if idx == 9 then
        if b ≥ 0x02#8 then .error .invalidVarint
        else .ok (acc ||| ((b &&& 0x7f#8).zeroExtend 64 <<< 63), rest)
      else
        let acc' := acc ||| ((b &&& 0x7f#8).zeroExtend 64 <<< (idx * 7))
        if b < 0x80#8 then .ok (acc', rest)
        else decodeVarintAux fuel (idx + 1) acc' rest

def decodeVarint (bs : Bytes) : Except DecodeErr (BitVec 64 × Bytes) := decodeVarintAux 10 0 0#64 bs

def encodeVarintAux : Nat → BitVec 64 → Bytes
  | 0, v => [v.truncate 8]
  | fuel + 1, v =>
    if v < 0x80#64 then [v.truncate 8]
    else ((v.truncate 8 ||| 0x80#8)) :: encodeVarintAux fuel (v >>> 7)

/-- `prost::encoding::varint::encode_varint`. -/
def encodeVarint (v : BitVec 64) : Bytes := encodeVarintAux 10 v
def encodedLenVarint (v : BitVec 64) : Nat := (encodeVarint v).length

/-- `prost::encoding::decode_key`: validates `key ≤ u32::MAX`, 3-bit `WireType`, and `tag ≥ 1`. -/
def decodeKey (bs : Bytes) : Except DecodeErr ((BitVec 32 × WireType) × Bytes) := do
  let (key, rest) ← decodeVarint bs
  if key > 0xffffffff#64 then .error (.invalidKey key)
  else
    let wt ← match WireType.ofU64? (key &&& 0x7#64) with
      | some w => .ok w
      | none => .error (.invalidWireType (key &&& 0x7#64))
    let tag : BitVec 32 := (key >>> 3).truncate 32
    if tag < MIN_TAG then .error (.invalidTag tag) else .ok ((tag, wt), rest)

def encodeKey (tag : BitVec 32) (wt : WireType) : Bytes :=
  encodeVarint (((tag <<< 3) ||| wt.toU32).zeroExtend 64)
def keyLen (tag : BitVec 32) : Nat := encodedLenVarint ((tag <<< 3).zeroExtend 64)

def checkWireType (expected actual : WireType) : Except DecodeErr Unit :=
  if expected != actual then .error (.unexpectedWireType expected actual) else .ok ()

def takeExact : Nat → Bytes → Except DecodeErr (Bytes × Bytes)
  | 0, bs => .ok ([], bs)
  | _ + 1, [] => .error .bufferUnderflow
  | n + 1, b :: rest => do let (hd, tl) ← takeExact n rest; .ok (b :: hd, tl)

def dropExact : Nat → Bytes → Except DecodeErr Bytes
  | 0, bs => .ok bs
  | _ + 1, [] => .error .bufferUnderflow
  | n + 1, _ :: rest => dropExact n rest

def skipGroupLoop (skipInner : WireType → BitVec 32 → Bytes → Except DecodeErr Bytes) :
    Nat → BitVec 32 → Bytes → Except DecodeErr Bytes
  | 0, _, _ => .error .bufferUnderflow
  | fuel + 1, groupTag, bs => do
    let ((innerTag, innerWt), rest) ← decodeKey bs
    if innerWt == .endGroup then
      if innerTag != groupTag then .error .unexpectedEndGroupTag else .ok rest
    else do
      let rest' ← skipInner innerWt innerTag rest
      skipGroupLoop skipInner fuel groupTag rest'

def skipFieldNonGroup (wt : WireType) (bs : Bytes) : Except DecodeErr Bytes :=
  match wt with
  | .varint => do let (_, rest) ← decodeVarint bs; .ok rest
  | .ThirtyTwoBit => dropExact 4 bs
  | .SixtyFourBit => dropExact 8 bs
  | .lengthDelimited => do let (len, rest) ← decodeVarint bs; dropExact len.toNat rest
  | _ => .error .unexpectedEndGroupTag

/-- `prost::encoding::skip_field`, checking `depth > 0` before dispatching on `wt`. -/
def skipFieldAux : Nat → WireType → BitVec 32 → Bytes → Except DecodeErr Bytes
  | 0, _, _, _ => .error .recursionLimitExceeded
  | depth' + 1, wt, tag, bs =>
    if wt == .startGroup then skipGroupLoop (skipFieldAux depth') bs.length tag bs
    else skipFieldNonGroup wt bs

def skipField (wt : WireType) (tag : BitVec 32) (bs : Bytes) (depth : Nat) : Except DecodeErr Bytes :=
  skipFieldAux depth wt tag bs

def mergeUint32 (wt : WireType) (bs : Bytes) : Except DecodeErr (BitVec 32 × Bytes) := do
  checkWireType .varint wt; let (v, rest) ← decodeVarint bs; .ok (v.truncate 32, rest)
def mergeUint64 (wt : WireType) (bs : Bytes) : Except DecodeErr (BitVec 64 × Bytes) := do
  checkWireType .varint wt; decodeVarint bs
def mergeInt32 (wt : WireType) (bs : Bytes) : Except DecodeErr (BitVec 32 × Bytes) := do
  checkWireType .varint wt; let (v, rest) ← decodeVarint bs; .ok (v.truncate 32, rest)
def mergeBool (wt : WireType) (bs : Bytes) : Except DecodeErr (Bool × Bytes) := do
  checkWireType .varint wt; let (v, rest) ← decodeVarint bs; .ok (v != 0#64, rest)
def mergeBytes (wt : WireType) (bs : Bytes) : Except DecodeErr (Bytes × Bytes) := do
  checkWireType .lengthDelimited wt; let (len, rest) ← decodeVarint bs; takeExact len.toNat rest
def mergeRepeatedBytes (wt : WireType) (vals : List Bytes) (bs : Bytes) :
    Except DecodeErr (List Bytes × Bytes) := do
  let (b, rest) ← mergeBytes wt bs; .ok (vals ++ [b], rest)

def encodeUint32Field (tag : BitVec 32) (v : BitVec 32) : Bytes :=
  if v == 0#32 then [] else encodeKey tag .varint ++ encodeVarint (v.zeroExtend 64)
def encodeUint64Field (tag : BitVec 32) (v : BitVec 64) : Bytes :=
  if v == 0#64 then [] else encodeKey tag .varint ++ encodeVarint v
def encodeInt32Field (tag : BitVec 32) (v : BitVec 32) : Bytes :=
  if v == 0#32 then [] else encodeKey tag .varint ++ encodeVarint (v.signExtend 64)
def encodeBoolField (tag : BitVec 32) (v : Bool) : Bytes :=
  if v then encodeKey tag .varint ++ [1#8] else []
/-- Encodes a `bool` member of a `oneof` (always emitted, even when `false`). -/
def encodeBoolOneof (tag : BitVec 32) (v : Bool) : Bytes :=
  encodeKey tag .varint ++ encodeVarint (if v then 1#64 else 0#64)
def encodeBytesUncond (tag : BitVec 32) (v : Bytes) : Bytes :=
  encodeKey tag .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 v.length) ++ v
def encodeBytesField (tag : BitVec 32) (v : Bytes) : Bytes :=
  if v.isEmpty then [] else encodeBytesUncond tag v
def encodeRepeatedBytes (tag : BitVec 32) (vs : List Bytes) : Bytes :=
  vs.foldr (fun v acc => encodeBytesUncond tag v ++ acc) []

def mergeFieldsLoop {M : Type}
    (mergeField : M → BitVec 32 → WireType → Bytes → Nat → Except DecodeErr (M × Bytes)) :
    Nat → M → Bytes → Nat → Except DecodeErr M
  | _, m, [], _ => .ok m
  | 0, _, _ :: _, _ => .error .bufferUnderflow
  | fuel + 1, m, bs, depth => do
    let ((tag, wt), rest) ← decodeKey bs
    let (m', rest') ← mergeField m tag wt rest depth
    mergeFieldsLoop mergeField fuel m' rest' depth

/-- `prost::encoding::message::merge`: decodes a length-prefixed nested message with recursion
budget `depth`. -/
def mergeMessage {M : Type}
    (mergeField : M → BitVec 32 → WireType → Bytes → Nat → Except DecodeErr (M × Bytes))
    (wt : WireType) (m : M) (bs : Bytes) (depth : Nat) : Except DecodeErr (M × Bytes) := do
  checkWireType .lengthDelimited wt
  match depth with
  | 0 => .error .recursionLimitExceeded
  | depth' + 1 => do
    let (len, rest) ← decodeVarint bs
    let (sub, after) ← takeExact len.toNat rest
    let m' ← mergeFieldsLoop mergeField sub.length m sub depth'
    .ok (m', after)

def mergeOptMessage {M : Type} [Inhabited M]
    (mergeField : M → BitVec 32 → WireType → Bytes → Nat → Except DecodeErr (M × Bytes))
    (wt : WireType) (opt : Option M) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (Option M × Bytes) := do
  let (m', rest) ← mergeMessage mergeField wt (opt.getD default) bs depth; .ok (some m', rest)

def mergeRepeatedMessage {M : Type} [Inhabited M]
    (mergeField : M → BitVec 32 → WireType → Bytes → Nat → Except DecodeErr (M × Bytes))
    (wt : WireType) (ms : List M) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (List M × Bytes) := do
  let (m', rest) ← mergeMessage mergeField wt default bs depth; .ok (ms ++ [m'], rest)

def encodeMessage {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32) (m : M) : Bytes :=
  let raw := encodeRaw m
  encodeKey tag .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 raw.length) ++ raw
def encodeOptMessage {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32) : Option M → Bytes
  | none => [] | some m => encodeMessage encodeRaw tag m
def encodeRepeatedMessage {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32) (ms : List M) : Bytes :=
  ms.foldr (fun m acc => encodeMessage encodeRaw tag m ++ acc) []

def mergeTopLevelMessage {M : Type}
    (mergeField : M → BitVec 32 → WireType → Bytes → Nat → Except DecodeErr (M × Bytes))
    (m : M) (bs : Bytes) : Except DecodeErr M :=
  mergeFieldsLoop mergeField bs.length m bs RECURSION_LIMIT
def decodeTopLevelMessage {M : Type} [Inhabited M]
    (mergeField : M → BitVec 32 → WireType → Bytes → Nat → Except DecodeErr (M × Bytes))
    (bs : Bytes) : Except DecodeErr M :=
  mergeTopLevelMessage mergeField default bs

end Proto

abbrev WireType := Proto.WireType
abbrev DecodeErr := Proto.DecodeErr

/-! ## 3. Per-message `mergeField`, `decode`, `encodeRaw`, `encodedLen`, `encode` -/

namespace PolynomialEncoder
open Proto in
def mergeField (m : PolynomialEncoder) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (PolynomialEncoder × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeUint32 wt bs; .ok ({ m with idx := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeRepeatedBytes wt m.pts bs; .ok ({ m with pts := v }, bs')
  else if tag == 3#32 then let (v, bs') ← mergeRepeatedBytes wt m.polys bs; .ok ({ m with polys := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def merge (m : PolynomialEncoder) (bs : Bytes) : Except DecodeErr PolynomialEncoder := Proto.mergeTopLevelMessage mergeField m bs
def decode (bs : Bytes) : Except DecodeErr PolynomialEncoder := Proto.decodeTopLevelMessage mergeField bs
def encodeRaw (m : PolynomialEncoder) : Bytes :=
  Proto.encodeUint32Field 1#32 m.idx ++ Proto.encodeRepeatedBytes 2#32 m.pts ++ Proto.encodeRepeatedBytes 3#32 m.polys
def encodedLen (m : PolynomialEncoder) : Nat := (encodeRaw m).length
def encode (m : PolynomialEncoder) : Bytes := encodeRaw m
end PolynomialEncoder

namespace PolynomialDecoder
open Proto in
def mergeField (m : PolynomialDecoder) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (PolynomialDecoder × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeUint32 wt bs; .ok ({ m with ptsNeeded := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeUint32 wt bs; .ok ({ m with polys := v }, bs')
  else if tag == 3#32 then let (v, bs') ← mergeRepeatedBytes wt m.pts bs; .ok ({ m with pts := v }, bs')
  else if tag == 4#32 then let (v, bs') ← mergeBool wt bs; .ok ({ m with isComplete := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def merge (m : PolynomialDecoder) (bs : Bytes) : Except DecodeErr PolynomialDecoder := Proto.mergeTopLevelMessage mergeField m bs
def decode (bs : Bytes) : Except DecodeErr PolynomialDecoder := Proto.decodeTopLevelMessage mergeField bs
def encodeRaw (m : PolynomialDecoder) : Bytes :=
  Proto.encodeUint32Field 1#32 m.ptsNeeded ++ Proto.encodeUint32Field 2#32 m.polys ++
  Proto.encodeRepeatedBytes 3#32 m.pts ++ Proto.encodeBoolField 4#32 m.isComplete
def encodedLen (m : PolynomialDecoder) : Nat := (encodeRaw m).length
def encode (m : PolynomialDecoder) : Bytes := encodeRaw m
end PolynomialDecoder

namespace ChainParamsPB
open Proto in
def mergeField (m : ChainParamsPB) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (ChainParamsPB × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeUint32 wt bs; .ok ({ m with maxJump := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeUint32 wt bs; .ok ({ m with maxOooKeys := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def merge (m : ChainParamsPB) (bs : Bytes) : Except DecodeErr ChainParamsPB := Proto.mergeTopLevelMessage mergeField m bs
def decode (bs : Bytes) : Except DecodeErr ChainParamsPB := Proto.decodeTopLevelMessage mergeField bs
def encodeRaw (m : ChainParamsPB) : Bytes := Proto.encodeUint32Field 1#32 m.maxJump ++ Proto.encodeUint32Field 2#32 m.maxOooKeys
def encodedLen (m : ChainParamsPB) : Nat := (encodeRaw m).length
def encode (m : ChainParamsPB) : Bytes := encodeRaw m
end ChainParamsPB

namespace ProtoChainParams
abbrev mergeField := ChainParamsPB.mergeField
abbrev merge := ChainParamsPB.merge
abbrev decode := ChainParamsPB.decode
abbrev encodeRaw := ChainParamsPB.encodeRaw
abbrev encodedLen := ChainParamsPB.encodedLen
abbrev encode := ChainParamsPB.encode
end ProtoChainParams

namespace EpochDirectionPB
open Proto in
def mergeField (m : EpochDirectionPB) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (EpochDirectionPB × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeUint32 wt bs; .ok ({ m with ctr := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with next := v }, bs')
  else if tag == 3#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with prev := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def merge (m : EpochDirectionPB) (bs : Bytes) : Except DecodeErr EpochDirectionPB := Proto.mergeTopLevelMessage mergeField m bs
def decode (bs : Bytes) : Except DecodeErr EpochDirectionPB := Proto.decodeTopLevelMessage mergeField bs
def encodeRaw (m : EpochDirectionPB) : Bytes :=
  Proto.encodeUint32Field 1#32 m.ctr ++ Proto.encodeBytesField 2#32 m.next ++ Proto.encodeBytesField 3#32 m.prev
def encodedLen (m : EpochDirectionPB) : Nat := (encodeRaw m).length
def encode (m : EpochDirectionPB) : Bytes := encodeRaw m
end EpochDirectionPB

namespace ProtoEpochDirection
abbrev mergeField := EpochDirectionPB.mergeField
abbrev merge := EpochDirectionPB.merge
abbrev decode := EpochDirectionPB.decode
abbrev encodeRaw := EpochDirectionPB.encodeRaw
abbrev encodedLen := EpochDirectionPB.encodedLen
abbrev encode := EpochDirectionPB.encode
end ProtoEpochDirection

namespace ChainEpochPB
open Proto in
def mergeField (m : ChainEpochPB) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (ChainEpochPB × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeOptMessage EpochDirectionPB.mergeField wt m.send bs depth; .ok ({ m with send := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage EpochDirectionPB.mergeField wt m.recv bs depth; .ok ({ m with recv := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def merge (m : ChainEpochPB) (bs : Bytes) : Except DecodeErr ChainEpochPB := Proto.mergeTopLevelMessage mergeField m bs
def decode (bs : Bytes) : Except DecodeErr ChainEpochPB := Proto.decodeTopLevelMessage mergeField bs
def encodeRaw (m : ChainEpochPB) : Bytes :=
  Proto.encodeOptMessage EpochDirectionPB.encodeRaw 1#32 m.send ++ Proto.encodeOptMessage EpochDirectionPB.encodeRaw 2#32 m.recv
def encodedLen (m : ChainEpochPB) : Nat := (encodeRaw m).length
def encode (m : ChainEpochPB) : Bytes := encodeRaw m
end ChainEpochPB

namespace ProtoChainEpoch
abbrev mergeField := ChainEpochPB.mergeField
abbrev merge := ChainEpochPB.merge
abbrev decode := ChainEpochPB.decode
abbrev encodeRaw := ChainEpochPB.encodeRaw
abbrev encodedLen := ChainEpochPB.encodedLen
abbrev encode := ChainEpochPB.encode
end ProtoChainEpoch

namespace ChainPB
open Proto in
def mergeField (m : ChainPB) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (ChainPB × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeInt32 wt bs; .ok ({ m with direction := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeUint64 wt bs; .ok ({ m with currentEpoch := v }, bs')
  else if tag == 3#32 then let (v, bs') ← mergeRepeatedMessage ChainEpochPB.mergeField wt m.links bs depth; .ok ({ m with links := v }, bs')
  else if tag == 4#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with nextRoot := v }, bs')
  else if tag == 5#32 then let (v, bs') ← mergeUint64 wt bs; .ok ({ m with sendEpoch := v }, bs')
  else if tag == 6#32 then let (v, bs') ← mergeOptMessage ChainParamsPB.mergeField wt m.params bs depth; .ok ({ m with params := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def merge (m : ChainPB) (bs : Bytes) : Except DecodeErr ChainPB := Proto.mergeTopLevelMessage mergeField m bs
def decode (bs : Bytes) : Except DecodeErr ChainPB := Proto.decodeTopLevelMessage mergeField bs
def encodeRaw (m : ChainPB) : Bytes :=
  Proto.encodeInt32Field 1#32 m.direction ++ Proto.encodeUint64Field 2#32 m.currentEpoch ++
  Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 m.links ++
  Proto.encodeBytesField 4#32 m.nextRoot ++ Proto.encodeUint64Field 5#32 m.sendEpoch ++
  Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 m.params
def encodedLen (m : ChainPB) : Nat := (encodeRaw m).length
def encode (m : ChainPB) : Bytes := encodeRaw m
end ChainPB

namespace ProtoChain
abbrev mergeField := ChainPB.mergeField
abbrev merge := ChainPB.merge
abbrev decode := ChainPB.decode
abbrev encodeRaw := ChainPB.encodeRaw
abbrev encodedLen := ChainPB.encodedLen
abbrev encode := ChainPB.encode
end ProtoChain

namespace VersionNegotiationPB
open Proto in
def mergeField (m : VersionNegotiationPB) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (VersionNegotiationPB × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with authKey := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeInt32 wt bs; .ok ({ m with direction := v }, bs')
  else if tag == 3#32 then let (v, bs') ← mergeInt32 wt bs; .ok ({ m with minVersion := v }, bs')
  else if tag == 4#32 then let (v, bs') ← mergeOptMessage ChainParamsPB.mergeField wt m.chainParams bs depth; .ok ({ m with chainParams := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def merge (m : VersionNegotiationPB) (bs : Bytes) : Except DecodeErr VersionNegotiationPB := Proto.mergeTopLevelMessage mergeField m bs
def decode (bs : Bytes) : Except DecodeErr VersionNegotiationPB := Proto.decodeTopLevelMessage mergeField bs
def encodeRaw (m : VersionNegotiationPB) : Bytes :=
  Proto.encodeBytesField 1#32 m.authKey ++ Proto.encodeInt32Field 2#32 m.direction ++
  Proto.encodeInt32Field 3#32 m.minVersion ++ Proto.encodeOptMessage ChainParamsPB.encodeRaw 4#32 m.chainParams
def encodedLen (m : VersionNegotiationPB) : Nat := (encodeRaw m).length
def encode (m : VersionNegotiationPB) : Bytes := encodeRaw m
end VersionNegotiationPB

namespace ProtoVersionNegotiation
abbrev mergeField := VersionNegotiationPB.mergeField
abbrev merge := VersionNegotiationPB.merge
abbrev decode := VersionNegotiationPB.decode
abbrev encodeRaw := VersionNegotiationPB.encodeRaw
abbrev encodedLen := VersionNegotiationPB.encodedLen
abbrev encode := VersionNegotiationPB.encode
end ProtoVersionNegotiation

namespace ProtoChunk
open Proto in
def mergeField (m : ProtoChunk) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (ProtoChunk × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeUint32 wt bs; .ok ({ m with index := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with data := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def merge (m : ProtoChunk) (bs : Bytes) : Except DecodeErr ProtoChunk := Proto.mergeTopLevelMessage mergeField m bs
def decode (bs : Bytes) : Except DecodeErr ProtoChunk := Proto.decodeTopLevelMessage mergeField bs
def encodeRaw (m : ProtoChunk) : Bytes := Proto.encodeUint32Field 1#32 m.index ++ Proto.encodeBytesField 2#32 m.data
def encodedLen (m : ProtoChunk) : Nat := (encodeRaw m).length
def encode (m : ProtoChunk) : Bytes := encodeRaw m
end ProtoChunk

namespace V1Msg.InnerMsg
open Proto in
def merge (cur : Option V1Msg.InnerMsg) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (Option V1Msg.InnerMsg × Bytes) := do
  if tag == 3#32 then
    let prev := match cur with | some (.hdr v) => v | _ => default
    let (v, rest) ← mergeMessage ProtoChunk.mergeField wt prev bs depth; .ok (some (.hdr v), rest)
  else if tag == 4#32 then
    let prev := match cur with | some (.ek v) => v | _ => default
    let (v, rest) ← mergeMessage ProtoChunk.mergeField wt prev bs depth; .ok (some (.ek v), rest)
  else if tag == 5#32 then
    let prev := match cur with | some (.ekCt1Ack v) => v | _ => default
    let (v, rest) ← mergeMessage ProtoChunk.mergeField wt prev bs depth; .ok (some (.ekCt1Ack v), rest)
  else if tag == 6#32 then let (v, rest) ← mergeBool wt bs; .ok (some (.ct1Ack v), rest)
  else if tag == 7#32 then
    let prev := match cur with | some (.ct1 v) => v | _ => default
    let (v, rest) ← mergeMessage ProtoChunk.mergeField wt prev bs depth; .ok (some (.ct1 v), rest)
  else if tag == 8#32 then
    let prev := match cur with | some (.ct2 v) => v | _ => default
    let (v, rest) ← mergeMessage ProtoChunk.mergeField wt prev bs depth; .ok (some (.ct2 v), rest)
  else let rest ← skipField wt tag bs depth; .ok (cur, rest)
def encode : V1Msg.InnerMsg → Bytes
  | .hdr v => Proto.encodeMessage ProtoChunk.encodeRaw 3#32 v | .ek v => Proto.encodeMessage ProtoChunk.encodeRaw 4#32 v
  | .ekCt1Ack v => Proto.encodeMessage ProtoChunk.encodeRaw 5#32 v | .ct1Ack v => Proto.encodeBoolOneof 6#32 v
  | .ct1 v => Proto.encodeMessage ProtoChunk.encodeRaw 7#32 v | .ct2 v => Proto.encodeMessage ProtoChunk.encodeRaw 8#32 v
def encodedLen (im : V1Msg.InnerMsg) : Nat := (encode im).length
end V1Msg.InnerMsg

namespace V1Msg
open Proto in
def mergeField (m : V1Msg) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (V1Msg × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeUint64 wt bs; .ok ({ m with epoch := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeUint32 wt bs; .ok ({ m with index := v }, bs')
  else if tag ≥ 3#32 && tag ≤ 8#32 then
    let (im', bs') ← V1Msg.InnerMsg.merge m.innerMsg tag wt bs depth; .ok ({ m with innerMsg := im' }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def merge (m : V1Msg) (bs : Bytes) : Except DecodeErr V1Msg := Proto.mergeTopLevelMessage mergeField m bs
def decode (bs : Bytes) : Except DecodeErr V1Msg := Proto.decodeTopLevelMessage mergeField bs
def encodeRaw (m : V1Msg) : Bytes :=
  Proto.encodeUint64Field 1#32 m.epoch ++ Proto.encodeUint32Field 2#32 m.index ++
  match m.innerMsg with | none => [] | some im => V1Msg.InnerMsg.encode im
def encodedLen (m : V1Msg) : Nat := (encodeRaw m).length
def encode (m : V1Msg) : Bytes := encodeRaw m
end V1Msg

namespace ProtoAuthenticator
open Proto in
def mergeField (m : ProtoAuthenticator) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (ProtoAuthenticator × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with rootKey := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with macKey := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def merge (m : ProtoAuthenticator) (bs : Bytes) : Except DecodeErr ProtoAuthenticator := Proto.mergeTopLevelMessage mergeField m bs
def decode (bs : Bytes) : Except DecodeErr ProtoAuthenticator := Proto.decodeTopLevelMessage mergeField bs
def encodeRaw (m : ProtoAuthenticator) : Bytes := Proto.encodeBytesField 1#32 m.rootKey ++ Proto.encodeBytesField 2#32 m.macKey
def encodedLen (m : ProtoAuthenticator) : Nat := (encodeRaw m).length
def encode (m : ProtoAuthenticator) : Bytes := encodeRaw m
end ProtoAuthenticator

namespace V1State.Unchunked
open Proto
def mergeField (m : V1State.Unchunked) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (V1State.Unchunked × Bytes) := do let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr V1State.Unchunked := decodeTopLevelMessage mergeField bs
def encodeRaw (_ : V1State.Unchunked) : Bytes := []
def encodedLen (_ : V1State.Unchunked) : Nat := 0
def encode (m : V1State.Unchunked) : Bytes := encodeRaw m

namespace KeysUnsampled
def mergeField (m : KeysUnsampled) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (KeysUnsampled × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeUint64 wt bs; .ok ({ m with epoch := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage ProtoAuthenticator.mergeField wt m.auth bs depth; .ok ({ m with auth := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr KeysUnsampled := decodeTopLevelMessage mergeField bs
def encodeRaw (m : KeysUnsampled) : Bytes := encodeUint64Field 1#32 m.epoch ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 m.auth
def encodedLen (m : KeysUnsampled) : Nat := (encodeRaw m).length
def encode (m : KeysUnsampled) : Bytes := encodeRaw m
end KeysUnsampled

namespace HeaderSent
def mergeField (m : HeaderSent) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (HeaderSent × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeUint64 wt bs; .ok ({ m with epoch := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage ProtoAuthenticator.mergeField wt m.auth bs depth; .ok ({ m with auth := v }, bs')
  else if tag == 3#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with ek := v }, bs')
  else if tag == 4#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with dk := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr HeaderSent := decodeTopLevelMessage mergeField bs
def encodeRaw (m : HeaderSent) : Bytes := encodeUint64Field 1#32 m.epoch ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 m.auth ++ encodeBytesField 3#32 m.ek ++ encodeBytesField 4#32 m.dk
def encodedLen (m : HeaderSent) : Nat := (encodeRaw m).length
def encode (m : HeaderSent) : Bytes := encodeRaw m
end HeaderSent

namespace EkSent
def mergeField (m : EkSent) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (EkSent × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeUint64 wt bs; .ok ({ m with epoch := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage ProtoAuthenticator.mergeField wt m.auth bs depth; .ok ({ m with auth := v }, bs')
  else if tag == 3#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with dk := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr EkSent := decodeTopLevelMessage mergeField bs
def encodeRaw (m : EkSent) : Bytes := encodeUint64Field 1#32 m.epoch ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 m.auth ++ encodeBytesField 3#32 m.dk
def encodedLen (m : EkSent) : Nat := (encodeRaw m).length
def encode (m : EkSent) : Bytes := encodeRaw m
end EkSent

namespace EkSentCt1Received
def mergeField (m : EkSentCt1Received) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (EkSentCt1Received × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeUint64 wt bs; .ok ({ m with epoch := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage ProtoAuthenticator.mergeField wt m.auth bs depth; .ok ({ m with auth := v }, bs')
  else if tag == 3#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with dk := v }, bs')
  else if tag == 4#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with ct1 := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr EkSentCt1Received := decodeTopLevelMessage mergeField bs
def encodeRaw (m : EkSentCt1Received) : Bytes := encodeUint64Field 1#32 m.epoch ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 m.auth ++ encodeBytesField 3#32 m.dk ++ encodeBytesField 4#32 m.ct1
def encodedLen (m : EkSentCt1Received) : Nat := (encodeRaw m).length
def encode (m : EkSentCt1Received) : Bytes := encodeRaw m
end EkSentCt1Received

namespace NoHeaderReceived
def mergeField (m : NoHeaderReceived) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (NoHeaderReceived × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeUint64 wt bs; .ok ({ m with epoch := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage ProtoAuthenticator.mergeField wt m.auth bs depth; .ok ({ m with auth := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr NoHeaderReceived := decodeTopLevelMessage mergeField bs
def encodeRaw (m : NoHeaderReceived) : Bytes := encodeUint64Field 1#32 m.epoch ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 m.auth
def encodedLen (m : NoHeaderReceived) : Nat := (encodeRaw m).length
def encode (m : NoHeaderReceived) : Bytes := encodeRaw m
end NoHeaderReceived

namespace HeaderReceived
def mergeField (m : HeaderReceived) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (HeaderReceived × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeUint64 wt bs; .ok ({ m with epoch := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage ProtoAuthenticator.mergeField wt m.auth bs depth; .ok ({ m with auth := v }, bs')
  else if tag == 3#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with hdr := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr HeaderReceived := decodeTopLevelMessage mergeField bs
def encodeRaw (m : HeaderReceived) : Bytes := encodeUint64Field 1#32 m.epoch ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 m.auth ++ encodeBytesField 3#32 m.hdr
def encodedLen (m : HeaderReceived) : Nat := (encodeRaw m).length
def encode (m : HeaderReceived) : Bytes := encodeRaw m
end HeaderReceived

namespace EkReceived
def mergeField (m : EkReceived) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (EkReceived × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeUint64 wt bs; .ok ({ m with epoch := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage ProtoAuthenticator.mergeField wt m.auth bs depth; .ok ({ m with auth := v }, bs')
  else if tag == 3#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with hdr := v }, bs')
  else if tag == 4#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with ek := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr EkReceived := decodeTopLevelMessage mergeField bs
def encodeRaw (m : EkReceived) : Bytes := encodeUint64Field 1#32 m.epoch ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 m.auth ++ encodeBytesField 3#32 m.hdr ++ encodeBytesField 4#32 m.ek
def encodedLen (m : EkReceived) : Nat := (encodeRaw m).length
def encode (m : EkReceived) : Bytes := encodeRaw m
end EkReceived

namespace Ct1Sent
def mergeField (m : Ct1Sent) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (Ct1Sent × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeUint64 wt bs; .ok ({ m with epoch := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage ProtoAuthenticator.mergeField wt m.auth bs depth; .ok ({ m with auth := v }, bs')
  else if tag == 3#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with hdr := v }, bs')
  else if tag == 4#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with es := v }, bs')
  else if tag == 5#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with ct1 := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr Ct1Sent := decodeTopLevelMessage mergeField bs
def encodeRaw (m : Ct1Sent) : Bytes := encodeUint64Field 1#32 m.epoch ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 m.auth ++ encodeBytesField 3#32 m.hdr ++ encodeBytesField 4#32 m.es ++ encodeBytesField 5#32 m.ct1
def encodedLen (m : Ct1Sent) : Nat := (encodeRaw m).length
def encode (m : Ct1Sent) : Bytes := encodeRaw m
end Ct1Sent

namespace Ct1SentEkReceived
def mergeField (m : Ct1SentEkReceived) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (Ct1SentEkReceived × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeUint64 wt bs; .ok ({ m with epoch := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage ProtoAuthenticator.mergeField wt m.auth bs depth; .ok ({ m with auth := v }, bs')
  else if tag == 3#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with es := v }, bs')
  else if tag == 4#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with ek := v }, bs')
  else if tag == 5#32 then let (v, bs') ← mergeBytes wt bs; .ok ({ m with ct1 := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr Ct1SentEkReceived := decodeTopLevelMessage mergeField bs
def encodeRaw (m : Ct1SentEkReceived) : Bytes := encodeUint64Field 1#32 m.epoch ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 m.auth ++ encodeBytesField 3#32 m.es ++ encodeBytesField 4#32 m.ek ++ encodeBytesField 5#32 m.ct1
def encodedLen (m : Ct1SentEkReceived) : Nat := (encodeRaw m).length
def encode (m : Ct1SentEkReceived) : Bytes := encodeRaw m
end Ct1SentEkReceived

namespace Ct2Sent
def mergeField (m : Ct2Sent) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (Ct2Sent × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeUint64 wt bs; .ok ({ m with epoch := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage ProtoAuthenticator.mergeField wt m.auth bs depth; .ok ({ m with auth := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr Ct2Sent := decodeTopLevelMessage mergeField bs
def encodeRaw (m : Ct2Sent) : Bytes := encodeUint64Field 1#32 m.epoch ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 m.auth
def encodedLen (m : Ct2Sent) : Nat := (encodeRaw m).length
def encode (m : Ct2Sent) : Bytes := encodeRaw m
end Ct2Sent
end V1State.Unchunked

namespace V1State.Chunked
open Proto
namespace KeysUnsampled
def mergeField (m : KeysUnsampled) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (KeysUnsampled × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeOptMessage Unchunked.KeysUnsampled.mergeField wt m.uc bs depth; .ok ({ m with uc := v }, bs') else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr KeysUnsampled := decodeTopLevelMessage mergeField bs
def encodeRaw (m : KeysUnsampled) : Bytes := encodeOptMessage Unchunked.KeysUnsampled.encodeRaw 1#32 m.uc
def encodedLen (m : KeysUnsampled) : Nat := (encodeRaw m).length
def encode (m : KeysUnsampled) : Bytes := encodeRaw m
end KeysUnsampled

namespace KeysSampled
def mergeField (m : KeysSampled) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (KeysSampled × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeOptMessage Unchunked.HeaderSent.mergeField wt m.uc bs depth; .ok ({ m with uc := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage PolynomialEncoder.mergeField wt m.sendingHdr bs depth; .ok ({ m with sendingHdr := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr KeysSampled := decodeTopLevelMessage mergeField bs
def encodeRaw (m : KeysSampled) : Bytes := encodeOptMessage Unchunked.HeaderSent.encodeRaw 1#32 m.uc ++ encodeOptMessage PolynomialEncoder.encodeRaw 2#32 m.sendingHdr
def encodedLen (m : KeysSampled) : Nat := (encodeRaw m).length
def encode (m : KeysSampled) : Bytes := encodeRaw m
end KeysSampled

namespace HeaderSent
def mergeField (m : HeaderSent) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (HeaderSent × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeOptMessage Unchunked.EkSent.mergeField wt m.uc bs depth; .ok ({ m with uc := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage PolynomialEncoder.mergeField wt m.sendingEk bs depth; .ok ({ m with sendingEk := v }, bs')
  else if tag == 3#32 then let (v, bs') ← mergeOptMessage PolynomialDecoder.mergeField wt m.receivingCt1 bs depth; .ok ({ m with receivingCt1 := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr HeaderSent := decodeTopLevelMessage mergeField bs
def encodeRaw (m : HeaderSent) : Bytes := encodeOptMessage Unchunked.EkSent.encodeRaw 1#32 m.uc ++ encodeOptMessage PolynomialEncoder.encodeRaw 2#32 m.sendingEk ++ encodeOptMessage PolynomialDecoder.encodeRaw 3#32 m.receivingCt1
def encodedLen (m : HeaderSent) : Nat := (encodeRaw m).length
def encode (m : HeaderSent) : Bytes := encodeRaw m
end HeaderSent

namespace Ct1Received
def mergeField (m : Ct1Received) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (Ct1Received × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeOptMessage Unchunked.EkSentCt1Received.mergeField wt m.uc bs depth; .ok ({ m with uc := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage PolynomialEncoder.mergeField wt m.sendingEk bs depth; .ok ({ m with sendingEk := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr Ct1Received := decodeTopLevelMessage mergeField bs
def encodeRaw (m : Ct1Received) : Bytes := encodeOptMessage Unchunked.EkSentCt1Received.encodeRaw 1#32 m.uc ++ encodeOptMessage PolynomialEncoder.encodeRaw 2#32 m.sendingEk
def encodedLen (m : Ct1Received) : Nat := (encodeRaw m).length
def encode (m : Ct1Received) : Bytes := encodeRaw m
end Ct1Received

namespace EkSentCt1Received
def mergeField (m : EkSentCt1Received) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (EkSentCt1Received × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeOptMessage Unchunked.EkSentCt1Received.mergeField wt m.uc bs depth; .ok ({ m with uc := v }, bs')
  else if tag == 3#32 then let (v, bs') ← mergeOptMessage PolynomialDecoder.mergeField wt m.receivingCt2 bs depth; .ok ({ m with receivingCt2 := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr EkSentCt1Received := decodeTopLevelMessage mergeField bs
def encodeRaw (m : EkSentCt1Received) : Bytes := encodeOptMessage Unchunked.EkSentCt1Received.encodeRaw 1#32 m.uc ++ encodeOptMessage PolynomialDecoder.encodeRaw 3#32 m.receivingCt2
def encodedLen (m : EkSentCt1Received) : Nat := (encodeRaw m).length
def encode (m : EkSentCt1Received) : Bytes := encodeRaw m
end EkSentCt1Received

namespace NoHeaderReceived
def mergeField (m : NoHeaderReceived) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (NoHeaderReceived × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeOptMessage Unchunked.NoHeaderReceived.mergeField wt m.uc bs depth; .ok ({ m with uc := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage PolynomialDecoder.mergeField wt m.receivingHdr bs depth; .ok ({ m with receivingHdr := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr NoHeaderReceived := decodeTopLevelMessage mergeField bs
def encodeRaw (m : NoHeaderReceived) : Bytes := encodeOptMessage Unchunked.NoHeaderReceived.encodeRaw 1#32 m.uc ++ encodeOptMessage PolynomialDecoder.encodeRaw 2#32 m.receivingHdr
def encodedLen (m : NoHeaderReceived) : Nat := (encodeRaw m).length
def encode (m : NoHeaderReceived) : Bytes := encodeRaw m
end NoHeaderReceived

namespace HeaderReceived
def mergeField (m : HeaderReceived) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (HeaderReceived × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeOptMessage Unchunked.HeaderReceived.mergeField wt m.uc bs depth; .ok ({ m with uc := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage PolynomialDecoder.mergeField wt m.receivingEk bs depth; .ok ({ m with receivingEk := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr HeaderReceived := decodeTopLevelMessage mergeField bs
def encodeRaw (m : HeaderReceived) : Bytes := encodeOptMessage Unchunked.HeaderReceived.encodeRaw 1#32 m.uc ++ encodeOptMessage PolynomialDecoder.encodeRaw 2#32 m.receivingEk
def encodedLen (m : HeaderReceived) : Nat := (encodeRaw m).length
def encode (m : HeaderReceived) : Bytes := encodeRaw m
end HeaderReceived

namespace Ct1Sampled
def mergeField (m : Ct1Sampled) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (Ct1Sampled × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeOptMessage Unchunked.Ct1Sent.mergeField wt m.uc bs depth; .ok ({ m with uc := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage PolynomialEncoder.mergeField wt m.sendingCt1 bs depth; .ok ({ m with sendingCt1 := v }, bs')
  else if tag == 3#32 then let (v, bs') ← mergeOptMessage PolynomialDecoder.mergeField wt m.receivingEk bs depth; .ok ({ m with receivingEk := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr Ct1Sampled := decodeTopLevelMessage mergeField bs
def encodeRaw (m : Ct1Sampled) : Bytes := encodeOptMessage Unchunked.Ct1Sent.encodeRaw 1#32 m.uc ++ encodeOptMessage PolynomialEncoder.encodeRaw 2#32 m.sendingCt1 ++ encodeOptMessage PolynomialDecoder.encodeRaw 3#32 m.receivingEk
def encodedLen (m : Ct1Sampled) : Nat := (encodeRaw m).length
def encode (m : Ct1Sampled) : Bytes := encodeRaw m
end Ct1Sampled

namespace EkReceivedCt1Sampled
def mergeField (m : EkReceivedCt1Sampled) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (EkReceivedCt1Sampled × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeOptMessage Unchunked.Ct1SentEkReceived.mergeField wt m.uc bs depth; .ok ({ m with uc := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage PolynomialEncoder.mergeField wt m.sendingCt1 bs depth; .ok ({ m with sendingCt1 := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr EkReceivedCt1Sampled := decodeTopLevelMessage mergeField bs
def encodeRaw (m : EkReceivedCt1Sampled) : Bytes := encodeOptMessage Unchunked.Ct1SentEkReceived.encodeRaw 1#32 m.uc ++ encodeOptMessage PolynomialEncoder.encodeRaw 2#32 m.sendingCt1
def encodedLen (m : EkReceivedCt1Sampled) : Nat := (encodeRaw m).length
def encode (m : EkReceivedCt1Sampled) : Bytes := encodeRaw m
end EkReceivedCt1Sampled

namespace Ct1Acknowledged
def mergeField (m : Ct1Acknowledged) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (Ct1Acknowledged × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeOptMessage Unchunked.Ct1Sent.mergeField wt m.uc bs depth; .ok ({ m with uc := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage PolynomialDecoder.mergeField wt m.receivingEk bs depth; .ok ({ m with receivingEk := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr Ct1Acknowledged := decodeTopLevelMessage mergeField bs
def encodeRaw (m : Ct1Acknowledged) : Bytes := encodeOptMessage Unchunked.Ct1Sent.encodeRaw 1#32 m.uc ++ encodeOptMessage PolynomialDecoder.encodeRaw 2#32 m.receivingEk
def encodedLen (m : Ct1Acknowledged) : Nat := (encodeRaw m).length
def encode (m : Ct1Acknowledged) : Bytes := encodeRaw m
end Ct1Acknowledged

namespace Ct2Sampled
def mergeField (m : Ct2Sampled) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) : Except DecodeErr (Ct2Sampled × Bytes) := do
  if tag == 1#32 then let (v, bs') ← mergeOptMessage Unchunked.Ct2Sent.mergeField wt m.uc bs depth; .ok ({ m with uc := v }, bs')
  else if tag == 2#32 then let (v, bs') ← mergeOptMessage PolynomialEncoder.mergeField wt m.sendingCt2 bs depth; .ok ({ m with sendingCt2 := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def decode (bs : Bytes) : Except DecodeErr Ct2Sampled := decodeTopLevelMessage mergeField bs
def encodeRaw (m : Ct2Sampled) : Bytes := encodeOptMessage Unchunked.Ct2Sent.encodeRaw 1#32 m.uc ++ encodeOptMessage PolynomialEncoder.encodeRaw 2#32 m.sendingCt2
def encodedLen (m : Ct2Sampled) : Nat := (encodeRaw m).length
def encode (m : Ct2Sampled) : Bytes := encodeRaw m
end Ct2Sampled
end V1State.Chunked

namespace V1State.InnerState
open Proto in
def merge (cur : Option V1State.InnerState) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (Option V1State.InnerState × Bytes) := do
  if tag == 1#32 then
    let (v, bs') ← mergeMessage Chunked.KeysUnsampled.mergeField wt (match cur with | some (.keysUnsampled v) => v | _ => default) bs depth; .ok (some (.keysUnsampled v), bs')
  else if tag == 2#32 then
    let (v, bs') ← mergeMessage Chunked.KeysSampled.mergeField wt (match cur with | some (.keysSampled v) => v | _ => default) bs depth; .ok (some (.keysSampled v), bs')
  else if tag == 3#32 then
    let (v, bs') ← mergeMessage Chunked.HeaderSent.mergeField wt (match cur with | some (.headerSent v) => v | _ => default) bs depth; .ok (some (.headerSent v), bs')
  else if tag == 4#32 then
    let (v, bs') ← mergeMessage Chunked.Ct1Received.mergeField wt (match cur with | some (.ct1Received v) => v | _ => default) bs depth; .ok (some (.ct1Received v), bs')
  else if tag == 5#32 then
    let (v, bs') ← mergeMessage Chunked.EkSentCt1Received.mergeField wt (match cur with | some (.ekSentCt1Received v) => v | _ => default) bs depth; .ok (some (.ekSentCt1Received v), bs')
  else if tag == 6#32 then
    let (v, bs') ← mergeMessage Chunked.NoHeaderReceived.mergeField wt (match cur with | some (.noHeaderReceived v) => v | _ => default) bs depth; .ok (some (.noHeaderReceived v), bs')
  else if tag == 7#32 then
    let (v, bs') ← mergeMessage Chunked.HeaderReceived.mergeField wt (match cur with | some (.headerReceived v) => v | _ => default) bs depth; .ok (some (.headerReceived v), bs')
  else if tag == 8#32 then
    let (v, bs') ← mergeMessage Chunked.Ct1Sampled.mergeField wt (match cur with | some (.ct1Sampled v) => v | _ => default) bs depth; .ok (some (.ct1Sampled v), bs')
  else if tag == 9#32 then
    let (v, bs') ← mergeMessage Chunked.EkReceivedCt1Sampled.mergeField wt (match cur with | some (.ekReceivedCt1Sampled v) => v | _ => default) bs depth; .ok (some (.ekReceivedCt1Sampled v), bs')
  else if tag == 10#32 then
    let (v, bs') ← mergeMessage Chunked.Ct1Acknowledged.mergeField wt (match cur with | some (.ct1Acknowledged v) => v | _ => default) bs depth; .ok (some (.ct1Acknowledged v), bs')
  else if tag == 11#32 then
    let (v, bs') ← mergeMessage Chunked.Ct2Sampled.mergeField wt (match cur with | some (.ct2Sampled v) => v | _ => default) bs depth; .ok (some (.ct2Sampled v), bs')
  else let bs' ← skipField wt tag bs depth; .ok (cur, bs')
def encode : V1State.InnerState → Bytes
  | .keysUnsampled v        => Proto.encodeMessage Chunked.KeysUnsampled.encodeRaw 1#32 v
  | .keysSampled v          => Proto.encodeMessage Chunked.KeysSampled.encodeRaw 2#32 v
  | .headerSent v           => Proto.encodeMessage Chunked.HeaderSent.encodeRaw 3#32 v
  | .ct1Received v          => Proto.encodeMessage Chunked.Ct1Received.encodeRaw 4#32 v
  | .ekSentCt1Received v    => Proto.encodeMessage Chunked.EkSentCt1Received.encodeRaw 5#32 v
  | .noHeaderReceived v     => Proto.encodeMessage Chunked.NoHeaderReceived.encodeRaw 6#32 v
  | .headerReceived v       => Proto.encodeMessage Chunked.HeaderReceived.encodeRaw 7#32 v
  | .ct1Sampled v           => Proto.encodeMessage Chunked.Ct1Sampled.encodeRaw 8#32 v
  | .ekReceivedCt1Sampled v => Proto.encodeMessage Chunked.EkReceivedCt1Sampled.encodeRaw 9#32 v
  | .ct1Acknowledged v      => Proto.encodeMessage Chunked.Ct1Acknowledged.encodeRaw 10#32 v
  | .ct2Sampled v           => Proto.encodeMessage Chunked.Ct2Sampled.encodeRaw 11#32 v
def encodedLen (is : V1State.InnerState) : Nat := (encode is).length
end V1State.InnerState

namespace V1State
open Proto in
def mergeField (m : V1State) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (V1State × Bytes) := do
  if tag ≥ 1#32 && tag ≤ 11#32 then
    let (is', bs') ← V1State.InnerState.merge m.innerState tag wt bs depth; .ok ({ m with innerState := is' }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def merge (m : V1State) (bs : Bytes) : Except DecodeErr V1State := Proto.mergeTopLevelMessage mergeField m bs
def decode (bs : Bytes) : Except DecodeErr V1State := Proto.decodeTopLevelMessage mergeField bs
def encodeRaw (m : V1State) : Bytes := match m.innerState with | none => [] | some is => V1State.InnerState.encode is
def encodedLen (m : V1State) : Nat := (encodeRaw m).length
def encode (m : V1State) : Bytes := encodeRaw m
end V1State

namespace PqRatchetState.Inner
open Proto in
def merge (cur : Option PqRatchetState.Inner) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (Option PqRatchetState.Inner × Bytes) := do
  if tag == 3#32 then
    let prev := match cur with | some (.v1 v) => v | none => default
    let (v, bs') ← mergeMessage V1State.mergeField wt prev bs depth; .ok (some (.v1 v), bs')
  else let bs' ← skipField wt tag bs depth; .ok (cur, bs')
def encode : PqRatchetState.Inner → Bytes | .v1 v => Proto.encodeMessage V1State.encodeRaw 3#32 v
def encodedLen (i : PqRatchetState.Inner) : Nat := (encode i).length
end PqRatchetState.Inner

namespace PqRatchetState
open Proto in
def mergeField (m : PqRatchetState) (tag : BitVec 32) (wt : WireType) (bs : Bytes) (depth : Nat) :
    Except DecodeErr (PqRatchetState × Bytes) := do
  if tag == 1#32 then
    let (v, bs') ← mergeOptMessage VersionNegotiationPB.mergeField wt m.versionNegotiation bs depth
    .ok ({ m with versionNegotiation := v }, bs')
  else if tag == 2#32 then
    let (v, bs') ← mergeOptMessage ChainPB.mergeField wt m.chain bs depth
    .ok ({ m with chain := v }, bs')
  else if tag == 3#32 then
    let (v, bs') ← PqRatchetState.Inner.merge m.inner tag wt bs depth
    .ok ({ m with inner := v }, bs')
  else let bs' ← skipField wt tag bs depth; .ok (m, bs')
def merge (m : PqRatchetState) (bs : Bytes) : Except DecodeErr PqRatchetState := Proto.mergeTopLevelMessage mergeField m bs
def decode (bs : Bytes) : Except DecodeErr PqRatchetState := Proto.decodeTopLevelMessage mergeField bs
def encodeRaw (m : PqRatchetState) : Bytes :=
  Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 m.versionNegotiation ++
  Proto.encodeOptMessage ChainPB.encodeRaw 2#32 m.chain ++
  match m.inner with | none => [] | some i => PqRatchetState.Inner.encode i
def encodedLen (m : PqRatchetState) : Nat := (encodeRaw m).length
def encode (m : PqRatchetState) : Bytes := encodeRaw m
end PqRatchetState

/-! ## 4. Top-level Protobuf decoder/encoder entry points (`namespace Proto`) -/

namespace Proto

/-- `PqRatchetState::decode` (`src/lib.rs:503`). -/
def decodeState (bs : Bytes) : Except DecodeErr PqRatchetState := PqRatchetState.decode bs

/-- `spqr::decode_state` (`src/lib.rs:495–505`): returns default `PqRatchetState` on `[]`, and maps
any decode error to `Error::StateDecode`. -/
def spqrDecodeState (bs : Bytes) : Except Error PqRatchetState :=
  if bs.isEmpty then .ok { versionNegotiation := none, chain := none, inner := none }
  else match PqRatchetState.decode bs with | .ok st => .ok st | .error _ => .error .stateDecode

/-- `PqRatchetState::encode_to_vec`. -/
def encodeState (s : PqRatchetState) : Bytes := PqRatchetState.encode s
def decodeV1Msg (bs : Bytes) : Except DecodeErr V1Msg := V1Msg.decode bs
def encodeV1Msg (m : V1Msg) : Bytes := V1Msg.encode m

end Proto

abbrev spqrDecodeState := Proto.spqrDecodeState

/-! ## 5. Kernel-checked round-trip guards -/

theorem guard_varint_roundtrip :
    ([0#64, 1#64, 127#64, 128#64, 16383#64, 16384#64,
      0xffffffff#64, 0x100000000#64, 0x7fffffffffffffff#64, 0xffffffffffffffff#64].all fun v =>
      Proto.decodeVarint (Proto.encodeVarint v) == .ok (v, []) &&
      Proto.encodedLenVarint v == (Proto.encodeVarint v).length) = true := by decide +kernel

theorem guard_varint_10th_byte :
    (Proto.decodeVarint [0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x01#8] ==
      .ok (0x8000000000000000#64, []) &&
     Proto.decodeVarint [0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x02#8] ==
      .error .invalidVarint) = true := by decide +kernel

theorem guard_direction_enums :
    (Direction.fromI32? (Direction.a2b.toI32) == some .a2b &&
     Direction.fromI32? (Direction.b2a.toI32) == some .b2a &&
     Direction.fromI32? (-1#32) == none) = true := by decide +kernel

theorem guard_state_roundtrip_all_v1_variants :
    (let auth : ProtoAuthenticator := { rootKey := [1#8], macKey := [2#8] }
     let pe : PolynomialEncoder := { idx := 2#32, pts := [[3#8]], polys := [[4#8]] }
     let pd : PolynomialDecoder := { ptsNeeded := 2#32, polys := 8#32, pts := [[5#8, 6#8]], isComplete := true }
     let states : List V1State.InnerState :=
       [ .keysUnsampled { uc := some { epoch := 1#64, auth := some auth } }
       , .keysSampled { uc := some { epoch := 2#64, auth := some auth, ek := [7#8], dk := [8#8] }, sendingHdr := some pe }
       , .headerSent { uc := some { epoch := 3#64, auth := some auth, dk := [9#8] }, sendingEk := some pe, receivingCt1 := some pd }
       , .ct1Received { uc := some { epoch := 4#64, auth := some auth, dk := [10#8], ct1 := [11#8] }, sendingEk := some pe }
       , .ekSentCt1Received { uc := some { epoch := 5#64, auth := some auth, dk := [12#8], ct1 := [13#8] }, receivingCt2 := some pd }
       , .noHeaderReceived { uc := some { epoch := 6#64, auth := some auth }, receivingHdr := some pd }
       , .headerReceived { uc := some { epoch := 7#64, auth := some auth, hdr := [14#8] }, receivingEk := some pd }
       , .ct1Sampled { uc := some { epoch := 8#64, auth := some auth, hdr := [15#8], es := [16#8], ct1 := [17#8] }, sendingCt1 := some pe, receivingEk := some pd }
       , .ekReceivedCt1Sampled { uc := some { epoch := 9#64, auth := some auth, es := [18#8], ek := [19#8], ct1 := [20#8] }, sendingCt1 := some pe }
       , .ct1Acknowledged { uc := some { epoch := 10#64, auth := some auth, hdr := [21#8], es := [22#8], ct1 := [23#8] }, receivingEk := some pd }
       , .ct2Sampled { uc := some { epoch := 11#64, auth := some auth }, sendingCt2 := some pe } ]
     states.all fun is =>
       let st : PqRatchetState := { inner := some (.v1 { innerState := some is }) }
       let bs := Proto.encodeState st
       bs.length == PqRatchetState.encodedLen st && Proto.decodeState bs == .ok st) = true := by decide +kernel

theorem guard_v1msg_roundtrip_all_variants :
    (let chk : ProtoChunk := { index := 7#32, data := [0xde#8, 0xad#8, 0xbe#8, 0xef#8] }
     let inners : List (Option V1Msg.InnerMsg) :=
       [ none, some (.hdr chk), some (.ek chk), some (.ekCt1Ack chk),
         some (.ct1Ack false), some (.ct1Ack true), some (.ct1 chk), some (.ct2 chk) ]
     inners.all fun im =>
       let m : V1Msg := { epoch := 9#64, index := 42#32, innerMsg := im }
       let bs := Proto.encodeV1Msg m
       bs.length == V1Msg.encodedLen m && Proto.decodeV1Msg bs == .ok m) = true := by decide +kernel

end CryptoVerification.LibsignalSpqrV1
