/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Concrete.MachineEvents
public import Symbolic.Specifications.Concrete.ImageSymbols
public import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import LibsignalBinary.Specifications.SignalSession.Run

/-!
# Wire and Pre-Key Bundle Codecs

Concrete protobuf and binary wire encoders, decoders, and field accessors for `SignalMessage` /
`trWireMsg` (`DY.Libsignal.Refinement`), `PreKeySignalMessage`, the SPQR message preamble, and the
1813-byte `PublicBundle` blob (`DY.Libsignal.PQXDH.Refinement`).
-/

@[expose] public section

namespace DY.Libsignal.Refinement

open DY.TrWire
export DY.TrWire (PbValue FieldItem EncodingVariation canonicalVariation)
export CryptoVerification.SignalSession (le32)

/-- `len` bytes of `b` starting at `off`. -/
def slice (b : HwBytes) (off len : Nat) : HwBytes := (b.drop off).take len

/-- Protobuf LEB128 varint of `n` padded with `pad` redundant continuation bytes (`pad = 0` is
minimal). -/
def paddedVarint (n pad : Nat) : HwBytes :=
  if n < 128 ∧ pad = 0 then [BitVec.ofNat 8 n]
  else BitVec.ofNat 8 (n % 128 + 128) :: paddedVarint (n / 128) (if n < 128 then pad - 1 else pad)
termination_by n + pad
decreasing_by all_goals (split <;> omega)

/-- Encode one protobuf field with `keyPad` and `valuePad` varint padding. -/
def encodeField (tag keyPad valuePad : Nat) : PbValue → HwBytes
  | .varint n => paddedVarint (tag * 8) keyPad ++ paddedVarint n valuePad
  | .bytes b => paddedVarint (tag * 8 + 2) keyPad ++ paddedVarint b.length valuePad ++ b
  | .unknown wt p => paddedVarint (tag * 8 + wt) keyPad ++ p

/-- Fields decoded by `SignalMessage::try_from`. -/
structure WireFields where
  version : Nat
  /-- 32-byte sender ratchet key (excluding the `0x05` type byte). -/
  ratchetKey : HwBytes
  counter : Nat
  previousCounter : Nat
  ciphertext : HwBytes

def knownValue? (v : EncodingVariation) (f : WireFields) : Nat → Option PbValue
  | 1 => some (.bytes (0x05#8 :: f.ratchetKey ++ v.ratchetKeyTrailingBytes))
  | 2 => some (.varint (f.counter + 2 ^ 32 * v.counterHigh))
  | 3 => some (.varint (f.previousCounter + 2 ^ 32 * v.previousCounterHigh))
  | 4 => some (.bytes f.ciphertext)
  | _ => none

def _root_.DY.TrWire.FieldItem.encode (v : EncodingVariation) (f : WireFields) : FieldItem → HwBytes
  | .known tag kp vp => ((knownValue? v f tag).map (encodeField tag kp vp)).getD []
  | .extra tag x kp vp => encodeField tag kp vp x

/-- Serialize `WireFields` `f` under Double Ratchet encoding variation `v`. -/
def encodeWith (v : EncodingVariation) (f : WireFields) : HwBytes :=
  BitVec.ofNat 8 (f.version * 16 + v.versionLowNibble % 16) ::
    v.fields.flatMap (FieldItem.encode v f)

def trItemEncode (addr : HwBytes) (v : EncodingVariation) (f : WireFields) (pq : HwBytes) :
    FieldItem → HwBytes
  | .known t kp vp =>
    if t = 5 then encodeField 5 kp vp (.bytes pq)
    else if t = 6 then encodeField 6 kp vp (.bytes addr)
    else FieldItem.encode v f (.known t kp vp)
  | .extra t x kp vp => FieldItem.encode v f (.extra t x kp vp)

def honestTrItems (addr pq : HwBytes) : List FieldItem :=
  (if pq = [] then [] else [FieldItem.known 5 0 0]) ++
    (if addr = [] then [] else [FieldItem.known 6 0 0])

def trFields (addr : HwBytes) (v : EncodingVariation) (pq : HwBytes) : List FieldItem :=
  if v = canonicalVariation then v.fields ++ honestTrItems addr pq else v.fields

/-- Serialize a Triple Ratchet `trWireMsg` body from `addr`, `v`, `f`, and `pq`. -/
def trWireBytes (addr : HwBytes) (v : EncodingVariation) (f : WireFields) (pq : HwBytes) :
    HwBytes :=
  BitVec.ofNat 8 (f.version * 16 + v.versionLowNibble % 16) ::
    (trFields addr v pq).flatMap (trItemEncode addr v f pq)

def decodeLittleEndianNat (b : HwBytes) : Nat := b.foldr (fun x acc => x.toNat + 256 * acc) 0

def WireFields.ofBytes (version ratchetKey counter previousCounter ciphertext : HwBytes) :
    WireFields :=
  { version := (version.headD 0).toNat, ratchetKey, counter := decodeLittleEndianNat counter,
    previousCounter := decodeLittleEndianNat previousCounter, ciphertext }

def _root_.DY.TrWire.FieldItem.toWireNats : FieldItem → List Nat
  | .known t kp vp => [0, t, kp, vp]
  | .extra t (.varint n) kp vp => [1, t, n, kp, vp]
  | .extra t (.bytes b) kp vp => [2, t, b.length] ++ b.map (·.toNat) ++ [kp, vp]
  | .extra t (.unknown wt p) kp vp => [3, t, wt, p.length] ++ p.map (·.toNat) ++ [kp, vp]

def _root_.DY.TrWire.EncodingVariation.toNats (v : EncodingVariation) : List Nat :=
  [v.versionLowNibble, v.counterHigh, v.previousCounterHigh, v.ratchetKeyTrailingBytes.length] ++
    v.ratchetKeyTrailingBytes.map (·.toNat) ++ v.fields.flatMap FieldItem.toWireNats

def _root_.DY.TrWire.EncodingVariation.toBytes (v : EncodingVariation) : HwBytes :=
  if v = canonicalVariation then [] else v.toNats.flatMap (paddedVarint · 0)

def readVarint : HwBytes → Option (Nat × HwBytes)
  | [] => none
  | b :: rest =>
    if b.toNat < 128 then some (b.toNat, rest)
    else (readVarint rest).map fun (n, r) => (b.toNat - 128 + 128 * n, r)

def readNats : Nat → HwBytes → Option (List Nat)
  | _, [] => some []
  | 0, _ :: _ => none
  | k + 1, bs@(_ :: _) => do
    let (n, r) ← readVarint bs
    let ns ← readNats k r
    pure (n :: ns)

def takeBytes (k : Nat) (ns : List Nat) : Option (HwBytes × List Nat) :=
  if k ≤ ns.length then some ((ns.take k).map (BitVec.ofNat 8), ns.drop k) else none

def itemsOfNats : Nat → List Nat → Option (List FieldItem)
  | _, [] => some []
  | 0, _ :: _ => none
  | k + 1, 0 :: t :: kp :: vp :: rest => (itemsOfNats k rest).map (.known t kp vp :: ·)
  | k + 1, 1 :: t :: n :: kp :: vp :: rest =>
    (itemsOfNats k rest).map (.extra t (.varint n) kp vp :: ·)
  | k + 1, 2 :: t :: len :: rest =>
    match takeBytes len rest with
    | some (b, kp :: vp :: rest') => (itemsOfNats k rest').map (.extra t (.bytes b) kp vp :: ·)
    | _ => none
  | k + 1, 3 :: t :: wt :: len :: rest =>
    match takeBytes len rest with
    | some (p, kp :: vp :: rest') =>
      (itemsOfNats k rest').map (.extra t (.unknown wt p) kp vp :: ·)
    | _ => none
  | _ + 1, _ :: _ => none

def _root_.DY.TrWire.EncodingVariation.ofNats? : List Nat → Option EncodingVariation
  | low :: ch :: pch :: len :: rest => do
    let (trailing, rest) ← takeBytes len rest
    let fields ← itemsOfNats rest.length rest
    pure ⟨low, trailing, ch, pch, fields⟩
  | _ => none

/-- Decode an `EncodingVariation` from `b` (defaulting to `canonicalVariation` on `[]` or
non-canonical inputs). -/
def _root_.DY.TrWire.EncodingVariation.ofBytes (b : HwBytes) : EncodingVariation :=
  match readNats b.length b >>= EncodingVariation.ofNats? with
  | some v => if v.toBytes = b then v else canonicalVariation
  | none => canonicalVariation

end DY.Libsignal.Refinement

namespace DY.Libsignal.PQXDH.Refinement

open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (le32 slice)
open CryptoVerification.LibsignalProtoCodec (WireType decodeKey encodeBytesField encodeUint32Field
  mergeBytes mergeUint32 skipField recursionLimit protoSignalCodec)
open CryptoVerification.SignalSession (PublicBundle bundleDir)

/-- Protobuf fields of `proto::wire::PreKeySignalMessage`. -/
structure PreKeyProto where
  registrationId : Option (BitVec 32)
  preKeyId : Option (BitVec 32)
  signedPreKeyId : Option (BitVec 32)
  kyberPreKeyId : Option (BitVec 32)
  kyberCiphertext : Option (List (BitVec 8))
  baseKey : Option (List (BitVec 8))
  identityKey : Option (List (BitVec 8))
  message : Option (List (BitVec 8))

/-- Canonical `prost` encoder for `PreKeySignalMessage` (fields 1..8 in ascending tag order). -/
def PreKeyProto.encode (m : PreKeyProto) : List (BitVec 8) :=
  encodeUint32Field 1 m.preKeyId ++
  encodeBytesField 2 m.baseKey ++
  encodeBytesField 3 m.identityKey ++
  encodeBytesField 4 m.message ++
  encodeUint32Field 5 m.registrationId ++
  encodeUint32Field 6 m.signedPreKeyId ++
  encodeUint32Field 7 m.kyberPreKeyId ++
  encodeBytesField 8 m.kyberCiphertext

/-- Header version byte `((v & 0x0F) << 4) | currentVersion`. -/
def versionByte (v : BitVec 8) : BitVec 8 :=
  ((v &&& 0x0F) <<< 4) ||| CryptoGames.LibsignalSession.currentVersion

def spqrMaxVarintBytes : Nat := 10

def spqrVarintAux : Nat → BitVec 64 → List (BitVec 8) → Option (BitVec 64 × List (BitVec 8))
  | _, _, [] => none
  | i, out, b :: rest =>
    let out := out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * i))
    if b &&& 0x80#8 = 0#8 then some (out, rest)
    else if i + 1 = spqrMaxVarintBytes then none
    else spqrVarintAux (i + 1) out rest

/-- SPQR `decode_varint` (at most 10 bytes). -/
def spqrDecodeVarint (bs : List (BitVec 8)) : Option (BitVec 64 × List (BitVec 8)) :=
  spqrVarintAux 0 0#64 bs

/-- Decoded SPQR message preamble (`version`, `epoch`, 32-bit `index`, and `remaining` payload). -/
structure MsgPreamble where
  version : BitVec 8
  epoch : BitVec 64
  index : BitVec 32
  remaining : List (BitVec 8)

/-- SPQR `msg_preamble`: returns `⟨0, 0, 0, []⟩` on `[]`, and otherwise decodes `version`, nonzero
`epoch`, and 32-bit `index`. -/
def msgPreamble? : List (BitVec 8) → Option MsgPreamble
  | [] => some ⟨0#8, 0#64, 0#32, []⟩
  | version :: rest =>
    match spqrDecodeVarint rest with
    | none => none
    | some (epoch, rest) =>
      if epoch = 0#64 then none
      else match spqrDecodeVarint rest with
        | none => none
        | some (index, rest) =>
          if index.toNat < 2 ^ 32 then some ⟨version, epoch, index.setWidth 32, rest⟩
          else none

def emptyPreKeyMsg : PreKeyProto :=
  { registrationId := none, preKeyId := none, signedPreKeyId := none, kyberPreKeyId := none,
    kyberCiphertext := none, baseKey := none, identityKey := none, message := none }

def mergePreKeyField (m : PreKeyProto) (tag : Nat) (wt : WireType) (bs : HwBytes) :
    Option (PreKeyProto × HwBytes) :=
  match tag with
  | 1 => (mergeUint32 wt bs).map fun (v, r) => ({ m with preKeyId := some v }, r)
  | 2 => (mergeBytes wt bs).map fun (v, r) => ({ m with baseKey := some v }, r)
  | 3 => (mergeBytes wt bs).map fun (v, r) => ({ m with identityKey := some v }, r)
  | 4 => (mergeBytes wt bs).map fun (v, r) => ({ m with message := some v }, r)
  | 5 => (mergeUint32 wt bs).map fun (v, r) => ({ m with registrationId := some v }, r)
  | 6 => (mergeUint32 wt bs).map fun (v, r) => ({ m with signedPreKeyId := some v }, r)
  | 7 => (mergeUint32 wt bs).map fun (v, r) => ({ m with kyberPreKeyId := some v }, r)
  | 8 => (mergeBytes wt bs).map fun (v, r) => ({ m with kyberCiphertext := some v }, r)
  | _ => (skipField (2 * bs.length + 2) recursionLimit tag wt bs).map fun r => (m, r)

def decodePreKeyLoop : Nat → PreKeyProto → HwBytes → Option PreKeyProto
  | _, m, [] => some m
  | 0, _, _ :: _ => none
  | fuel + 1, m, bs@(_ :: _) =>
    match decodeKey bs with
    | none => none
    | some ((tag, wt), rest) =>
      match mergePreKeyField m tag wt rest with
      | none => none
      | some (m', rest') => decodePreKeyLoop fuel m' rest'

def decodePreKey (bs : HwBytes) : Option PreKeyProto :=
  decodePreKeyLoop bs.length emptyPreKeyMsg bs

/-- Whether `PublicKey::deserialize` accepts `b` (`0x05` prefix and length `≥ 33`). -/
def ecKeyParses (b : HwBytes) : Bool := b.head? == some 0x05#8 && 33 ≤ b.length

/-- Validated `PreKeySignalMessage` fields accepted by `PreKeySignalMessage::try_from`. -/
structure PreKeyFields where
  version : Nat
  preKeyId : Option (BitVec 32)
  signedPreKeyId : BitVec 32
  kyberPreKeyId : Option (BitVec 32)
  kyberCiphertext : Option HwBytes
  baseKey : HwBytes
  identityKey : HwBytes
  message : HwBytes
  inner : CryptoGames.LibsignalSession.SignalMessage

/-- `PreKeySignalMessage::try_from` (versions 3..4, valid EC keys, and valid inner `SignalMessage`). -/
def parsePreKey (v : HwBytes) : Option PreKeyFields :=
  match v with
  | [] => none
  | vb :: body =>
    let ver := (vb >>> 4).toNat
    if ver < 3 ∨ 4 < ver then none else
    match decodePreKey body with
    | none => none
    | some m =>
      match m.baseKey, m.identityKey, m.message, m.signedPreKeyId with
      | some bk, some ik, some msg, some sid =>
        let kyberOk := (m.kyberPreKeyId.isSome && m.kyberCiphertext.isSome) ||
          (m.kyberPreKeyId.isNone && m.kyberCiphertext.isNone && ver ≤ 3)
        if kyberOk && ecKeyParses bk && ecKeyParses ik then
          match CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg with
          | .ok inner =>
            some { version := ver, preKeyId := m.preKeyId, signedPreKeyId := sid,
                   kyberPreKeyId := m.kyberPreKeyId, kyberCiphertext := m.kyberCiphertext,
                   baseKey := bk, identityKey := ik, message := msg, inner }
          | .error _ => none
        else none
      | _, _, _, _ => none

/-- Decode a `wirePrekeyTag`-prefixed `PreKeySignalMessage` frame. -/
def parsePreKeyWire (b : HwBytes) : Option PreKeyFields :=
  match b with
  | t :: body => if t = wirePrekeyTag then parsePreKey body else none
  | [] => none

/-- Canonical `wirePrekeyTag`-prefixed version-4 `PreKeySignalMessage` wire frame. -/
def preKeyWire (preKeyId : Option (BitVec 32)) (spkId kpkId regId : BitVec 32)
    (ik ek ct msg : HwBytes) : HwBytes :=
  wirePrekeyTag :: versionByte 4#8 ::
    PreKeyProto.encode
      { registrationId := some regId, preKeyId, signedPreKeyId := some spkId,
        kyberPreKeyId := some kpkId, kyberCiphertext := some (0x08#8 :: ct),
        baseKey := some (0x05#8 :: ek), identityKey := some ik, message := some msg }

/-- SPQR message index extracted from the inner `pq_ratchet` preamble (`0` on decode failure). -/
def preKeySpqrIndex (p : PreKeyFields) : UInt32 :=
  ((msgPreamble? p.inner.pqRatchet).map fun x => UInt32.ofNat x.index.toNat).getD 0

/-- Serialize `PublicBundle` `b` to the 1813-byte `session_initiate` bundle blob. -/
def bundleBlob (b : PublicBundle) : HwBytes :=
  le32 b.registrationId ++
    (match b.oneTime with
     | some (id, key) => 1#8 :: (le32 id ++ key)
     | none => List.replicate 38 0#8) ++
    le32 b.signedId ++ b.signedKey ++ b.signedSig ++
    le32 b.kyberId ++ b.kyberKey ++ b.kyberSig ++ b.identityKey

def bundleU32 : HwBytes → Option (BitVec 32)
  | [b0, b1, b2, b3] => some (b3 ++ b2 ++ b1 ++ b0)
  | _ => none

def decodeLe32 (bs : HwBytes) : BitVec 32 :=
  (bundleU32 bs).getD 0#32

def bundleSplitId : HwBytes → Option (BitVec 32 × HwBytes)
  | b0 :: b1 :: b2 :: b3 :: rest => (bundleU32 [b0, b1, b2, b3]).map (·, rest)
  | _ => none

def bundleSplitSigned (file : HwBytes) : Option (BitVec 32 × HwBytes × HwBytes) :=
  match bundleSplitId file with
  | some (id, rest) =>
    if 64 ≤ rest.length then some (id, rest.take (rest.length - 64), rest.drop (rest.length - 64))
    else none
  | none => none

def parseEcKey (b : HwBytes) : Option HwBytes :=
  if ecKeyParses b then some (b.take 33) else none

def parseKyberKey : HwBytes → Option HwBytes
  | t :: rest => if t = 0x08#8 ∧ rest.length = 1568 then some (t :: rest) else none
  | [] => none

/-- Parse a `PublicBundle` from the `bundle/` directory of `d` following `public.rs::read_bundle`. -/
def parseBundleFiles (d : String → Option HwBytes) : Option PublicBundle := do
  let file := fun name => (d (bundleDir ++ "/" ++ name)).getD []
  let identityKey ← parseEcKey (file "identity-key")
  let registrationId ← bundleU32 (file "registration-id")
  let (signedId, spk, signedSig) ← bundleSplitSigned (file "signed-pre-key")
  let (kyberId, kpk, kyberSig) ← bundleSplitSigned (file "kyber-pre-key")
  let oneTime ← (match file "one-time-pre-key" with
    | [] => some none
    | opk => do
      let (id, key) ← bundleSplitId opk
      let key ← parseEcKey key
      some (some (id, key)) : Option (Option (BitVec 32 × HwBytes)))
  let signedKey ← parseEcKey spk
  let kyberKey ← parseKyberKey kpk
  some { identityKey, registrationId, signedId, signedKey, signedSig, kyberId, kyberKey, kyberSig,
         oneTime }

/-! ### `bundleBlob` 1813-byte layout projections -/
namespace BundleBlob

abbrev regId (b : HwBytes) : BitVec 32 := decodeLe32 (slice b 0 4)

abbrev hasOpkByte (b : HwBytes) : Option (BitVec 8) := b[4]?

abbrev opkId (b : HwBytes) : Option (BitVec 32) :=
  if hasOpkByte b == some 1#8 then some (decodeLe32 (slice b 5 4)) else none

abbrev opkPub (b : HwBytes) : HwBytes := slice b 9 33

abbrev spkId (b : HwBytes) : BitVec 32 := decodeLe32 (slice b 42 4)

abbrev spkPub (b : HwBytes) : HwBytes := slice b 46 33

abbrev spkSig (b : HwBytes) : HwBytes := slice b 79 64

abbrev kpkId (b : HwBytes) : BitVec 32 := decodeLe32 (slice b 143 4)

abbrev kpkPub (b : HwBytes) : HwBytes := slice b 147 1569

abbrev kpkSig (b : HwBytes) : HwBytes := slice b 1716 64

abbrev ikPub (b : HwBytes) : HwBytes := slice b 1780 33

end BundleBlob

end DY.Libsignal.PQXDH.Refinement
