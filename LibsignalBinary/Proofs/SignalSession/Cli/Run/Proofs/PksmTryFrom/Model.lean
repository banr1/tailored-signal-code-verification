/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBase
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodePure

/-!
# Total Parse Specification for `PreKeySignalMessage::try_from`

Defines `pksmParse b`, the functional specification of
`<PreKeySignalMessage as TryFrom<&[u8]>>::try_from(b)` on every input byte list `b`:
1. `b` is non-empty and its high version nibble `b[0] >> 4` is `3` or `4`;
2. `b.tail` decodes as `proto::wire::PreKeySignalMessage` (unknown tags skipped, repeated tags
   overwritten by the last value);
3. `base_key`, `identity_key`, `message`, and `signed_pre_key_id` are present;
4. `kyber_pre_key_id` and `kyber_ciphertext` are either both present or both absent at version `3`;
5. `base_key` and `identity_key` deserialize as X25519 public keys (`0x05` followed by `≥ 32`
   bytes), and `message` parses via `SignalMessage.tryFrom protoSignalCodec`.

`pksmParse_bytes` proves agreement with `preKeyResultAt` on serialized pre-key messages of
length `< 2 ^ 32`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Pksm

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Pqxdh.ResponderWire

/-! ## prost's decoder for `proto::wire::PreKeySignalMessage` -/

/-- `PreKeySignalMessage::default()`: every field `None`. -/
def emptyProto : ProtoPreKeySignalMessage :=
  { registrationId := none, preKeyId := none, signedPreKeyId := none, kyberPreKeyId := none,
    kyberCiphertext := none, baseKey := none, identityKey := none, message := none }

/-- `PreKeySignalMessage::merge_field(tag, wire_type, buf, ctx)` (prost-derive, `proto/wire.proto:19-28`):
the updated message and the rest of the input. Unknown tags are skipped. -/
def mergeProtoField (m : ProtoPreKeySignalMessage) (tag : ℕ) (wt : WireType)
    (bs : List (BitVec 8)) : Option (ProtoPreKeySignalMessage × List (BitVec 8)) :=
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

/-- The `while buf.has_remaining()` loop of `Message::merge`, as `LibsignalProtoCodec.decodeLoop`.
Fuel = the input length suffices: each round consumes at least the key byte. -/
def decodeProtoLoop :
    ℕ → ProtoPreKeySignalMessage → List (BitVec 8) → Option ProtoPreKeySignalMessage
  | _, m, [] => some m
  | 0, _, _ :: _ => none
  | fuel + 1, m, bs@(_ :: _) =>
    match decodeKey bs with
    | none => none
    | some ((tag, wt), rest) =>
      match mergeProtoField m tag wt rest with
      | none => none
      | some (m', rest') => decodeProtoLoop fuel m' rest'

/-- `<proto::wire::PreKeySignalMessage as Message>::decode(&[u8])`; `none` = `Err`. -/
def decodeProto (bs : List (BitVec 8)) : Option ProtoPreKeySignalMessage :=
  decodeProtoLoop bs.length emptyProto bs

/-! ## `try_from` -/

/-- The Kyber fields are acceptable: both present, or both absent at version
`PRE_KYBER_MESSAGE_VERSION` or below. -/
def kyberOk (ver : BitVec 8) (m : ProtoPreKeySignalMessage) : Bool :=
  (m.kyberPreKeyId.isSome && m.kyberCiphertext.isSome) ||
    (m.kyberPreKeyId.isNone && m.kyberCiphertext.isNone && decide (ver ≤ preKyberVersion))

/-- `kyber_payload`: `Some` iff both the Kyber id and the ciphertext are present. -/
def kyberPayloadOf : Option (BitVec 32) → Option (List (BitVec 8)) → Option KyberPayload
  | some k, some ct => some { preKeyId := k, ciphertext := ct }
  | _, _ => none

/-- Functional specification of `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from(b)`
on every input byte slice (`some m` for `Ok(m)`, `none` for `Err(_)`). -/
def pksmParse : List (BitVec 8) → Option PreKeySignalMessage
  | [] => none
  | vb :: body =>
    let ver := vb >>> 4
    if ver < preKyberVersion ∨ currentVersion < ver then none else
    match decodeProto body with
    | none => none
    | some m =>
      match m.baseKey, m.identityKey, m.message, m.signedPreKeyId with
      | some bk, some ik, some msg, some sid =>
        if kyberOk ver m then
          match PublicKey.deserialize bk, PublicKey.deserialize ik,
              SignalMessage.tryFrom protoSignalCodec msg with
          | .ok baseKey, .ok idKey, .ok inner =>
            some { messageVersion := ver
                   registrationId := m.registrationId.getD 0#32
                   preKeyId := m.preKeyId
                   signedPreKeyId := sid
                   kyberPayload := kyberPayloadOf m.kyberPreKeyId m.kyberCiphertext
                   baseKey := baseKey
                   identityKey := ⟨idKey⟩
                   message := inner
                   serialized := vb :: body }
          | _, _, _ => none
        else none
      | _, _, _, _ => none

/-- On well-formed serialized pre-key bytes `x.bytes` (when the inner message has length
`< 2 ^ 32 - 2048`), `pksmParse` agrees with `preKeyResultAt`: `some (x.toModel i)` when
the inner `SignalMessage` parses to `i`, and `none` otherwise. -/
theorem pksmParse_bytes (x : PreKeyTryFromArgs) (hx : x.inner.length + 2048 < 2 ^ 32) :
    pksmParse x.bytes =
      match SignalMessage.tryFrom protoSignalCodec x.inner with
      | .ok i => some (x.toModel i)
      | .error _ => none := by
  have prost_key_eq : ∀ (t : ℕ) (wt : WireType), t < 2 ^ 28 →
      Prost.key t wt.toNat = encodeKey t wt := by
    intro t wt ht
    have hw : wt.toNat < 8 := by cases wt <;> decide
    rw [Prost.key,
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode.prost_varint_length_eq_encodeVarint
        _ (by omega),
      show 8 * t + wt.toNat = t * 8 + wt.toNat by omega, encodeKey]
  have prost_uint32Field_eq : ∀ (t : ℕ) (o : Option (BitVec 32)), t < 2 ^ 28 →
      Prost.uint32Field t o = encodeUint32Field t o := by
    intro t o ht
    cases o with
    | none => rfl
    | some v =>
      rw [CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode.prost_uint32Field_some,
        show (0 : ℕ) = WireType.varint.toNat from rfl, prost_key_eq t .varint ht,
        encodeUint32Field]
  have prost_bytesField_eq : ∀ (t : ℕ) (o : Option (List (BitVec 8))), t < 2 ^ 28 →
      (∀ v, o = some v → v.length < 2 ^ 64) →
      Prost.bytesField t o = encodeBytesField t o := by
    intro t o ht hl
    cases o with
    | none => rfl
    | some v =>
      rw [CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode.prost_bytesField_some
          t v (hl v rfl),
        show (2 : ℕ) = WireType.lengthDelimited.toNat from rfl,
        prost_key_eq t .lengthDelimited ht, encodeBytesField]
  let ProtoLoopsTo (m : ProtoPreKeySignalMessage) (bs : List (BitVec 8))
      (r : ProtoPreKeySignalMessage) : Prop :=
    ∀ n, bs.length ≤ n → decodeProtoLoop n m bs = some r
  have protoLoopsTo_nil : ∀ m : ProtoPreKeySignalMessage, ProtoLoopsTo m [] m := by
    intro m n _
    cases n <;> simp [decodeProtoLoop]
  have protoLoopsTo_field : ∀ (t : ℕ) (wt : WireType), 1 ≤ t → t < 2 ^ 28 →
      ∀ (m m' r : ProtoPreKeySignalMessage) (body rest : List (BitVec 8)),
      mergeProtoField m t wt (body ++ rest) = some (m', rest) →
      ProtoLoopsTo m' rest r →
      ProtoLoopsTo m (encodeKey t wt ++ (body ++ rest)) r := by
    intro t wt h1 h2 m m' r body rest hmerge h n hn
    have hkey := decodeKey_encodeKey t wt (body ++ rest) h1 h2
    have hpos : 0 < (encodeKey t wt).length := List.length_pos_iff.mpr (encodeVarint_ne_nil _)
    simp only [List.length_append] at hn
    obtain ⟨b, bs, hk⟩ := List.exists_cons_of_ne_nil
      (List.length_pos_iff.mp (by simp only [List.length_append]; omega) :
        encodeKey t wt ++ (body ++ rest) ≠ [])
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [hk] at hkey ⊢
    simp only [decodeProtoLoop, hkey, hmerge]
    exact h n' (by omega)
  have protoLoopsTo_uint32 : ∀ (t : ℕ), 1 ≤ t → t < 2 ^ 28 →
      ∀ (o : Option (BitVec 32)) (upd : Option (BitVec 32) → ProtoPreKeySignalMessage)
        (rest : List (BitVec 8)) (r : ProtoPreKeySignalMessage),
      (∀ bs, mergeProtoField (upd none) t .varint bs =
        (mergeUint32 .varint bs).map fun (v, r) => (upd (some v), r)) →
      ProtoLoopsTo (upd o) rest r →
      ProtoLoopsTo (upd none) (Prost.uint32Field t o ++ rest) r := by
    intro t h1 h2 o upd rest r hm h
    rw [prost_uint32Field_eq t o h2]
    cases o with
    | none => simpa [encodeUint32Field] using h
    | some v =>
      rw [show encodeUint32Field t (some v) ++ rest =
        encodeKey t .varint ++ (encodeVarint (v.zeroExtend 64) ++ rest) by simp [encodeUint32Field]]
      refine protoLoopsTo_field t _ h1 h2 _ _ _ _ _ ?_ h
      rw [hm, mergeUint32_encode v rest]
      rfl
  have protoLoopsTo_bytes : ∀ (t : ℕ), 1 ≤ t → t < 2 ^ 28 →
      ∀ (o : Option (List (BitVec 8))) (upd : Option (List (BitVec 8)) → ProtoPreKeySignalMessage)
        (rest : List (BitVec 8)) (r : ProtoPreKeySignalMessage),
      (∀ v, o = some v → v.length < 2 ^ 64) →
      (∀ bs, mergeProtoField (upd none) t .lengthDelimited bs =
        (mergeBytes .lengthDelimited bs).map fun (v, r) => (upd (some v), r)) →
      ProtoLoopsTo (upd o) rest r →
      ProtoLoopsTo (upd none) (Prost.bytesField t o ++ rest) r := by
    intro t h1 h2 o upd rest r hl hm h
    rw [prost_bytesField_eq t o h2 hl]
    cases o with
    | none => simpa [encodeBytesField] using h
    | some v =>
      rw [show encodeBytesField t (some v) ++ rest =
        encodeKey t .lengthDelimited ++
          ((encodeVarint (BitVec.ofNat 64 v.length) ++ v) ++ rest) by simp [encodeBytesField]]
      refine protoLoopsTo_field t _ h1 h2 _ _ _ _ _ ?_ h
      rw [hm, List.append_assoc, mergeBytes_encode v rest (hl v rfl)]
      rfl
  have hbk_fit : ∀ v, some x.bkBytes = some v → v.length < 2 ^ 64 := by
    rintro v ⟨rfl⟩; simp
  have hik_fit : ∀ v, some x.ikBytes = some v → v.length < 2 ^ 64 := by
    rintro v ⟨rfl⟩; simp
  have hin_fit : ∀ v, some x.inner = some v → v.length < 2 ^ 64 := by
    rintro v ⟨rfl⟩; omega
  have hkyb_fit : ∀ v, some x.kyberBytes = some v → v.length < 2 ^ 64 := by
    rintro v ⟨rfl⟩; simp
  have hloop : ProtoLoopsTo emptyProto
      (Prost.uint32Field 1 x.opkId ++ (Prost.bytesField 2 (some x.bkBytes) ++
        (Prost.bytesField 3 (some x.ikBytes) ++ (Prost.bytesField 4 (some x.inner) ++
          (Prost.uint32Field 5 (some x.regId) ++ (Prost.uint32Field 6 (some x.spkId) ++
            (Prost.uint32Field 7 (some x.kpkId) ++
              (Prost.bytesField 8 (some x.kyberBytes) ++ []))))))))
      x.protoMsg :=
    protoLoopsTo_uint32 1 (by omega) (by omega) x.opkId
      (fun o => ⟨none, o, none, none, none, none, none, none⟩) _ _ (fun _ => rfl) <|
    protoLoopsTo_bytes 2 (by omega) (by omega) (some x.bkBytes)
      (fun o => ⟨none, x.opkId, none, none, none, o, none, none⟩) _ _ hbk_fit (fun _ => rfl) <|
    protoLoopsTo_bytes 3 (by omega) (by omega) (some x.ikBytes)
      (fun o => ⟨none, x.opkId, none, none, none, some x.bkBytes, o, none⟩) _ _ hik_fit
      (fun _ => rfl) <|
    protoLoopsTo_bytes 4 (by omega) (by omega) (some x.inner)
      (fun o => ⟨none, x.opkId, none, none, none, some x.bkBytes, some x.ikBytes, o⟩) _ _ hin_fit
      (fun _ => rfl) <|
    protoLoopsTo_uint32 5 (by omega) (by omega) (some x.regId)
      (fun o => ⟨o, x.opkId, none, none, none, some x.bkBytes, some x.ikBytes, some x.inner⟩) _ _
      (fun _ => rfl) <|
    protoLoopsTo_uint32 6 (by omega) (by omega) (some x.spkId)
      (fun o => ⟨some x.regId, x.opkId, o, none, none, some x.bkBytes, some x.ikBytes,
        some x.inner⟩) _ _ (fun _ => rfl) <|
    protoLoopsTo_uint32 7 (by omega) (by omega) (some x.kpkId)
      (fun o => ⟨some x.regId, x.opkId, some x.spkId, o, none, some x.bkBytes, some x.ikBytes,
        some x.inner⟩) _ _ (fun _ => rfl) <|
    protoLoopsTo_bytes 8 (by omega) (by omega) (some x.kyberBytes)
      (fun o => ⟨some x.regId, x.opkId, some x.spkId, some x.kpkId, o, some x.bkBytes,
        some x.ikBytes, some x.inner⟩) _ _ hkyb_fit (fun _ => rfl) <|
    protoLoopsTo_nil _
  have hdec : decodeProto x.protoBytes = some x.protoMsg := by
    have henc : x.protoBytes =
        Prost.uint32Field 1 x.opkId ++ (Prost.bytesField 2 (some x.bkBytes) ++
          (Prost.bytesField 3 (some x.ikBytes) ++ (Prost.bytesField 4 (some x.inner) ++
            (Prost.uint32Field 5 (some x.regId) ++ (Prost.uint32Field 6 (some x.spkId) ++
              (Prost.uint32Field 7 (some x.kpkId) ++
                (Prost.bytesField 8 (some x.kyberBytes) ++ []))))))) := by
      simp only [PreKeyTryFromArgs.protoBytes, PreKeyTryFromArgs.protoMsg,
        ProtoPreKeySignalMessage.encode, List.append_assoc, List.append_nil]
    rw [decodeProto, henc]
    exact hloop _ (Nat.le_refl _)
  have deserialize_djb_ok : ∀ v : List.Vector (BitVec 8) 32,
      PublicKey.deserialize (0x05#8 :: v.toList) = .ok ⟨v⟩ := by
    rintro ⟨l, hl⟩
    simp [PublicKey.deserialize, djbType, hl, List.take_of_length_le (Nat.le_of_eq hl)]
  have hvb : versionByte 4#8 >>> 4 = 4#8 := by decide
  have hver : ¬ (4#8 < preKyberVersion ∨ currentVersion < 4#8) := by decide
  have hkyb : kyberOk 4#8 x.protoMsg = true := rfl
  have hbk : PublicKey.deserialize x.bkBytes = .ok ⟨x.baseKey⟩ := deserialize_djb_ok x.baseKey
  have hik : PublicKey.deserialize x.ikBytes = .ok ⟨x.idPub⟩ := deserialize_djb_ok x.idPub
  simp only [PreKeyTryFromArgs.bytes, pksmParse, hvb, hver, ↓reduceIte, hdec, hkyb]
  simp only [PreKeyTryFromArgs.protoMsg, hbk, hik]
  cases SignalMessage.tryFrom protoSignalCodec x.inner <;> rfl

end CryptoVerification.SignalSession.Cli.RunProofs.Pksm
