/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhSessionModel
public import Symbolic.Specifications.Refinement.TraceExplanation
import LibsignalBinary.Proofs.ProtoCodecRoundTrip

/-!
# Pre-Key Wire Protobuf Round-Trip Lemmas

Establishes byte-level equivalences between `Prost` and `LibsignalProtoCodec` field encoders and
proves round-trip decoding lemmas (`decodePreKey_encode`, `parsePreKeyWire_preKeyWire`, and
`parsePreKeyWire_preKeyMsgE`) for `PreKeyProto` and `PreKeyMessageFields`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open DY.Libsignal (HwBytes)
open DY.Libsignal.PQXDH.Refinement (PreKeyProto wirePrekeyTag)
open DY.Libsignal.Composed.Refinement
  (PreKeyFields ecKeyParses parsePreKey parsePreKeyWire decodePreKey decodePreKeyLoop
   mergePreKeyField emptyPreKeyMsg preKeyWire ecKey)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E (PreKeyMessageFields wirePrekey djbKey)
open CryptoVerification.LibsignalProtoCodec

/-! ## Field encoder equivalences -/

private theorem varint_cont_byte_eq (v : BitVec 64) :
    ((v &&& 127#64) ||| 128#64).setWidth 8 = (v &&& 127#64).setWidth 8 + 128#8 := by
  have h1 : ((v &&& 127#64) ||| 128#64).setWidth 8 = (v.setWidth 8 &&& 127#8) ||| 128#8 := by
    ext i hi; simp
  have h2 : (v &&& 127#64).setWidth 8 = v.setWidth 8 &&& 127#8 := by
    ext i hi; simp
  rw [h1, h2]
  generalize v.setWidth 8 = b
  revert b
  decide

private theorem prostVarint_eq_encodeVarintAux :
    ∀ (k : Nat) (n : Nat),
      k ≠ 0 → n < 2 ^ (7 * k) → n < 2 ^ 64 →
      Prost.varint n = encodeVarintAux k (BitVec.ofNat 64 n)
  | 0, _, hk, _, _ => absurd rfl hk
  | k + 1, n, _, hpow, hn => by
    unfold encodeVarintAux
    rw [Prost.varint]
    have htoNat : (BitVec.ofNat 64 n).toNat = n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    by_cases hlt : n < 128
    · have hlt' : (BitVec.ofNat 64 n).toNat < 128 := by rw [htoNat]; exact hlt
      simp only [hlt, hlt', ↓reduceDIte, ↓reduceIte, List.cons.injEq, and_true]
      apply BitVec.eq_of_toNat_eq
      simp
    · have hlt' : ¬((BitVec.ofNat 64 n).toNat < 128) := by rw [htoNat]; omega
      simp only [hlt, hlt', ↓reduceDIte, ↓reduceIte, List.cons.injEq]
      have hk_ne : k ≠ 0 := by rintro rfl; simp at hpow; omega
      have hdiv_pow : n / 128 < 2 ^ (7 * k) := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        have : 2 ^ (7 * k) * 128 = 2 ^ (7 * (k + 1)) := by
          rw [show 7 * (k + 1) = 7 * k + 7 by omega, Nat.pow_add]
        omega
      constructor
      · change BitVec.ofNat 8 (n % 128 + 128) = ((BitVec.ofNat 64 n &&& 127#64) ||| 128#64).setWidth 8
        rw [varint_cont_byte_eq]
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add, BitVec.toNat_and, Nat.and_two_pow_sub_one_eq_mod _ 7]
      · rw [prostVarint_eq_encodeVarintAux k (n / 128) hk_ne hdiv_pow (by omega)]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_ushiftRight, htoNat, Nat.shiftRight_eq_div_pow]
        omega

theorem prostVarint_eq_encodeVarint_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    Prost.varint n = encodeVarint (BitVec.ofNat 64 n) :=
  prostVarint_eq_encodeVarintAux 10 n (by decide) (by omega) hn

theorem prostVarint_toNat_eq_encodeVarint (v : BitVec 64) :
    Prost.varint v.toNat = encodeVarint v := by
  rw [prostVarint_eq_encodeVarint_ofNat v.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem prostKey_eq_encodeKey {tag : Nat} (wt : WireType) (htag : 8 * tag + 7 < 2 ^ 64) :
    Prost.key tag wt.toNat = encodeKey tag wt := by
  have hw : wt.toNat < 8 := by cases wt <;> decide
  unfold Prost.key encodeKey
  rw [prostVarint_eq_encodeVarint_ofNat (by omega), show 8 * tag + wt.toNat = tag * 8 + wt.toNat by omega]

theorem prostUint32Field_eq_encodeUint32Field {tag : Nat} (htag : 8 * tag + 7 < 2 ^ 64)
    (o : Option (BitVec 32)) :
    Prost.uint32Field tag o = encodeUint32Field tag o := by
  cases o with
  | none => rfl
  | some v =>
    simp only [Prost.uint32Field, encodeUint32Field]
    have hk := prostKey_eq_encodeKey (tag := tag) .varint htag
    have hv : (v.zeroExtend 64).toNat = v.toNat := by
      change (v.setWidth 64).toNat = v.toNat
      rw [BitVec.toNat_setWidth]; have := v.isLt; omega
    rw [show WireType.varint.toNat = 0 from rfl] at hk
    rw [hk, ← hv, prostVarint_toNat_eq_encodeVarint]

theorem prostBytesField_eq_encodeBytesField {tag : Nat} (htag : 8 * tag + 7 < 2 ^ 64)
    (o : Option HwBytes) (hl : ∀ b, o = some b → b.length < 2 ^ 64) :
    Prost.bytesField tag o = encodeBytesField tag o := by
  cases o with
  | none => rfl
  | some b =>
    simp only [Prost.bytesField, encodeBytesField]
    have hk := prostKey_eq_encodeKey (tag := tag) .lengthDelimited htag
    rw [show WireType.lengthDelimited.toNat = 2 from rfl] at hk
    rw [hk, prostVarint_eq_encodeVarint_ofNat (hl b rfl), List.append_assoc]

theorem preKeyWire_eq_preKeyMsgE_bytes (m : PreKeyMessageFields) (hlen : m.inner.length < 2 ^ 64) :
    wirePrekey :: m.bytes =
      preKeyWire m.opkId m.spkId m.kpkId m.regId
        (ecKey m.idPub.toList) m.baseKey.toList m.kyberCt.toList m.inner := by
  have htag : wirePrekey = wirePrekeyTag := by decide
  have hver : CryptoGames.LibsignalSession.versionByte currentVersion =
      DY.Libsignal.PQXDH.Refinement.versionByte 4#8 := by decide
  have hdjb_bk : djbKey m.baseKey = 5#8 :: m.baseKey.toList := rfl
  have hdjb_id : djbKey m.idPub = ecKey m.idPub.toList := rfl
  have hkyb : CryptoVerification.E2E.kyberKey m.kyberCt = 8#8 :: m.kyberCt.toList := rfl
  unfold PreKeyMessageFields.bytes ProtoPreKeySignalMessage.encode preKeyWire PreKeyProto.encode
  rw [htag, hver, hdjb_bk, hdjb_id, hkyb]
  simp only [List.cons.injEq, true_and]
  rw [prostUint32Field_eq_encodeUint32Field (by decide),
      prostBytesField_eq_encodeBytesField (by decide) _ (by rintro _ ⟨⟩; simp),
      prostBytesField_eq_encodeBytesField (by decide) _ (by rintro _ ⟨⟩; simp [ecKey]),
      prostBytesField_eq_encodeBytesField (by decide) _ (by rintro _ ⟨⟩; exact hlen),
      prostUint32Field_eq_encodeUint32Field (by decide),
      prostUint32Field_eq_encodeUint32Field (by decide),
      prostUint32Field_eq_encodeUint32Field (by decide),
      prostBytesField_eq_encodeBytesField (by decide) _ (by rintro _ ⟨⟩; simp)]

/-! ## `decodePreKey` and `parsePreKeyWire` round-trips -/

private def PreKeyLoops (m : PreKeyProto) (bs : HwBytes) (r : PreKeyProto) : Prop :=
  ∀ n, bs.length ≤ n → decodePreKeyLoop n m bs = some r

private theorem preKeyLoops_nil (m : PreKeyProto) : PreKeyLoops m [] m := by
  intro n _; cases n <;> rfl

private theorem preKeyLoops_field (t : Nat) (wt : WireType) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    (m m' r : PreKeyProto) (body rest : HwBytes)
    (hmerge : mergePreKeyField m t wt (body ++ rest) = some (m', rest))
    (h : PreKeyLoops m' rest r) :
    PreKeyLoops m (encodeKey t wt ++ (body ++ rest)) r := by
  intro n hn
  have hkey := decodeKey_encodeKey t wt (body ++ rest) h1 h2
  have hpos : 0 < (encodeKey t wt).length := List.length_pos_iff.mpr (encodeVarint_ne_nil _)
  simp only [List.length_append] at hn
  obtain ⟨b, bs, hk⟩ := List.exists_cons_of_ne_nil
    (List.length_pos_iff.mp (by simp only [List.length_append]; omega) :
      encodeKey t wt ++ (body ++ rest) ≠ [])
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [hk] at hkey ⊢
  simp only [decodePreKeyLoop, hkey, hmerge]
  exact h n' (by omega)

private theorem preKeyLoops_optBytes (upd : PreKeyProto → Option HwBytes → PreKeyProto)
    (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    (m r : PreKeyProto) (o : Option HwBytes) (rest : HwBytes)
    (hnone : upd m none = m)
    (hl : ∀ v, o = some v → v.length < 2 ^ 64)
    (hmf : ∀ wt bs, mergePreKeyField m t wt bs =
      (mergeBytes wt bs).map fun (v, rest') => (upd m (some v), rest'))
    (h : PreKeyLoops (upd m o) rest r) :
    PreKeyLoops m (encodeBytesField t o ++ rest) r := by
  cases o with
  | none => rw [hnone] at h; simpa [encodeBytesField] using h
  | some v =>
    have hsp : encodeBytesField t (some v) ++ rest =
        encodeKey t .lengthDelimited ++ ((encodeVarint (BitVec.ofNat 64 v.length) ++ v) ++ rest) := by
      simp [encodeBytesField]
    rw [hsp]
    refine preKeyLoops_field t .lengthDelimited h1 h2 m (upd m (some v)) r _ rest ?_ h
    rw [hmf, List.append_assoc, mergeBytes_encode v rest (hl v rfl)]; rfl

private theorem preKeyLoops_optUint32 (upd : PreKeyProto → Option (BitVec 32) → PreKeyProto)
    (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    (m r : PreKeyProto) (o : Option (BitVec 32)) (rest : HwBytes)
    (hnone : upd m none = m)
    (hmf : ∀ wt bs, mergePreKeyField m t wt bs =
      (mergeUint32 wt bs).map fun (v, rest') => (upd m (some v), rest'))
    (h : PreKeyLoops (upd m o) rest r) :
    PreKeyLoops m (encodeUint32Field t o ++ rest) r := by
  cases o with
  | none => rw [hnone] at h; simpa [encodeUint32Field] using h
  | some x =>
    have hsp : encodeUint32Field t (some x) ++ rest =
        encodeKey t .varint ++ (encodeVarint (x.zeroExtend 64) ++ rest) := by
      simp [encodeUint32Field]
    rw [hsp]
    refine preKeyLoops_field t .varint h1 h2 m (upd m (some x)) r _ rest ?_ h
    rw [hmf, mergeUint32_encode x rest]; rfl

theorem decodePreKey_encode (p : PreKeyProto)
    (hbk : ∀ b, p.baseKey = some b → b.length < 2 ^ 64)
    (hik : ∀ b, p.identityKey = some b → b.length < 2 ^ 64)
    (hmsg : ∀ b, p.message = some b → b.length < 2 ^ 64)
    (hkct : ∀ b, p.kyberCiphertext = some b → b.length < 2 ^ 64) :
    decodePreKey (PreKeyProto.encode p) = some p := by
  unfold decodePreKey
  suffices h : PreKeyLoops emptyPreKeyMsg (PreKeyProto.encode p) p from h _ (Nat.le_refl _)
  unfold PreKeyProto.encode
  simp only [List.append_assoc]
  refine preKeyLoops_optUint32 (fun m v => { m with preKeyId := v })
    1 (by decide) (by decide) _ p p.preKeyId _ rfl (fun _ _ => rfl) ?_
  refine preKeyLoops_optBytes (fun m v => { m with baseKey := v })
    2 (by decide) (by decide) _ p p.baseKey _ rfl hbk (fun _ _ => rfl) ?_
  refine preKeyLoops_optBytes (fun m v => { m with identityKey := v })
    3 (by decide) (by decide) _ p p.identityKey _ rfl hik (fun _ _ => rfl) ?_
  refine preKeyLoops_optBytes (fun m v => { m with message := v })
    4 (by decide) (by decide) _ p p.message _ rfl hmsg (fun _ _ => rfl) ?_
  refine preKeyLoops_optUint32 (fun m v => { m with registrationId := v })
    5 (by decide) (by decide) _ p p.registrationId _ rfl (fun _ _ => rfl) ?_
  refine preKeyLoops_optUint32 (fun m v => { m with signedPreKeyId := v })
    6 (by decide) (by decide) _ p p.signedPreKeyId _ rfl (fun _ _ => rfl) ?_
  refine preKeyLoops_optUint32 (fun m v => { m with kyberPreKeyId := v })
    7 (by decide) (by decide) _ p p.kyberPreKeyId _ rfl (fun _ _ => rfl) ?_
  have hend : encodeBytesField 8 p.kyberCiphertext =
      encodeBytesField 8 p.kyberCiphertext ++ [] := by simp
  rw [hend]
  refine preKeyLoops_optBytes (fun m v => { m with kyberCiphertext := v })
    8 (by decide) (by decide) _ p p.kyberCiphertext [] rfl hkct (fun _ _ => rfl) ?_
  cases p; exact preKeyLoops_nil _

theorem parsePreKeyWire_preKeyWire (preKeyId : Option (BitVec 32)) (spkId kpkId regId : BitVec 32)
    (ik ek ct msg : HwBytes) (hik : ik.length = 32) (hek : ek.length = 32)
    (hct : ct.length = 1568) (hmsg : msg.length < 2 ^ 64) :
    parsePreKeyWire (preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg) =
      match SignalMessage.tryFrom protoSignalCodec msg with
      | .ok inner =>
        some { version := 4, preKeyId, signedPreKeyId := spkId, kyberPreKeyId := some kpkId,
               kyberCiphertext := some (DY.Libsignal.Composed.Refinement.kyberKey ct),
               baseKey := ecKey ek, identityKey := ecKey ik, message := msg, inner }
      | .error _ => none := by
  have hver : ((DY.Libsignal.PQXDH.Refinement.versionByte 4#8) >>> 4).toNat = 4 := by decide
  have hdec := decodePreKey_encode
    { registrationId := some regId, preKeyId, signedPreKeyId := some spkId,
      kyberPreKeyId := some kpkId,
      kyberCiphertext := some (DY.Libsignal.Composed.Refinement.kyberKey ct),
      baseKey := some (ecKey ek), identityKey := some (ecKey ik), message := some msg }
    (by rintro _ ⟨⟩; simp [ecKey, hek]) (by rintro _ ⟨⟩; simp [ecKey, hik])
    (by rintro _ ⟨⟩; exact hmsg)
    (by rintro _ ⟨⟩; simp [DY.Libsignal.Composed.Refinement.kyberKey, hct])
  have hec_ek : ecKeyParses (ecKey ek) = true := by simp [ecKeyParses, ecKey, hek]
  have hec_ik : ecKeyParses (ecKey ik) = true := by simp [ecKeyParses, ecKey, hik]
  dsimp only [ecKey, DY.Libsignal.Composed.Refinement.kyberKey] at hdec hec_ek hec_ik ⊢
  unfold parsePreKeyWire preKeyWire parsePreKey
  simp only [↓reduceIte, hver, show ¬ (4 < 3 ∨ 4 < 4) by omega, hdec, hec_ek, hec_ik,
    Option.isSome_some, Bool.true_and, Bool.true_or]
  rfl

theorem parsePreKeyWire_preKeyMsgE (m : PreKeyMessageFields) (hlen : m.inner.length < 2 ^ 64) :
    parsePreKeyWire (wirePrekey :: m.bytes) =
      match SignalMessage.tryFrom protoSignalCodec m.inner with
      | .ok inner =>
        some { version := 4, preKeyId := m.opkId, signedPreKeyId := m.spkId,
               kyberPreKeyId := some m.kpkId,
               kyberCiphertext := some (CryptoVerification.E2E.kyberKey m.kyberCt),
               baseKey := djbKey m.baseKey, identityKey := djbKey m.idPub,
               message := m.inner, inner }
      | .error _ => none := by
  rw [preKeyWire_eq_preKeyMsgE_bytes m hlen,
      parsePreKeyWire_preKeyWire m.opkId m.spkId m.kpkId m.regId
        m.idPub.toList m.baseKey.toList m.kyberCt.toList m.inner
        m.idPub.2 m.baseKey.2 m.kyberCt.2 hlen]
  rfl

end DY.Libsignal.Composed.Refinement.Cli
