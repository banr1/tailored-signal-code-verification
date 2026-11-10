/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.SDet.Defs
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.StateXModelProofDefs

/-!
# Store and Session Record Codec Injectivity

Proves injectivity of fixed-width key encodings, pre-key wire messages, and protobuf store
records, and establishes `encodeRecordUnderExtras` round-trip decoding up to `PqSessionEquiv`.
-/

@[expose] public section

set_option autoImplicit false

namespace CodecInjAux

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement.Cli.SDet (PqSessionEquiv)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E
open CryptoVerification.SignalSession (le32 PqSignedKey PqKyberKey signedRecordBytes
  kyberRecordBytes oneTimeRecordBytes baseKeysBytes)

/-! ## Fixed-width byte encodings -/

theorem le32_length (v : BitVec 32) : (le32 v).length = 4 := rfl

theorem le32_inj {a b : BitVec 32} (h : le32 a = le32 b) : a = b := by
  unfold le32 at h
  injection h with h0 h
  injection h with h1 h
  injection h with h2 h
  injection h with h3 _
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hbyte : ∀ s, a.extractLsb' s 8 = b.extractLsb' s 8 →
      ∀ k < 8, a.getLsbD (s + k) = b.getLsbD (s + k) := by
    intro s hs k hk
    have := congrArg (fun x : BitVec 8 => x.getLsbD k) hs
    simpa [BitVec.getLsbD_extractLsb', hk] using this
  by_cases h8 : i < 8
  · simpa using hbyte 0 h0 i h8
  · by_cases h16 : i < 16
    · simpa [show 8 + (i - 8) = i by omega] using hbyte 8 h1 (i - 8) (by omega)
    · by_cases h24 : i < 24
      · simpa [show 16 + (i - 16) = i by omega] using hbyte 16 h2 (i - 16) (by omega)
      · simpa [show 24 + (i - 24) = i by omega] using hbyte 24 h3 (i - 24) (by omega)

theorem djbKey_length (k : List.Vector (BitVec 8) 32) : (djbKey k).length = 33 := by
  simp [djbKey]

theorem djbKey_inj {a b : List.Vector (BitVec 8) 32} (h : djbKey a = djbKey b) : a = b := by
  unfold djbKey at h
  injection h with _ ht
  exact Subtype.ext ht

theorem kyberKey_length (k : List.Vector (BitVec 8) 1568) : (kyberKey k).length = 1569 := by
  simp [kyberKey]

theorem kyberKey_inj {a b : List.Vector (BitVec 8) 1568} (h : kyberKey a = kyberKey b) : a = b := by
  unfold kyberKey at h
  injection h with _ ht
  exact Subtype.ext ht

private theorem extractLsb'_zero_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) (j : Nat)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 256 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToKey32 (bs : List (BitVec 8)) (j : Nat)
    (hj : j < bs.length) (h32 : j < 32) :
    (HKDF.bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [HKDF.bytesToKey32] using extractLsb'_zero_bytesToKey32_cons b (HKDF.bytesToKey32 rest)
    | succ j =>
      have hcons : HKDF.bytesToKey32 (b :: rest) =
          (HKDF.bytesToKey32 rest <<< 8) ||| b.zeroExtend 256 := rfl
      rw [hcons, extractLsb'_succ_bytesToKey32_cons b (HKDF.bytesToKey32 rest) j h32,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

theorem bytesToKey32_keyToBytes32 (k : BitVec 256) :
    HKDF.bytesToKey32 (HMAC.keyToBytes32 k) = k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < 32 := by omega
  have hr : i % 8 < 8 := by omega
  have hbyte := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8))
    (extractLsb'_bytesToKey32 (HMAC.keyToBytes32 k) (i / 8) (by simp [HMAC.keyToBytes32, hj]) hj)
  simp only [HMAC.keyToBytes32, List.getElem_ofFn, BitVec.getLsbD_extractLsb', hr, decide_true,
    Bool.true_and, Nat.div_add_mod] at hbyte
  exact hbyte

theorem keyToBytes32_inj {a b : BitVec 256} (h : HMAC.keyToBytes32 a = HMAC.keyToBytes32 b) :
    a = b := by
  have := congrArg HKDF.bytesToKey32 h
  simpa [bytesToKey32_keyToBytes32] using this

theorem baseKeysBytes_inj {s₀ s₁ : List (BitVec 32 × List.Vector (BitVec 8) 32)}
    (h : baseKeysBytes s₀ = baseKeysBytes s₁) : s₀ = s₁ := by
  unfold baseKeysBytes at h
  induction s₀ generalizing s₁ with
  | nil =>
    cases s₁ with
    | nil => rfl
    | cons y ys =>
      rcases y with ⟨id, bk⟩
      simp only [List.map_nil, List.flatten_nil, List.map_cons, List.flatten_cons] at h
      have hlen := congrArg List.length h
      simp [le32_length, djbKey_length] at hlen; omega
  | cons x xs ih =>
    rcases x with ⟨id₀, bk₀⟩
    cases s₁ with
    | nil =>
      simp only [List.map_nil, List.flatten_nil, List.map_cons, List.flatten_cons] at h
      have hlen := congrArg List.length h
      simp [le32_length, djbKey_length] at hlen
    | cons y ys =>
      rcases y with ⟨id₁, bk₁⟩
      simp only [List.map_cons, List.flatten_cons] at h
      have hchunk : (le32 id₀ ++ djbKey bk₀).length = (le32 id₁ ++ djbKey bk₁).length := by
        simp [le32_length, djbKey_length]
      obtain ⟨hhead, htail⟩ := List.append_inj h hchunk
      obtain ⟨hid, hbk⟩ := List.append_inj hhead (by simp [le32_length])
      rw [le32_inj hid, djbKey_inj hbk, ih htail]

/-! ## `PreKeyMessageFields.bytes` injectivity -/

private def decProstVarint : List (BitVec 8) → Option (Nat × List (BitVec 8))
  | [] => none
  | b :: rest =>
    if b.toNat < 128 then some (b.toNat, rest)
    else (decProstVarint rest).map fun (hi, r) => (b.toNat % 128 + 128 * hi, r)

private theorem decProstVarint_varint (n : Nat) (rest : List (BitVec 8)) :
    decProstVarint (Prost.varint n ++ rest) = some (n, rest) := by
  induction n using Nat.strongRecOn generalizing rest with
  | ind n ih =>
    rw [Prost.varint]
    split_ifs with h
    · have hb : (BitVec.ofNat 8 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
      simp [decProstVarint, hb, h]
    · rw [List.cons_append, decProstVarint]
      split_ifs with hlt
      · rw [BitVec.toNat_ofNat] at hlt; omega
      · rw [ih (n / 128) (by omega) rest, Option.map_some, Option.some.injEq, Prod.mk.injEq]
        refine ⟨?_, rfl⟩
        rw [BitVec.toNat_ofNat]; omega

private def decOptTag1 (bs : List (BitVec 8)) : Option (Option (BitVec 32) × List (BitVec 8)) :=
  match decProstVarint bs with
  | none => none
  | some (k, r1) =>
    if k = 8 then
      match decProstVarint r1 with
      | none => none
      | some (val, r2) => some (some (BitVec.ofNat 32 val), r2)
    else some (none, bs)

private def decProstBytes (bs : List (BitVec 8)) : Option (List (BitVec 8) × List (BitVec 8)) :=
  match decProstVarint bs with
  | none => none
  | some (_, r1) =>
    match decProstVarint r1 with
    | none => none
    | some (len, r2) => some (r2.take len, r2.drop len)

private def decProstUint32 (bs : List (BitVec 8)) : Option (BitVec 32 × List (BitVec 8)) :=
  match decProstVarint bs with
  | none => none
  | some (_, r1) =>
    match decProstVarint r1 with
    | none => none
    | some (val, r2) => some (BitVec.ofNat 32 val, r2)

private theorem decProstBytes_some (tag : Nat) (v rest : List (BitVec 8)) :
    decProstBytes (Prost.bytesField tag (some v) ++ rest) = some (v, rest) := by
  simp only [Prost.bytesField, Prost.key, List.append_assoc, decProstBytes,
    decProstVarint_varint, List.take_left, List.drop_left]

private theorem decProstUint32_some (tag : Nat) (v : BitVec 32) (rest : List (BitVec 8)) :
    decProstUint32 (Prost.uint32Field tag (some v) ++ rest) = some (v, rest) := by
  simp only [Prost.uint32Field, Prost.key, List.append_assoc, decProstUint32,
    decProstVarint_varint, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem decOptTag1_encode (opk : Option (BitVec 32)) (b rest : List (BitVec 8)) :
    decOptTag1 (Prost.uint32Field 1 opk ++ (Prost.bytesField 2 (some b) ++ rest)) =
      some (opk, Prost.bytesField 2 (some b) ++ rest) := by
  cases opk with
  | none =>
    simp only [Prost.uint32Field, List.nil_append, Prost.bytesField, Prost.key, List.append_assoc,
      decOptTag1, decProstVarint_varint]
    rfl
  | some v =>
    simp only [Prost.uint32Field, Prost.key, List.append_assoc, decOptTag1,
      decProstVarint_varint, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private def decProtoPreKey (bs : List (BitVec 8)) :
    Option (Option (BitVec 32) × List (BitVec 8) × List (BitVec 8) × List (BitVec 8) ×
      BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 8)) := do
  let (opk, r1) ← decOptTag1 bs
  let (bk, r2) ← decProstBytes r1
  let (ik, r3) ← decProstBytes r2
  let (msg, r4) ← decProstBytes r3
  let (reg, r5) ← decProstUint32 r4
  let (spk, r6) ← decProstUint32 r5
  let (kpk, r7) ← decProstUint32 r6
  let (kct, _) ← decProstBytes r7
  pure (opk, bk, ik, msg, reg, spk, kpk, kct)

private theorem decProtoPreKey_bytes_tail (m : PreKeyMessageFields) :
    decProtoPreKey (ProtoPreKeySignalMessage.encode
      { registrationId := some m.regId, preKeyId := m.opkId, signedPreKeyId := some m.spkId,
        kyberPreKeyId := some m.kpkId, kyberCiphertext := some (kyberKey m.kyberCt),
        baseKey := some (djbKey m.baseKey), identityKey := some (djbKey m.idPub),
        message := some m.inner }) =
      some (m.opkId, djbKey m.baseKey, djbKey m.idPub, m.inner,
        m.regId, m.spkId, m.kpkId, kyberKey m.kyberCt) := by
  unfold ProtoPreKeySignalMessage.encode
  have hend : Prost.bytesField 8 (some (kyberKey m.kyberCt)) =
      Prost.bytesField 8 (some (kyberKey m.kyberCt)) ++ [] := by simp
  rw [hend]
  simp only [List.append_assoc, decProtoPreKey, bind, Option.bind,
    decOptTag1_encode, decProstBytes_some, decProstUint32_some, pure]

theorem preKeyMsgE_bytes_inj {m₀ m₁ : PreKeyMessageFields} (h : m₀.bytes = m₁.bytes) : m₀ = m₁ := by
  unfold PreKeyMessageFields.bytes at h
  injection h with _ hpb
  have hdec := (decProtoPreKey_bytes_tail m₀).symm.trans (hpb ▸ decProtoPreKey_bytes_tail m₁)
  simp only [Option.some.injEq, Prod.mk.injEq] at hdec
  rcases hdec with ⟨hopk, hbk, hik, hmsg, hreg, hspk, hkpk, hkct⟩
  cases m₀; cases m₁
  dsimp only at hopk hbk hik hmsg hreg hspk hkpk hkct
  rw [hopk, djbKey_inj hbk, djbKey_inj hik, hmsg, hreg, hspk, hkpk, kyberKey_inj hkct]

/-! ## Store record codecs -/

theorem identityKeyPair_encode_inj (C : Crypto) {a b : List.Vector (BitVec 8) 32}
    (h : IdentityKeyPairStructure.encode ⟨djbKey (keyPairOf C a).publicKey.bytes, a.toList⟩ =
         IdentityKeyPairStructure.encode ⟨djbKey (keyPairOf C b).publicKey.bytes, b.toList⟩) :
    a = b := by
  have hd₀ := IdentityKeyPairStructure.decode_encode
    ⟨djbKey (keyPairOf C a).publicKey.bytes, a.toList⟩ (by simp [djbKey]) (by simp)
  have hd₁ := IdentityKeyPairStructure.decode_encode
    ⟨djbKey (keyPairOf C b).publicKey.bytes, b.toList⟩ (by simp [djbKey]) (by simp)
  rw [h] at hd₀
  have heq := Option.some.inj (hd₀.symm.trans hd₁)
  injection heq with _ hpriv
  exact Subtype.ext hpriv

theorem identityKey_serialize_inj {a b : IdentityKey} (h : a.serialize = b.serialize) : a = b := by
  have hd₀ := decodeIdentityKey_serialize a
  have hd₁ := decodeIdentityKey_serialize b
  rw [h] at hd₀
  have := hd₀.symm.trans hd₁
  injection this

theorem signedRecordBytes_inj (C : Crypto) (id : BitVec 32) {k₀ k₁ : PqSignedKey}
    (h : signedRecordBytes C id k₀ = signedRecordBytes C id k₁) : k₀ = k₁ := by
  unfold signedRecordBytes at h
  have hd₀ := SignedPreKeyRecordStructure.decode_encode
    ⟨id, djbKey (keyPairOf C k₀.priv).publicKey.bytes, k₀.priv.toList, k₀.sig.toList, k₀.timestamp⟩
    (by simp [djbKey]) (by simp) (by simp)
  have hd₁ := SignedPreKeyRecordStructure.decode_encode
    ⟨id, djbKey (keyPairOf C k₁.priv).publicKey.bytes, k₁.priv.toList, k₁.sig.toList, k₁.timestamp⟩
    (by simp [djbKey]) (by simp) (by simp)
  rw [h] at hd₀
  have heq := Option.some.inj (hd₀.symm.trans hd₁)
  injection heq with _ _ hpriv hsig hts
  cases k₀; cases k₁
  dsimp only at hpriv hsig hts
  rw [Subtype.ext hpriv, Subtype.ext hsig, hts]

theorem kyberRecordBytes_inj (id : BitVec 32) {k₀ k₁ : PqKyberKey}
    (h : kyberRecordBytes id k₀ = kyberRecordBytes id k₁) : k₀ = k₁ := by
  unfold kyberRecordBytes at h
  have hd₀ := SignedPreKeyRecordStructure.decode_encode
    ⟨id, kyberKey k₀.pub, 0x08#8 :: k₀.sec.toList, k₀.sig.toList, k₀.timestamp⟩
    (by simp [kyberKey]) (by simp) (by simp)
  have hd₁ := SignedPreKeyRecordStructure.decode_encode
    ⟨id, kyberKey k₁.pub, 0x08#8 :: k₁.sec.toList, k₁.sig.toList, k₁.timestamp⟩
    (by simp [kyberKey]) (by simp) (by simp)
  rw [h] at hd₀
  have heq := Option.some.inj (hd₀.symm.trans hd₁)
  injection heq with _ hpub hsec hsig hts
  injection hsec with _ hsec'
  cases k₀; cases k₁
  dsimp only at hpub hsec' hsig hts
  rw [kyberKey_inj hpub, Subtype.ext hsec', Subtype.ext hsig, hts]

theorem kyberRecordBytes_ne_nil (id : BitVec 32) (k : PqKyberKey) :
    kyberRecordBytes id k ≠ [] := by
  unfold kyberRecordBytes SignedPreKeyRecordStructure.encode
  intro h
  have hlen := congrArg List.length h
  have hpub : kyberKey k.pub ≠ [] := by simp [kyberKey]
  have henc : (encodeProto3BytesField 2 (kyberKey k.pub)).length > 0 := by
    simp [encodeProto3BytesField, hpub, encodeBytesField, List.length_pos_iff.mpr (encodeVarint_ne_nil _)]
  simp only [List.length_append, List.length_nil] at hlen
  omega

theorem oneTimeRecordBytes_inj (C : Crypto) (id : BitVec 32)
    {sk₀ sk₁ : List.Vector (BitVec 8) 32}
    (h : oneTimeRecordBytes C id sk₀ = oneTimeRecordBytes C id sk₁) : sk₀ = sk₁ := by
  unfold oneTimeRecordBytes at h
  have hd₀ := PreKeyRecordStructure.decode_encode
    ⟨id, djbKey (keyPairOf C sk₀).publicKey.bytes, sk₀.toList⟩
    (by simp [djbKey]) (by simp)
  have hd₁ := PreKeyRecordStructure.decode_encode
    ⟨id, djbKey (keyPairOf C sk₁).publicKey.bytes, sk₁.toList⟩
    (by simp [djbKey]) (by simp)
  rw [h] at hd₀
  have heq := Option.some.inj (hd₀.symm.trans hd₁)
  injection heq with _ _ hpriv
  exact Subtype.ext hpriv

theorem oneTimeRecordBytes_ne_nil (C : Crypto) (id : BitVec 32)
    (sk : List.Vector (BitVec 8) 32) : oneTimeRecordBytes C id sk ≠ [] := by
  unfold oneTimeRecordBytes PreKeyRecordStructure.encode
  intro h
  have hlen := congrArg List.length h
  have hpub : djbKey (keyPairOf C sk).publicKey.bytes ≠ [] := by simp [djbKey]
  have henc : (encodeProto3BytesField 2 (djbKey (keyPairOf C sk).publicKey.bytes)).length > 0 := by
    simp [encodeProto3BytesField, hpub, encodeBytesField, List.length_pos_iff.mpr (encodeVarint_ne_nil _)]
  simp only [List.length_append, List.length_nil] at hlen
  omega

/-! ## `encodeRecordUnderExtras` round-trip up to `PqSessionEquiv` -/

private def bytesToPk? (bs : HwBytes) : Option PublicKey :=
  if h : bs.length = 32 then some ⟨⟨bs, h⟩⟩ else none

private def decDjbPk? : HwBytes → Option PublicKey
  | b :: rest => if b == 0x05#8 then bytesToPk? rest else none
  | [] => none

private def mergeChainKeyField (ck : ChainKey) (tag : Nat) (wt : WireType) (bs : HwBytes) :
    Option (ChainKey × HwBytes) :=
  match tag with
  | 1 => (mergeUint32 wt bs).map fun (v, r) => ({ ck with index := v }, r)
  | 2 => (mergeBytes wt bs).map fun (v, r) => ({ ck with key := HKDF.bytesToKey32 v }, r)
  | _ => skipUnknown ck tag wt bs

private def decChainKey (bs : HwBytes) : Option ChainKey :=
  decodeFieldsLoop mergeChainKeyField bs.length ⟨0, 0⟩ bs

private def mergeMsgKeyField (mk : MessageKeyGenerator) (tag : Nat) (wt : WireType)
    (bs : HwBytes) : Option (MessageKeyGenerator × HwBytes) :=
  match tag with
  | 1 => (mergeUint32 wt bs).map fun (v, r) => ({ mk with counter := v }, r)
  | 5 => (mergeBytes wt bs).map fun (v, r) => ({ mk with seed := v }, r)
  | _ => skipUnknown mk tag wt bs

private def decMsgKey (bs : HwBytes) : Option MessageKeyGenerator :=
  decodeFieldsLoop mergeMsgKeyField bs.length ⟨[], 0⟩ bs

private structure RawChain where
  pub  : PublicKey
  priv : List.Vector (BitVec 8) 32
  ck   : Option ChainKey
  mks  : List MessageKeyGenerator

private def initRawChain : RawChain :=
  ⟨placeholderBaseKey, List.Vector.replicate 32 0#8, none, []⟩

private def mergeChainField (c : RawChain) (tag : Nat) (wt : WireType) (bs : HwBytes) :
    Option (RawChain × HwBytes) :=
  match tag with
  | 1 => (mergeBytes wt bs).bind fun (v, r) => (decDjbPk? v).map fun pk => ({ c with pub := pk }, r)
  | 2 => (mergeBytes wt bs).bind fun (v, r) =>
      if h : v.length = 32 then some ({ c with priv := ⟨v, h⟩ }, r) else none
  | 3 => (mergeBytes wt bs).bind fun (v, r) => (decChainKey v).map fun ck => ({ c with ck := some ck }, r)
  | 4 => (mergeBytes wt bs).bind fun (v, r) => (decMsgKey v).map fun mk => ({ c with mks := c.mks ++ [mk] }, r)
  | _ => skipUnknown c tag wt bs

private def decSenderChain (bs : HwBytes) : Option SenderChain :=
  (decodeFieldsLoop mergeChainField bs.length initRawChain bs).bind fun c =>
    c.ck.map fun ck => ⟨⟨c.pub, ⟨c.priv⟩⟩, ck⟩

private def decReceiverChain (bs : HwBytes) : Option ReceiverChain :=
  (decodeFieldsLoop mergeChainField bs.length initRawChain bs).map fun c => ⟨c.pub, c.ck, c.mks⟩

private def mergePendingPreKeyField (p : PendingPreKey) (tag : Nat) (wt : WireType)
    (bs : HwBytes) : Option (PendingPreKey × HwBytes) :=
  match tag with
  | 1 => (mergeUint32 wt bs).map fun (v, r) => ({ p with preKeyId := some v }, r)
  | 2 => (mergeBytes wt bs).bind fun (v, r) => (decDjbPk? v).map fun pk => ({ p with baseKey := pk }, r)
  | 3 => (mergeUint32 wt bs).map fun (v, r) => ({ p with signedPreKeyId := v }, r)
  | 4 => if wt ≠ .varint then none else (decodeVarint bs).map fun (v, r) => ({ p with timestamp := v }, r)
  | _ => skipUnknown p tag wt bs

private def decPendingPreKey (bs : HwBytes) : Option PendingPreKey :=
  decodeFieldsLoop mergePendingPreKeyField bs.length ⟨none, 0#32, placeholderBaseKey, 0#64⟩ bs

private def mergePendingKyberField (p : PendingKyberPreKey) (tag : Nat) (wt : WireType)
    (bs : HwBytes) : Option (PendingKyberPreKey × HwBytes) :=
  match tag with
  | 1 => (mergeUint32 wt bs).map fun (v, r) => ({ p with preKeyId := v }, r)
  | 2 => (mergeBytes wt bs).map fun (v, r) => ({ p with ciphertext := v }, r)
  | _ => skipUnknown p tag wt bs

private def decPendingKyber (bs : HwBytes) : Option PendingKyberPreKey :=
  decodeFieldsLoop mergePendingKyberField bs.length ⟨0#32, []⟩ bs

private def initDecodedSession : RecordExtras × SessionState HwBytes :=
  (seedRecordExtras .A,
   { sessionVersion := 0#32, localIdentity := ⟨placeholderBaseKey⟩, remoteIdentity := none,
     rootKey := 0, previousCounter := 0#32, senderChain := none, receiverChains := [],
     pendingPreKey := false, pqRatchetState := [] })

private def mergeSessionField (acc : RecordExtras × SessionState HwBytes) (tag : Nat)
    (wt : WireType) (bs : HwBytes) :
    Option ((RecordExtras × SessionState HwBytes) × HwBytes) :=
  let (x, st) := acc
  match tag with
  | 1  => (mergeUint32 wt bs).map fun (v, r) => ((x, { st with sessionVersion := v }), r)
  | 2  => (mergeBytes wt bs).bind fun (v, r) =>
      (decDjbPk? v).map fun pk => ((x, { st with localIdentity := ⟨pk⟩ }), r)
  | 3  => (mergeBytes wt bs).bind fun (v, r) =>
      if v.isEmpty then some ((x, { st with remoteIdentity := none }), r)
      else (decDjbPk? v).map fun pk => ((x, { st with remoteIdentity := some ⟨pk⟩ }), r)
  | 4  => (mergeBytes wt bs).map fun (v, r) => ((x, { st with rootKey := HKDF.bytesToKey32 v }), r)
  | 5  => (mergeUint32 wt bs).map fun (v, r) => ((x, { st with previousCounter := v }), r)
  | 6  => (mergeBytes wt bs).bind fun (v, r) =>
      (decSenderChain v).map fun sc => ((x, { st with senderChain := some sc }), r)
  | 7  => (mergeBytes wt bs).bind fun (v, r) =>
      (decReceiverChain v).map fun rc => ((x, { st with receiverChains := st.receiverChains ++ [rc] }), r)
  | 9  => (mergeBytes wt bs).bind fun (v, r) =>
      (decPendingPreKey v).map fun p => (({ x with pending := p }, { st with pendingPreKey := true }), r)
  | 10 => (mergeUint32 wt bs).map fun (v, r) => (({ x with remoteRegistrationId := v }, st), r)
  | 11 => (mergeUint32 wt bs).map fun (v, r) => (({ x with localRegistrationId := v }, st), r)
  | 13 => (mergeBytes wt bs).map fun (v, r) => (({ x with aliceBaseKey := v }, st), r)
  | 14 => (mergeBytes wt bs).bind fun (v, r) =>
      (decPendingKyber v).map fun kp => (({ x with kyber := some kp }, st), r)
  | 15 => (mergeBytes wt bs).map fun (v, r) => ((x, { st with pqRatchetState := v }), r)
  | _  => skipUnknown acc tag wt bs

private def mergeRecordSessionField (acc : Option (RecordExtras × SessionState HwBytes))
    (tag : Nat) (wt : WireType) (bs : HwBytes) :
    Option (Option (RecordExtras × SessionState HwBytes) × HwBytes) :=
  match tag with
  | 1 => (mergeBytes wt bs).bind fun (sessBytes, rest) =>
      (decodeFieldsLoop mergeSessionField sessBytes.length
        (acc.getD initDecodedSession) sessBytes).map fun dec => (some dec, rest)
  | _ => skipUnknown acc tag wt bs

private def decodeRecordX (bs : HwBytes) : Option (RecordExtras × SessionState HwBytes) :=
  (decodeFieldsLoop mergeRecordSessionField bs.length none bs).join

private def decodedExtras (x : RecordExtras) (ppk : Bool) : RecordExtras :=
  if ppk then x
  else { x with pending := (seedRecordExtras .A).pending, kyber := none }

private theorem option_map_eq_some {α β : Type} {x : Option α} {f : α → β} {a : α} {b : β}
    (hx : x = some a) (hf : f a = b) : x.map f = some b := by
  rw [hx, Option.map_some, hf]

private theorem option_bind_eq_some {α β : Type} {x : Option α} {f : α → Option β} {a : α} {b : β}
    (hx : x = some a) (hf : f a = some b) : x.bind f = some b := by
  rw [hx]; exact hf

private theorem keyToBytes32_length (k : BitVec 256) : (HMAC.keyToBytes32 k).length = 32 := by
  simp [HMAC.keyToBytes32]

private theorem keyToBytes32_ne_nil (k : BitVec 256) : HMAC.keyToBytes32 k ≠ [] := by
  intro h; have hlen := keyToBytes32_length k; rw [h] at hlen; cases hlen

private theorem pk_serialize_length (pk : PublicKey) : pk.serialize.length = 33 := by
  simp [PublicKey.serialize, pk.bytes.toList_length]

private theorem pk_serialize_ne_nil (pk : PublicKey) : pk.serialize ≠ [] := by
  intro h; have hlen := pk_serialize_length pk; rw [h] at hlen; cases hlen

private theorem ik_serialize_length (ik : IdentityKey) : ik.serialize.length = 33 :=
  pk_serialize_length ik.publicKey

private theorem ik_serialize_ne_nil (ik : IdentityKey) : ik.serialize ≠ [] :=
  pk_serialize_ne_nil ik.publicKey

private theorem decDjbPk?_serialize (pk : PublicKey) :
    decDjbPk? pk.serialize = some pk := by
  rcases pk with ⟨⟨l, hl⟩⟩
  unfold PublicKey.serialize decDjbPk? bytesToPk?
  simp [hl, djbType]

private theorem mergeUint32_signExtend_encode (v : BitVec 32) (rest : HwBytes) :
    mergeUint32 .varint (encodeVarint (v.signExtend 64) ++ rest) = some (v, rest) := by
  unfold mergeUint32
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, decodeVarint_encodeVarint, Option.some.injEq,
    Prod.mk.injEq, and_true]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  have h64 : i < 64 := by omega
  simp [hi, h64]

private theorem loopsTo_field_auto {M : Type}
    {mf : M → Nat → WireType → HwBytes → Option (M × HwBytes)}
    (t : Nat) (wt : WireType) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    {m m' r : M} {body rest : HwBytes}
    (hmerge : mf m t wt (body ++ rest) = some (m', rest))
    (h : RecordCodecs.LoopsTo mf m' rest r) :
    RecordCodecs.LoopsTo mf m (encodeKey t wt ++ body ++ rest) r := by
  rw [List.append_assoc]
  exact RecordCodecs.loopsTo_field mf t wt h1 h2 m m' r body rest hmerge h

private theorem loopsTo_lenField {M : Type}
    {mf : M → Nat → WireType → HwBytes → Option (M × HwBytes)}
    (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    {m m' r : M} {v rest : HwBytes}
    (hmerge : mf m t .lengthDelimited (encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) =
      some (m', rest))
    (h : RecordCodecs.LoopsTo mf m' rest r) :
    RecordCodecs.LoopsTo mf m (lenField t v ++ rest) r := by
  have hf := RecordCodecs.loopsTo_field mf t .lengthDelimited h1 h2 m m' r
    (encodeVarint (BitVec.ofNat 64 v.length) ++ v) rest
    (by simpa only [List.append_assoc] using hmerge) h
  simpa only [lenField, List.append_assoc] using hf

private theorem loopsTo_bytesField {M : Type}
    {mf : M → Nat → WireType → HwBytes → Option (M × HwBytes)} (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    {m m' r : M} {v rest : HwBytes}
    (hmerge : v ≠ [] → mf m t .lengthDelimited (encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) = some (m', rest))
    (hdef : v = [] → m' = m) (h : RecordCodecs.LoopsTo mf m' rest r) :
    RecordCodecs.LoopsTo mf m (bytesField t v ++ rest) r := by
  unfold bytesField; split_ifs with hv
  · rw [hdef hv] at h; simpa only [List.nil_append] using h
  · exact loopsTo_lenField t h1 h2 (hmerge hv) h

private theorem loopsTo_msgField {M : Type}
    {mf : M → Nat → WireType → HwBytes → Option (M × HwBytes)} (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    {m m' r : M} {ov : Option HwBytes} {rest : HwBytes}
    (hmerge : ∀ v, ov = some v → mf m t .lengthDelimited (encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) = some (m', rest))
    (hdef : ov = none → m' = m) (h : RecordCodecs.LoopsTo mf m' rest r) :
    RecordCodecs.LoopsTo mf m (msgField t ov ++ rest) r := by
  rcases ov with _ | v
  · rw [hdef rfl] at h; simpa only [msgField, List.nil_append] using h
  · simpa only [msgField] using loopsTo_lenField t h1 h2 (hmerge v rfl) h

private theorem loopsTo_uint32Field {M : Type}
    {mf : M → Nat → WireType → HwBytes → Option (M × HwBytes)} (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    {m m' r : M} {x : BitVec 32} {rest : HwBytes}
    (hmerge : mf m t .varint (encodeVarint (x.setWidth 64) ++ rest) = some (m', rest))
    (hdef : x = 0 → m' = m) (h : RecordCodecs.LoopsTo mf m' rest r) :
    RecordCodecs.LoopsTo mf m (uint32Field t x ++ rest) r := by
  unfold uint32Field; split_ifs with hx
  · rw [hdef hx] at h; simpa only [List.nil_append] using h
  · exact loopsTo_field_auto t .varint h1 h2 hmerge h

private theorem loopsTo_int32FieldX {M : Type}
    {mf : M → Nat → WireType → HwBytes → Option (M × HwBytes)} (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    {m m' r : M} {x : BitVec 32} {rest : HwBytes}
    (hmerge : mf m t .varint (encodeVarint (x.signExtend 64) ++ rest) = some (m', rest))
    (hdef : x = 0 → m' = m) (h : RecordCodecs.LoopsTo mf m' rest r) :
    RecordCodecs.LoopsTo mf m (int32FieldX t x ++ rest) r := by
  unfold int32FieldX; split_ifs with hx
  · rw [hdef hx] at h; simpa only [List.nil_append] using h
  · exact loopsTo_field_auto t .varint h1 h2 hmerge h

private theorem loopsTo_uint64FieldX {M : Type}
    {mf : M → Nat → WireType → HwBytes → Option (M × HwBytes)} (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    {m m' r : M} {x : BitVec 64} {rest : HwBytes}
    (hmerge : mf m t .varint (encodeVarint x ++ rest) = some (m', rest))
    (hdef : x = 0 → m' = m) (h : RecordCodecs.LoopsTo mf m' rest r) :
    RecordCodecs.LoopsTo mf m (uint64FieldX t x ++ rest) r := by
  unfold uint64FieldX; split_ifs with hx
  · rw [hdef hx] at h; simpa only [List.nil_append] using h
  · exact loopsTo_field_auto t .varint h1 h2 hmerge h

private theorem loopsTo_optUint32FieldX {M : Type}
    {mf : M → Nat → WireType → HwBytes → Option (M × HwBytes)} (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    {m m' r : M} {ox : Option (BitVec 32)} {rest : HwBytes}
    (hmerge : ∀ x, ox = some x → mf m t .varint (encodeVarint (x.setWidth 64) ++ rest) = some (m', rest))
    (hdef : ox = none → m' = m) (h : RecordCodecs.LoopsTo mf m' rest r) :
    RecordCodecs.LoopsTo mf m (optUint32FieldX t ox ++ rest) r := by
  rcases ox with _ | x
  · rw [hdef rfl] at h; simpa only [optUint32FieldX, List.nil_append] using h
  · simpa only [optUint32FieldX] using loopsTo_field_auto t .varint h1 h2 (hmerge x rfl) h

private theorem loopsTo_list_lenField_hom {M α β : Type}
    {mf : M → Nat → WireType → HwBytes → Option (M × HwBytes)}
    (proj : M → α) (stepα : α → β → α)
    (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    (encB : β → HwBytes) (xs : List β)
    (hstep : ∀ (m : M) (b : β) (rest : HwBytes),
      b ∈ xs →
      ∃ m', mf m t .lengthDelimited
          (encodeVarint (BitVec.ofNat 64 (encB b).length) ++ (encB b ++ rest)) =
            some (m', rest) ∧
        proj m' = stepα (proj m) b)
    (m : M) (rest : HwBytes) :
    ∃ m_end,
      (∀ r, RecordCodecs.LoopsTo mf m_end rest r →
        RecordCodecs.LoopsTo mf m ((xs.map fun b => lenField t (encB b)).flatten ++ rest) r) ∧
      proj m_end = xs.foldl stepα (proj m) := by
  induction xs generalizing m with
  | nil => exact ⟨m, fun _ hr => by simpa using hr, rfl⟩
  | cons b bs ih =>
    obtain ⟨m1, hm1, hp1⟩ := hstep m b ((bs.map fun x => lenField t (encB x)).flatten ++ rest)
      (List.mem_cons_self ..)
    obtain ⟨m_end, htail, hp_end⟩ :=
      ih (fun m' b' rest' hb' => hstep m' b' rest' (List.mem_cons_of_mem _ hb')) m1
    refine ⟨m_end, fun r hr => ?_, ?_⟩
    · simp only [List.map_cons, List.flatten_cons, List.append_assoc]
      exact loopsTo_lenField t h1 h2 hm1 (htail r hr)
    · simpa only [List.foldl_cons, hp1] using hp_end

private theorem apply_loopsTo_list_lenField_hom {M α β : Type}
    {mf : M → Nat → WireType → HwBytes → Option (M × HwBytes)}
    (proj : M → α) (stepα : α → β → α)
    (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    (encB : β → HwBytes) (xs : List β) {m r : M} {rest : HwBytes}
    (hstep : ∀ (m : M) (b : β) (rest : HwBytes),
      b ∈ xs →
      ∃ m', mf m t .lengthDelimited
          (encodeVarint (BitVec.ofNat 64 (encB b).length) ++ (encB b ++ rest)) =
            some (m', rest) ∧
        proj m' = stepα (proj m) b)
    (hcont : ∀ m_end, proj m_end = xs.foldl stepα (proj m) → RecordCodecs.LoopsTo mf m_end rest r) :
    RecordCodecs.LoopsTo mf m ((xs.map fun b => lenField t (encB b)).flatten ++ rest) r := by
  obtain ⟨m_end, htail, hp⟩ := loopsTo_list_lenField_hom proj stepα t h1 h2 encB xs hstep m rest
  exact htail r (hcont m_end hp)

private theorem exists_loopsTo_list_lenField_hom {M α β : Type}
    {mf : M → Nat → WireType → HwBytes → Option (M × HwBytes)}
    (proj : M → α) (stepα : α → β → α)
    (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    (encB : β → HwBytes) (xs : List β) {m : M} {rest : HwBytes} {target : α}
    (hstep : ∀ (m : M) (b : β) (rest : HwBytes),
      b ∈ xs →
      ∃ m', mf m t .lengthDelimited
          (encodeVarint (BitVec.ofNat 64 (encB b).length) ++ (encB b ++ rest)) =
            some (m', rest) ∧
        proj m' = stepα (proj m) b)
    (hcont : ∀ m_end, proj m_end = xs.foldl stepα (proj m) →
      ∃ r, RecordCodecs.LoopsTo mf m_end rest r ∧ proj r = target) :
    ∃ r, RecordCodecs.LoopsTo mf m ((xs.map fun b => lenField t (encB b)).flatten ++ rest) r ∧
      proj r = target := by
  obtain ⟨m_end, htail, hp⟩ := loopsTo_list_lenField_hom proj stepα t h1 h2 encB xs hstep m rest
  obtain ⟨r, hr, hpr⟩ := hcont m_end hp
  exact ⟨r, htail r hr, hpr⟩

private theorem lenField_length_ge (tag : Nat) (b : HwBytes) :
    b.length ≤ (lenField tag b).length := by
  unfold lenField
  simp only [List.length_append]
  omega

private theorem bytesField_length_ge_of_lt {tag : Nat} {b : HwBytes} {B : Nat}
    (h : (bytesField tag b).length < B) (hB : 0 < B) : b.length < B := by
  unfold bytesField at h
  split_ifs at h with hb
  · subst hb; simpa using hB
  · exact Nat.lt_of_le_of_lt (lenField_length_ge tag b) h

private theorem mem_flatten_length_le {α : Type} (f : α → HwBytes) {x : α} {xs : List α}
    (hx : x ∈ xs) : (f x).length ≤ ((xs.map f).flatten).length := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | hmem
    · omega
    · have := ih hmem; omega

private theorem exists_loopsTo_run {M α : Type}
    {mf : M → Nat → WireType → HwBytes → Option (M × HwBytes)}
    {proj : M → α} {m : M} {bs bs' : HwBytes} {target : α} (heq : bs = bs')
    (h : ∃ r, RecordCodecs.LoopsTo mf m bs' r ∧ proj r = target) :
    ∃ r, RecordCodecs.decodeFieldsLoop mf bs.length m bs = some r ∧ proj r = target := by
  subst heq; obtain ⟨r, hl, hp⟩ := h; exact ⟨r, hl _ (Nat.le_refl _), hp⟩

private theorem option_bind_of_loopsTo {M β : Type}
    {mf : M → Nat → WireType → HwBytes → Option (M × HwBytes)}
    {f : M → Option β} {m : M} {bs bs' : HwBytes} {target : β} (heq : bs = bs')
    (h : ∃ r, RecordCodecs.LoopsTo mf m bs' r ∧ f r = some target) :
    (RecordCodecs.decodeFieldsLoop mf bs.length m bs).bind f = some target := by
  subst heq; obtain ⟨r, hl, hf⟩ := h; exact option_bind_eq_some (hl _ (Nat.le_refl _)) hf

private theorem exists_loopsTo_lenField {M α : Type}
    {mf : M → Nat → WireType → HwBytes → Option (M × HwBytes)}
    (proj : M → α) (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28) {m : M} {v rest : HwBytes} {target : α}
    (hstep : ∃ m', mf m t .lengthDelimited (encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) = some (m', rest) ∧
      ∃ r, RecordCodecs.LoopsTo mf m' rest r ∧ proj r = target) :
    ∃ r, RecordCodecs.LoopsTo mf m (lenField t v ++ rest) r ∧ proj r = target := by
  obtain ⟨m', hm, r, hr, hp⟩ := hstep; exact ⟨r, loopsTo_lenField t h1 h2 hm hr, hp⟩

private theorem exists_loopsTo_bytesField {M α : Type}
    {mf : M → Nat → WireType → HwBytes → Option (M × HwBytes)}
    (proj : M → α) (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28) {m : M} {v rest : HwBytes} {target : α} (hv : v ≠ [])
    (hstep : ∃ m', mf m t .lengthDelimited (encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) = some (m', rest) ∧
      ∃ r, RecordCodecs.LoopsTo mf m' rest r ∧ proj r = target) :
    ∃ r, RecordCodecs.LoopsTo mf m (bytesField t v ++ rest) r ∧ proj r = target := by
  obtain ⟨m', hm, r, hr, hp⟩ := hstep
  exact ⟨r, loopsTo_bytesField t h1 h2 (fun _ => hm) (fun h => (hv h).elim) hr, hp⟩

private theorem decChainKey_encChainKey (ck : ChainKey) :
    decChainKey (encChainKey ck) = some ck := by
  unfold decChainKey
  have heq : encChainKey ck =
      uint32Field 1 ck.index ++ (bytesField 2 (HMAC.keyToBytes32 ck.key) ++ []) := by
    simp [encChainKey, List.append_nil]
  rw [heq]
  refine (loopsTo_uint32Field (m' := { key := 0#256, index := ck.index }) 1 (by decide) (by decide)
    (by simp [mergeChainKeyField, mergeUint32_encode])
    (fun h0 => by rw [h0]; rfl) ?_) _ (Nat.le_refl _)
  refine loopsTo_bytesField (m' := ck) 2 (by decide) (by decide)
    (fun _ => by
      simp only [mergeChainKeyField]
      exact option_map_eq_some
        (mergeBytes_encode _ _ (by rw [keyToBytes32_length]; decide))
        (by dsimp only; rw [bytesToKey32_keyToBytes32]))
    (fun hnil => (keyToBytes32_ne_nil ck.key hnil).elim)
    (RecordCodecs.loopsTo_nil _ _)

private theorem decMsgKey_encMessageKey (mk : MessageKeyGenerator) (hseed : mk.seed.length < 2 ^ 64) :
    decMsgKey (encMessageKey mk) = some mk := by
  unfold decMsgKey
  have heq : encMessageKey mk = uint32Field 1 mk.counter ++ (bytesField 5 mk.seed ++ []) := by
    simp [encMessageKey, List.append_nil]
  rw [heq]
  refine (loopsTo_uint32Field (m' := { seed := [], counter := mk.counter }) 1 (by decide) (by decide)
    (by simp [mergeMsgKeyField, mergeUint32_encode])
    (fun h0 => by rw [h0]) ?_) _ (Nat.le_refl _)
  refine loopsTo_bytesField (m' := mk) 5 (by decide) (by decide)
    (fun _ => by
      simp only [mergeMsgKeyField]
      exact option_map_eq_some (mergeBytes_encode _ [] hseed) (by cases mk; rfl))
    (by intro hnil; cases mk with | mk s c => dsimp only at hnil ⊢; subst hnil; rfl)
    (RecordCodecs.loopsTo_nil _ _)

private theorem decPendingPreKey_encPendingPreKeyX (p : PendingPreKey) :
    decPendingPreKey (encPendingPreKeyX p) = some p := by
  unfold decPendingPreKey
  have heq : encPendingPreKeyX p =
      optUint32FieldX 1 p.preKeyId ++
      (bytesField 2 p.baseKey.serialize ++
      (int32FieldX 3 p.signedPreKeyId ++
      (uint64FieldX 4 p.timestamp ++ []))) := by
    simp [encPendingPreKeyX, List.append_assoc]
  rw [heq]
  refine (loopsTo_optUint32FieldX
    (m' := ⟨p.preKeyId, 0#32, placeholderBaseKey, 0#64⟩)
    1 (by decide) (by decide)
    (fun v hv => by rw [hv]; simp [mergePendingPreKeyField, mergeUint32_encode])
    (fun hnone => by rw [hnone]) ?_) _ (Nat.le_refl _)
  refine loopsTo_bytesField (m' := ⟨p.preKeyId, 0#32, p.baseKey, 0#64⟩) 2 (by decide) (by decide)
    (fun _ => by
      simp only [mergePendingPreKeyField]
      exact option_bind_eq_some
        (mergeBytes_encode _ _ (by rw [pk_serialize_length]; decide))
        (option_map_eq_some (decDjbPk?_serialize _) rfl))
    (fun hnil => (pk_serialize_ne_nil p.baseKey hnil).elim) ?_
  refine loopsTo_int32FieldX (m' := ⟨p.preKeyId, p.signedPreKeyId, p.baseKey, 0#64⟩)
    3 (by decide) (by decide)
    (by simp [mergePendingPreKeyField, mergeUint32_signExtend_encode])
    (fun h0 => by rw [h0]; rfl) ?_
  refine loopsTo_uint64FieldX (m' := p) 4 (by decide) (by decide)
    (by
      simp only [mergePendingPreKeyField]
      exact option_map_eq_some (decodeVarint_encodeVarint _ _) (by cases p; rfl))
    (by intro h0; cases p; dsimp only at h0 ⊢; subst h0; rfl)
    (RecordCodecs.loopsTo_nil _ _)

private theorem decPendingKyber_encPendingKyberX (kp : PendingKyberPreKey)
    (hct : kp.ciphertext.length < 2 ^ 64) :
    decPendingKyber (encPendingKyberX kp) = some kp := by
  unfold decPendingKyber
  have heq : encPendingKyberX kp =
      uint32Field 1 kp.preKeyId ++ (bytesField 2 kp.ciphertext ++ []) := by
    simp [encPendingKyberX, List.append_nil]
  rw [heq]
  refine (loopsTo_uint32Field (m' := { preKeyId := kp.preKeyId, ciphertext := [] })
    1 (by decide) (by decide)
    (by simp [mergePendingKyberField, mergeUint32_encode])
    (fun h0 => by rw [h0]; rfl) ?_) _ (Nat.le_refl _)
  refine loopsTo_bytesField (m' := kp) 2 (by decide) (by decide)
    (fun _ => by
      simp only [mergePendingKyberField]
      exact option_map_eq_some (mergeBytes_encode _ [] hct) (by cases kp; rfl))
    (by intro hnil; cases kp with | mk pid ct => dsimp only at hnil ⊢; subst hnil; rfl)
    (RecordCodecs.loopsTo_nil _ _)

set_option maxHeartbeats 800000 in
private theorem decodeRecordX_encodeRecordX (x : RecordExtras) (g : GhostState HwBytes)
    (hlen : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 64) :
    decodeRecordX (encodeRecordUnderExtras (fun _ => x) g) =
      some (decodedExtras x g.session.pendingPreKey, g.session) := by
  rcases g with ⟨pty, st, ep, chs⟩
  unfold encodeRecordUnderExtras at hlen ⊢
  dsimp only at hlen ⊢
  have hsess_lt : (encStateUnderExtras x st).length < 2 ^ 64 := by
    have hge := lenField_length_ge 1 (encStateUnderExtras x st)
    unfold msgField at hlen
    exact Nat.lt_of_le_of_lt hge hlen
  have h64_pos : 0 < 2 ^ 64 := by decide
  have hrparts :
      (msgField 6 (st.senderChain.map encSenderChain)).length ≤ (encStateUnderExtras x st).length ∧
      ((st.receiverChains.map fun c => lenField 7 (encReceiverChain c)).flatten).length ≤
        (encStateUnderExtras x st).length ∧
      (msgField 9 (if st.pendingPreKey then some (encPendingPreKeyX x.pending) else none)).length ≤
        (encStateUnderExtras x st).length ∧
      (bytesField 13 x.aliceBaseKey).length ≤ (encStateUnderExtras x st).length ∧
      (msgField 14 (if st.pendingPreKey then x.kyber.map encPendingKyberX else none)).length ≤
        (encStateUnderExtras x st).length ∧
      (bytesField 15 st.pqRatchetState).length ≤ (encStateUnderExtras x st).length := by
    unfold encStateUnderExtras
    simp only [List.length_append]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have habk_lt : x.aliceBaseKey.length < 2 ^ 64 :=
    bytesField_length_ge_of_lt (Nat.lt_of_le_of_lt hrparts.2.2.2.1 hsess_lt) h64_pos
  have hpq_lt : st.pqRatchetState.length < 2 ^ 64 :=
    bytesField_length_ge_of_lt (Nat.lt_of_le_of_lt hrparts.2.2.2.2.2 hsess_lt) h64_pos
  have hsc_lt : ∀ sc, st.senderChain = some sc →
      (encSenderChain sc).length < 2 ^ 64 ∧ (encChainKey sc.chainKey).length < 2 ^ 64 := by
    intro sc hsc
    have h6 := hrparts.1
    simp only [hsc, Option.map_some, msgField] at h6
    have hge1 := lenField_length_ge 6 (encSenderChain sc)
    have hesc : (encSenderChain sc).length < 2 ^ 64 := by omega
    have hck_f : (lenField 3 (encChainKey sc.chainKey)).length ≤ (encSenderChain sc).length := by
      unfold encSenderChain msgField; simp only [List.length_append]; omega
    have hge2 := lenField_length_ge 3 (encChainKey sc.chainKey)
    exact ⟨hesc, by omega⟩
  have hrc_lt : ∀ rc ∈ st.receiverChains, (encReceiverChain rc).length < 2 ^ 64 := by
    intro rc hrc
    have h1 := lenField_length_ge 7 (encReceiverChain rc)
    have h2 := mem_flatten_length_le (fun c => lenField 7 (encReceiverChain c)) hrc
    have h7 := hrparts.2.1
    omega
  have hrcck_lt : ∀ rc ∈ st.receiverChains, ∀ ck, rc.chainKey = some ck →
      (encChainKey ck).length < 2 ^ 64 := by
    intro rc hrc ck hck
    have hrc_b := hrc_lt rc hrc
    have hck_f : (msgField 3 (rc.chainKey.map encChainKey)).length ≤ (encReceiverChain rc).length := by
      unfold encReceiverChain; simp only [List.length_append]; omega
    simp only [hck, Option.map_some, msgField] at hck_f
    have hge := lenField_length_ge 3 (encChainKey ck)
    omega
  have hmk_lt : ∀ rc ∈ st.receiverChains, ∀ mk ∈ rc.messageKeys,
      (encMessageKey mk).length < 2 ^ 64 ∧ mk.seed.length < 2 ^ 64 := by
    intro rc hrc mk hmk
    have hrc_b := hrc_lt rc hrc
    have hmk_fl : ((rc.messageKeys.map fun m => lenField 4 (encMessageKey m)).flatten).length ≤
        (encReceiverChain rc).length := by
      unfold encReceiverChain; simp only [List.length_append]; omega
    have h1 := lenField_length_ge 4 (encMessageKey mk)
    have h2 := mem_flatten_length_le (fun m => lenField 4 (encMessageKey m)) hmk
    have hemk : (encMessageKey mk).length < 2 ^ 64 := by omega
    have hseed_f : (bytesField 5 mk.seed).length ≤ (encMessageKey mk).length := by
      unfold encMessageKey; simp only [List.length_append]; omega
    exact ⟨hemk, bytesField_length_ge_of_lt (Nat.lt_of_le_of_lt hseed_f hemk) h64_pos⟩
  have hppk_lt : st.pendingPreKey = true → (encPendingPreKeyX x.pending).length < 2 ^ 64 := by
    intro hppk
    have h9 := hrparts.2.2.1
    simp only [hppk, ↓reduceIte, msgField] at h9
    have hge := lenField_length_ge 9 (encPendingPreKeyX x.pending)
    omega
  have hky_lt : st.pendingPreKey = true → ∀ kp, x.kyber = some kp →
      (encPendingKyberX kp).length < 2 ^ 64 ∧ kp.ciphertext.length < 2 ^ 64 := by
    intro hppk kp hkp
    have h14 := hrparts.2.2.2.2.1
    simp only [hppk, ↓reduceIte, hkp, Option.map_some, msgField] at h14
    have hge := lenField_length_ge 14 (encPendingKyberX kp)
    have hekp : (encPendingKyberX kp).length < 2 ^ 64 := by omega
    have hct_f : (bytesField 2 kp.ciphertext).length ≤ (encPendingKyberX kp).length := by
      unfold encPendingKyberX; simp only [List.length_append]; omega
    exact ⟨hekp, bytesField_length_ge_of_lt (Nat.lt_of_le_of_lt hct_f hekp) h64_pos⟩
  have option_join_eq_some : ∀ {α : Type} {o : Option (Option α)} {a : α},
      o = some (some a) → o.join = some a := fun ho => by rw [ho]; rfl
  have option_map_eq_some_of_exists : ∀ {α β : Type} {o : Option α} {f : α → β} {b : β},
      (∃ a, o = some a ∧ f a = b) → o.map f = some b := fun ⟨_, ho, hf⟩ => option_map_eq_some ho hf
  unfold decodeRecordX
  refine option_join_eq_some ?_
  have hencRec : msgField 1 (some (encStateUnderExtras x st)) = lenField 1 (encStateUnderExtras x st) ++ [] := by
    simp [msgField]
  rw [hencRec]
  refine (loopsTo_lenField 1 (by decide) (by decide) ?_ (RecordCodecs.loopsTo_nil _ _)) _ (Nat.le_refl _)
  simp only [mergeRecordSessionField, Option.getD_none]
  refine option_bind_eq_some (mergeBytes_encode (encStateUnderExtras x st) [] hsess_lt) ?_
  dsimp only
  refine option_map_eq_some ?_ rfl
  have hencSt : encStateUnderExtras x st =
      uint32Field 1 st.sessionVersion ++
      (bytesField 2 st.localIdentity.serialize ++
      (bytesField 3 ((st.remoteIdentity.map IdentityKey.serialize).getD []) ++
      (bytesField 4 (HMAC.keyToBytes32 st.rootKey) ++
      (uint32Field 5 st.previousCounter ++
      (msgField 6 (st.senderChain.map encSenderChain) ++
      ((st.receiverChains.map fun c => lenField 7 (encReceiverChain c)).flatten ++
      (msgField 9 (if st.pendingPreKey then some (encPendingPreKeyX x.pending) else none) ++
      (uint32Field 10 x.remoteRegistrationId ++
      (uint32Field 11 x.localRegistrationId ++
      (bytesField 13 x.aliceBaseKey ++
      (msgField 14 (if st.pendingPreKey then x.kyber.map encPendingKyberX else none) ++
      (bytesField 15 st.pqRatchetState ++ [])))))))))))) := by
    simp only [encStateUnderExtras, List.append_assoc, List.append_nil]
  rw [hencSt]
  refine (?_ : RecordCodecs.LoopsTo _ _ _ (decodedExtras x st.pendingPreKey, st)) _ (Nat.le_refl _)
  refine loopsTo_uint32Field
    (m' := (seedRecordExtras .A,
      ⟨st.sessionVersion, ⟨placeholderBaseKey⟩, none, 0, 0#32, none, [], false, []⟩))
    1 (by decide) (by decide)
    (option_map_eq_some (mergeUint32_encode _ _) rfl)
    (by intro h0; rw [h0]; rfl) ?_
  refine loopsTo_bytesField
    (m' := (seedRecordExtras .A,
      ⟨st.sessionVersion, st.localIdentity, none, 0, 0#32, none, [], false, []⟩))
    2 (by decide) (by decide)
    (fun _ => option_bind_eq_some
      (mergeBytes_encode _ _ (by rw [ik_serialize_length]; decide))
      (option_map_eq_some (decDjbPk?_serialize st.localIdentity.publicKey)
        (by cases st.localIdentity; rfl)))
    (fun hnil => (ik_serialize_ne_nil st.localIdentity hnil).elim) ?_
  refine loopsTo_bytesField
    (m' := (seedRecordExtras .A,
      ⟨st.sessionVersion, st.localIdentity, st.remoteIdentity, 0, 0#32, none, [], false, []⟩))
    3 (by decide) (by decide)
    (fun hv => by
      rcases hrem : st.remoteIdentity with _ | rem
      · simp [hrem] at hv
      · simp only [Option.map_some, Option.getD_some, mergeSessionField]
        refine option_bind_eq_some (mergeBytes_encode rem.serialize _ (by rw [ik_serialize_length]; decide)) ?_
        have hneB : rem.serialize.isEmpty = false := List.isEmpty_eq_false_iff.mpr (ik_serialize_ne_nil rem)
        dsimp only; rw [hneB]
        exact option_map_eq_some (decDjbPk?_serialize rem.publicKey) (by cases rem; rfl))
    (fun hnil => by
      rcases hrem : st.remoteIdentity with _ | rem
      · rfl
      · simp only [hrem, Option.map_some, Option.getD_some] at hnil
        exact (ik_serialize_ne_nil rem hnil).elim) ?_
  refine loopsTo_bytesField
    (m' := (seedRecordExtras .A,
      ⟨st.sessionVersion, st.localIdentity, st.remoteIdentity, st.rootKey, 0#32, none, [], false, []⟩))
    4 (by decide) (by decide)
    (fun _ => option_map_eq_some
      (mergeBytes_encode _ _ (by rw [keyToBytes32_length]; decide))
      (by dsimp only; rw [bytesToKey32_keyToBytes32]))
    (fun hnil => (keyToBytes32_ne_nil st.rootKey hnil).elim) ?_
  refine loopsTo_uint32Field
    (m' := (seedRecordExtras .A,
      ⟨st.sessionVersion, st.localIdentity, st.remoteIdentity, st.rootKey, st.previousCounter, none, [], false, []⟩))
    5 (by decide) (by decide)
    (option_map_eq_some (mergeUint32_encode _ _) rfl)
    (by intro h0; rw [h0]; rfl) ?_
  refine loopsTo_msgField
    (m' := (seedRecordExtras .A,
      { sessionVersion := st.sessionVersion, localIdentity := st.localIdentity,
        remoteIdentity := st.remoteIdentity, rootKey := st.rootKey,
        previousCounter := st.previousCounter, senderChain := st.senderChain,
        receiverChains := [], pendingPreKey := false, pqRatchetState := [] }))
    6 (by decide) (by decide)
    (fun v hv => by
      rcases hsc : st.senderChain with _ | sc
      · simp [hsc] at hv
      · simp only [hsc, Option.map_some, Option.some.injEq] at hv; subst hv
        obtain ⟨hesc, heck⟩ := hsc_lt sc hsc
        simp only [mergeSessionField]
        refine option_bind_eq_some (mergeBytes_encode (encSenderChain sc) _ hesc) ?_
        dsimp only
        refine option_map_eq_some ?_ rfl
        unfold decSenderChain
        have hencSC : encSenderChain sc =
            bytesField 1 sc.ratchetKey.publicKey.serialize ++
            (bytesField 2 sc.ratchetKey.privateKey.bytes.toList ++
            (lenField 3 (encChainKey sc.chainKey) ++ [])) := by
          simp [encSenderChain, msgField, List.append_assoc]
        refine option_bind_of_loopsTo hencSC ?_
        refine exists_loopsTo_bytesField _ 1 (by decide) (by decide)
          (pk_serialize_ne_nil sc.ratchetKey.publicKey)
          ⟨_, option_bind_eq_some
            (mergeBytes_encode _ _ (by rw [pk_serialize_length]; decide))
            (option_map_eq_some (decDjbPk?_serialize _) rfl), ?_⟩
        refine exists_loopsTo_bytesField _ 2 (by decide) (by decide)
          (by intro hnil; have h32 := sc.ratchetKey.privateKey.bytes.toList_length; rw [hnil] at h32; cases h32)
          ⟨_, option_bind_eq_some
            (mergeBytes_encode _ _ (by rw [sc.ratchetKey.privateKey.bytes.toList_length]; decide))
            (by dsimp only; simp only [sc.ratchetKey.privateKey.bytes.toList_length, ↓reduceDIte]; rfl), ?_⟩
        refine exists_loopsTo_lenField _ 3 (by decide) (by decide)
          ⟨_, option_bind_eq_some
            (mergeBytes_encode _ _ heck)
            (option_map_eq_some (decChainKey_encChainKey sc.chainKey) rfl), ?_⟩
        refine ⟨_, RecordCodecs.loopsTo_nil _ _, ?_⟩
        cases sc with | mk kp ck =>
          cases kp with | mk pub priv =>
            cases priv with | mk pv =>
              cases pv with | mk l hl => rfl)
    (fun hnone => by
      rcases hsc : st.senderChain with _ | sc
      · rfl
      · simp [hsc] at hnone) ?_
  refine apply_loopsTo_list_lenField_hom
    id
    (fun (acc : RecordExtras × SessionState HwBytes) rc =>
      (acc.1, { acc.2 with receiverChains := acc.2.receiverChains ++ [rc] }))
    7 (by decide) (by decide) encReceiverChain st.receiverChains
    (fun acc rc rest hrc => by
      rcases acc with ⟨ax, ast⟩
      refine ⟨(ax, { ast with receiverChains := ast.receiverChains ++ [rc] }), ?_, rfl⟩
      simp only [mergeSessionField]
      refine option_bind_eq_some (mergeBytes_encode (encReceiverChain rc) rest (hrc_lt rc hrc)) ?_
      dsimp only
      refine option_map_eq_some ?_ rfl
      unfold decReceiverChain
      refine option_map_eq_some_of_exists ?_
      have hencRC : encReceiverChain rc =
          bytesField 1 rc.senderRatchetKey.serialize ++
          (msgField 3 (rc.chainKey.map encChainKey) ++
          ((rc.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten ++ [])) := by
        simp [encReceiverChain, List.append_assoc]
      refine exists_loopsTo_run hencRC ?_
      refine exists_loopsTo_bytesField _ 1 (by decide) (by decide)
        (pk_serialize_ne_nil rc.senderRatchetKey)
        ⟨_, option_bind_eq_some
          (mergeBytes_encode _ _ (by rw [pk_serialize_length]; decide))
          (option_map_eq_some (decDjbPk?_serialize _) rfl), ?_⟩
      have hFoldMk : ∀ (oks : Option ChainKey),
          rc.messageKeys.foldl
            (fun (r : ReceiverChain) mk => { r with messageKeys := r.messageKeys ++ [mk] })
            ⟨rc.senderRatchetKey, oks, []⟩ =
          ⟨rc.senderRatchetKey, oks, rc.messageKeys⟩ := by
        intro oks
        have : ∀ (mks : List MessageKeyGenerator) (acc : List MessageKeyGenerator),
            mks.foldl
              (fun (r : ReceiverChain) mk => { r with messageKeys := r.messageKeys ++ [mk] })
              ⟨rc.senderRatchetKey, oks, acc⟩ =
            ⟨rc.senderRatchetKey, oks, acc ++ mks⟩ := by
          intro mks
          induction mks with
          | nil => intro acc; simp
          | cons m ms ih =>
            intro acc; simp only [List.foldl_cons]
            rw [ih (acc ++ [m]), List.append_assoc, List.singleton_append]
        simpa using this rc.messageKeys []
      rcases hck_opt : rc.chainKey with _ | ck
      · simp only [Option.map_none, msgField, List.nil_append]
        refine exists_loopsTo_list_lenField_hom
          (fun c : RawChain => (⟨c.pub, c.ck, c.mks⟩ : ReceiverChain))
          (fun (r : ReceiverChain) mk => { r with messageKeys := r.messageKeys ++ [mk] })
          4 (by decide) (by decide) encMessageKey rc.messageKeys
          (fun _ mk _ hmk =>
            ⟨_, option_bind_eq_some
              (mergeBytes_encode _ _ (hmk_lt rc hrc mk hmk).1)
              (option_map_eq_some (decMsgKey_encMessageKey mk (hmk_lt rc hrc mk hmk).2) rfl), rfl⟩) ?_
        intro m_end hm_end
        exact ⟨m_end, RecordCodecs.loopsTo_nil _ _, hm_end.trans ((hFoldMk none).trans
          (by cases rc; dsimp only at hck_opt ⊢; subst hck_opt; rfl))⟩
      · simp only [Option.map_some, msgField]
        refine exists_loopsTo_lenField
          (fun c : RawChain => (⟨c.pub, c.ck, c.mks⟩ : ReceiverChain))
          3 (by decide) (by decide)
          ⟨_, option_bind_eq_some
            (mergeBytes_encode _ _ (hrcck_lt rc hrc ck hck_opt))
            (option_map_eq_some (decChainKey_encChainKey ck) rfl), ?_⟩
        refine exists_loopsTo_list_lenField_hom
          (fun c : RawChain => (⟨c.pub, c.ck, c.mks⟩ : ReceiverChain))
          (fun (r : ReceiverChain) mk => { r with messageKeys := r.messageKeys ++ [mk] })
          4 (by decide) (by decide) encMessageKey rc.messageKeys
          (fun _ mk _ hmk =>
            ⟨_, option_bind_eq_some
              (mergeBytes_encode _ _ (hmk_lt rc hrc mk hmk).1)
              (option_map_eq_some (decMsgKey_encMessageKey mk (hmk_lt rc hrc mk hmk).2) rfl), rfl⟩) ?_
        intro m_end hm_end
        exact ⟨m_end, RecordCodecs.loopsTo_nil _ _, hm_end.trans ((hFoldMk (some ck)).trans
          (by cases rc; dsimp only at hck_opt ⊢; subst hck_opt; rfl))⟩)
    ?_
  intro m_rc hm_rc_eq
  have hm_rc_val : m_rc = (seedRecordExtras .A,
      ⟨st.sessionVersion, st.localIdentity, st.remoteIdentity, st.rootKey,
        st.previousCounter, st.senderChain, st.receiverChains, false, []⟩) := by
    have hfold : ∀ (rcs acc : List ReceiverChain),
        rcs.foldl (fun (p : RecordExtras × SessionState HwBytes) rc =>
            (p.1, { p.2 with receiverChains := p.2.receiverChains ++ [rc] }))
          (seedRecordExtras .A, ⟨st.sessionVersion, st.localIdentity, st.remoteIdentity, st.rootKey,
            st.previousCounter, st.senderChain, acc, false, []⟩) =
        (seedRecordExtras .A, ⟨st.sessionVersion, st.localIdentity, st.remoteIdentity, st.rootKey,
            st.previousCounter, st.senderChain, acc ++ rcs, false, []⟩) := by
      intro rcs; induction rcs with
      | nil => intro acc; simp
      | cons rc rcs ih =>
        intro acc; simp only [List.foldl_cons]; rw [ih (acc ++ [rc]), List.append_assoc, List.singleton_append]
    simpa only [id_eq, hfold st.receiverChains [], List.nil_append] using hm_rc_eq
  rw [hm_rc_val]
  have hx_nonppk : { seedRecordExtras .A with
      remoteRegistrationId := x.remoteRegistrationId,
      localRegistrationId := x.localRegistrationId,
      aliceBaseKey := x.aliceBaseKey } =
      { x with pending := (seedRecordExtras .A).pending, kyber := none } := by cases x; rfl
  cases hppk : st.pendingPreKey
  · simp only [Bool.false_eq_true, ↓reduceIte, msgField, List.nil_append, decodedExtras]
    refine loopsTo_uint32Field 10 (by decide) (by decide)
      (option_map_eq_some (mergeUint32_encode _ _) rfl) (by intro h0; simp [h0, seedRecordExtras]) ?_
    refine loopsTo_uint32Field 11 (by decide) (by decide)
      (option_map_eq_some (mergeUint32_encode _ _) rfl) (by intro h0; simp [h0, seedRecordExtras]) ?_
    refine loopsTo_bytesField 13 (by decide) (by decide)
      (fun _ => option_map_eq_some (mergeBytes_encode _ _ habk_lt) rfl)
      (by intro hnil; simp [hnil, seedRecordExtras]) ?_
    refine loopsTo_bytesField 15 (by decide) (by decide)
      (fun _ => option_map_eq_some (mergeBytes_encode _ [] hpq_lt) (by
        dsimp only; rw [hx_nonppk]; congr 1; cases st; dsimp only at hppk; subst hppk; rfl))
      (fun hnil => by rw [hx_nonppk]; congr 1; cases st; dsimp only at hppk hnil; subst hppk; subst hnil; rfl)
      (RecordCodecs.loopsTo_nil _ _)
  · simp only [↓reduceIte, msgField, decodedExtras]
    refine loopsTo_lenField 9 (by decide) (by decide)
      (option_bind_eq_some (mergeBytes_encode _ _ (hppk_lt hppk))
        (option_map_eq_some (decPendingPreKey_encPendingPreKeyX x.pending) rfl)) ?_
    refine loopsTo_uint32Field 10 (by decide) (by decide)
      (option_map_eq_some (mergeUint32_encode _ _) rfl) (by intro h0; simp [h0, seedRecordExtras]) ?_
    refine loopsTo_uint32Field 11 (by decide) (by decide)
      (option_map_eq_some (mergeUint32_encode _ _) rfl) (by intro h0; simp [h0, seedRecordExtras]) ?_
    refine loopsTo_bytesField 13 (by decide) (by decide)
      (fun _ => option_map_eq_some (mergeBytes_encode _ _ habk_lt) rfl)
      (by intro hnil; simp [hnil, seedRecordExtras]) ?_
    refine loopsTo_msgField
      (m' := (x, ⟨st.sessionVersion, st.localIdentity, st.remoteIdentity,
        st.rootKey, st.previousCounter, st.senderChain, st.receiverChains, true, []⟩))
      14 (by decide) (by decide)
      (fun v hv => by
        rcases hkx : x.kyber with _ | kp
        · simp [hkx] at hv
        · simp only [hkx, Option.map_some, Option.some.injEq] at hv; subst hv
          obtain ⟨hekp, hct⟩ := hky_lt hppk kp hkx
          simp only [mergeSessionField]
          refine option_bind_eq_some (mergeBytes_encode (encPendingKyberX kp) _ hekp) ?_
          dsimp only; refine option_map_eq_some (decPendingKyber_encPendingKyberX kp hct) ?_
          cases x; dsimp only at hkx; subst hkx; rfl)
      (fun hnone => by
        rcases hkx : x.kyber with _ | kp
        · cases x; dsimp only at hkx; subst hkx; rfl
        · simp [hkx] at hnone) ?_
    refine loopsTo_bytesField 15 (by decide) (by decide)
      (fun _ => option_map_eq_some (mergeBytes_encode _ [] hpq_lt) (by
        dsimp only; congr 1; cases st; dsimp only at hppk; subst hppk; rfl))
      (fun hnil => by congr 1; cases st; dsimp only at hppk hnil; subst hppk; subst hnil; rfl)
      (RecordCodecs.loopsTo_nil _ _)

theorem pqSessionEquiv_of_encodeRecordX_eq {x x' : RecordExtras} {g g' : GhostState HwBytes}
    (hparty : g.party = g'.party)
    (hlen : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31)
    (hlen' : (encodeRecordUnderExtras (fun _ => x') g').length < 2 ^ 31)
    (henc : encodeRecordUnderExtras (fun _ => x) g = encodeRecordUnderExtras (fun _ => x') g') :
    PqSessionEquiv x g x' g' := by
  have hd := decodeRecordX_encodeRecordX x g (by omega)
  have hd' := decodeRecordX_encodeRecordX x' g' (by omega)
  rw [henc] at hd
  have heq := Option.some.inj (hd.symm.trans hd')
  injection heq with hx_dec hsess
  cases hppk : g.session.pendingPreKey
  · have hppk' : g'.session.pendingPreKey = false := hsess ▸ hppk
    simp only [decodedExtras, hppk, hppk', Bool.false_eq_true, ↓reduceIte] at hx_dec
    exact ⟨hparty, hsess,
      by simpa using congrArg RecordExtras.remoteRegistrationId hx_dec,
      by simpa using congrArg RecordExtras.localRegistrationId hx_dec,
      by simpa using congrArg RecordExtras.aliceBaseKey hx_dec,
      fun h => by rw [hppk] at h; cases h⟩
  · have hppk' : g'.session.pendingPreKey = true := hsess ▸ hppk
    simp only [decodedExtras, hppk, hppk', ↓reduceIte] at hx_dec
    subst hx_dec
    exact ⟨hparty, hsess, rfl, rfl, rfl, fun _ => rfl⟩

end CodecInjAux

namespace DY.Libsignal.Composed.Refinement.Cli.SDet
export CodecInjAux (le32_length le32_inj djbKey_length djbKey_inj kyberKey_length kyberKey_inj
  bytesToKey32_keyToBytes32 keyToBytes32_inj baseKeysBytes_inj preKeyMsgE_bytes_inj
  identityKeyPair_encode_inj identityKey_serialize_inj signedRecordBytes_inj kyberRecordBytes_inj
  kyberRecordBytes_ne_nil oneTimeRecordBytes_inj oneTimeRecordBytes_ne_nil
  pqSessionEquiv_of_encodeRecordX_eq)
end DY.Libsignal.Composed.Refinement.Cli.SDet
