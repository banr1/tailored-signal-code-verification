/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.RecordCodecs
public import LibsignalBinary.Proofs.ProtoCodecRoundTrip
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalProtoCodec
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import LibsignalBinary.Specifications.RecordCodecs.Proto

set_option autoImplicit false

/-!
# Round-Trip and Known-Answer Theorems for `RecordCodecs`

* `decode (encode m) = some m` for `PreKeyRecordStructure`, `SignedPreKeyRecordStructure`, and
  `IdentityKeyPairStructure`, and `deserialize (serialize r) = .ok r` for `PreKeyRecord`,
  `SignedPreKeyRecord`, and `KyberPreKeyRecord` whenever every byte field has length `< 2 ^ 64`.
* `IdentityKeyPair.tryFrom (serialize kp) = .ok kp` for clamped private keys, and every key
  returned by `tryFrom` is clamped.
* `decodeIdentityKey (IdentityKey.serialize k) = .ok k`.
* Reject-case characterizations: empty `identity-key-pair` yields `NoKeyTypeIdentifier`; empty
  pre-key input decodes to the proto3 default record; malformed trailing bytes yield
  `InvalidProtobufEncoding`.
-/

@[expose] public section

namespace CryptoVerification.RecordCodecs

open CryptoGames CryptoGames.LibsignalSession CryptoVerification.LibsignalProtoCodec
section Loop

variable {M : Type} (mf : M → ℕ → WireType → List (BitVec 8) → Option (M × List (BitVec 8)))

/-- `decodeFieldsLoop mf` reaches `r` from `m` on `bs` with any fuel that covers the input. -/
def LoopsTo (m : M) (bs : List (BitVec 8)) (r : M) : Prop :=
  ∀ n, bs.length ≤ n → decodeFieldsLoop mf n m bs = some r

theorem loopsTo_nil (m : M) : LoopsTo mf m [] m := by
  intro n _
  cases n <;> rfl

/-- One field: key, then a body that `mf` consumes. -/
theorem loopsTo_field (t : ℕ) (wt : WireType) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    (m m' r : M) (body rest : List (BitVec 8))
    (hmerge : mf m t wt (body ++ rest) = some (m', rest)) (h : LoopsTo mf m' rest r) :
    LoopsTo mf m (encodeKey t wt ++ (body ++ rest)) r := by
  intro n hn
  have hne : encodeKey t wt ≠ [] := encodeVarint_ne_nil _
  have hpos : 1 ≤ (encodeKey t wt).length := List.length_pos_iff.mpr hne
  have hlen : 1 + rest.length ≤ (encodeKey t wt ++ (body ++ rest)).length := by
    simp only [List.length_append]
    omega
  cases n with
  | zero => omega
  | succ fuel =>
    cases h_bs : encodeKey t wt ++ (body ++ rest) with
    | nil =>
      rw [h_bs] at hlen
      simp at hlen
    | cons b bs_tail =>
      unfold decodeFieldsLoop
      rw [← h_bs, decodeKey_encodeKey t wt (body ++ rest) h1 h2]
      dsimp only
      rw [hmerge]
      exact h fuel (by omega)

end Loop

/-! ## `fixed64` -/

private theorem mergeFixed64_encode (v : BitVec 64) (rest : List (BitVec 8)) :
    mergeFixed64 .sixtyFourBit (le64Bytes v ++ rest) = some (v, rest) := by
  unfold mergeFixed64 le64Bytes
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, List.cons_append, List.nil_append]
  congr 2
  apply BitVec.eq_of_toNat_eq
  unfold le64
  rw [BitVec.toNat_ofNat]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hv : v.toNat < 2 ^ 64 := v.isLt
  omega

private theorem loopsTo_proto3_bytes {M : Type}
    (mf : M → ℕ → WireType → List (BitVec 8) → Option (M × List (BitVec 8)))
    (t : ℕ) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    (v : List (BitVec 8)) (m m' r : M) (rest : List (BitVec 8))
    (hempty : v = [] → m = m')
    (hmerge : mf m t .lengthDelimited
      (encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) = some (m', rest))
    (h : LoopsTo mf m' rest r) :
    LoopsTo mf m (encodeProto3BytesField t v ++ rest) r := by
  unfold encodeProto3BytesField
  by_cases hv0 : v = []
  · have hm := hempty hv0
    subst hm
    simpa [hv0] using h
  · simp only [hv0, ↓reduceIte]
    simpa only [encodeBytesField, List.append_assoc] using
      loopsTo_field mf t .lengthDelimited h1 h2 m m' r
        (encodeVarint (BitVec.ofNat 64 v.length) ++ v) rest
        (by simpa only [List.append_assoc] using hmerge) h

private theorem loopsTo_proto3_uint32 {M : Type}
    (mf : M → ℕ → WireType → List (BitVec 8) → Option (M × List (BitVec 8)))
    (t : ℕ) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    (v : BitVec 32) (m m' r : M) (rest : List (BitVec 8))
    (hzero : v = 0 → m = m')
    (hmerge : mf m t .varint (encodeVarint (v.zeroExtend 64) ++ rest) = some (m', rest))
    (h : LoopsTo mf m' rest r) :
    LoopsTo mf m (encodeProto3Uint32Field t v ++ rest) r := by
  unfold encodeProto3Uint32Field
  by_cases hv0 : v = 0
  · have hm := hzero hv0
    subst hm
    simpa [hv0] using h
  · simp only [hv0, ↓reduceIte]
    simpa only [encodeUint32Field, List.append_assoc] using
      loopsTo_field mf t .varint h1 h2 m m' r
        (encodeVarint (v.zeroExtend 64)) rest hmerge h

private theorem loopsTo_proto3_fixed64 {M : Type}
    (mf : M → ℕ → WireType → List (BitVec 8) → Option (M × List (BitVec 8)))
    (t : ℕ) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    (v : BitVec 64) (m m' r : M) (rest : List (BitVec 8))
    (hzero : v = 0 → m = m')
    (hmerge : mf m t .sixtyFourBit (le64Bytes v ++ rest) = some (m', rest))
    (h : LoopsTo mf m' rest r) :
    LoopsTo mf m (encodeProto3Fixed64Field t v ++ rest) r := by
  unfold encodeProto3Fixed64Field
  by_cases hv0 : v = 0
  · have hm := hzero hv0
    subst hm
    simpa [hv0] using h
  · simp only [hv0, ↓reduceIte, List.append_assoc]
    exact loopsTo_field mf t .sixtyFourBit h1 h2 m m' r (le64Bytes v) rest hmerge h

theorem PreKeyRecordStructure.decode_encode (m : PreKeyRecordStructure)
    (hpub : m.publicKey.length < 2 ^ 64) (hpriv : m.privateKey.length < 2 ^ 64) :
    PreKeyRecordStructure.decode m.encode = some m := by
  unfold PreKeyRecordStructure.decode
  suffices hloop : LoopsTo PreKeyRecordStructure.mergeField PreKeyRecordStructure.empty m.encode m from
    hloop m.encode.length (le_refl _)
  unfold PreKeyRecordStructure.encode
  simp only [List.append_assoc]
  let s0 := PreKeyRecordStructure.empty
  let s1 : PreKeyRecordStructure := { s0 with id := m.id }
  let s2 : PreKeyRecordStructure := { s1 with publicKey := m.publicKey }
  let s3 : PreKeyRecordStructure := { s2 with privateKey := m.privateKey }
  have hs3 : s3 = m := by cases m; rfl
  rw [← List.append_nil (encodeProto3BytesField 3 m.privateKey)]
  refine loopsTo_proto3_uint32 PreKeyRecordStructure.mergeField 1 (by omega) (by omega)
    m.id s0 s1 m _ (fun hz => by simp [s0, s1, PreKeyRecordStructure.empty, hz]) ?_ ?_
  · unfold PreKeyRecordStructure.mergeField
    rw [mergeUint32_encode]
    rfl
  refine loopsTo_proto3_bytes PreKeyRecordStructure.mergeField 2 (by omega) (by omega)
    m.publicKey s1 s2 m _ (fun he => by simp [s0, s1, s2, PreKeyRecordStructure.empty, he]) ?_ ?_
  · unfold PreKeyRecordStructure.mergeField
    rw [mergeBytes_encode m.publicKey _ hpub]
    rfl
  refine loopsTo_proto3_bytes PreKeyRecordStructure.mergeField 3 (by omega) (by omega)
    m.privateKey s2 s3 m [] (fun he => by simp [s0, s1, s2, s3, PreKeyRecordStructure.empty, he]) ?_ ?_
  · unfold PreKeyRecordStructure.mergeField
    rw [mergeBytes_encode m.privateKey [] hpriv]
    rfl
  · rw [hs3]
    exact loopsTo_nil _ m

theorem SignedPreKeyRecordStructure.decode_encode (m : SignedPreKeyRecordStructure)
    (hpub : m.publicKey.length < 2 ^ 64) (hpriv : m.privateKey.length < 2 ^ 64)
    (hsig : m.signature.length < 2 ^ 64) :
    SignedPreKeyRecordStructure.decode m.encode = some m := by
  unfold SignedPreKeyRecordStructure.decode
  suffices hloop :
      LoopsTo SignedPreKeyRecordStructure.mergeField SignedPreKeyRecordStructure.empty m.encode m from
    hloop m.encode.length (le_refl _)
  unfold SignedPreKeyRecordStructure.encode
  simp only [List.append_assoc]
  let s0 := SignedPreKeyRecordStructure.empty
  let s1 : SignedPreKeyRecordStructure := { s0 with id := m.id }
  let s2 : SignedPreKeyRecordStructure := { s1 with publicKey := m.publicKey }
  let s3 : SignedPreKeyRecordStructure := { s2 with privateKey := m.privateKey }
  let s4 : SignedPreKeyRecordStructure := { s3 with signature := m.signature }
  let s5 : SignedPreKeyRecordStructure := { s4 with timestamp := m.timestamp }
  have hs5 : s5 = m := by cases m; rfl
  rw [← List.append_nil (encodeProto3Fixed64Field 5 m.timestamp)]
  refine loopsTo_proto3_uint32 SignedPreKeyRecordStructure.mergeField 1 (by omega) (by omega)
    m.id s0 s1 m _ (fun hz => by simp [s0, s1, SignedPreKeyRecordStructure.empty, hz]) ?_ ?_
  · unfold SignedPreKeyRecordStructure.mergeField
    rw [mergeUint32_encode]
    rfl
  refine loopsTo_proto3_bytes SignedPreKeyRecordStructure.mergeField 2 (by omega) (by omega)
    m.publicKey s1 s2 m _ (fun he => by simp [s0, s1, s2, SignedPreKeyRecordStructure.empty, he]) ?_ ?_
  · unfold SignedPreKeyRecordStructure.mergeField
    rw [mergeBytes_encode m.publicKey _ hpub]
    rfl
  refine loopsTo_proto3_bytes SignedPreKeyRecordStructure.mergeField 3 (by omega) (by omega)
    m.privateKey s2 s3 m _
    (fun he => by simp [s0, s1, s2, s3, SignedPreKeyRecordStructure.empty, he]) ?_ ?_
  · unfold SignedPreKeyRecordStructure.mergeField
    rw [mergeBytes_encode m.privateKey _ hpriv]
    rfl
  refine loopsTo_proto3_bytes SignedPreKeyRecordStructure.mergeField 4 (by omega) (by omega)
    m.signature s3 s4 m _
    (fun he => by simp [s0, s1, s2, s3, s4, SignedPreKeyRecordStructure.empty, he]) ?_ ?_
  · unfold SignedPreKeyRecordStructure.mergeField
    rw [mergeBytes_encode m.signature _ hsig]
    rfl
  refine loopsTo_proto3_fixed64 SignedPreKeyRecordStructure.mergeField 5 (by omega) (by omega)
    m.timestamp s4 s5 m []
    (fun hz => by simp [s0, s1, s2, s3, s4, s5, SignedPreKeyRecordStructure.empty, hz]) ?_ ?_
  · unfold SignedPreKeyRecordStructure.mergeField
    rw [mergeFixed64_encode]
    rfl
  · rw [hs5]
    exact loopsTo_nil _ m

theorem IdentityKeyPairStructure.decode_encode (m : IdentityKeyPairStructure)
    (hpub : m.publicKey.length < 2 ^ 64) (hpriv : m.privateKey.length < 2 ^ 64) :
    IdentityKeyPairStructure.decode m.encode = some m := by
  unfold IdentityKeyPairStructure.decode
  suffices hloop :
      LoopsTo IdentityKeyPairStructure.mergeField IdentityKeyPairStructure.empty m.encode m from
    hloop m.encode.length (le_refl _)
  unfold IdentityKeyPairStructure.encode
  let s0 := IdentityKeyPairStructure.empty
  let s1 : IdentityKeyPairStructure := { s0 with publicKey := m.publicKey }
  let s2 : IdentityKeyPairStructure := { s1 with privateKey := m.privateKey }
  have hs2 : s2 = m := by cases m; rfl
  rw [← List.append_nil (encodeProto3BytesField 2 m.privateKey)]
  refine loopsTo_proto3_bytes IdentityKeyPairStructure.mergeField 1 (by omega) (by omega)
    m.publicKey s0 s1 m _ (fun he => by simp [s0, s1, IdentityKeyPairStructure.empty, he]) ?_ ?_
  · unfold IdentityKeyPairStructure.mergeField
    rw [mergeBytes_encode m.publicKey _ hpub]
    rfl
  refine loopsTo_proto3_bytes IdentityKeyPairStructure.mergeField 2 (by omega) (by omega)
    m.privateKey s1 s2 m []
    (fun he => by simp [s0, s1, s2, IdentityKeyPairStructure.empty, he]) ?_ ?_
  · unfold IdentityKeyPairStructure.mergeField
    rw [mergeBytes_encode m.privateKey [] hpriv]
    rfl
  · rw [hs2]
    exact loopsTo_nil _ m

theorem decodeIdentityKey_serialize (k : IdentityKey) :
    decodeIdentityKey k.serialize = .ok k := by
  rcases k with ⟨⟨⟨xs, hxs⟩⟩⟩
  unfold decodeIdentityKey IdentityKey.serialize PublicKey.serialize PublicKey.deserialize
  have hge : 32 ≤ xs.length := by omega
  simp only [List.Vector.toList, ne_eq, not_true_eq_false, ↓reduceIte, hge, ↓reduceDIte, Except.map]
  congr 3
  apply Subtype.ext
  exact List.take_of_length_le (by omega)

end CryptoVerification.RecordCodecs
