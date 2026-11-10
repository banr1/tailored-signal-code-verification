/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.RecordX.BridgeCommon
import LibsignalBinary.Proofs.E2E.Epochs
import LibsignalBinary.Proofs.E2E.Reach.BundleCommon

/-!
# Encoded record length bounds for `encodeRecordUnderExtras` on reachable states

**Checked by Lean.** Shows `(encodeRecordUnderExtras E g).length < 2 ^ 21` (hence `< 2 ^ 32`) on
every reachable session-model state `g` whenever `aliceBaseKey` and any pending Kyber ciphertext
have length `< 2 ^ 16` (in particular under `FixedIdRecordExtras`).
-/

@[expose] public section

namespace CryptoVerification.E2E.RecordX

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec CryptoVerification.E2E

/-! ## Protobuf field length bounds -/

theorem encodeVarintAux_length_le' (n : Nat) (v : BitVec 64) :
    (encodeVarintAux n v).length ≤ n := by
  induction n generalizing v with
  | zero => simp [encodeVarintAux]
  | succ n ih =>
    unfold encodeVarintAux
    split
    · simp
    · simp only [List.length_cons]
      have := ih (v >>> 7)
      omega

theorem encodeVarint_length_le' (v : BitVec 64) : (encodeVarint v).length ≤ 10 :=
  encodeVarintAux_length_le' 10 v

theorem encodeKey_length_le' (tag : Nat) (wt : WireType) :
    (encodeKey tag wt).length ≤ 10 :=
  encodeVarint_length_le' _

theorem lenField_length_le' (tag : Nat) (b : Bytes) :
    (lenField tag b).length ≤ b.length + 20 := by
  unfold lenField
  have h1 := encodeKey_length_le' tag .lengthDelimited
  have h2 := encodeVarint_length_le' (BitVec.ofNat 64 b.length)
  simp only [List.length_append]
  omega

theorem lenField_length_ge' (tag : Nat) (b : Bytes) :
    b.length ≤ (lenField tag b).length := by
  unfold lenField
  simp only [List.length_append]
  omega

theorem bytesField_length_le' (tag : Nat) (b : Bytes) :
    (bytesField tag b).length ≤ b.length + 20 := by
  unfold bytesField
  split_ifs
  · simp
  · exact lenField_length_le' tag b

theorem uint32Field_length_le' (tag : Nat) (v : BitVec 32) :
    (uint32Field tag v).length ≤ 20 := by
  unfold uint32Field
  split_ifs
  · simp
  · have h1 := encodeKey_length_le' tag .varint
    have h2 := encodeVarint_length_le' (v.setWidth 64)
    simp only [List.length_append]
    omega

theorem uint64FieldX_length_le (tag : Nat) (v : BitVec 64) :
    (uint64FieldX tag v).length ≤ 20 := by
  unfold uint64FieldX
  split_ifs
  · simp
  · have h1 := encodeKey_length_le' tag .varint
    have h2 := encodeVarint_length_le' v
    simp only [List.length_append]
    omega

theorem int32FieldX_length_le (tag : Nat) (v : BitVec 32) :
    (int32FieldX tag v).length ≤ 20 := by
  unfold int32FieldX
  split_ifs
  · simp
  · have h1 := encodeKey_length_le' tag .varint
    have h2 := encodeVarint_length_le' (v.signExtend 64)
    simp only [List.length_append]
    omega

theorem optUint32FieldX_length_le (tag : Nat) (ov : Option (BitVec 32)) :
    (optUint32FieldX tag ov).length ≤ 20 := by
  rcases ov with _ | v
  · simp [optUint32FieldX]
  · unfold optUint32FieldX
    have h1 := encodeKey_length_le' tag .varint
    have h2 := encodeVarint_length_le' (v.setWidth 64)
    simp only [List.length_append]
    omega

theorem serialize_pk_length' (pk : PublicKey) : pk.serialize.length = 33 := by
  unfold PublicKey.serialize
  simp [pk.bytes.toList_length]

/-! ## Extras-dependent field length (`extraLen`) -/

/-- The fields of `encStateUnderExtras x st` that depend on `x` (tags 9, 10, 11, 13, 14). -/
private def extraLen (x : RecordExtras) (b : Bool) : Nat :=
  (msgField 9 (if b then some (encPendingPreKeyX x.pending) else none)).length +
  (uint32Field 10 x.remoteRegistrationId).length +
  (uint32Field 11 x.localRegistrationId).length +
  (bytesField 13 x.aliceBaseKey).length +
  (msgField 14 (if b then x.kyber.map encPendingKyberX else none)).length

private theorem encStateX_length (x y : RecordExtras) (st : SessionState Bytes) :
    (encStateUnderExtras x st).length + extraLen y st.pendingPreKey =
      (encStateUnderExtras y st).length + extraLen x st.pendingPreKey := by
  simp only [encStateUnderExtras, extraLen, List.length_append]
  omega

private theorem extraLen_le (x : RecordExtras) (b : Bool)
    (ha : x.aliceBaseKey.length < 2 ^ 16)
    (hk : ∀ k, x.kyber = some k → k.ciphertext.length < 2 ^ 16) :
    extraLen x b ≤ 2 * 2 ^ 16 + 300 := by
  unfold extraLen
  have h9 : (msgField 9 (if b then some (encPendingPreKeyX x.pending) else none)).length ≤ 133 := by
    cases b
    · simp [msgField]
    · simp only [↓reduceIte, msgField]
      have h0 := lenField_length_le' 9 (encPendingPreKeyX x.pending)
      have heq : (encPendingPreKeyX x.pending).length =
          (optUint32FieldX 1 x.pending.preKeyId).length +
          (bytesField 2 x.pending.baseKey.serialize).length +
          (int32FieldX 3 x.pending.signedPreKeyId).length +
          (uint64FieldX 4 x.pending.timestamp).length := by
        simp only [encPendingPreKeyX, List.length_append]
      have ha := optUint32FieldX_length_le 1 x.pending.preKeyId
      have hb := bytesField_length_le' 2 x.pending.baseKey.serialize
      rw [serialize_pk_length'] at hb
      have hc := int32FieldX_length_le 3 x.pending.signedPreKeyId
      have hd := uint64FieldX_length_le 4 x.pending.timestamp
      omega
  have h10 := uint32Field_length_le' 10 x.remoteRegistrationId
  have h11 := uint32Field_length_le' 11 x.localRegistrationId
  have h13 := bytesField_length_le' 13 x.aliceBaseKey
  have h14 : (msgField 14 (if b then x.kyber.map encPendingKyberX else none)).length ≤
      2 ^ 16 + 60 := by
    cases b
    · simp [msgField]
    · simp only [↓reduceIte]
      rcases hkx : x.kyber with _ | k
      · simp [msgField]
      · simp only [Option.map_some, msgField]
        have h0 := lenField_length_le' 14 (encPendingKyberX k)
        have heq : (encPendingKyberX k).length =
            (uint32Field 1 k.preKeyId).length + (bytesField 2 k.ciphertext).length := by
          simp only [encPendingKyberX, List.length_append]
        have ha' := uint32Field_length_le' 1 k.preKeyId
        have hb' := bytesField_length_le' 2 k.ciphertext
        have hc' := hk k hkx
        omega
  omega

/-! ## Reachable-state encoded length bounds -/

/-- On every reachable state `g` under `< 2 ^ 16`-byte extras, `(encodeRecordUnderExtras E g).length < 2 ^ 21`. -/
theorem reach_encodeRecordX_length_lt_21 (Z : EParams) (E : Party → RecordExtras)
    (ha : ∀ P, (E P).aliceBaseKey.length < 2 ^ 16)
    (hk : ∀ P k, (E P).kyber = some k → k.ciphertext.length < 2 ^ 16)
    {g : GhostState Bytes} (hg : Reach Z.params g) :
    (encodeRecordUnderExtras E g).length < 2 ^ 21 := by
  have hseed := Reach.reach_encodeRecord_length_lt_20 Z hg
  rw [← encodeRecordX_extrasSeed] at hseed
  unfold encodeRecordUnderExtras at hseed ⊢
  simp only [msgField] at hseed ⊢
  have hge := lenField_length_ge' 1 (encStateUnderExtras (seedRecordExtras g.party) g.session)
  have hle := lenField_length_le' 1 (encStateUnderExtras (E g.party) g.session)
  have heq := encStateX_length (E g.party) (seedRecordExtras g.party) g.session
  have hx := extraLen_le (E g.party) g.session.pendingPreKey (ha g.party) (hk g.party)
  omega

/-- `< 2 ^ 32` specialization of `reach_encodeRecordX_length_lt_21`. -/
theorem reach_encodeRecordX_length_lt (Z : EParams) (E : Party → RecordExtras)
    (ha : ∀ P, (E P).aliceBaseKey.length < 2 ^ 16)
    (hk : ∀ P k, (E P).kyber = some k → k.ciphertext.length < 2 ^ 16)
    {g : GhostState Bytes} (hg : Reach Z.params g) :
    (encodeRecordUnderExtras E g).length < 2 ^ 32 :=
  Nat.lt_trans (reach_encodeRecordX_length_lt_21 Z E ha hk hg) (by decide)

/-- `< 2 ^ 32` encoded record length bound on reachable states under `FixedIdRecordExtras`. -/
theorem reach_encodeRecordX_length_lt_of_lite (Z : EParams) (E : Party → RecordExtras)
    (hE : ∀ P, FixedIdRecordExtras (E P)) {g : GhostState Bytes} (hg : Reach Z.params g) :
    (encodeRecordUnderExtras E g).length < 2 ^ 32 :=
  reach_encodeRecordX_length_lt Z E (fun P => (hE P).2.2.2.2.2.2)
    (fun P k hk => ((hE P).2.2.2.2.2.1 k hk).2) hg

end CryptoVerification.E2E.RecordX
