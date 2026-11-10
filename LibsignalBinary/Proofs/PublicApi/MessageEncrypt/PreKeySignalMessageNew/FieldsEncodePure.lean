/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.Split

/-!
# Pure Prefix Encodings and `Vec` Buffer Helpers for `PreKeySignalMessage::new`

Relates concrete `encodeVarint` output to `Prost.varint`, defines the cumulative serialized prefixes
`serPrefix0..serPrefix8` after each protobuf tag, and provides `vecU8Buf` slice-splitting helpers.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split

/-! ## Equivalence of `encodeVarint` and `Prost.varint` -/

private theorem bv8_contByte_eq_ofNat :
    ∀ b : BitVec 8, (b &&& 0x7F#8) ||| 0x80#8 = BitVec.ofNat 8 (b.toNat % 128 + 128) := by
  decide

private theorem contByte64_eq_ofNat (v : BitVec 64) :
    ((v &&& 0x7F) ||| 0x80).setWidth 8 = BitVec.ofNat 8 (v.toNat % 128 + 128) := by
  have h1 : ((v &&& 0x7F) ||| 0x80).setWidth 8 = (v.setWidth 8 &&& 0x7F#8) ||| 0x80#8 := by
    change ((v &&& 0x7F#64) ||| 0x80#64).setWidth 8 = (v.setWidth 8 &&& 0x7F#8) ||| 0x80#8
    simp [BitVec.setWidth_or, BitVec.setWidth_and]
  have h2 : (v.setWidth 8).toNat % 128 = v.toNat % 128 := by
    rw [BitVec.toNat_setWidth]
    omega
  rw [h1, bv8_contByte_eq_ofNat (v.setWidth 8), h2]

private theorem encodeVarintAux_eq_prost_varint :
    ∀ (k : Nat) (v : BitVec 64), v.toNat < 128 ^ (k + 1) →
      encodeVarintAux (k + 1) v = LibsignalSessionApi.Prost.varint v.toNat
  | 0, v, hlt => by
    have hlt128 : v.toNat < 128 := by simpa using hlt
    rw [encodeVarintAux, LibsignalSessionApi.Prost.varint]
    simp [hlt128]
  | k + 1, v, hlt => by
    by_cases hlt128 : v.toNat < 128
    · rw [encodeVarintAux, LibsignalSessionApi.Prost.varint]
      simp [hlt128]
    · rw [encodeVarintAux, LibsignalSessionApi.Prost.varint]
      simp only [hlt128, ↓reduceIte, ↓reduceDIte]
      have hdiv : (v >>> 7).toNat = v.toNat / 128 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have hdiv_lt : (v >>> 7).toNat < 128 ^ (k + 1) := by
        rw [hdiv]
        rw [Nat.pow_succ, Nat.mul_comm] at hlt
        exact Nat.div_lt_of_lt_mul hlt
      rw [contByte64_eq_ofNat, encodeVarintAux_eq_prost_varint k (v >>> 7) hdiv_lt, hdiv]

theorem encodeVarint_eq_prost_varint (v : BitVec 64) :
    encodeVarint v = LibsignalSessionApi.Prost.varint v.toNat := by
  apply encodeVarintAux_eq_prost_varint 9 v
  have := v.isLt
  omega

theorem prost_varint_eq_encodeVarint (v : BitVec 64) :
    LibsignalSessionApi.Prost.varint v.toNat = encodeVarint v :=
  (encodeVarint_eq_prost_varint v).symm

theorem prost_varint_length_eq_encodeVarint (n : Nat) (hn : n < 2 ^ 64) :
    LibsignalSessionApi.Prost.varint n = encodeVarint (BitVec.ofNat 64 n) := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  rw [encodeVarint_eq_prost_varint, htoNat]

/-! ## Cumulative Serialized Prefixes `serPrefix0..serPrefix8` -/

def serPrefix0 (x : PreKeyMsgNewCall) : List (BitVec 8) :=
  [versionByte x.ver]

def serPrefix1 (x : PreKeyMsgNewCall) : List (BitVec 8) :=
  serPrefix0 x ++ LibsignalSessionApi.Prost.uint32Field 1 x.preKeyId

def serPrefix2 (x : PreKeyMsgNewCall) : List (BitVec 8) :=
  serPrefix1 x ++ LibsignalSessionApi.Prost.bytesField 2 (some x.baseKey.serialize)

def serPrefix3 (x : PreKeyMsgNewCall) : List (BitVec 8) :=
  serPrefix2 x ++ LibsignalSessionApi.Prost.bytesField 3 (some x.ik.serialize)

def serPrefix4 (x : PreKeyMsgNewCall) : List (BitVec 8) :=
  serPrefix3 x ++ LibsignalSessionApi.Prost.bytesField 4 (some x.msg.serialized)

def serPrefix5 (x : PreKeyMsgNewCall) : List (BitVec 8) :=
  serPrefix4 x ++ LibsignalSessionApi.Prost.uint32Field 5 (some x.regId)

def serPrefix6 (x : PreKeyMsgNewCall) : List (BitVec 8) :=
  serPrefix5 x ++ LibsignalSessionApi.Prost.uint32Field 6 (some x.spk)

def serPrefix7 (x : PreKeyMsgNewCall) : List (BitVec 8) :=
  serPrefix6 x ++ LibsignalSessionApi.Prost.uint32Field 7 (x.kp.map (·.preKeyId))

def serPrefix8 (x : PreKeyMsgNewCall) : List (BitVec 8) :=
  serPrefix7 x ++ LibsignalSessionApi.Prost.bytesField 8 (x.kp.map (·.ciphertext))

theorem serPrefix8_eq_model_serialized (x : PreKeyMsgNewCall) :
    serPrefix8 x = x.model.serialized := by
  simp [serPrefix8, serPrefix7, serPrefix6, serPrefix5, serPrefix4,
    serPrefix3, serPrefix2, serPrefix1, serPrefix0,
    model_serialized_eq, PreKeyMsgNewCall.protoMsg, ProtoPreKeySignalMessage.encode,
    List.append_assoc]

theorem serPrefix_lengths_le (x : PreKeyMsgNewCall) :
    (serPrefix0 x).length = 1 ∧
    (serPrefix0 x).length ≤ (serPrefix1 x).length ∧
    (serPrefix1 x).length ≤ (serPrefix2 x).length ∧
    (serPrefix2 x).length ≤ (serPrefix3 x).length ∧
    (serPrefix3 x).length ≤ (serPrefix4 x).length ∧
    (serPrefix4 x).length ≤ (serPrefix5 x).length ∧
    (serPrefix5 x).length ≤ (serPrefix6 x).length ∧
    (serPrefix6 x).length ≤ (serPrefix7 x).length ∧
    (serPrefix7 x).length ≤ (serPrefix8 x).length ∧
    (serPrefix8 x).length = x.model.serialized.length := by
  refine ⟨by simp [serPrefix0], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [serPrefix1]
  · simp [serPrefix2]
  · simp [serPrefix3]
  · simp [serPrefix4]
  · simp [serPrefix5]
  · simp [serPrefix6]
  · simp [serPrefix7]
  · simp [serPrefix8]
  · rw [serPrefix8_eq_model_serialized]

/-! ## Concrete Field-Encoding Unfoldings -/

theorem prost_key_1_0 : LibsignalSessionApi.Prost.key 1 0 = [0x08#8] := by
  rw [LibsignalSessionApi.Prost.key, prost_varint_length_eq_encodeVarint _ (by decide)]; decide
theorem prost_key_2_2 : LibsignalSessionApi.Prost.key 2 2 = [0x12#8] := by
  rw [LibsignalSessionApi.Prost.key, prost_varint_length_eq_encodeVarint _ (by decide)]; decide
theorem prost_key_3_2 : LibsignalSessionApi.Prost.key 3 2 = [0x1a#8] := by
  rw [LibsignalSessionApi.Prost.key, prost_varint_length_eq_encodeVarint _ (by decide)]; decide
theorem prost_key_4_2 : LibsignalSessionApi.Prost.key 4 2 = [0x22#8] := by
  rw [LibsignalSessionApi.Prost.key, prost_varint_length_eq_encodeVarint _ (by decide)]; decide
theorem prost_key_5_0 : LibsignalSessionApi.Prost.key 5 0 = [0x28#8] := by
  rw [LibsignalSessionApi.Prost.key, prost_varint_length_eq_encodeVarint _ (by decide)]; decide
theorem prost_key_6_0 : LibsignalSessionApi.Prost.key 6 0 = [0x30#8] := by
  rw [LibsignalSessionApi.Prost.key, prost_varint_length_eq_encodeVarint _ (by decide)]; decide
theorem prost_key_7_0 : LibsignalSessionApi.Prost.key 7 0 = [0x38#8] := by
  rw [LibsignalSessionApi.Prost.key, prost_varint_length_eq_encodeVarint _ (by decide)]; decide
theorem prost_key_8_2 : LibsignalSessionApi.Prost.key 8 2 = [0x42#8] := by
  rw [LibsignalSessionApi.Prost.key, prost_varint_length_eq_encodeVarint _ (by decide)]; decide
theorem encodeVarint_33 : encodeVarint 33#64 = [0x21#8] := by decide

theorem prost_uint32Field_some (tag : Nat) (v : BitVec 32) :
    LibsignalSessionApi.Prost.uint32Field tag (some v) =
      LibsignalSessionApi.Prost.key tag 0 ++ encodeVarint (v.zeroExtend 64) := by
  simp only [LibsignalSessionApi.Prost.uint32Field, encodeVarint_eq_prost_varint,
    BitVec.toNat_setWidth, Nat.mod_eq_of_lt (lt_trans v.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem prost_bytesField_some (tag : Nat) (bs : List (BitVec 8)) (hlen : bs.length < 2 ^ 64) :
    LibsignalSessionApi.Prost.bytesField tag (some bs) =
      LibsignalSessionApi.Prost.key tag 2 ++ encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  simp only [LibsignalSessionApi.Prost.bytesField, prost_varint_length_eq_encodeVarint bs.length hlen]

/-! ## `vecU8Buf` Slice Helpers -/

def vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_header_sep_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs = vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8At vecU8Buf
  ac_rfl

theorem vecU8Buf_bounds {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hm : m ⊨ vecU8Buf A cap ptr bs ∗ R) :
    bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 := by
  unfold vecU8Buf at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact hm.1

def vecRest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length + 1 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 (bs.length + 1)) (cap.toNat - (bs.length + 1))

theorem memRegion_one_eq (a : BitVec 64) : memRegion a 1 = ∃∗ y : BitVec 8, a ↦₈ y :=
  IsBlock.eq (IsBlock.memRegion a 1)
    (IsBlock.sepExists fun v => IsBlock.pointsTo8 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem vecU8Buf_eq_open_one (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat) :
    vecU8Buf A cap ptr bs =
      ∃∗ y : BitVec 8, ((ptr + BitVec.ofNat 64 bs.length) ↦₈ y) ∗ vecRest A cap ptr bs := by
  have hne : cap ≠ 0 := by
    intro h0; subst h0; simp at hlt
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) =
      (bs.length + 1 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) := by
    apply propext; constructor <;> (intro ⟨_, h2, h3⟩; exact ⟨by omega, h2, h3⟩)
  unfold vecU8Buf vecRest
  simp only [hne, ↓reduceIte, hpure]
  have hsplit := memRegion_split (ptr + BitVec.ofNat 64 bs.length) 1 (cap.toNat - (bs.length + 1)) (by omega)
  rw [show 1 + (cap.toNat - (bs.length + 1)) = cap.toNat - bs.length by omega,
    BitVec.add_assoc, ← BitVec.ofNat_add, memRegion_one_eq] at hsplit
  rw [hsplit]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  congr 1; funext y
  ac_rfl

theorem pointsToBytes_snoc_eq (ptr : BitVec 64) (bs : List (BitVec 8)) (byte : BitVec 8) :
    (ptr ↦ₛ bs) ∗ ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte) = ptr ↦ₛ (bs ++ [byte]) := by
  rw [pointsToBytes_append, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem vecU8Buf_snoc_eq (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (byte : BitVec 8) (hlt : bs.length < cap.toNat) :
    ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte) ∗ vecRest A cap ptr bs =
      vecU8Buf A cap ptr (bs ++ [byte]) := by
  have hne : cap ≠ 0 := by
    intro h0; subst h0; simp at hlt
  unfold vecU8Buf vecRest
  simp only [hne, ↓reduceIte]
  have h1 : ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte) ∗
      (⌜bs.length + 1 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + 1)) (cap.toNat - (bs.length + 1))) =
      ⌜bs.length + 1 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗ ((ptr ↦ₛ bs) ∗ ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte)) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + 1)) (cap.toNat - (bs.length + 1)) := by
    ac_rfl
  rw [h1, pointsToBytes_snoc_eq]
  simp only [List.length_append, List.length_singleton]

def vecSliceRest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) (n : Nat) : SepProp :=
  ⌜bs.length + n ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 (bs.length + n)) (cap.toNat - (bs.length + n))

theorem vecU8Buf_eq_open_slice (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (n : Nat) (hle : bs.length + n ≤ cap.toNat) (hcap_pos : 0 < cap.toNat) :
    vecU8Buf A cap ptr bs =
      memRegion (ptr + BitVec.ofNat 64 bs.length) n ∗ vecSliceRest A cap ptr bs n := by
  have hne : cap ≠ 0 := by
    intro h0; subst h0; simp at hcap_pos
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) =
      (bs.length + n ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) := by
    apply propext; constructor <;> (intro ⟨_, h2, h3⟩; exact ⟨by omega, h2, h3⟩)
  unfold vecU8Buf vecSliceRest
  simp only [hne, ↓reduceIte, hpure]
  have hsplit := memRegion_split (ptr + BitVec.ofNat 64 bs.length) n (cap.toNat - (bs.length + n)) (by omega)
  rw [show n + (cap.toNat - (bs.length + n)) = cap.toNat - bs.length by omega,
    BitVec.add_assoc, ← BitVec.ofNat_add] at hsplit
  rw [hsplit]
  ac_rfl

theorem vecU8Buf_append_eq (A : RustAlloc) (cap ptr : BitVec 64) (bs payload : List (BitVec 8))
    (hcap_pos : 0 < cap.toNat) :
    ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ payload) ∗ vecSliceRest A cap ptr bs payload.length =
      vecU8Buf A cap ptr (bs ++ payload) := by
  have hne : cap ≠ 0 := by
    intro h0; subst h0; simp at hcap_pos
  unfold vecU8Buf vecSliceRest
  simp only [hne, ↓reduceIte]
  have h1 : ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ payload) ∗
      (⌜bs.length + payload.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + payload.length))
          (cap.toNat - (bs.length + payload.length))) =
      ⌜bs.length + payload.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗ ((ptr ↦ₛ bs) ∗ ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ payload)) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + payload.length))
          (cap.toNat - (bs.length + payload.length)) := by
    ac_rfl
  rw [h1, ← pointsToBytes_append, List.length_append]

theorem vecU8AtLen_eq_header_sep_buf (A : RustAlloc) (v cap ptr lenW : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8AtLen A v cap ptr lenW bs = vecHeader v cap ptr lenW ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8AtLen vecU8Buf
  ac_rfl

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
