/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.Append
public meta import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.Append
public import LibsignalBinary.Proofs.ProtoCodecRoundTrip
public import LibsignalBinary.Specifications.AsmConstants
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
public import LibsignalBinary.Specifications.LibsignalAesCbc
public import LibsignalBinary.Specifications.LibsignalHmac
public import LibsignalBinary.Specifications.LibsignalProtoCodec
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import LibsignalBinary.Specifications.LibsignalSpqr
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import LibsignalBinary.Specifications.RustHeap.Vec
public import ProofLib

set_option autoImplicit false

/-!
# Prost and SPQR Wire Varint Round-Trips

Length bounds, equivalence, and round-trip theorems for the two 64-bit varint codecs in SPQR V1:
* `Proto.decodeVarint` / `Proto.encodeVarint`, used by prost for protobuf tags, lengths, and
  scalar fields;
* `decode_varint` / `encode_varint`, used by `Message.serialize` and `msg_preamble` for wire
  epochs, message indices, and chunk indices.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Codec

open CryptoVerification.LibsignalSpqrV1 hiding WireType DecodeErr decodeVarint encodeVarint

/-! ## prost varints (`Proto`) -/

private theorem proto_encodeVarintAux_pos (fuel : Nat) (v : BitVec 64) :
    1 ≤ (Proto.encodeVarintAux fuel v).length := by
  cases fuel with
  | zero => simp [Proto.encodeVarintAux]
  | succ k =>
    unfold Proto.encodeVarintAux
    split <;> simp

private theorem proto_encodeVarintAux_le :
    ∀ (fuel : Nat) (v : BitVec 64), 1 ≤ fuel → v.toNat < 2 ^ (7 * fuel) →
      (Proto.encodeVarintAux fuel v).length ≤ fuel
  | 0, _, h1, _ => by omega
  | fuel + 1, v, _, hv => by
    unfold Proto.encodeVarintAux
    by_cases hlt : v < 0x80#64
    · simp [hlt]
    · simp only [hlt, ↓reduceIte, List.length_cons]
      have hv_ge : 128 ≤ v.toNat := by
        change ¬ (v.toNat < 128) at hlt
        omega
      have hfuel1 : 1 ≤ fuel := by
        by_cases hf0 : fuel = 0
        · subst hf0
          omega
        · omega
      have hshift : (v >>> 7).toNat < 2 ^ (7 * fuel) := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        have hpow : 2 ^ (7 * (fuel + 1)) = 128 * 2 ^ (7 * fuel) := by
          rw [Nat.mul_add, Nat.pow_add]
          omega
        rw [hpow] at hv
        omega
      have ih := proto_encodeVarintAux_le fuel (v >>> 7) hfuel1 hshift
      omega

theorem proto_encodeVarint_length (v : BitVec 64) :
    1 ≤ (Proto.encodeVarint v).length ∧ (Proto.encodeVarint v).length ≤ 10 := by
  refine ⟨proto_encodeVarintAux_pos 10 v, proto_encodeVarintAux_le 10 v (by omega) ?_⟩
  have hv : v.toNat < 2 ^ 64 := v.isLt
  omega

private theorem testBit_127_of_lt {m : Nat} (hm : m < 7) : (127 : Nat).testBit m = true := by
  match m, hm with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => decide

private theorem testBit_127_of_ge {m : Nat} (hm : 7 ≤ m) : (127 : Nat).testBit m = false :=
  Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le (by decide : 127 < 2 ^ 7) (Nat.pow_le_pow_right (by omega) hm))

private theorem testBit_128_of_lt {m : Nat} (hm : m < 7) : (128 : Nat).testBit m = false := by
  match m, hm with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => decide

private theorem getLsbD_false_of_toNat_lt {w : Nat} (x : BitVec w) {k m : Nat}
    (hx : x.toNat < 2 ^ k) (hm : k ≤ m) : x.getLsbD m = false := by
  change x.toNat.testBit m = false
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hm))

private theorem getLsbD_0x7f_8 {m : Nat} : (0x7f#8).getLsbD m = decide (m < 7) := by
  change ((0x7f#8).toNat).testBit m = decide (m < 7)
  have h127 : (0x7f#8).toNat = 127 := rfl
  rw [h127]
  by_cases hm : m < 7
  · simp [hm, testBit_127_of_lt hm]
  · have hm' : 7 ≤ m := by omega
    simp [hm, testBit_127_of_ge hm']

private theorem getLsbD_0x7f_64 {m : Nat} : (0x7f#64).getLsbD m = decide (m < 7) := by
  change ((0x7f#64).toNat).testBit m = decide (m < 7)
  have h127 : (0x7f#64).toNat = 127 := rfl
  rw [h127]
  by_cases hm : m < 7
  · simp [hm, testBit_127_of_lt hm]
  · have hm' : 7 ≤ m := by omega
    simp [hm, testBit_127_of_ge hm']

private theorem getLsbD_0x80_8_of_lt {m : Nat} (hm : m < 7) : (0x80#8).getLsbD m = false := by
  change ((0x80#8).toNat).testBit m = false
  exact testBit_128_of_lt hm

private theorem truncate_and_0x7f_of_lt (w : BitVec 64) (hw : w < 0x80#64) :
    (w &&& 0x7f#64).truncate 8 = w.truncate 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.truncate, BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_setWidth,
    getLsbD_0x7f_64]
  by_cases hj7 : j < 7
  · simp [hj, hj7]
  · have hj_eq : j = 7 := by omega
    subst hj_eq
    have hw_lt : w.toNat < 2 ^ 7 := hw
    have hw7 : w.getLsbD 7 = false := getLsbD_false_of_toNat_lt (k := 7) w hw_lt (le_refl 7)
    rw [hw7]
    simp

private theorem cont_byte_eq_proto (w : BitVec 64) :
    0x80#8 ||| (w &&& 0x7f#64).truncate 8 = w.truncate 8 ||| 0x80#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_or, BitVec.truncate, BitVec.getLsbD_setWidth, BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_setWidth, getLsbD_0x7f_64]
  by_cases hj7 : j < 7
  · have h80 := getLsbD_0x80_8_of_lt hj7
    rw [h80]
    simp [hj, hj7]
  · have hj_eq : j = 7 := by omega
    subst hj_eq
    simp

private theorem encodeVarintLoop_eq_aux :
    ∀ (fuel : Nat) (v : BitVec 64), 1 ≤ fuel → v.toNat < 2 ^ (7 * fuel) →
      encodeVarintLoop fuel v = Proto.encodeVarintAux fuel v
  | 0, _, h1, _ => by omega
  | fuel + 1, v, _, hv => by
    unfold encodeVarintLoop Proto.encodeVarintAux
    by_cases hlt : v < 0x80#64
    · simp [hlt, truncate_and_0x7f_of_lt v hlt]
    · simp only [hlt, ↓reduceIte, cont_byte_eq_proto]
      congr 1
      have hv_ge : 128 ≤ v.toNat := by
        change ¬ (v.toNat < 128) at hlt
        omega
      have hfuel1 : 1 ≤ fuel := by
        by_cases hf0 : fuel = 0
        · subst hf0
          omega
        · omega
      have hshift : (v >>> 7).toNat < 2 ^ (7 * fuel) := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        have hpow : 2 ^ (7 * (fuel + 1)) = 128 * 2 ^ (7 * fuel) := by
          rw [Nat.mul_add, Nat.pow_add]
          omega
        rw [hpow] at hv
        omega
      exact encodeVarintLoop_eq_aux fuel (v >>> 7) hfuel1 hshift

/-- The spqr encoder writes the same bytes as prost. -/
theorem encodeVarintLoop_eq_proto (v : BitVec 64) :
    encodeVarintLoop 10 v = Proto.encodeVarint v := by
  apply encodeVarintLoop_eq_aux 10 v (by omega)
  have hv : v.toNat < 2 ^ 64 := v.isLt
  omega

private theorem term_byte_and_0x80 (w : BitVec 64) :
    ((w &&& 0x7f#64).truncate 8) &&& 0x80#8 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_and, BitVec.truncate, BitVec.getLsbD_setWidth, BitVec.getLsbD_and,
    getLsbD_0x7f_64]
  by_cases hj7 : j < 7
  · have h80 := getLsbD_0x80_8_of_lt hj7
    rw [h80]
    simp
  · have hj_eq : j = 7 := by omega
    subst hj_eq
    simp

private theorem cont_byte_and_0x80_ne (w : BitVec 64) :
    (0x80#8 ||| (w &&& 0x7f#64).truncate 8) &&& 0x80#8 ≠ 0#8 := by
  intro heq
  have h7 := congrArg (fun x => x.getLsbD 7) heq
  rw [BitVec.getLsbD_and, BitVec.getLsbD_or] at h7
  simp at h7

private theorem ushiftRight_63_lt_0x80 (v : BitVec 64) : v >>> 63 < 0x80#64 := by
  change (v >>> 63).toNat < 128
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hv : v.toNat < 2 ^ 64 := v.isLt
  omega

private theorem ushiftRight_ushiftRight_seven (v : BitVec 64) (i : Nat) :
    (v >>> (7 * i)) >>> 7 = v >>> (7 * (i + 1)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j _
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  congr 1
  omega

private theorem decodeVarintLoop_encodeVarintLoop :
    ∀ (k i : Nat) (v out : BitVec 64) (rest : Bytes),
      i + k = 10 →
      1 ≤ k →
      (∀ j < 64, out.getLsbD j = (decide (j < 7 * i) && v.getLsbD j)) →
      decodeVarintLoop i out (encodeVarintLoop k (v >>> (7 * i)) ++ rest) = some (v, rest)
  | 0, _, _, _, _, _, hk, _ => by omega
  | k + 1, i, v, out, rest, hik, _, hout => by
    unfold encodeVarintLoop
    by_cases hw : v >>> (7 * i) < 0x80#64
    · simp only [hw, ↓reduceIte, List.singleton_append]
      unfold decodeVarintLoop
      simp only [term_byte_and_0x80, ↓reduceIte]
      congr 2
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      rw [BitVec.getLsbD_or, hout j hj, BitVec.getLsbD_shiftLeft, BitVec.zeroExtend,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.truncate, BitVec.getLsbD_setWidth,
        BitVec.getLsbD_and, getLsbD_0x7f_8, getLsbD_0x7f_64, BitVec.getLsbD_ushiftRight]
      by_cases h1 : j < 7 * i
      · simp [hj, h1]
      · by_cases h2 : j < 7 * i + 7
        · have hm7 : j - 7 * i < 7 := by omega
          have hm8 : j - 7 * i < 8 := by omega
          have hm64 : j - 7 * i < 64 := by omega
          have hadd : 7 * i + (j - 7 * i) = j := by omega
          simp [hj, h1, hm7, hm8, hm64, hadd]
        · have hm7 : ¬ (j - 7 * i < 7) := by omega
          have hw_nat : (v >>> (7 * i)).toNat < 2 ^ 7 := hw
          have hvj : v.getLsbD j = false := by
            have hadd : j = 7 * i + (j - 7 * i) := by omega
            rw [hadd, ← BitVec.getLsbD_ushiftRight]
            exact getLsbD_false_of_toNat_lt (k := 7) (v >>> (7 * i)) hw_nat (by omega)
          rw [hvj]
          simp [hj, h1, hm7]
    · simp only [hw, ↓reduceIte, List.cons_append]
      have hk1 : 1 ≤ k := by
        by_cases hk0 : k = 0
        · subst hk0
          have hi9 : i = 9 := by omega
          subst hi9
          have h63 : 7 * 9 = 63 := rfl
          rw [h63] at hw
          exact False.elim (hw (ushiftRight_63_lt_0x80 v))
        · omega
      have hi10 : i + 1 ≠ MAX_VARINT_BYTES_LEN := by
        unfold MAX_VARINT_BYTES_LEN
        omega
      unfold decodeVarintLoop
      simp only [cont_byte_and_0x80_ne, ↓reduceIte, hi10]
      rw [ushiftRight_ushiftRight_seven]
      apply decodeVarintLoop_encodeVarintLoop k (i + 1) v _ rest (by omega) hk1
      intro j hj
      rw [BitVec.getLsbD_or, hout j hj, BitVec.getLsbD_shiftLeft, BitVec.zeroExtend,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.truncate,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_and, getLsbD_0x7f_8, getLsbD_0x7f_64,
        BitVec.getLsbD_ushiftRight]
      by_cases h1 : j < 7 * i
      · have h1' : j < 7 * (i + 1) := by omega
        simp [hj, h1, h1']
      · by_cases h2 : j < 7 * (i + 1)
        · have hm7 : j - 7 * i < 7 := by omega
          have hm8 : j - 7 * i < 8 := by omega
          have hm64 : j - 7 * i < 64 := by omega
          have h80 := getLsbD_0x80_8_of_lt hm7
          have hadd : 7 * i + (j - 7 * i) = j := by omega
          rw [h80]
          simp [hj, h1, h2, hm7, hm8, hm64, hadd]
        · have hm7 : ¬ (j - 7 * i < 7) := by omega
          simp [hj, h1, h2, hm7]

/-- spqr wire varint round trip, with any trailing bytes (used for the epoch, index and chunk
index of `Message.serialize`). -/
theorem decode_varint_encode_varint (v : BitVec 64) (rest : Bytes) :
    decode_varint (encode_varint v [] ++ rest) = .ok (v, rest) := by
  unfold decode_varint encode_varint MAX_VARINT_BYTES_LEN
  simp only [List.nil_append]
  have hv0 : v = v >>> (7 * 0) := by simp
  have hloop : decodeVarintLoop 0 0#64 (encodeVarintLoop 10 v ++ rest) = some (v, rest) := by
    conv_lhs => rw [hv0]
    apply decodeVarintLoop_encodeVarintLoop 10 0 v 0#64 rest rfl (by omega)
    intro j _
    simp
  rw [hloop]



theorem proto_encodeVarint_of_lt (v : BitVec 64) (h : v < 0x80#64) :
    Proto.encodeVarint v = [v.truncate 8] := by
  simp [Proto.encodeVarint, Proto.encodeVarintAux, h]


end CryptoVerification.SpqrV1Sync.Codec
