/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common

/-!
# Pure arithmetic and layout lemmas for `Chain::encoded_len` (`0x26aa0`)
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Hardware varint length normalization -/

private theorem or_one_ne_zero (x : BitVec 64) : x ||| 1#64 ≠ 0#64 := by
  intro h
  have h0 : (x ||| 1#64).getLsbD 0 = (0#64 : BitVec 64).getLsbD 0 :=
    congrArg (fun v => v.getLsbD 0) h
  simp at h0

private theorem or_one_div_two (x : BitVec 64) :
    (x ||| 1#64).toNat / 2 = x.toNat / 2 := by
  have h : (x ||| 1#64) >>> 1 = x >>> 1 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp [BitVec.getLsbD_one]
  have h1 : ((x ||| 1#64) >>> 1).toNat = (x >>> 1).toNat := congrArg BitVec.toNat h
  simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using h1

private theorem clz_or_one_bounds (x : BitVec 64) :
    let c := (x ||| 1#64).clz.toNat
    c ≤ 63 ∧ 2 ^ (63 - c) ≤ (x ||| 1#64).toNat ∧ (x ||| 1#64).toNat < 2 ^ (64 - c) := by
  intro c
  exact ⟨ProofLib.clz_or_one_toNat_le x,
    BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by decide : 0 < 64) (or_one_ne_zero x),
    BitVec.toNat_lt_two_pow_sub_clz⟩

private theorem toNat_bounds_of_clz (x : BitVec 64) {k1 k2 : Nat}
    (hk1 : 1 ≤ k1)
    (hlo_b : k1 ≤ 63 - (x ||| 1#64).clz.toNat)
    (hhi_b : 64 - (x ||| 1#64).clz.toNat ≤ k2) :
    2 ^ k1 ≤ x.toNat ∧ x.toNat < 2 ^ k2 := by
  obtain ⟨hc, hlo, hhi⟩ := clz_or_one_bounds x
  have hpow1 : 2 ^ k1 ≤ 2 ^ (63 - (x ||| 1#64).clz.toNat) :=
    Nat.pow_le_pow_right (by decide) hlo_b
  have hpow2 : 2 ^ (64 - (x ||| 1#64).clz.toNat) ≤ 2 ^ k2 :=
    Nat.pow_le_pow_right (by decide) hhi_b
  have hy_lo : 2 ^ k1 ≤ (x ||| 1#64).toNat := Nat.le_trans hpow1 hlo
  have hy_hi : (x ||| 1#64).toNat < 2 ^ k2 := Nat.lt_of_lt_of_le hhi hpow2
  have hdiv := or_one_div_two x
  have hk2 : 1 ≤ k2 := by omega
  have heven1 : 2 ^ k1 = 2 * 2 ^ (k1 - 1) := by
    conv => lhs; rw [← Nat.sub_add_cancel hk1, Nat.pow_succ, Nat.mul_comm]
  have heven2 : 2 ^ k2 = 2 * 2 ^ (k2 - 1) := by
    conv => lhs; rw [← Nat.sub_add_cancel hk2, Nat.pow_succ, Nat.mul_comm]
  omega

private theorem clz_or_one_bv_eq (x : BitVec 64) :
    ((((x ||| 1#64).clz ^^^ 63#64) + (((x ||| 1#64).clz ^^^ 63#64) <<< 3)) + 73#64) >>> 6 =
      ((63#64 - (x ||| 1#64).clz) * 9#64 + 73#64) / 64#64 := by
  have hle : (x ||| 1#64).clz ≤ 63#64 := ProofLib.clz_or_one_le x
  generalize (x ||| 1#64).clz = c at hle ⊢
  have hc : c = (c.truncate 8).zeroExtend 64 := by bv_bits
  have hc8 : c.truncate 8 ≤ 63#8 := by bv_bits
  rw [hc]
  generalize c.truncate 8 = b at hc8 ⊢
  revert b hc8; decide

private theorem hwVarintLen_eq_ofNat_div (x : BitVec 64) :
    ((((x ||| 1#64).clz ^^^ 63#64) + (((x ||| 1#64).clz ^^^ 63#64) <<< 3)) + 73#64) >>> 6 =
      BitVec.ofNat 64 (((63 - (x ||| 1#64).clz.toNat) * 9 + 73) / 64) := by
  rw [clz_or_one_bv_eq]
  have hle := ProofLib.clz_or_one_toNat_le x
  apply BitVec.eq_of_toNat_eq
  generalize (x ||| 1#64).clz = c at hle ⊢
  have h1 : ((63#64 - c) * 9#64 + 73#64).toNat = (63 - c.toNat) * 9 + 73 := by
    have hsub : (63#64 - c).toNat = 63 - c.toNat := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
    simp only [BitVec.toNat_add, BitVec.toNat_mul, hsub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  simp only [BitVec.toNat_udiv, h1, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

private theorem lt_128_iff (x : BitVec 64) :
    (x < 0x80#64) ↔ x.toNat < 2 ^ 7 := by
  simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]

private theorem toNat_shr_lt_128_iff (x : BitVec 64) (k : Nat) :
    ((x >>> k).toNat < 2 ^ 7) ↔ x.toNat < 2 ^ (7 + k) := by
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_add]
  exact Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)

private theorem hwVarintLen_eq_varintLenBV' (x : BitVec 64) :
    ((((x ||| 1#64).clz ^^^ 0x3f#64) + (((x ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
      varintLenBV x := by
  rw [hwVarintLen_eq_ofNat_div]
  unfold varintLenBV
  simp only [lt_128_iff, toNat_shr_lt_128_iff, Nat.reduceAdd]
  obtain ⟨hc, hlo_y, hhi_y⟩ := clz_or_one_bounds x
  set c := (x ||| 1#64).clz.toNat
  let b := 63 - c
  if hb1 : b < 7 then
    have hpow : 2 ^ (64 - c) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have hy : (x ||| 1#64).toNat < 2 ^ 7 := Nat.lt_of_lt_of_le hhi_y hpow
    have hdiv := or_one_div_two x
    have hx : x.toNat < 2 ^ 7 := by omega
    have hval : ((63 - c) * 9 + 73) / 64 = 1 := by omega
    simp only [hx, ↓reduceIte, hval]
  else if hb2 : b < 14 then
    have ⟨hx1, hx2⟩ := toNat_bounds_of_clz x (k1 := 7) (k2 := 14) (by decide) (by omega) (by omega)
    have hval : ((63 - c) * 9 + 73) / 64 = 2 := by omega
    simp only [show ¬(x.toNat < 2 ^ 7) by omega, hx2, ↓reduceIte, hval]
  else if hb3 : b < 21 then
    have ⟨hx1, hx2⟩ := toNat_bounds_of_clz x (k1 := 14) (k2 := 21) (by decide) (by omega) (by omega)
    have hval : ((63 - c) * 9 + 73) / 64 = 3 := by omega
    simp only [show ¬(x.toNat < 2 ^ 7) by omega, show ¬(x.toNat < 2 ^ 14) by omega,
      hx2, ↓reduceIte, hval]
  else if hb4 : b < 28 then
    have ⟨hx1, hx2⟩ := toNat_bounds_of_clz x (k1 := 21) (k2 := 28) (by decide) (by omega) (by omega)
    have hval : ((63 - c) * 9 + 73) / 64 = 4 := by omega
    simp only [show ¬(x.toNat < 2 ^ 7) by omega, show ¬(x.toNat < 2 ^ 14) by omega,
      show ¬(x.toNat < 2 ^ 21) by omega, hx2, ↓reduceIte, hval]
  else if hb5 : b < 35 then
    have ⟨hx1, hx2⟩ := toNat_bounds_of_clz x (k1 := 28) (k2 := 35) (by decide) (by omega) (by omega)
    have hval : ((63 - c) * 9 + 73) / 64 = 5 := by omega
    simp only [show ¬(x.toNat < 2 ^ 7) by omega, show ¬(x.toNat < 2 ^ 14) by omega,
      show ¬(x.toNat < 2 ^ 21) by omega, show ¬(x.toNat < 2 ^ 28) by omega,
      hx2, ↓reduceIte, hval]
  else if hb6 : b < 42 then
    have ⟨hx1, hx2⟩ := toNat_bounds_of_clz x (k1 := 35) (k2 := 42) (by decide) (by omega) (by omega)
    have hval : ((63 - c) * 9 + 73) / 64 = 6 := by omega
    simp only [show ¬(x.toNat < 2 ^ 7) by omega, show ¬(x.toNat < 2 ^ 14) by omega,
      show ¬(x.toNat < 2 ^ 21) by omega, show ¬(x.toNat < 2 ^ 28) by omega,
      show ¬(x.toNat < 2 ^ 35) by omega, hx2, ↓reduceIte, hval]
  else if hb7 : b < 49 then
    have ⟨hx1, hx2⟩ := toNat_bounds_of_clz x (k1 := 42) (k2 := 49) (by decide) (by omega) (by omega)
    have hval : ((63 - c) * 9 + 73) / 64 = 7 := by omega
    simp only [show ¬(x.toNat < 2 ^ 7) by omega, show ¬(x.toNat < 2 ^ 14) by omega,
      show ¬(x.toNat < 2 ^ 21) by omega, show ¬(x.toNat < 2 ^ 28) by omega,
      show ¬(x.toNat < 2 ^ 35) by omega, show ¬(x.toNat < 2 ^ 42) by omega,
      hx2, ↓reduceIte, hval]
  else if hb8 : b < 56 then
    have ⟨hx1, hx2⟩ := toNat_bounds_of_clz x (k1 := 49) (k2 := 56) (by decide) (by omega) (by omega)
    have hval : ((63 - c) * 9 + 73) / 64 = 8 := by omega
    simp only [show ¬(x.toNat < 2 ^ 7) by omega, show ¬(x.toNat < 2 ^ 14) by omega,
      show ¬(x.toNat < 2 ^ 21) by omega, show ¬(x.toNat < 2 ^ 28) by omega,
      show ¬(x.toNat < 2 ^ 35) by omega, show ¬(x.toNat < 2 ^ 42) by omega,
      show ¬(x.toNat < 2 ^ 49) by omega, hx2, ↓reduceIte, hval]
  else if hb9 : b < 63 then
    have ⟨hx1, hx2⟩ := toNat_bounds_of_clz x (k1 := 56) (k2 := 63) (by decide) (by omega) (by omega)
    have hval : ((63 - c) * 9 + 73) / 64 = 9 := by omega
    simp only [show ¬(x.toNat < 2 ^ 7) by omega, show ¬(x.toNat < 2 ^ 14) by omega,
      show ¬(x.toNat < 2 ^ 21) by omega, show ¬(x.toNat < 2 ^ 28) by omega,
      show ¬(x.toNat < 2 ^ 35) by omega, show ¬(x.toNat < 2 ^ 42) by omega,
      show ¬(x.toNat < 2 ^ 49) by omega, show ¬(x.toNat < 2 ^ 56) by omega,
      hx2, ↓reduceIte, hval]
  else
    have ⟨hx1, _⟩ := toNat_bounds_of_clz x (k1 := 63) (k2 := 64) (by decide) (by omega) (by omega)
    have hval : ((63 - c) * 9 + 73) / 64 = 10 := by omega
    simp only [show ¬(x.toNat < 2 ^ 7) by omega, show ¬(x.toNat < 2 ^ 14) by omega,
      show ¬(x.toNat < 2 ^ 21) by omega, show ¬(x.toNat < 2 ^ 28) by omega,
      show ¬(x.toNat < 2 ^ 35) by omega, show ¬(x.toNat < 2 ^ 42) by omega,
      show ¬(x.toNat < 2 ^ 49) by omega, show ¬(x.toNat < 2 ^ 56) by omega,
      show ¬(x.toNat < 2 ^ 63) by omega, ↓reduceIte, hval]

private theorem ushiftRight_add' (w : BitVec 64) (a b : Nat) :
    (w >>> a) >>> b = w >>> (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    ← Nat.pow_add]

private theorem toNat_lt_128_eq' (w : BitVec 64) : (w.toNat < 128) = (w < 0x80#64) := rfl

theorem varintLenBV_eq_encodeVarint_length' (v : BitVec 64) :
    varintLenBV v = BitVec.ofNat 64 (encodeVarint v).length := by
  unfold varintLenBV encodeVarint
  dsimp only [encodeVarintAux]
  simp only [ushiftRight_add', Nat.reduceAdd, toNat_lt_128_eq']
  by_cases h0 : v < 0x80#64 <;> simp only [h0, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  by_cases h1 : v >>> 7 < 0x80#64 <;> simp only [h1, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h2 : v >>> 14 < 0x80#64 <;> simp only [h2, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h3 : v >>> 21 < 0x80#64 <;> simp only [h3, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h4 : v >>> 28 < 0x80#64 <;> simp only [h4, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h5 : v >>> 35 < 0x80#64 <;> simp only [h5, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h6 : v >>> 42 < 0x80#64 <;> simp only [h6, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h7 : v >>> 49 < 0x80#64 <;> simp only [h7, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h8 : v >>> 56 < 0x80#64 <;> simp only [h8, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  have h9 : v >>> 63 < 0x80#64 := by bv_omega
  simp only [h9, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]

@[simp, arm64_norm]
theorem hwVarintLen_eq_encodeVarint_length' (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 0x3f#64) + (((v ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
      BitVec.ofNat 64 (encodeVarint v).length := by
  rw [hwVarintLen_eq_varintLenBV', varintLenBV_eq_encodeVarint_length']

@[simp, arm64_norm]
theorem hwVarintLen_bvShift_eq_encodeVarint_length' (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 63#64) + (((v ||| 1#64).clz ^^^ 63#64) <<< 3#64)) + 73#64) >>> 6#64 =
      BitVec.ofNat 64 (encodeVarint v).length :=
  hwVarintLen_eq_encodeVarint_length' v

@[simp, arm64_norm]
theorem hwVarintLen_mix1_eq_encodeVarint_length (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 63#64) + (((v ||| 1#64).clz ^^^ 63#64) <<< 3#64)) + 73#64) >>> 6 =
      BitVec.ofNat 64 (encodeVarint v).length :=
  hwVarintLen_eq_encodeVarint_length' v

@[simp, arm64_norm]
theorem hwVarintLen_mix2_eq_encodeVarint_length (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 0x3f#64) + (((v ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6#64 =
      BitVec.ofNat 64 (encodeVarint v).length :=
  hwVarintLen_eq_encodeVarint_length' v

/-! ## Unsigned overflow helpers -/

theorem ule_ofNat_add_left_of_lt {a b : Nat} (h : a + b < 2 ^ 64) :
    BitVec.ule (BitVec.ofNat 64 a) (BitVec.ofNat 64 (a + b)) = true := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem ult_ofNat_add_left_of_lt {a b : Nat} (h : a + b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 (a + b)) (BitVec.ofNat 64 a) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## Encoded length decomposition of `encChainMem` -/

/-- Encoded byte length of a `message_keys` element inside `Chain::encoded_len`, excluding the
1-byte field tag added once after the loop. -/
def mkBodyLen (mk : MessageKeyGenerator) : Nat :=
  (encMessageKey mk).length + (encodeVarint (BitVec.ofNat 64 (encMessageKey mk).length)).length

/-- Sum of `mkBodyLen` over a list of `MessageKeyGenerator`s. -/
def mksBodyLen : List MessageKeyGenerator → Nat
  | [] => 0
  | mk :: rest => mkBodyLen mk + mksBodyLen rest

theorem lenField4_encMessageKey_length (mk : MessageKeyGenerator) :
    (lenField 4 (encMessageKey mk)).length = 1 + mkBodyLen mk := by
  simp only [lenField, mkBodyLen, List.length_append]
  have hkey : (encodeKey 4 .lengthDelimited).length = 1 := rfl
  omega

theorem flatten_lenField4_length : ∀ (mks : List MessageKeyGenerator),
    ((mks.map fun mk => lenField 4 (encMessageKey mk)).flatten).length =
      mksBodyLen mks + mks.length
  | [] => rfl
  | mk :: rest => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      lenField4_encMessageKey_length, mksBodyLen, flatten_lenField4_length rest]
    omega

theorem mksBodyLen_le_flatten (mks : List MessageKeyGenerator) :
    mksBodyLen mks ≤ ((mks.map fun mk => lenField 4 (encMessageKey mk)).flatten).length := by
  rw [flatten_lenField4_length]
  omega

theorem encChainMem_length (g : ChainGhost) (c : ReceiverChain) :
    (encChainMem (g, c)).length =
      (bytesField 1 g.srk.bytes).length +
      (bytesField 2 g.priv.bytes).length +
      (msgField 3 (c.chainKey.map encChainKey)).length +
      ((c.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length := by
  simp only [encChainMem, List.length_append]

/-! ## Field length lemmas for tags 1, 2, and 3 -/

theorem ofNat_len_beq_zero_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ [])
    (hlt : bs.length < 2 ^ 63) :
    (BitVec.ofNat 64 bs.length == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have hpos : 0 < bs.length := List.length_pos_of_ne_nil hne
  have h := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at h
  rw [Nat.mod_eq_of_lt (by omega)] at h
  omega

theorem bv_bytesField_length_of_ne_nil {tag : Nat} {bs : List (BitVec 8)}
    (hne : bs ≠ []) (hkey : (encodeKey tag .lengthDelimited).length = 1) :
    BitVec.ofNat 64 bs.length +
      BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 bs.length)).length + 1#64 =
      BitVec.ofNat 64 (bytesField tag bs).length := by
  simp only [bytesField, hne, ↓reduceIte, lenField, List.length_append, hkey,
    ← BitVec.ofNat_add]
  congr 1
  omega

theorem keyToBytes32_ne_nil (k : BitVec 256) : keyToBytes32 k ≠ [] := by
  intro h
  have hlen : (keyToBytes32 k).length = 32 := by simp [keyToBytes32]
  rw [h] at hlen
  contradiction

theorem bytesField2_keyToBytes32_length (k : BitVec 256) :
    (bytesField 2 (keyToBytes32 k)).length = 34 := by
  have hne := keyToBytes32_ne_nil k
  have hlen : (keyToBytes32 k).length = 32 := by simp [keyToBytes32]
  simp only [bytesField, hne, ↓reduceIte, lenField, List.length_append, hlen]
  rfl

theorem msgField3_encChainKey_zero_length (k : BitVec 256) :
    (msgField 3 (some (encChainKey ⟨k, 0#32⟩))).length = 36 := by
  have hck : (encChainKey ⟨k, 0#32⟩).length = 34 := by
    simp only [encChainKey, show uint32Field 1 0#32 = [] from rfl, List.nil_append,
      bytesField2_keyToBytes32_length]
  simp only [msgField, lenField, List.length_append, hck]
  rfl

theorem uint32Field1_length_of_ne_zero {idx : BitVec 32} (hne : idx ≠ 0#32) :
    (encodeVarint (BitVec.zeroExtend 64 idx)).length + 1 =
      (uint32Field 1 idx).length := by
  have hne' : idx ≠ 0 := hne
  simp only [uint32Field, hne', ↓reduceIte, List.length_append]
  have hkey : (encodeKey 1 .varint).length = 1 := rfl
  rw [hkey, Nat.add_comm]

theorem bv_uint32Field1_length_of_ne_zero {idx : BitVec 32} (hne : idx ≠ 0#32) :
    BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 idx)).length + 1#64 =
      BitVec.ofNat 64 (uint32Field 1 idx).length := by
  rw [← BitVec.ofNat_add, uint32Field1_length_of_ne_zero hne]

theorem bv_encChainKey_length (ck : ChainKey) :
    34#64 + BitVec.ofNat 64 (uint32Field 1 ck.index).length =
      BitVec.ofNat 64 (encChainKey ck).length := by
  have h : (encChainKey ck).length = (uint32Field 1 ck.index).length + 34 := by
    simp only [encChainKey, List.length_append, bytesField2_keyToBytes32_length]
  rw [h, Nat.add_comm, BitVec.ofNat_add]

theorem bv_msgField3_encChainKey_length (ck : ChainKey) :
    BitVec.ofNat 64 (encChainKey ck).length +
      BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length + 1#64 =
      BitVec.ofNat 64 (msgField 3 (some (encChainKey ck))).length := by
  simp only [msgField, lenField, List.length_append, ← BitVec.ofNat_add]
  have hkey : (encodeKey 3 .lengthDelimited).length = 1 := rfl
  rw [hkey]
  congr 1
  omega

/-! ## Stack and register preservation helpers -/

theorem stackAt_chainLen_split (sp : BitVec 64) :
    stackAt sp chainLenStack =
      stackAt (sp - 64#64) msgKeyLenStack ∗ cells (sp - 64#64) 8 :=
  ProofLib.stackAt_split_cells sp msgKeyLenStack 8 (by decide)

@[reducible]
def chainLenSavedAt (sp fp lr x23 v3 x22 x21 x20 x19 : BitVec 64) : SepProp :=
  ((sp - 64#64) ↦₆₄ fp) ∗ ((sp - 56#64) ↦₆₄ lr) ∗
  ((sp - 48#64) ↦₆₄ x23) ∗ ((sp - 40#64) ↦₆₄ v3) ∗
  ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
  ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)

theorem cells8_sub64_eq (sp : BitVec 64) :
    cells (sp - 64#64) 8 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        chainLenSavedAt sp v0 v1 v2 v3 v4 v5 v6 v7 := by
  unfold chainLenSavedAt
  cells_unfold

theorem chainLenSavedAt_entails_cells (sp fp lr x23 v3 x22 x21 x20 x19 : BitVec 64) :
    chainLenSavedAt sp fp lr x23 v3 x22 x21 x20 x19 ⊢ cells (sp - 64#64) 8 := by
  unfold chainLenSavedAt
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x23 (Entails.sepExists_right v3
      (Entails.sepExists_right x22 (Entails.sepExists_right x21
        (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))))))

theorem stack_restore_chainLen (sp fp lr x23 v3 x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 64#64) msgKeyLenStack ∗
      chainLenSavedAt sp fp lr x23 v3 x22 x21 x20 x19 ⊢
    stackAt sp chainLenStack := by
  rw [stackAt_chainLen_split sp]
  exact sepConj_mono_right (chainLenSavedAt_entails_cells sp fp lr x23 v3 x22 x21 x20 x19)

/-- Preservation of `x24..x28`, stack alignment at `fsp`, and execution trace. -/
@[reducible]
def Saved64Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)

theorem msgKeyLen_fnAddr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr msgKeyLenName =
      (tripleRatchetProgAt b C ctl abs).fnAddr chainLenName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len"),
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len"), BitVec.add_assoc]
  rfl

theorem SepWP.seq_clean {prog : Program} {mid target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _ hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

theorem SepWP.align_pre {prog : Program} {target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (heq : P = P_mid)
    (h : SepWP prog target s P_mid (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm) := by
  rwa [heq]

/-! ## `protoChainAt` layout decomposition -/

theorem vecGhostAt_eq (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a =
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
      Prost.vecU8Buf A g.cap g.ptr g.bytes := by
  unfold vecGhostAt
  rw [Prost.vecU8At_eq_header_sep_buf]
  unfold vecHeader
  ac_rfl

theorem optChainKeyAt_some_eq (A : RustAlloc) (pin : VecPin) (ck : ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin (some ck) a =
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
      ((a + 16#64) ↦₆₄ 32#64) ∗
      ((a + 24#64) ↦₃₂ ck.index) ∗ memRegion (a + 28#64) 4 ∗
      Prost.vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key) := by
  unfold optChainKeyAt
  dsimp only
  have hlen : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  rw [Prost.vecU8At_eq_header_sep_buf, hlen]
  unfold vecHeader
  ac_rfl

theorem optChainKeyAt_some_offset72_eq (A : RustAlloc) (pin : VecPin) (ck : ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin (some ck) (a + 72#64) =
      ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
      ((a + 88#64) ↦₆₄ 32#64) ∗
      ((a + 96#64) ↦₃₂ ck.index) ∗ memRegion (a + 100#64) 4 ∗
      Prost.vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key) := by
  rw [optChainKeyAt_some_eq]
  have h80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
  have h88 : a + 72#64 + 16#64 = a + 88#64 := by bv_omega
  have h96 : a + 72#64 + 24#64 = a + 96#64 := by bv_omega
  have h100 : a + 72#64 + 28#64 = a + 100#64 := by bv_omega
  rw [h80, h88, h96, h100]

theorem optChainKeyAt_none_offset72_eq (A : RustAlloc) (pin : VecPin) (a : BitVec 64) :
    optChainKeyAt A pin none (a + 72#64) =
      ((a + 72#64) ↦₆₄ optChainKeyNone) ∗ memRegion (a + 80#64) 24 := by
  unfold optChainKeyAt
  dsimp only
  have h80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
  rw [h80]

theorem vecU8Buf_dup_bounds (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    Prost.vecU8Buf A cap ptr bs ⊢
      ⌜bs.length < 2 ^ 63 ∧ cap.toNat < 2 ^ 63⌝ ∗ Prost.vecU8Buf A cap ptr bs := by
  unfold Prost.vecU8Buf
  apply Entails.pure_left
  rintro ⟨hlen, hcap, hptr⟩
  exact Entails.pure_right ⟨by omega, hcap⟩ (Entails.pure_right ⟨hlen, hcap, hptr⟩ (Entails.refl _))

theorem optChainKeyAt_dup_bounds (A : RustAlloc) (pin : VecPin) (ck : Option ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin ck a ⊢
      ⌜∀ c, ck = some c → pin.cap.toNat < 2 ^ 63⌝ ∗ optChainKeyAt A pin ck a := by
  cases ck with
  | none =>
    exact Entails.pure_right (by intro _ h; cases h) (Entails.refl _)
  | some c =>
    rw [optChainKeyAt_some_eq]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (vecU8Buf_dup_bounds A pin.cap pin.ptr (keyToBytes32 c.key))))))) ?_
    have hpull :
        ((a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
          ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4 ∗
          (⌜(keyToBytes32 c.key).length < 2 ^ 63 ∧ pin.cap.toNat < 2 ^ 63⌝ ∗
            Prost.vecU8Buf A pin.cap pin.ptr (keyToBytes32 c.key))) =
        (⌜(keyToBytes32 c.key).length < 2 ^ 63 ∧ pin.cap.toNat < 2 ^ 63⌝ ∗
          ((a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
            ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4 ∗
            Prost.vecU8Buf A pin.cap pin.ptr (keyToBytes32 c.key))) := by
      ac_rfl
    rw [hpull]
    apply Entails.pure_left
    rintro ⟨_, hcap⟩
    exact Entails.pure_right (fun _ _ => hcap) (Entails.refl _)

@[reducible]
def vecMksTail (A : RustAlloc) (cap ptr : BitVec 64) (n : Nat) : SepProp :=
  if cap = 0 then emp
  else A.live ptr (cap.toNat * 104) 8 ∗
    memRegion (ptr + BitVec.ofNat 64 (n * 104)) ((cap.toNat - n) * 104)

theorem vecAt_mks_expose (A : RustAlloc) (base cap ptr : BitVec 64)
    (mks : List (MessageKeyGhost × MessageKeyGenerator)) :
    vecAt A 104 8 (messageKeyAt A) base cap ptr mks ⊢
      ⌜mks.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ mks.length * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (base ↦₆₄ cap) ∗ ((base + 8#64) ↦₆₄ ptr) ∗
      ((base + 16#64) ↦₆₄ BitVec.ofNat 64 mks.length) ∗
      arrayAt (messageKeyAt A) 104 ptr mks ∗
      vecMksTail A cap ptr mks.length :=
  Getters.DropGlueFacts.vecAt_expose_loop A 104 8 (messageKeyAt A) base cap ptr mks

theorem vecBuf_restore_arrayAt {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α)
    (hlen : xs.length ≤ cap.toNat) (hlt : cap.toNat * stride < 2 ^ 63) (hptr : ptr ≠ 0) :
    arrayAt elem stride ptr xs ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * stride) align ∗
         memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride)) ⊢
      vecBuf A stride align elem cap ptr xs := by
  unfold vecBuf
  apply Entails.pure_right ⟨hlen, hlt, hptr⟩
  by_cases hcap : cap = 0
  · subst hcap
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hnil
    simp only [↓reduceIte, arrayAt_nil, emp_sepConj]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    apply Entails.of_eq
    ac_rfl

theorem vecAt_mks_restore (A : RustAlloc) (base cap ptr : BitVec 64)
    (mks : List (MessageKeyGhost × MessageKeyGenerator))
    (hlen : mks.length ≤ cap.toNat) (hlt : cap.toNat * 104 < 2 ^ 63) (hptr : ptr ≠ 0) :
    (base ↦₆₄ cap) ∗ ((base + 8#64) ↦₆₄ ptr) ∗
      ((base + 16#64) ↦₆₄ BitVec.ofNat 64 mks.length) ∗
      arrayAt (messageKeyAt A) 104 ptr mks ∗
      vecMksTail A cap ptr mks.length ⊢
    vecAt A 104 8 (messageKeyAt A) base cap ptr mks := by
  unfold vecAt vecHeader vecMksTail
  have hpull :
      ((base ↦₆₄ cap) ∗ ((base + 8#64) ↦₆₄ ptr) ∗
        ((base + 16#64) ↦₆₄ BitVec.ofNat 64 mks.length) ∗
        arrayAt (messageKeyAt A) 104 ptr mks ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 104) 8 ∗
           memRegion (ptr + BitVec.ofNat 64 (mks.length * 104)) ((cap.toNat - mks.length) * 104))) =
      (((base ↦₆₄ cap) ∗ ((base + 8#64) ↦₆₄ ptr) ∗
        ((base + 16#64) ↦₆₄ BitVec.ofNat 64 mks.length)) ∗
        (arrayAt (messageKeyAt A) 104 ptr mks ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 104) 8 ∗
             memRegion (ptr + BitVec.ofNat 64 (mks.length * 104)) ((cap.toNat - mks.length) * 104)))) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right (vecBuf_restore_arrayAt A 104 8 (messageKeyAt A) cap ptr mks hlen hlt hptr)

@[reducible]
def chainFieldsAt (A : RustAlloc) (g : ChainGhost) (c : ReceiverChain) (a : BitVec 64) : SepProp :=
  (a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗
  ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.srk.bytes.length) ∗
  Prost.vecU8Buf A g.srk.cap g.srk.ptr g.srk.bytes ∗
  ((a + 24#64) ↦₆₄ g.priv.cap) ∗ ((a + 32#64) ↦₆₄ g.priv.ptr) ∗
  ((a + 40#64) ↦₆₄ BitVec.ofNat 64 g.priv.bytes.length) ∗
  Prost.vecU8Buf A g.priv.cap g.priv.ptr g.priv.bytes ∗
  ((a + 48#64) ↦₆₄ g.mkCap) ∗ ((a + 56#64) ↦₆₄ g.mkPtr) ∗
  ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (g.keys.zip c.messageKeys).length) ∗
  vecMksTail A g.mkCap g.mkPtr (g.keys.zip c.messageKeys).length ∗
  optChainKeyAt A g.ck c.chainKey (a + 72#64)

theorem chainAt_expose (A : RustAlloc) (g : ChainGhost) (c : ReceiverChain) (a : BitVec 64) :
    protoChainAt A (g, c) a ⊢
      ⌜PublicKey.deserialize g.srk.bytes = .ok c.senderRatchetKey ∧
        c.messageKeys.length ≤ maxMessageKeys ∧
        g.keys.length = c.messageKeys.length ∧
        g.srk.bytes.length < 2 ^ 63 ∧
        g.priv.bytes.length < 2 ^ 63 ∧
        (∀ ck, c.chainKey = some ck → g.ck.cap.toNat < 2 ^ 63) ∧
        (g.keys.zip c.messageKeys).length ≤ g.mkCap.toNat ∧
        g.mkCap.toNat * 104 < 2 ^ 63 ∧
        (g.keys.zip c.messageKeys).length * 104 < 2 ^ 63 ∧
        g.mkPtr ≠ 0⌝ ∗
      chainFieldsAt A g c a ∗
      arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) := by
  unfold protoChainAt
  apply Entails.pure_left
  rintro ⟨hsrk, hmax, hklen⟩
  rw [vecGhostAt_eq A g.srk a, vecGhostAt_eq A g.priv (a + 24#64)]
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
  have h56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
  have h64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
  rw [h32, h40]
  refine Entails.trans (sepConj_mono
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (vecU8Buf_dup_bounds A g.srk.cap g.srk.ptr g.srk.bytes))))
    (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (vecU8Buf_dup_bounds A g.priv.cap g.priv.ptr g.priv.bytes))))
      (sepConj_mono
        (vecAt_mks_expose A (a + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys))
        (optChainKeyAt_dup_bounds A g.ck c.chainKey (a + 72#64))))) ?_
  rw [h56, h64]
  have hpull :
      (((a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.srk.bytes.length) ∗
        (⌜g.srk.bytes.length < 2 ^ 63 ∧ g.srk.cap.toNat < 2 ^ 63⌝ ∗
          Prost.vecU8Buf A g.srk.cap g.srk.ptr g.srk.bytes)) ∗
       (((a + 24#64) ↦₆₄ g.priv.cap) ∗ ((a + 32#64) ↦₆₄ g.priv.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 g.priv.bytes.length) ∗
        (⌜g.priv.bytes.length < 2 ^ 63 ∧ g.priv.cap.toNat < 2 ^ 63⌝ ∗
          Prost.vecU8Buf A g.priv.cap g.priv.ptr g.priv.bytes)) ∗
       (⌜(g.keys.zip c.messageKeys).length ≤ g.mkCap.toNat ∧
          g.mkCap.toNat * 104 < 2 ^ 63 ∧
          (g.keys.zip c.messageKeys).length * 104 < 2 ^ 63 ∧
          g.mkPtr ≠ 0⌝ ∗
        ((a + 48#64) ↦₆₄ g.mkCap) ∗ ((a + 56#64) ↦₆₄ g.mkPtr) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (g.keys.zip c.messageKeys).length) ∗
        arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
        vecMksTail A g.mkCap g.mkPtr (g.keys.zip c.messageKeys).length) ∗
       (⌜∀ ck, c.chainKey = some ck → g.ck.cap.toNat < 2 ^ 63⌝ ∗
        optChainKeyAt A g.ck c.chainKey (a + 72#64))) =
      (⌜g.srk.bytes.length < 2 ^ 63 ∧ g.srk.cap.toNat < 2 ^ 63⌝ ∗
       (⌜g.priv.bytes.length < 2 ^ 63 ∧ g.priv.cap.toNat < 2 ^ 63⌝ ∗
        (⌜(g.keys.zip c.messageKeys).length ≤ g.mkCap.toNat ∧
           g.mkCap.toNat * 104 < 2 ^ 63 ∧
           (g.keys.zip c.messageKeys).length * 104 < 2 ^ 63 ∧
           g.mkPtr ≠ 0⌝ ∗
         (⌜∀ ck, c.chainKey = some ck → g.ck.cap.toNat < 2 ^ 63⌝ ∗
          (chainFieldsAt A g c a ∗
           arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys)))))) := by
    unfold chainFieldsAt
    ac_rfl
  rw [hpull]
  apply Entails.pure_left
  rintro ⟨hsrk_lt, _⟩
  apply Entails.pure_left
  rintro ⟨hpriv_lt, _⟩
  apply Entails.pure_left
  rintro ⟨hlen, hcap_lt, hlen_lt, hptr⟩
  apply Entails.pure_left
  intro hck
  exact Entails.pure_right
    ⟨hsrk, hmax, hklen, hsrk_lt, hpriv_lt, hck, hlen, hcap_lt, hlen_lt, hptr⟩
    (Entails.refl _)

theorem chainAt_restore (A : RustAlloc) (g : ChainGhost) (c : ReceiverChain) (a : BitVec 64)
    (hsrk : PublicKey.deserialize g.srk.bytes = .ok c.senderRatchetKey)
    (hmax : c.messageKeys.length ≤ maxMessageKeys)
    (hklen : g.keys.length = c.messageKeys.length)
    (hlen : (g.keys.zip c.messageKeys).length ≤ g.mkCap.toNat)
    (hcap_lt : g.mkCap.toNat * 104 < 2 ^ 63)
    (hptr : g.mkPtr ≠ 0) :
    chainFieldsAt A g c a ∗
      arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ⊢
    protoChainAt A (g, c) a := by
  unfold protoChainAt
  apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
  rw [vecGhostAt_eq A g.srk a, vecGhostAt_eq A g.priv (a + 24#64)]
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
  have h56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
  have h64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
  rw [h32, h40]
  have hrestore := vecAt_mks_restore A (a + 48#64) g.mkCap g.mkPtr
    (g.keys.zip c.messageKeys) hlen hcap_lt hptr
  rw [h56, h64] at hrestore
  unfold chainFieldsAt
  have hpull :
      (((a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.srk.bytes.length) ∗
        Prost.vecU8Buf A g.srk.cap g.srk.ptr g.srk.bytes ∗
        ((a + 24#64) ↦₆₄ g.priv.cap) ∗ ((a + 32#64) ↦₆₄ g.priv.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 g.priv.bytes.length) ∗
        Prost.vecU8Buf A g.priv.cap g.priv.ptr g.priv.bytes ∗
        ((a + 48#64) ↦₆₄ g.mkCap) ∗ ((a + 56#64) ↦₆₄ g.mkPtr) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (g.keys.zip c.messageKeys).length) ∗
        vecMksTail A g.mkCap g.mkPtr (g.keys.zip c.messageKeys).length ∗
        optChainKeyAt A g.ck c.chainKey (a + 72#64)) ∗
       arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys)) =
      (((a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.srk.bytes.length) ∗
        Prost.vecU8Buf A g.srk.cap g.srk.ptr g.srk.bytes) ∗
       (((a + 24#64) ↦₆₄ g.priv.cap) ∗ ((a + 32#64) ↦₆₄ g.priv.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 g.priv.bytes.length) ∗
        Prost.vecU8Buf A g.priv.cap g.priv.ptr g.priv.bytes) ∗
       (((a + 48#64) ↦₆₄ g.mkCap) ∗ ((a + 56#64) ↦₆₄ g.mkPtr) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (g.keys.zip c.messageKeys).length) ∗
        arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
        vecMksTail A g.mkCap g.mkPtr (g.keys.zip c.messageKeys).length) ∗
       optChainKeyAt A g.ck c.chainKey (a + 72#64)) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hrestore))

/-! ## Loop arithmetic and framing helpers -/

theorem bv_mkBodyLen_eq (mk : MessageKeyGenerator) :
    BitVec.ofNat 64 (encMessageKey mk).length +
      BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 (encMessageKey mk).length)).length =
      BitVec.ofNat 64 (mkBodyLen mk) := by
  rw [← BitVec.ofNat_add, mkBodyLen]

theorem mkBodyLen_ule {mk : MessageKeyGenerator} (h : mkBodyLen mk < 2 ^ 64) :
    BitVec.ule (BitVec.ofNat 64 (encMessageKey mk).length) (BitVec.ofNat 64 (mkBodyLen mk)) = true :=
  ule_ofNat_add_left_of_lt (a := (encMessageKey mk).length)
    (b := (encodeVarint (BitVec.ofNat 64 (encMessageKey mk).length)).length) h

theorem mkBodyLen_ult {mk : MessageKeyGenerator} (h : mkBodyLen mk < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 (mkBodyLen mk)) (BitVec.ofNat 64 (encMessageKey mk).length) = false :=
  ult_ofNat_add_left_of_lt (a := (encMessageKey mk).length)
    (b := (encodeVarint (BitVec.ofNat 64 (encMessageKey mk).length)).length) h

theorem sep_pull_mk (M Arr Stk Frame : SepProp) :
    (M ∗ Arr) ∗ Stk ∗ Frame = M ∗ Stk ∗ (Arr ∗ Frame) := by
  ac_rfl

theorem sep_push_mk (M Arr Stk Frame : SepProp) :
    M ∗ Stk ∗ (Arr ∗ Frame) = Arr ∗ Stk ∗ (M ∗ Frame) := by
  ac_rfl

theorem sep_rejoin_mk (M Arr Stk Frame : SepProp) :
    Arr ∗ Stk ∗ (M ∗ Frame) = (M ∗ Arr) ∗ Stk ∗ Frame := by
  ac_rfl

theorem zip_length_eq {α β : Type} {xs : List α} {ys : List β} (h : xs.length = ys.length) :
    (xs.zip ys).length = ys.length := by
  simp [h]

theorem zip_map_snd_eq {α β : Type} {xs : List α} {ys : List β} (h : xs.length = ys.length) :
    (xs.zip ys).map Prod.snd = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp [ih h]

end CryptoVerification.E2E.Record.Serialization




