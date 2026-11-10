/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
import LibsignalBinary.Specifications.CryptoGames.AEAD.CBC
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# AES-256-CBC decryption: correctness and IND-CPA of the full cipher

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Proves that AES-256-CBC decryption with strict PKCS#7 unpadding (`CBCDecDefs.lean`) inverts
encryption when `D k` inverts `E k`, and transfers the one-time IND-CPA bound of `specCbc_indcpa`
to `cbcPkcs7`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames
namespace CBC

/-! ### Bytes and blocks -/

/-- `bytesToBlock` inverts `blockToBytesLE`. -/
theorem bytesToBlock_blockToBytesLE (b : Block) : bytesToBlock (blockToBytesLE b) = b := by
  have h0 (x : BitVec 8) : ((0 : BitVec 128) <<< 8) ||| x.setWidth 128 = x.setWidth 128 := by simp
  have hstep {w : ℕ} (x : BitVec w) (y : BitVec 8) :
      ((x.setWidth 128) <<< 8) ||| y.setWidth 128 = (x ++ y).setWidth 128 := by
    ext i hi
    simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getLsbD_append]
    by_cases h8 : i < 8
    · simp [h8]
    · simp [h8, BitVec.getLsbD_of_ge y i (by omega)]
  have hext (s₂ s₁ n₂ n₁ : ℕ) (h : s₂ = s₁ + n₁) :
      b.extractLsb' s₂ n₂ ++ b.extractLsb' s₁ n₁ = b.extractLsb' s₁ (n₂ + n₁) := by
    subst h
    ext i hi
    simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
    split
    · rfl
    · congr 1; omega
  change bytesToBlock
      [b.extractLsb' 0 8, b.extractLsb' 8 8, b.extractLsb' 16 8, b.extractLsb' 24 8,
       b.extractLsb' 32 8, b.extractLsb' 40 8, b.extractLsb' 48 8, b.extractLsb' 56 8,
       b.extractLsb' 64 8, b.extractLsb' 72 8, b.extractLsb' 80 8, b.extractLsb' 88 8,
       b.extractLsb' 96 8, b.extractLsb' 104 8, b.extractLsb' 112 8, b.extractLsb' 120 8] = b
  dsimp only [bytesToBlock, List.foldr, BitVec.zeroExtend]
  rw [h0]
  repeat rw [hstep]
  rw [BitVec.setWidth_eq]
  rw [hext 120 112 _ 8 rfl, hext 112 104 _ 8 rfl, hext 104 96 _ 8 rfl,
      hext 96 88 _ 8 rfl, hext 88 80 _ 8 rfl, hext 80 72 _ 8 rfl,
      hext 72 64 _ 8 rfl, hext 64 56 _ 8 rfl, hext 56 48 _ 8 rfl,
      hext 48 40 _ 8 rfl, hext 40 32 _ 8 rfl, hext 32 24 _ 8 rfl,
      hext 24 16 _ 8 rfl, hext 16 8 _ 8 rfl, hext 8 0 _ 8 rfl]
  ext i hi
  simp

private theorem blockToBytesLE_eq_list (b : Block) :
    blockToBytesLE b =
      [b.extractLsb' 0 8, b.extractLsb' 8 8, b.extractLsb' 16 8, b.extractLsb' 24 8,
       b.extractLsb' 32 8, b.extractLsb' 40 8, b.extractLsb' 48 8, b.extractLsb' 56 8,
       b.extractLsb' 64 8, b.extractLsb' 72 8, b.extractLsb' 80 8, b.extractLsb' 88 8,
       b.extractLsb' 96 8, b.extractLsb' 104 8, b.extractLsb' 112 8, b.extractLsb' 120 8] :=
  rfl

theorem bytesToBlock_16_eq
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] =
      b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++
      b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 := by
  have h0 (x : BitVec 8) : ((0 : BitVec 128) <<< 8) ||| x.setWidth 128 = x.setWidth 128 := by simp
  have hstep {w : ℕ} (x : BitVec w) (y : BitVec 8) :
      ((x.setWidth 128) <<< 8) ||| y.setWidth 128 = (x ++ y).setWidth 128 := by
    ext i hi
    simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getLsbD_append]
    by_cases h8 : i < 8
    · simp [h8]
    · simp [h8, BitVec.getLsbD_of_ge y i (by omega)]
  dsimp only [bytesToBlock, List.foldr, BitVec.zeroExtend]
  rw [h0]
  repeat rw [hstep]
  exact BitVec.setWidth_eq _

private theorem getLsbD_bytesToBlock (bs : List (BitVec 8)) :
    ∀ (j k : ℕ), k < 8 → 8 * j + k < 128 →
      (bytesToBlock bs).getLsbD (8 * j + k) = (bs[j]?.getD 0#8).getLsbD k := by
  have hstep (b : BitVec 8) (acc : Block) (m : ℕ) (hm : m < 128) :
      ((acc <<< 8) ||| b.zeroExtend 128).getLsbD m =
        if m < 8 then b.getLsbD m else acc.getLsbD (m - 8) := by
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hm,
      decide_true, Bool.true_and]
    by_cases h8 : m < 8
    · simp [h8]
    · simp [h8, BitVec.getLsbD_of_ge b m (by omega)]
  induction bs with
  | nil =>
    intro j k _ _
    simp [bytesToBlock]
  | cons b tl ih =>
    intro j k hk hlt
    change ((bytesToBlock tl <<< 8) ||| b.zeroExtend 128).getLsbD (8 * j + k) =
      ((b :: tl)[j]?.getD 0#8).getLsbD k
    rw [hstep b (bytesToBlock tl) (8 * j + k) hlt]
    cases j with
    | zero =>
      simp [hk]
    | succ j' =>
      have hnot8 : ¬ (8 * (j' + 1) + k < 8) := by omega
      have hsub : 8 * (j' + 1) + k - 8 = 8 * j' + k := by omega
      simp only [hnot8, ↓reduceIte, hsub, List.getElem?_cons_succ]
      exact ih j' k hk (by omega)

/-- `blockToBytesLE` inverts `bytesToBlock` on 16-byte lists. -/
theorem blockToBytesLE_bytesToBlock (bs : List (BitVec 8)) (h : bs.length = 16) :
    blockToBytesLE (bytesToBlock bs) = bs := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 16
  · have hj_len : j < bs.length := by omega
    simp only [blockToBytesLE, List.getElem?_ofFn, hj, ↓reduceDIte, List.getElem?_eq_getElem hj_len]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [BitVec.getLsbD_extractLsb']
    simp only [hk, decide_true, Bool.true_and]
    have htag := getLsbD_bytesToBlock bs j k hk (by omega)
    rw [htag, List.getElem?_eq_getElem hj_len, Option.getD_some]
  · rw [List.getElem?_eq_none (by simp [blockToBytesLE]; omega), List.getElem?_eq_none (by omega)]

private theorem length_blockToBytesLE (b : Block) : (blockToBytesLE b).length = 16 := by
  simp [blockToBytesLE]

private theorem length_flatMap_blockToBytesLE (cs : List Block) :
    (cs.flatMap blockToBytesLE).length = 16 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp [List.flatMap_cons, length_blockToBytesLE, ih]
    omega

private theorem drop_take_flatMap_blockToBytesLE (cs : List Block) (i : ℕ) (hi : i < cs.length) :
    ((cs.flatMap blockToBytesLE).drop (16 * i)).take 16 = blockToBytesLE cs[i] := by
  induction cs generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero =>
      simp [List.flatMap_cons, length_blockToBytesLE]
    | succ i =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.drop_append, List.drop_eq_nil_of_le (by rw [length_blockToBytesLE]; omega),
        List.nil_append]
      have hsub : 16 * (i + 1) - (blockToBytesLE c).length = 16 * i := by
        rw [length_blockToBytesLE]; omega
      rw [hsub]
      exact ih i (by simpa using hi)

/-- Splitting the LE bytes of blocks back into blocks gives the blocks. -/
theorem chunks16_flatMap (cs : List Block) : chunks16 (cs.flatMap blockToBytesLE) = cs := by
  unfold chunks16
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · rw [List.length_ofFn, length_flatMap_blockToBytesLE]
    omega
  · simp only [List.getElem_ofFn]
    rw [drop_take_flatMap_blockToBytesLE cs i h2, bytesToBlock_blockToBytesLE]

private theorem flatMap_ofFn_chunks16 (k : ℕ) (bs : List (BitVec 8)) (h : bs.length = 16 * k) :
    (List.ofFn fun i : Fin k => bytesToBlock ((bs.drop (16 * i.val)).take 16)).flatMap
      blockToBytesLE = bs := by
  induction k generalizing bs with
  | zero =>
    have h0 : bs.length = 0 := by omega
    rw [List.eq_nil_of_length_eq_zero h0]
    rfl
  | succ k ih =>
    rw [List.ofFn_succ, List.flatMap_cons]
    simp only [Fin.val_zero, Nat.mul_zero, List.drop_zero, Fin.val_succ]
    rw [blockToBytesLE_bytesToBlock (bs.take 16) (by simp [h])]
    have hrest : (List.ofFn fun i : Fin k =>
        bytesToBlock ((bs.drop (16 * (i.val + 1))).take 16)) =
      List.ofFn fun i : Fin k =>
        bytesToBlock (((bs.drop 16).drop (16 * i.val)).take 16) := by
      congr 1
      ext i
      rw [List.drop_drop]
      have : 16 * (i.val + 1) = 16 + 16 * i.val := by omega
      rw [this]
    rw [hrest, ih (bs.drop 16) (by simp [h]; omega), List.take_append_drop]

/-- The bytes of the PKCS#7 blocks are the padded bytes. -/
theorem flatMap_pkcs7Blocks {ℓ : ℕ} (m : Plain ℓ) :
    (pkcs7Blocks m).toList.flatMap blockToBytesLE = pkcs7Bytes m := by
  have hlen : (pkcs7Bytes m).length = 16 * nBlocks ℓ := by
    simp only [pkcs7Bytes, List.length_append, List.Vector.toList_length, List.length_replicate,
      padLen, nBlocks]
    omega
  unfold pkcs7Blocks
  rw [List.Vector.toList_ofFn]
  exact flatMap_ofFn_chunks16 (nBlocks ℓ) (pkcs7Bytes m) hlen

/-- CBC decryption inverts CBC encryption when `g` inverts `f`. -/
theorem cbcDecryptBlocks_cbcEncrypt {f g : Block → Block} (hfg : ∀ x, g (f x) = x)
    (prev : Block) {n : ℕ} (P : List.Vector Block n) :
    cbcDecryptBlocks g prev (cbcEncrypt f prev P).toList = P.toList := by
  induction n generalizing prev with
  | zero =>
    rcases P with ⟨_ | _, hlen⟩
    · rfl
    · simp at hlen
  | succ n ih =>
    simp only [cbcEncrypt, List.Vector.toList_cons, cbcDecryptBlocks, hfg]
    have hxor : (P.head ^^^ prev) ^^^ prev = P.head := by
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    rw [hxor, ih (f (P.head ^^^ prev)) P.tail]
    rcases P with ⟨_ | ⟨p, ps⟩, hlen⟩
    · simp at hlen
    · rfl

/-! ### Unpadding and decryption -/

private theorem getLast?_append_replicate_pos {α : Type} (xs : List α) (k : ℕ) (hk : 1 ≤ k)
    (x : α) : (xs ++ List.replicate k x).getLast? = some x := by
  have hk' : k = (k - 1) + 1 := by omega
  rw [hk', List.replicate_succ', ← List.append_assoc, List.getLast?_concat]

private theorem all_beq_replicate (k : ℕ) (x : BitVec 8) :
    (List.replicate k x).all (· == x) = true := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-- Strict PKCS#7 unpadding inverts PKCS#7 padding. -/
theorem pkcs7Unpad_pkcs7Bytes {ℓ : ℕ} (m : Plain ℓ) : pkcs7Unpad (pkcs7Bytes m) = some m.toList := by
  unfold pkcs7Unpad pkcs7Bytes
  have hp1 : 1 ≤ padLen ℓ := by unfold padLen; omega
  have hp16 : padLen ℓ ≤ 16 := by unfold padLen; omega
  rw [getLast?_append_replicate_pos m.toList (padLen ℓ) hp1]
  dsimp only
  have htoNat : (BitVec.ofNat 8 (padLen ℓ)).toNat = padLen ℓ := by
    rw [BitVec.toNat_ofNat]
    omega
  have hmlen : m.toList.length = ℓ := m.toList_length
  have hlen : (m.toList ++ List.replicate (padLen ℓ) (BitVec.ofNat 8 (padLen ℓ))).length =
      ℓ + padLen ℓ := by
    simp [hmlen]
  have hcond : ¬ ((BitVec.ofNat 8 (padLen ℓ)).toNat = 0 ∨
      16 < (BitVec.ofNat 8 (padLen ℓ)).toNat ∨
      (m.toList ++ List.replicate (padLen ℓ) (BitVec.ofNat 8 (padLen ℓ))).length <
        (BitVec.ofNat 8 (padLen ℓ)).toNat) := by
    rw [htoNat, hlen]
    omega
  simp only [hcond, ↓reduceIte]
  have hsub : (m.toList ++ List.replicate (padLen ℓ) (BitVec.ofNat 8 (padLen ℓ))).length -
      (BitVec.ofNat 8 (padLen ℓ)).toNat = m.toList.length := by
    rw [hlen, htoNat, hmlen]
    omega
  rw [hsub, List.drop_left, List.take_left]
  simp only [all_beq_replicate, ↓reduceIte]

/-- If `D k` inverts `E k`, `cbcDecRaw` recovers `m` from the CBC-PKCS#7 encryption of `m`. -/
theorem cbcDecRaw_correct {E D : AesKey → Block → Block} (hD : ∀ k x, D k (E k x) = x)
    (k : AesKey) (iv : Block) {ℓ : ℕ} (m : Plain ℓ) :
    cbcDecRaw D k iv ((cbcEncrypt (E k) iv (pkcs7Blocks m)).toList.flatMap blockToBytesLE) =
      some m.toList := by
  have hlen : ((cbcEncrypt (E k) iv (pkcs7Blocks m)).toList.flatMap blockToBytesLE).length =
      16 * nBlocks ℓ := by
    rw [List.length_flatMap]
    have h16 : ∀ b : Block, (blockToBytesLE b).length = 16 := fun b => by simp [blockToBytesLE]
    simp [h16, List.sum_replicate, Nat.mul_comm]
  have hne : ¬ ((cbcEncrypt (E k) iv (pkcs7Blocks m)).toList.flatMap blockToBytesLE = [] ∨
      ((cbcEncrypt (E k) iv (pkcs7Blocks m)).toList.flatMap blockToBytesLE).length % 16 ≠ 0) := by
    rw [hlen]
    rintro (h | h)
    · have := congrArg List.length h
      rw [hlen] at this
      simp [nBlocks] at this
    · simp at h
  simp only [cbcDecRaw, hne, ↓reduceIte]
  rw [chunks16_flatMap, cbcDecryptBlocks_cbcEncrypt (hD k), flatMap_pkcs7Blocks,
    pkcs7Unpad_pkcs7Bytes]

/-- `cbcPkcs7 E D ℓ` is a correct cipher if `D k` inverts `E k`. -/
theorem specCbcFull_correct {E D : AesKey → Block → Block} (hD : ∀ k x, D k (E k x) = x)
    (ℓ : ℕ) : (cbcPkcs7 E D ℓ).Correct := by
  rintro ⟨k, iv⟩ m
  simp only [cbcPkcs7, cbcPkcs7EncryptOnly, cbcScheme]
  rw [cbcDecRaw_correct hD]
  simp

/-! ### IND-CPA -/

/-- The IND-CPA advantage depends only on `enc`. -/
theorem indcpaAdvantage_congr_enc {K M C : Type} [SampleableType K] [SampleableType C]
    (c₁ c₂ : CipherScheme K M C) (h : c₁.enc = c₂.enc) (A : CipherScheme.INDCPAAdversary M C) :
    c₁.indcpaAdvantage A = c₂.indcpaAdvantage A := by
  unfold CipherScheme.indcpaAdvantage CipherScheme.indcpaGame CipherScheme.indcpaEncrypt
  rw [h]

/-- One-time IND-CPA bound for `cbcPkcs7 E D ℓ`. -/
theorem specCbcFull_indcpa (E D : AesKey → Block → Block) (ℓ : ℕ)
    (A : CipherScheme.INDCPAAdversary (Plain ℓ) (List.Vector Block (nBlocks ℓ))) :
    (cbcPkcs7 E D ℓ).indcpaAdvantage A ≤
      (blockPRF E).prfAdvantage (cbcRed pkcs7Blocks A) +
        ((nBlocks ℓ * (nBlocks ℓ - 1) / 2 : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
  rw [indcpaAdvantage_congr_enc (cbcPkcs7 E D ℓ) (cbcPkcs7EncryptOnly E ℓ) rfl A]
  exact specCbc_indcpa E ℓ A

end CBC
end CryptoGames
