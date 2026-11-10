/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Data.Vector.Basic

/-!
# Byte-level AES-256-CBC with PKCS#7 padding

Defines byte-level AES-256-CBC encryption and decryption with strict PKCS#7 padding and unpadding,
and proves round-trip correctness (`cbcDecRaw_correct`) when the block-cipher inverse `D k`
inverts `E k`.
-/

@[expose] public section

namespace ByteSpecs

/-! ## AES-256-CBC encryption with PKCS#7 padding -/

abbrev Block := BitVec 128

abbrev AesKey := BitVec 256

/-- CBC encryption of blocks under block function `f` from initial chaining value `prev`. -/
def cbcEncrypt (f : Block → Block) (prev : Block) :
    {n : ℕ} → List.Vector Block n → List.Vector Block n
  | 0, _ => List.Vector.nil
  | _ + 1, P =>
    let c := f (P.head ^^^ prev)
    c ::ᵥ cbcEncrypt f c P.tail

abbrev Plain (ℓ : ℕ) := List.Vector (BitVec 8) ℓ

def nBlocks (ℓ : ℕ) : ℕ := ℓ / 16 + 1

def padLen (ℓ : ℕ) : ℕ := 16 - ℓ % 16

def pkcs7Bytes {ℓ : ℕ} (m : Plain ℓ) : List (BitVec 8) :=
  m.toList ++ List.replicate (padLen ℓ) (BitVec.ofNat 8 (padLen ℓ))

/-- Packs up to 16 bytes into a little-endian 128-bit block (byte `j` at bits `8*j .. 8*j + 7`). -/
def bytesToBlock (bs : List (BitVec 8)) : Block :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.zeroExtend 128) 0

/-- Splits `pkcs7Bytes m` into `nBlocks ℓ` 16-byte blocks. -/
def pkcs7Blocks {ℓ : ℕ} (m : Plain ℓ) : List.Vector Block (nBlocks ℓ) :=
  List.Vector.ofFn fun i => bytesToBlock (((pkcs7Bytes m).drop (16 * i.val)).take 16)

/-! ## AES-256-CBC decryption with strict PKCS#7 unpadding -/

/-- Unpacks a 128-bit block into 16 little-endian bytes; inverse of `bytesToBlock`. -/
def blockToBytesLE (b : Block) : List (BitVec 8) :=
  List.ofFn fun j : Fin 16 => b.extractLsb' (8 * j.val) 8

/-- Splits `bs` into 16-byte blocks, dropping any trailing partial chunk. -/
def chunks16 (bs : List (BitVec 8)) : List Block :=
  List.ofFn fun i : Fin (bs.length / 16) => bytesToBlock ((bs.drop (16 * i.val)).take 16)

/-- CBC decryption of blocks under inverse block function `g` from initial chaining value `prev`. -/
def cbcDecryptBlocks (g : Block → Block) (prev : Block) : List Block → List Block
  | [] => []
  | c :: cs => (g c ^^^ prev) :: cbcDecryptBlocks g c cs

/-- Strict PKCS#7 unpadding: rejects unless the final byte `n` satisfies `1 ≤ n ≤ 16` and the
trailing `n` bytes all equal `n`. -/
def pkcs7Unpad (bs : List (BitVec 8)) : Option (List (BitVec 8)) :=
  match bs.getLast? with
  | none => none
  | some last =>
    let n := last.toNat
    if n = 0 ∨ 16 < n ∨ bs.length < n then none
    else if (bs.drop (bs.length - n)).all (· == last) then some (bs.take (bs.length - n))
    else none

/-- AES-256-CBC decryption with strict PKCS#7 unpadding, returning `none` if `ct` is empty, not
block-aligned, or has invalid padding. -/
def cbcDecRaw (D : AesKey → Block → Block) (k : AesKey) (iv : Block)
    (ct : List (BitVec 8)) : Option (List (BitVec 8)) :=
  if ct = [] ∨ ct.length % 16 ≠ 0 then none
  else pkcs7Unpad ((cbcDecryptBlocks (D k) iv (chunks16 ct)).flatMap blockToBytesLE)

/-! ## Round-trip correctness -/

private theorem shiftLeft8_or_setWidth_zero (W : ℕ) (x : BitVec 8) :
    ((0 : BitVec W) <<< 8) ||| x.setWidth W = x.setWidth W := by
  simp

private theorem shiftLeft8_or_setWidth_step {W w : ℕ} (x : BitVec w) (y : BitVec 8) :
    ((x.setWidth W) <<< 8) ||| y.setWidth W = (x ++ y).setWidth W := by
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
    BitVec.getLsbD_append]
  by_cases h8 : i < 8
  · simp [h8]
  · simp [h8, BitVec.getLsbD_of_ge y i (by omega)]

private theorem extractLsb'_append_eq {W : ℕ} (b : BitVec W) (s₂ s₁ n₂ n₁ : ℕ) (h : s₂ = s₁ + n₁) :
    b.extractLsb' s₂ n₂ ++ b.extractLsb' s₁ n₁ = b.extractLsb' s₁ (n₂ + n₁) := by
  subst h
  ext i hi
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
  split
  · rfl
  · congr 1; omega

private theorem extractLsb'_zero_append8 {w : ℕ} (x : BitVec w) (y : BitVec 8) :
    (x ++ y).extractLsb' 0 8 = y := by
  ext i hi
  simp [BitVec.getLsbD_append, hi]

private theorem extractLsb'_succ8_append8 {w : ℕ} (x : BitVec w) (y : BitVec 8) (s : ℕ) :
    (x ++ y).extractLsb' (s + 8) 8 = x.extractLsb' s 8 := by
  ext i hi
  have hnotlt : ¬ (s + 8 + i < 8) := by omega
  have hsub : s + 8 + i - 8 = s + i := by omega
  simp [BitVec.getLsbD_append, hnotlt, hsub]

private theorem extractLsb'_zero_self8 (y : BitVec 8) :
    y.extractLsb' 0 8 = y := by
  ext i hi
  simp

private theorem extractLsb'_zero_self {w : ℕ} (x : BitVec w) :
    x.extractLsb' 0 w = x := by
  ext i hi
  simp

theorem bytesToBlock_blockToBytesLE (b : Block) : bytesToBlock (blockToBytesLE b) = b := by
  change bytesToBlock
      [b.extractLsb' 0 8, b.extractLsb' 8 8, b.extractLsb' 16 8, b.extractLsb' 24 8,
       b.extractLsb' 32 8, b.extractLsb' 40 8, b.extractLsb' 48 8, b.extractLsb' 56 8,
       b.extractLsb' 64 8, b.extractLsb' 72 8, b.extractLsb' 80 8, b.extractLsb' 88 8,
       b.extractLsb' 96 8, b.extractLsb' 104 8, b.extractLsb' 112 8, b.extractLsb' 120 8] = b
  dsimp only [bytesToBlock, List.foldr, BitVec.zeroExtend]
  rw [shiftLeft8_or_setWidth_zero 128]
  repeat rw [shiftLeft8_or_setWidth_step]
  rw [BitVec.setWidth_eq]
  rw [extractLsb'_append_eq b 120 112 _ 8 rfl, extractLsb'_append_eq b 112 104 _ 8 rfl,
      extractLsb'_append_eq b 104 96 _ 8 rfl, extractLsb'_append_eq b 96 88 _ 8 rfl,
      extractLsb'_append_eq b 88 80 _ 8 rfl, extractLsb'_append_eq b 80 72 _ 8 rfl,
      extractLsb'_append_eq b 72 64 _ 8 rfl, extractLsb'_append_eq b 64 56 _ 8 rfl,
      extractLsb'_append_eq b 56 48 _ 8 rfl, extractLsb'_append_eq b 48 40 _ 8 rfl,
      extractLsb'_append_eq b 40 32 _ 8 rfl, extractLsb'_append_eq b 32 24 _ 8 rfl,
      extractLsb'_append_eq b 24 16 _ 8 rfl, extractLsb'_append_eq b 16 8 _ 8 rfl,
      extractLsb'_append_eq b 8 0 _ 8 rfl]
  exact extractLsb'_zero_self b

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
  dsimp only [bytesToBlock, List.foldr, BitVec.zeroExtend]
  rw [shiftLeft8_or_setWidth_zero 128]
  repeat rw [shiftLeft8_or_setWidth_step]
  exact BitVec.setWidth_eq _

theorem blockToBytesLE_bytesToBlock (bs : List (BitVec 8)) (h : bs.length = 16) :
    blockToBytesLE (bytesToBlock bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at h)
  rw [blockToBytesLE_eq_list, bytesToBlock_16_eq]
  simp only [extractLsb'_succ8_append8, extractLsb'_zero_append8, extractLsb'_zero_self8]

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
    rw [blockToBytesLE_bytesToBlock (bs.take 16) (by rw [List.length_take, h]; omega)]
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

theorem flatMap_pkcs7Blocks {ℓ : ℕ} (m : Plain ℓ) :
    (pkcs7Blocks m).toList.flatMap blockToBytesLE = pkcs7Bytes m := by
  have hlen : (pkcs7Bytes m).length = 16 * nBlocks ℓ := by
    simp only [pkcs7Bytes, List.length_append, List.Vector.toList_length, List.length_replicate,
      padLen, nBlocks]
    omega
  unfold pkcs7Blocks
  rw [List.Vector.toList_ofFn]
  exact flatMap_ofFn_chunks16 (nBlocks ℓ) (pkcs7Bytes m) hlen

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

private theorem getLast?_append_replicate_pos {α : Type} (xs : List α) (k : ℕ) (hk : 1 ≤ k)
    (x : α) : (xs ++ List.replicate k x).getLast? = some x := by
  have hk' : k = (k - 1) + 1 := by omega
  rw [hk', List.replicate_succ', ← List.append_assoc, List.getLast?_concat]

private theorem all_beq_replicate (k : ℕ) (x : BitVec 8) :
    (List.replicate k x).all (· == x) = true := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

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

/-- If `D k` inverts `E k`, `cbcDecRaw` recovers `m.toList` from the serialized CBC-PKCS#7
encryption of `m` under `(k, iv)`. -/
theorem cbcDecRaw_correct {E D : AesKey → Block → Block} (hD : ∀ k x, D k (E k x) = x)
    (k : AesKey) (iv : Block) {ℓ : ℕ} (m : Plain ℓ) :
    cbcDecRaw D k iv ((cbcEncrypt (E k) iv (pkcs7Blocks m)).toList.flatMap blockToBytesLE) =
      some m.toList := by
  have hlen : ((cbcEncrypt (E k) iv (pkcs7Blocks m)).toList.flatMap blockToBytesLE).length =
      16 * nBlocks ℓ := by
    rw [length_flatMap_blockToBytesLE, List.Vector.toList_length]
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

end ByteSpecs
