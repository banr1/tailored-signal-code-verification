/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalAesCbc
public import ProofLib.Lemmas
public import ProofLib.SepLogic.Frame
import ProofLib.SepLogic.WP.StateNorm
public import LibsignalBinary.Proofs.AesCbc.LibsignalAesCbcProofDefs

/-!
# Byte Encoding and Memory Slice Lemmas

Round-trip and XOR lemmas for `LibsignalAesCbc` byte/block/key encodings (`toLEBytes`,
`blockToBytes`, `bytesToBlock`, `keyToBytes`, `bytesToKey`), together with `Memory.readBytes` and
`Memory.writeBytes` slicing, disjointness, and 8/32/64/128-bit load/store bridges.
-/

@[expose] public section

namespace CryptoVerification.LibsignalAesCbc.Run.Bytes

open Arm64 ProofLib CryptoGames CryptoGames.CBC

/-! ## Byte, Block, and Key Encodings -/

@[simp]
theorem toLEBytes_length (n : ℕ) {w : ℕ} (x : BitVec w) :
    (toLEBytes n x).length = n := by
  simp [toLEBytes]

@[simp]
theorem blockToBytes_length (b : Block) :
    (blockToBytes b).length = 16 := by
  simp [blockToBytes]

@[simp]
theorem keyToBytes_length (k : AesKey) :
    (keyToBytes k).length = 32 := by
  simp [keyToBytes]

@[simp]
theorem toLEBytes_getElem (n : ℕ) {w : ℕ} (x : BitVec w) (j : ℕ)
    (hj : j < (toLEBytes n x).length) :
    (toLEBytes n x)[j] = x.extractLsb' (8 * j) 8 := by
  simp [toLEBytes]

@[simp]
theorem blockToBytes_getElem (b : Block) (j : ℕ) (hj : j < (blockToBytes b).length) :
    (blockToBytes b)[j] = b.extractLsb' (8 * j) 8 := by
  simp [blockToBytes]

@[simp]
theorem keyToBytes_getElem (k : AesKey) (j : ℕ) (hj : j < (keyToBytes k).length) :
    (keyToBytes k)[j] = k.extractLsb' (8 * j) 8 := by
  simp [keyToBytes]

theorem toLEBytes_4_eq_list {w : ℕ} (x : BitVec w) :
    toLEBytes 4 x =
      [x.extractLsb' 0 8, x.extractLsb' 8 8, x.extractLsb' 16 8, x.extractLsb' 24 8] :=
  rfl

theorem toLEBytes_8_eq_list {w : ℕ} (x : BitVec w) :
    toLEBytes 8 x =
      [x.extractLsb' 0 8, x.extractLsb' 8 8, x.extractLsb' 16 8, x.extractLsb' 24 8,
       x.extractLsb' 32 8, x.extractLsb' 40 8, x.extractLsb' 48 8, x.extractLsb' 56 8] :=
  rfl

theorem blockToBytes_eq_list (b : Block) :
    blockToBytes b =
      [b.extractLsb' 0 8, b.extractLsb' 8 8, b.extractLsb' 16 8, b.extractLsb' 24 8,
       b.extractLsb' 32 8, b.extractLsb' 40 8, b.extractLsb' 48 8, b.extractLsb' 56 8,
       b.extractLsb' 64 8, b.extractLsb' 72 8, b.extractLsb' 80 8, b.extractLsb' 88 8,
       b.extractLsb' 96 8, b.extractLsb' 104 8, b.extractLsb' 112 8, b.extractLsb' 120 8] :=
  rfl

private theorem shiftLeft8_or_setWidth_zero (w : ℕ) (b : BitVec 8) :
    ((0 : BitVec w) <<< 8) ||| b.setWidth w = b.setWidth w := by
  simp

private theorem shiftLeft8_or_setWidth_step {w k : ℕ} (a : BitVec k) (b : BitVec 8) :
    (a.setWidth w <<< 8) ||| b.setWidth w = (a ++ b).setWidth w := by
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
    BitVec.getLsbD_append]
  by_cases h8 : i < 8
  · simp [h8]
  · have hb : b.getLsbD i = false := BitVec.getLsbD_of_ge b i (by omega)
    simp [h8, hb]

private theorem extractLsb'_append_eq {w : ℕ} (x : BitVec w) (a b c d : ℕ) (h : b + d = a) :
    x.extractLsb' a c ++ x.extractLsb' b d = x.extractLsb' b (c + d) := by
  subst h
  ext i hi
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
  (split <;> congr 1); omega

private theorem extractLsb'_zero_append8 {k : ℕ} (a : BitVec k) (b : BitVec 8) :
    (a ++ b).extractLsb' 0 8 = b := by
  ext i hi
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_append, hi]

private theorem extractLsb'_append8_of_ge {k : ℕ} (a : BitVec k) (b : BitVec 8) (s : ℕ)
    (h : 8 ≤ s) :
    (a ++ b).extractLsb' s 8 = a.extractLsb' (s - 8) 8 := by
  ext i hi
  have hnot : ¬ (s + i < 8) := by omega
  have hsub : s + i - 8 = s - 8 + i := by omega
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_append, hnot, hsub]

private theorem extractLsb'_zero_self {w : ℕ} (x : BitVec w) :
    x.extractLsb' 0 w = x := by
  ext i hi
  simp

private theorem extractLsb'_zero_self8 (b : BitVec 8) :
    b.extractLsb' 0 8 = b :=
  extractLsb'_zero_self b

private theorem xor_append_distrib {w v : ℕ} (a c : BitVec w) (b d : BitVec v) :
    (a ++ b) ^^^ (c ++ d) = (a ^^^ c) ++ (b ^^^ d) := by
  ext i hi
  simp only [BitVec.getElem_xor, BitVec.getElem_append]
  split <;> rfl

@[simp]
theorem bytesToKey_keyToBytes (k : AesKey) :
    bytesToKey (keyToBytes k) = k := by
  dsimp only [bytesToKey, keyToBytes, toLEBytes, List.ofFn, Fin.foldr, Fin.foldr.loop,
    List.foldr, BitVec.zeroExtend]
  rw [shiftLeft8_or_setWidth_zero 256]
  repeat rw [shiftLeft8_or_setWidth_step]
  rw [BitVec.setWidth_eq]
  rw [extractLsb'_append_eq k 248 240 8 8 rfl]
  rw [extractLsb'_append_eq k 240 232 16 8 rfl]
  rw [extractLsb'_append_eq k 232 224 24 8 rfl]
  rw [extractLsb'_append_eq k 224 216 32 8 rfl]
  rw [extractLsb'_append_eq k 216 208 40 8 rfl]
  rw [extractLsb'_append_eq k 208 200 48 8 rfl]
  rw [extractLsb'_append_eq k 200 192 56 8 rfl]
  rw [extractLsb'_append_eq k 192 184 64 8 rfl]
  rw [extractLsb'_append_eq k 184 176 72 8 rfl]
  rw [extractLsb'_append_eq k 176 168 80 8 rfl]
  rw [extractLsb'_append_eq k 168 160 88 8 rfl]
  rw [extractLsb'_append_eq k 160 152 96 8 rfl]
  rw [extractLsb'_append_eq k 152 144 104 8 rfl]
  rw [extractLsb'_append_eq k 144 136 112 8 rfl]
  rw [extractLsb'_append_eq k 136 128 120 8 rfl]
  rw [extractLsb'_append_eq k 128 120 128 8 rfl]
  rw [extractLsb'_append_eq k 120 112 136 8 rfl]
  rw [extractLsb'_append_eq k 112 104 144 8 rfl]
  rw [extractLsb'_append_eq k 104 96 152 8 rfl]
  rw [extractLsb'_append_eq k 96 88 160 8 rfl]
  rw [extractLsb'_append_eq k 88 80 168 8 rfl]
  rw [extractLsb'_append_eq k 80 72 176 8 rfl]
  rw [extractLsb'_append_eq k 72 64 184 8 rfl]
  rw [extractLsb'_append_eq k 64 56 192 8 rfl]
  rw [extractLsb'_append_eq k 56 48 200 8 rfl]
  rw [extractLsb'_append_eq k 48 40 208 8 rfl]
  rw [extractLsb'_append_eq k 40 32 216 8 rfl]
  rw [extractLsb'_append_eq k 32 24 224 8 rfl]
  rw [extractLsb'_append_eq k 24 16 232 8 rfl]
  rw [extractLsb'_append_eq k 16 8 240 8 rfl]
  rw [extractLsb'_append_eq k 8 0 248 8 rfl]
  exact extractLsb'_zero_self k

@[simp]
theorem bytesToBlock_blockToBytes (b : Block) :
    bytesToBlock (blockToBytes b) = b := by
  dsimp only [bytesToBlock, blockToBytes, toLEBytes, List.ofFn, Fin.foldr, Fin.foldr.loop,
    List.foldr, BitVec.zeroExtend]
  rw [shiftLeft8_or_setWidth_zero 128]
  repeat rw [shiftLeft8_or_setWidth_step]
  rw [BitVec.setWidth_eq]
  rw [extractLsb'_append_eq b 120 112 8 8 rfl]
  rw [extractLsb'_append_eq b 112 104 16 8 rfl]
  rw [extractLsb'_append_eq b 104 96 24 8 rfl]
  rw [extractLsb'_append_eq b 96 88 32 8 rfl]
  rw [extractLsb'_append_eq b 88 80 40 8 rfl]
  rw [extractLsb'_append_eq b 80 72 48 8 rfl]
  rw [extractLsb'_append_eq b 72 64 56 8 rfl]
  rw [extractLsb'_append_eq b 64 56 64 8 rfl]
  rw [extractLsb'_append_eq b 56 48 72 8 rfl]
  rw [extractLsb'_append_eq b 48 40 80 8 rfl]
  rw [extractLsb'_append_eq b 40 32 88 8 rfl]
  rw [extractLsb'_append_eq b 32 24 96 8 rfl]
  rw [extractLsb'_append_eq b 24 16 104 8 rfl]
  rw [extractLsb'_append_eq b 16 8 112 8 rfl]
  rw [extractLsb'_append_eq b 8 0 120 8 rfl]
  exact extractLsb'_zero_self b

theorem bytesToBlock_16_eq
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] =
      b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++
      b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 := by
  dsimp only [bytesToBlock, List.foldr, BitVec.zeroExtend]
  rw [shiftLeft8_or_setWidth_zero 128]
  repeat rw [shiftLeft8_or_setWidth_step]
  exact BitVec.setWidth_eq _

@[simp] theorem bytesToBlock_extractLsb'_0
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).extractLsb' 0 8 = b0 := by
  rw [bytesToBlock_16_eq]
  exact extractLsb'_zero_append8 _ _

@[simp] theorem bytesToBlock_extractLsb'_8
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).extractLsb' 8 8 = b1 := by
  rw [bytesToBlock_16_eq]
  simp (disch := decide) only [extractLsb'_append8_of_ge, Nat.reduceSub, extractLsb'_zero_append8]

@[simp] theorem bytesToBlock_extractLsb'_16
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).extractLsb' 16 8 = b2 := by
  rw [bytesToBlock_16_eq]
  simp (disch := decide) only [extractLsb'_append8_of_ge, Nat.reduceSub, extractLsb'_zero_append8]

@[simp] theorem bytesToBlock_extractLsb'_24
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).extractLsb' 24 8 = b3 := by
  rw [bytesToBlock_16_eq]
  simp (disch := decide) only [extractLsb'_append8_of_ge, Nat.reduceSub, extractLsb'_zero_append8]

@[simp] theorem bytesToBlock_extractLsb'_32
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).extractLsb' 32 8 = b4 := by
  rw [bytesToBlock_16_eq]
  simp (disch := decide) only [extractLsb'_append8_of_ge, Nat.reduceSub, extractLsb'_zero_append8]

@[simp] theorem bytesToBlock_extractLsb'_40
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).extractLsb' 40 8 = b5 := by
  rw [bytesToBlock_16_eq]
  simp (disch := decide) only [extractLsb'_append8_of_ge, Nat.reduceSub, extractLsb'_zero_append8]

@[simp] theorem bytesToBlock_extractLsb'_48
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).extractLsb' 48 8 = b6 := by
  rw [bytesToBlock_16_eq]
  simp (disch := decide) only [extractLsb'_append8_of_ge, Nat.reduceSub, extractLsb'_zero_append8]

@[simp] theorem bytesToBlock_extractLsb'_56
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).extractLsb' 56 8 = b7 := by
  rw [bytesToBlock_16_eq]
  simp (disch := decide) only [extractLsb'_append8_of_ge, Nat.reduceSub, extractLsb'_zero_append8]

@[simp] theorem bytesToBlock_extractLsb'_64
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).extractLsb' 64 8 = b8 := by
  rw [bytesToBlock_16_eq]
  simp (disch := decide) only [extractLsb'_append8_of_ge, Nat.reduceSub, extractLsb'_zero_append8]

@[simp] theorem bytesToBlock_extractLsb'_72
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).extractLsb' 72 8 = b9 := by
  rw [bytesToBlock_16_eq]
  simp (disch := decide) only [extractLsb'_append8_of_ge, Nat.reduceSub, extractLsb'_zero_append8]

@[simp] theorem bytesToBlock_extractLsb'_80
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).extractLsb' 80 8 = b10 := by
  rw [bytesToBlock_16_eq]
  simp (disch := decide) only [extractLsb'_append8_of_ge, Nat.reduceSub, extractLsb'_zero_append8]

@[simp] theorem bytesToBlock_extractLsb'_88
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).extractLsb' 88 8 = b11 := by
  rw [bytesToBlock_16_eq]
  simp (disch := decide) only [extractLsb'_append8_of_ge, Nat.reduceSub, extractLsb'_zero_append8]

@[simp] theorem bytesToBlock_extractLsb'_96
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).extractLsb' 96 8 = b12 := by
  rw [bytesToBlock_16_eq]
  simp (disch := decide) only [extractLsb'_append8_of_ge, Nat.reduceSub, extractLsb'_zero_append8]

@[simp] theorem bytesToBlock_extractLsb'_104
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).extractLsb' 104 8 = b13 := by
  rw [bytesToBlock_16_eq]
  simp (disch := decide) only [extractLsb'_append8_of_ge, Nat.reduceSub, extractLsb'_zero_append8]

@[simp] theorem bytesToBlock_extractLsb'_112
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).extractLsb' 112 8 = b14 := by
  rw [bytesToBlock_16_eq]
  simp (disch := decide) only [extractLsb'_append8_of_ge, Nat.reduceSub, extractLsb'_zero_append8]

@[simp] theorem bytesToBlock_extractLsb'_120
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).extractLsb' 120 8 = b15 := by
  rw [bytesToBlock_16_eq]
  simp (disch := decide) only [extractLsb'_append8_of_ge, Nat.reduceSub, extractLsb'_zero_self8]

@[simp]
theorem blockToBytes_bytesToBlock_16
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    blockToBytes (bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]) =
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] := by
  rw [blockToBytes_eq_list]
  simp

theorem eq_list_16_of_length {α : Type} (bs : List α) (h : bs.length = 16) :
    bs = [bs[0], bs[1], bs[2], bs[3], bs[4], bs[5], bs[6], bs[7],
          bs[8], bs[9], bs[10], bs[11], bs[12], bs[13], bs[14], bs[15]] := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals (first | rfl | (simp at h))

theorem blockToBytes_bytesToBlock (bs : List (BitVec 8)) (h : bs.length = 16) :
    blockToBytes (bytesToBlock bs) = bs := by
  rw [eq_list_16_of_length bs h]
  exact blockToBytes_bytesToBlock_16 ..

theorem bytesToBlock_xor_16
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
     y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : BitVec 8) :
    bytesToBlock [x0 ^^^ y0, x1 ^^^ y1, x2 ^^^ y2, x3 ^^^ y3,
                  x4 ^^^ y4, x5 ^^^ y5, x6 ^^^ y6, x7 ^^^ y7,
                  x8 ^^^ y8, x9 ^^^ y9, x10 ^^^ y10, x11 ^^^ y11,
                  x12 ^^^ y12, x13 ^^^ y13, x14 ^^^ y14, x15 ^^^ y15] =
      bytesToBlock [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] ^^^
      bytesToBlock [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15] := by
  rw [bytesToBlock_16_eq, bytesToBlock_16_eq, bytesToBlock_16_eq]
  repeat rw [← xor_append_distrib]

theorem bytesToBlock_zipWith_xor (xs ys : List (BitVec 8))
    (hx : xs.length = 16) (hy : ys.length = 16) :
    bytesToBlock (List.zipWith (· ^^^ ·) xs ys) = bytesToBlock xs ^^^ bytesToBlock ys := by
  rw [eq_list_16_of_length xs hx, eq_list_16_of_length ys hy]
  exact bytesToBlock_xor_16 ..

theorem bytesToBlock_xor_extractLsb'
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : BitVec 8) (b : Block) :
    bytesToBlock [
      p0 ^^^ b.extractLsb' 0 8, p1 ^^^ b.extractLsb' 8 8,
      p2 ^^^ b.extractLsb' 16 8, p3 ^^^ b.extractLsb' 24 8,
      p4 ^^^ b.extractLsb' 32 8, p5 ^^^ b.extractLsb' 40 8,
      p6 ^^^ b.extractLsb' 48 8, p7 ^^^ b.extractLsb' 56 8,
      p8 ^^^ b.extractLsb' 64 8, p9 ^^^ b.extractLsb' 72 8,
      p10 ^^^ b.extractLsb' 80 8, p11 ^^^ b.extractLsb' 88 8,
      p12 ^^^ b.extractLsb' 96 8, p13 ^^^ b.extractLsb' 104 8,
      p14 ^^^ b.extractLsb' 112 8, p15 ^^^ b.extractLsb' 120 8
    ] = bytesToBlock [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ^^^ b := by
  rw [bytesToBlock_xor_16, ← blockToBytes_eq_list, bytesToBlock_blockToBytes]

theorem bytesToBlock_extractLsb'_xor
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : BitVec 8) (b : Block) :
    bytesToBlock [
      b.extractLsb' 0 8 ^^^ p0, b.extractLsb' 8 8 ^^^ p1,
      b.extractLsb' 16 8 ^^^ p2, b.extractLsb' 24 8 ^^^ p3,
      b.extractLsb' 32 8 ^^^ p4, b.extractLsb' 40 8 ^^^ p5,
      b.extractLsb' 48 8 ^^^ p6, b.extractLsb' 56 8 ^^^ p7,
      b.extractLsb' 64 8 ^^^ p8, b.extractLsb' 72 8 ^^^ p9,
      b.extractLsb' 80 8 ^^^ p10, b.extractLsb' 88 8 ^^^ p11,
      b.extractLsb' 96 8 ^^^ p12, b.extractLsb' 104 8 ^^^ p13,
      b.extractLsb' 112 8 ^^^ p14, b.extractLsb' 120 8 ^^^ p15
    ] = bytesToBlock [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ^^^ b := by
  rw [bytesToBlock_xor_16, ← blockToBytes_eq_list, bytesToBlock_blockToBytes, BitVec.xor_comm]

theorem bytesToBlock_extractLsb'_xor_extractLsb' (p b : Block) :
    bytesToBlock [
      p.extractLsb' 0 8 ^^^ b.extractLsb' 0 8, p.extractLsb' 8 8 ^^^ b.extractLsb' 8 8,
      p.extractLsb' 16 8 ^^^ b.extractLsb' 16 8, p.extractLsb' 24 8 ^^^ b.extractLsb' 24 8,
      p.extractLsb' 32 8 ^^^ b.extractLsb' 32 8, p.extractLsb' 40 8 ^^^ b.extractLsb' 40 8,
      p.extractLsb' 48 8 ^^^ b.extractLsb' 48 8, p.extractLsb' 56 8 ^^^ b.extractLsb' 56 8,
      p.extractLsb' 64 8 ^^^ b.extractLsb' 64 8, p.extractLsb' 72 8 ^^^ b.extractLsb' 72 8,
      p.extractLsb' 80 8 ^^^ b.extractLsb' 80 8, p.extractLsb' 88 8 ^^^ b.extractLsb' 88 8,
      p.extractLsb' 96 8 ^^^ b.extractLsb' 96 8, p.extractLsb' 104 8 ^^^ b.extractLsb' 104 8,
      p.extractLsb' 112 8 ^^^ b.extractLsb' 112 8, p.extractLsb' 120 8 ^^^ b.extractLsb' 120 8
    ] = p ^^^ b := by
  rw [bytesToBlock_xor_extractLsb', ← blockToBytes_eq_list, bytesToBlock_blockToBytes]

@[simp]
theorem truncate8_zeroExtend_xor_32 (a b : BitVec 8) :
    (((a.zeroExtend 64 ^^^ b.zeroExtend 64).truncate 32).zeroExtend 64).truncate 8 = a ^^^ b := by
  bv_kernel

@[simp]
theorem truncate8_zeroExtend_xor_64 (a b : BitVec 8) :
    (a.zeroExtend 64 ^^^ b.zeroExtend 64).truncate 8 = a ^^^ b := by
  bv_kernel

/-! ## `Memory.readBytes` and `Memory.writeBytes` Lemmas -/

@[simp]
theorem write8_write8_same (m : Memory) (a : BitVec 64) (x y : BitVec 8) :
    (m.write8 a x).write8 a y = m.write8 a y :=
  Memory.write8_write8_same m a x y

theorem write8_write8_comm (m : Memory) (a₁ a₂ : BitVec 64) (v₁ v₂ : BitVec 8) (hne : a₁ ≠ a₂) :
    (m.write8 a₁ v₁).write8 a₂ v₂ = (m.write8 a₂ v₂).write8 a₁ v₁ :=
  Memory.write8_write8_comm m a₁ a₂ v₁ v₂ hne

theorem writeBytes_append (m : Memory) (a : BitVec 64) (xs ys : List (BitVec 8)) :
    m.writeBytes a (xs ++ ys) =
      (m.writeBytes a xs).writeBytes (a + BitVec.ofNat 64 xs.length) ys := by
  induction xs generalizing m a with
  | nil => simp [Memory.writeBytes]
  | cons x xs ih =>
    have hadd : a + 1#64 + BitVec.ofNat 64 xs.length = a + BitVec.ofNat 64 (xs.length + 1) := by
      bv_omega
    simp only [List.cons_append, List.length_cons, Memory.writeBytes, ih, hadd]

theorem readBytes_add (m : Memory) (a : BitVec 64) (n k : ℕ) :
    m.readBytes a (n + k) = m.readBytes a n ++ m.readBytes (a + BitVec.ofNat 64 n) k := by
  induction n generalizing a with
  | zero => simp [Memory.readBytes]
  | succ n ih =>
    have hadd : a + 1#64 + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (n + 1) := by bv_omega
    simp only [Nat.succ_add, Memory.readBytes, List.cons_append, ih (a + 1#64), hadd]

theorem read8_writeBytes_outside (m : Memory) (addr a : BitVec 64) (bs : List (BitVec 8))
    (h : OutsideRegion addr bs.length a) :
    (m.writeBytes addr bs).read8 a = m.read8 a := by
  induction bs generalizing m addr with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons, OutsideRegion] at h
    have hne : a ≠ addr := by bv_omega
    have hout : OutsideRegion (addr + 1#64) rest.length a := by
      unfold OutsideRegion; bv_omega
    simp only [Memory.writeBytes]
    rw [ih _ _ hout, Memory.read8_write8_ne hne]

theorem read8_writeBytes_inbounds (m : Memory) (addr : BitVec 64) (bs : List (BitVec 8))
    (i : ℕ) (hi : i < bs.length) (hwrap : bs.length ≤ 2 ^ 64) :
    (m.writeBytes addr bs).read8 (addr + BitVec.ofNat 64 i) = bs[i] := by
  induction bs generalizing m addr i with
  | nil => simp at hi
  | cons b rest ih =>
    simp only [List.length_cons] at hi hwrap
    cases i with
    | zero =>
      simp only [BitVec.add_zero, List.getElem_cons_zero, Memory.writeBytes]
      rw [read8_writeBytes_outside]
      · exact Memory.read8_write8_same m addr b
      · unfold OutsideRegion; bv_omega
    | succ j =>
      have hadd : addr + BitVec.ofNat 64 (j + 1) = (addr + 1#64) + BitVec.ofNat 64 j := by
        bv_omega
      simp only [Memory.writeBytes, List.getElem_cons_succ, hadd]
      exact ih (m.write8 addr b) (addr + 1#64) j (by omega) (by omega)

theorem readBytes_writeBytes_same (m : Memory) (addr : BitVec 64) (bs : List (BitVec 8))
    (hwrap : bs.length ≤ 2 ^ 64) :
    (m.writeBytes addr bs).readBytes addr bs.length = bs := by
  induction bs generalizing m addr with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons] at hwrap
    simp only [List.length_cons, Memory.writeBytes, Memory.readBytes_succ, List.cons.injEq]
    refine ⟨?_, ih (m.write8 addr b) (addr + 1#64) (by omega)⟩
    have h0 := read8_writeBytes_outside (m.write8 addr b) (addr + 1#64) addr rest
      (by unfold OutsideRegion; bv_omega)
    rw [h0, Memory.read8_write8_same]

theorem readBytes_writeBytes_eq (m : Memory) (addr : BitVec 64) (bs : List (BitVec 8))
    (h : addr.toNat + bs.length ≤ 2 ^ 64) :
    (m.writeBytes addr bs).readBytes addr bs.length = bs :=
  readBytes_writeBytes_same m addr bs (by omega)

theorem readBytes_slice_of_readBytes_eq (m : Memory) (addr : BitVec 64) (bs : List (BitVec 8))
    (h : m.readBytes addr bs.length = bs) (off len : ℕ) (hle : off + len ≤ bs.length) :
    m.readBytes (addr + BitVec.ofNat 64 off) len = (bs.drop off).take len := by
  have hsplit : bs.length = off + (len + (bs.length - (off + len))) := by omega
  have hb := h
  rw [hsplit, readBytes_add, readBytes_add] at hb
  rw [← hb]
  rw [List.drop_left' (Memory.readBytes_length m addr off)]
  rw [List.take_left' (Memory.readBytes_length m (addr + BitVec.ofNat 64 off) len)]

theorem readBytes_writeBytes_slice (m : Memory) (addr : BitVec 64) (bs : List (BitVec 8))
    (off len : ℕ) (hle : off + len ≤ bs.length) (hwrap : bs.length ≤ 2 ^ 64) :
    (m.writeBytes addr bs).readBytes (addr + BitVec.ofNat 64 off) len =
      (bs.drop off).take len :=
  readBytes_slice_of_readBytes_eq (m.writeBytes addr bs) addr bs
    (readBytes_writeBytes_same m addr bs hwrap) off len hle

theorem readBytes_writeBytes_take (m : Memory) (addr : BitVec 64) (bs : List (BitVec 8))
    (len : ℕ) (hle : len ≤ bs.length) (hwrap : bs.length ≤ 2 ^ 64) :
    (m.writeBytes addr bs).readBytes addr len = bs.take len := by
  have h := readBytes_writeBytes_slice m addr bs 0 len (by omega) hwrap
  simpa using h

theorem readBytes_writeBytes_prefix (m : Memory) (addr : BitVec 64) (bs1 bs2 : List (BitVec 8))
    (hwrap : bs1.length + bs2.length ≤ 2 ^ 64) :
    (m.writeBytes addr (bs1 ++ bs2)).readBytes addr bs1.length = bs1 := by
  rw [readBytes_writeBytes_take m addr (bs1 ++ bs2) bs1.length (by simp) (by simpa using hwrap)]
  exact List.take_left

theorem agreesOutside_writeBytes (m : Memory) (addr : BitVec 64) (bs : List (BitVec 8)) :
    AgreesOutside m (m.writeBytes addr bs) addr bs.length :=
  ProofLib.agreesOutside_writeBytes m addr bs

theorem AgreesOutside.writeBytes {m₁ m₂ : Memory} {base : BitVec 64} {len : ℕ}
    {b : BitVec 64} {bs : List (BitVec 8)}
    (h : AgreesOutside m₁ m₂ base len)
    (hb : (b - base).toNat + bs.length ≤ len) (_hlen : len ≤ 2 ^ 64) :
    AgreesOutside m₁ (m₂.writeBytes b bs) base len :=
  ProofLib.AgreesOutside.writeBytes bs h hb

theorem readBytes_writeBytes_disjoint (m : Memory) (a1 : BitVec 64) (n1 : ℕ)
    (a2 : BitVec 64) (bs : List (BitVec 8))
    (hd : DisjointRegions a1 n1 a2 bs.length) :
    (m.writeBytes a2 bs).readBytes a1 n1 = m.readBytes a1 n1 :=
  (agreesOutside_writeBytes m a2 bs).readBytes_eq hd.symm (by have := hd.1; bv_omega)

theorem readBytes_writeBytes_disjoint' (m : Memory) (a1 : BitVec 64) (n1 : ℕ)
    (a2 : BitVec 64) (bs : List (BitVec 8))
    (hd : DisjointRegions a2 bs.length a1 n1) :
    (m.writeBytes a2 bs).readBytes a1 n1 = m.readBytes a1 n1 :=
  readBytes_writeBytes_disjoint m a1 n1 a2 bs hd.symm

theorem read64_writeBytes_disjoint (m : Memory) (a1 a2 : BitVec 64) (bs : List (BitVec 8))
    (hd : DisjointRegions a1 8 a2 bs.length) :
    (m.writeBytes a2 bs).read64 a1 = m.read64 a1 :=
  (agreesOutside_writeBytes m a2 bs).read64_eq hd.symm

theorem read128_writeBytes_disjoint (m : Memory) (a1 a2 : BitVec 64) (bs : List (BitVec 8))
    (hd : DisjointRegions a1 16 a2 bs.length) :
    (m.writeBytes a2 bs).read128 a1 = m.read128 a1 :=
  (agreesOutside_writeBytes m a2 bs).read128_eq hd.symm

theorem write8_writeBytes_comm (m : Memory) (a : BitVec 64) (v : BitVec 8)
    (base : BitVec 64) (bs : List (BitVec 8)) (hout : OutsideRegion base bs.length a) :
    (m.writeBytes base bs).write8 a v = (m.write8 a v).writeBytes base bs := by
  induction bs generalizing m base with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons, OutsideRegion] at hout
    have hne : base ≠ a := by bv_omega
    have hout' : OutsideRegion (base + 1#64) rest.length a := by
      unfold OutsideRegion; bv_omega
    simp only [Memory.writeBytes]
    rw [ih (m.write8 base b) (base + 1#64) hout', write8_write8_comm m base a b v hne]

theorem writeBytes_writeBytes_overwrite (m : Memory) (addr : BitVec 64)
    (bs1 bs2 : List (BitVec 8)) (hwrap : bs1.length ≤ 2 ^ 64) :
    (m.writeBytes addr bs1).writeBytes addr bs2 =
      m.writeBytes addr (bs2 ++ bs1.drop bs2.length) := by
  induction bs2 generalizing m addr bs1 with
  | nil => simp [Memory.writeBytes]
  | cons b2 rest2 ih =>
    cases bs1 with
    | nil => simp [Memory.writeBytes]
    | cons b1 rest1 =>
      simp only [List.length_cons] at hwrap
      simp only [Memory.writeBytes, List.cons_append, List.length_cons, List.drop_succ_cons]
      rw [write8_writeBytes_comm (m.write8 addr b1) addr b2 (addr + 1#64) rest1
            (by unfold OutsideRegion; bv_omega)]
      rw [write8_write8_same]
      exact ih (m.write8 addr b2) (addr + 1#64) rest1 (by omega)

theorem writeBytes_writeBytes_same (m : Memory) (addr : BitVec 64)
    (bs1 bs2 : List (BitVec 8)) (hle : bs1.length ≤ bs2.length) (hwrap : bs1.length ≤ 2 ^ 64) :
    (m.writeBytes addr bs1).writeBytes addr bs2 = m.writeBytes addr bs2 := by
  rw [writeBytes_writeBytes_overwrite m addr bs1 bs2 hwrap,
      List.drop_eq_nil_of_le hle, List.append_nil]

/-! ### 8 / 32 / 64 / 128-bit Load/Store and `readBytes` / `writeBytes` Bridges -/

theorem readBytes_8_eq (m : Memory) (a : BitVec 64) :
    m.readBytes a 8 =
      [m.read8 a, m.read8 (a + 1#64), m.read8 (a + 2#64), m.read8 (a + 3#64),
       m.read8 (a + 4#64), m.read8 (a + 5#64), m.read8 (a + 6#64), m.read8 (a + 7#64)] := by
  simp only [Memory.readBytes, BitVec.add_assoc]
  rfl

theorem readBytes_16_eq (m : Memory) (a : BitVec 64) :
    m.readBytes a 16 =
      [m.read8 a, m.read8 (a + 1#64), m.read8 (a + 2#64), m.read8 (a + 3#64),
       m.read8 (a + 4#64), m.read8 (a + 5#64), m.read8 (a + 6#64), m.read8 (a + 7#64),
       m.read8 (a + 8#64), m.read8 (a + 9#64), m.read8 (a + 10#64), m.read8 (a + 11#64),
       m.read8 (a + 12#64), m.read8 (a + 13#64), m.read8 (a + 14#64), m.read8 (a + 15#64)] := by
  simp only [Memory.readBytes, BitVec.add_assoc]
  rfl

theorem write8_16_eq_writeBytes (m : Memory) (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (((((((((((((((m.write8 a b0).write8 (a + 1#64) b1).write8 (a + 2#64) b2).write8
      (a + 3#64) b3).write8 (a + 4#64) b4).write8 (a + 5#64) b5).write8
      (a + 6#64) b6).write8 (a + 7#64) b7).write8 (a + 8#64) b8).write8
      (a + 9#64) b9).write8 (a + 10#64) b10).write8 (a + 11#64) b11).write8
      (a + 12#64) b12).write8 (a + 13#64) b13).write8 (a + 14#64) b14).write8
      (a + 15#64) b15 =
      m.writeBytes a [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] := by
  simp only [Memory.writeBytes, BitVec.add_assoc]
  rfl

@[simp]
theorem readBytes_write8_16 (m : Memory) (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    ((((((((((((((((m.write8 a b0).write8 (a + 1#64) b1).write8 (a + 2#64) b2).write8
      (a + 3#64) b3).write8 (a + 4#64) b4).write8 (a + 5#64) b5).write8
      (a + 6#64) b6).write8 (a + 7#64) b7).write8 (a + 8#64) b8).write8
      (a + 9#64) b9).write8 (a + 10#64) b10).write8 (a + 11#64) b11).write8
      (a + 12#64) b12).write8 (a + 13#64) b13).write8 (a + 14#64) b14).write8
      (a + 15#64) b15).readBytes a 16 =
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] := by
  rw [write8_16_eq_writeBytes]
  exact readBytes_writeBytes_same m a _ (by simp)

@[simp]
theorem readBytes_getElem (m : Memory) (a : BitVec 64) (n i : ℕ)
    (hi : i < (m.readBytes a n).length) :
    (m.readBytes a n)[i] = m.read8 (a + BitVec.ofNat 64 i) := by
  induction n generalizing a i with
  | zero => simp [Memory.readBytes] at hi
  | succ n ih =>
    cases i with
    | zero => simp [Memory.readBytes]
    | succ j =>
      have hadd : a + 1#64 + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (j + 1) := by bv_omega
      simp only [Memory.readBytes, List.getElem_cons_succ]
      rw [ih (a + 1#64) j (by simpa [Memory.readBytes] using hi), hadd]

theorem write32_eq_writeBytes (m : Memory) (a : BitVec 64) (v : BitVec 32) :
    m.write32 a v = m.writeBytes a (toLEBytes 4 v) := by
  rw [toLEBytes_4_eq_list]
  simp only [Memory.write32, Memory.writeBytes, BitVec.add_zero, BitVec.add_assoc]
  rfl

theorem write64_eq_writeBytes (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    m.write64 a v = m.writeBytes a (toLEBytes 8 v) := by
  rw [toLEBytes_8_eq_list]
  simp only [Memory.write64, Memory.writeBytes, BitVec.add_zero, BitVec.add_assoc]
  rfl

private theorem extractLsb'_extractLsb'_of_le_gen {w : ℕ} (v : BitVec w) (s1 l1 s2 l2 s3 : ℕ)
    (h1 : s1 + s2 = s3) (h2 : s2 + l2 ≤ l1) :
    (v.extractLsb' s1 l1).extractLsb' s2 l2 = v.extractLsb' s3 l2 := by
  ext i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb']
  rw [decide_eq_true (by omega), Bool.true_and]
  congr 1
  omega

theorem toLEBytes_8_extractLsb'_append (v : BitVec 128) :
    toLEBytes 8 (v.extractLsb' 0 64) ++ toLEBytes 8 (v.extractLsb' 64 64) =
      blockToBytes v := by
  rw [toLEBytes_8_eq_list, toLEBytes_8_eq_list, blockToBytes_eq_list]
  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
  refine ⟨extractLsb'_extractLsb'_of_le_gen v _ 64 _ 8 _ rfl (by decide),
          extractLsb'_extractLsb'_of_le_gen v _ 64 _ 8 _ rfl (by decide),
          extractLsb'_extractLsb'_of_le_gen v _ 64 _ 8 _ rfl (by decide),
          extractLsb'_extractLsb'_of_le_gen v _ 64 _ 8 _ rfl (by decide),
          extractLsb'_extractLsb'_of_le_gen v _ 64 _ 8 _ rfl (by decide),
          extractLsb'_extractLsb'_of_le_gen v _ 64 _ 8 _ rfl (by decide),
          extractLsb'_extractLsb'_of_le_gen v _ 64 _ 8 _ rfl (by decide),
          extractLsb'_extractLsb'_of_le_gen v _ 64 _ 8 _ rfl (by decide),
          extractLsb'_extractLsb'_of_le_gen v _ 64 _ 8 _ rfl (by decide),
          extractLsb'_extractLsb'_of_le_gen v _ 64 _ 8 _ rfl (by decide),
          extractLsb'_extractLsb'_of_le_gen v _ 64 _ 8 _ rfl (by decide),
          extractLsb'_extractLsb'_of_le_gen v _ 64 _ 8 _ rfl (by decide),
          extractLsb'_extractLsb'_of_le_gen v _ 64 _ 8 _ rfl (by decide),
          extractLsb'_extractLsb'_of_le_gen v _ 64 _ 8 _ rfl (by decide),
          extractLsb'_extractLsb'_of_le_gen v _ 64 _ 8 _ rfl (by decide),
          extractLsb'_extractLsb'_of_le_gen v _ 64 _ 8 _ rfl (by decide)⟩

theorem write128_eq_writeBytes (m : Memory) (a : BitVec 64) (v : BitVec 128) :
    m.write128 a v = m.writeBytes a (blockToBytes v) := by
  simp only [Memory.write128]
  rw [write64_eq_writeBytes, write64_eq_writeBytes]
  have hlen : (toLEBytes 8 (v.extractLsb' 0 64)).length = 8 := toLEBytes_length 8 _
  rw [← toLEBytes_8_extractLsb'_append v, writeBytes_append, hlen]

private theorem append_step_8 {w v : ℕ} (x : BitVec w) (y : BitVec v) (z : BitVec 8) (i : ℕ) :
    (x ++ (y ++ z)).getLsbD i = (x ++ y ++ z).getLsbD i := by
  simp only [BitVec.getLsbD_append]
  by_cases h1 : i < 8
  · have h2 : i < v + 8 := by omega
    simp [h1, h2]
  · by_cases h2 : i < v + 8
    · have h3 : i - 8 < v := by omega
      simp [h1, h2, h3]
    · have h3 : ¬ (i - 8 < v) := by omega
      have h4 : i - (v + 8) = i - 8 - v := by omega
      simp [h1, h2, h3, h4]

private theorem getLsbD_append_congr {w : ℕ} {a b : BitVec w} (c : BitVec 8) (i : ℕ)
    (h : a.getLsbD (i - 8) = b.getLsbD (i - 8)) :
    (a ++ c).getLsbD i = (b ++ c).getLsbD i := by
  simp only [BitVec.getLsbD_append, h]

private theorem append_read64_assoc
    (x : BitVec 64) (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    x ++ (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) =
      x ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  repeat (rw [append_step_8]; apply getLsbD_append_congr)
  exact append_step_8 x b7 b6 _

theorem read128_eq_bytesToBlock_readBytes (m : Memory) (a : BitVec 64) :
    m.read128 a = bytesToBlock (m.readBytes a 16) := by
  rw [readBytes_16_eq, bytesToBlock_16_eq]
  dsimp only [Memory.read128, Memory.read64]
  simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
  exact append_read64_assoc ..

@[simp]
theorem blockToBytes_read128 (m : Memory) (a : BitVec 64) :
    blockToBytes (m.read128 a) = m.readBytes a 16 := by
  rw [read128_eq_bytesToBlock_readBytes, blockToBytes_bytesToBlock _ (Memory.readBytes_length m a 16)]

theorem write128_read128_eq_writeBytes (m : Memory) (dst src : BitVec 64) :
    m.write128 dst (m.read128 src) = m.writeBytes dst (m.readBytes src 16) := by
  rw [write128_eq_writeBytes, blockToBytes_read128]

@[simp]
theorem readBytes_write128 (m : Memory) (a : BitVec 64) (v : BitVec 128) :
    (m.write128 a v).readBytes a 16 = blockToBytes v := by
  rw [write128_eq_writeBytes]
  exact readBytes_writeBytes_same m a (blockToBytes v) (by simp)

@[simp]
theorem readBytes_write128_read128 (m : Memory) (dst src : BitVec 64) :
    (m.write128 dst (m.read128 src)).readBytes dst 16 = m.readBytes src 16 := by
  rw [readBytes_write128, blockToBytes_read128]

@[simp]
theorem read64_writeBytes_toLEBytes (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    (m.writeBytes a (toLEBytes 8 v)).read64 a = v := by
  rw [← write64_eq_writeBytes, Memory.read64_write64_same]

@[simp]
theorem read128_writeBytes_blockToBytes (m : Memory) (a : BitVec 64) (v : Block) :
    (m.writeBytes a (blockToBytes v)).read128 a = v := by
  have h := readBytes_writeBytes_same m a (blockToBytes v) (by simp)
  simp only [blockToBytes_length] at h
  rw [read128_eq_bytesToBlock_readBytes, h, bytesToBlock_blockToBytes]

end CryptoVerification.LibsignalAesCbc.Run.Bytes

namespace CryptoVerification.LibsignalAesCbc.Run.Layout

open Arm64 ProofLib

theorem readBytes_writeBytes (m : Memory) (a : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length ≤ 2 ^ 64) :
    (m.writeBytes a bs).readBytes a bs.length = bs := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons] at hlen ⊢
    rw [Memory.writeBytes_cons, Memory.readBytes_succ]
    have hout : OutsideRegion (a + 1#64) bs.length a := by
      simp only [OutsideRegion]
      bv_omega
    rw [(agreesOutside_writeBytes (m.write8 a b) (a + 1#64) bs).read8_eq hout,
      Memory.read8_write8_same, ih (m.write8 a b) (a + 1#64) (by omega)]

theorem readBytes_writeBytes_eq (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) (n : ℕ)
    (hn : bs.length = n) (hlen : n ≤ 2 ^ 64) :
    (m.writeBytes a bs).readBytes a n = bs := by
  subst hn; exact readBytes_writeBytes m a bs hlen

theorem readBytes_writeBytes_of_disjoint (m : Memory) (a : BitVec 64) (bs : List (BitVec 8))
    (b : BitVec 64) (n : ℕ) (hd : DisjointRegions a bs.length b n) (hn : n ≤ 2 ^ 64) :
    (m.writeBytes a bs).readBytes b n = m.readBytes b n :=
  (agreesOutside_writeBytes m a bs).readBytes_eq hd hn

end CryptoVerification.LibsignalAesCbc.Run.Layout
