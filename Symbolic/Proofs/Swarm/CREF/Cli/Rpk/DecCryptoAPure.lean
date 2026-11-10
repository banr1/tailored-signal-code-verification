/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Hooks2.BridgeXPure
import Symbolic.Proofs.Refinement.LemmasPure

/-!
# Byte-Encoding, HKDF, and Scalar-Clamping Lemmas for Session Decrypt

Proves round-trip identities between byte lists and fixed-width keys and blocks (`bytesToKey32`,
`keyToBytes32`, `CBC.bytesToBlock`), the 64-byte `hkdf` two-block expansion for
`whisperRatchetInfo`, scalar-clamping equivalences, and low-order X25519 rejection in
`rootCreateChain`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Proofs.libsignal.RngG.CliPure.DecCrypto

open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.CBC CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession
open CryptoVerification
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal DY.Libsignal.Rust
open DY.Libsignal.HwEvents
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement
open DY.Libsignal.Composed.Refinement (vec32)
open Proofs.libsignal.Hooks2 (cryptoOf' vec32_toList_of_length_32')

@[local simp] private theorem toBEBytes_length_pure (n : ℕ) (w : BitVec (8 * n)) :
    (ByteSpecs.toBEBytes n w).length = n := by
  simp [ByteSpecs.toBEBytes]

@[local simp] private theorem shaState_flatMap_length_pure (h : ByteSpecs.ShaState) :
    (h.toList.flatMap (ByteSpecs.toBEBytes 4)).length = 32 := by
  rcases h with ⟨l, hl⟩
  simp [List.length_flatMap, hl]

private theorem nck_length_hmacWith (F : ByteSpecs.ShaState → List (BitVec 8) → ByteSpecs.ShaState)
    (key msg : List (BitVec 8)) :
    (CryptoGames.HMAC.hmacWith F key msg).length = 32 := by
  unfold CryptoGames.HMAC.hmacWith CryptoGames.HMAC.sha256With
  exact shaState_flatMap_length_pure _

theorem vec32_toList_of_length_eq_32 (b : List (BitVec 8)) (hb : b.length = 32) :
    (vec32 b).toList = b :=
  vec32_toList_of_length_32' b hb

private theorem extractLsb'_zero_bytesToKey32_cons_dc (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons_dc (b : BitVec 8) (acc : BitVec 256) (j : Nat)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
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

private theorem extractLsb'_bytesToKey32_dc (bs : List (BitVec 8)) (j : Nat)
    (hj : j < bs.length) (h32 : j < 32) :
    (bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero => simpa [bytesToKey32] using extractLsb'_zero_bytesToKey32_cons_dc b (bytesToKey32 rest)
    | succ j =>
      have hcons : bytesToKey32 (b :: rest) = (bytesToKey32 rest <<< 8) ||| b.zeroExtend 256 := rfl
      rw [hcons, extractLsb'_succ_bytesToKey32_cons_dc b (bytesToKey32 rest) j h32, List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

theorem keyToBytes32_bytesToKey32_of_length_eq_32 (b : List (BitVec 8)) (hb : b.length = 32) :
    keyToBytes32 (bytesToKey32 b) = b := by
  refine List.ext_getElem (by simp [keyToBytes32, hb]) fun j h1 h2 => ?_
  simp only [keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32_dc b j h2 (by omega)

@[simp]
theorem length_keyToBytes32 (k : BitVec 256) :
    (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

private theorem extractLsb'_append_zero {w : Nat} (hi : BitVec w) (lo : BitVec 8) :
    (hi ++ lo).extractLsb' 0 8 = lo := by
  ext i hlt
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_append, hlt]

private theorem extractLsb'_append_add8 {w : Nat} (hi : BitVec w) (lo : BitVec 8) (s : Nat) :
    (hi ++ lo).extractLsb' (s + 8) 8 = hi.extractLsb' s 8 := by
  ext i hlt
  have hge : ¬ (s + 8 + i < 8) := by omega
  have hsub : s + 8 + i - 8 = s + i := by omega
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_append, hge, hsub]

private theorem extractLsb'_self_8 (x : BitVec 8) : x.extractLsb' 0 8 = x := by
  ext i hi; simp

private theorem extractLsb'_concat_adj {w : Nat} (v : BitVec w) (s₂ s₁ n₂ n₁ : Nat)
    (h : s₂ = s₁ + n₁) :
    v.extractLsb' s₂ n₂ ++ v.extractLsb' s₁ n₁ = v.extractLsb' s₁ (n₂ + n₁) := by
  subst h
  ext i hi
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
  split
  · rfl
  · congr 1; omega

theorem blockToBytesLE_bytesToBlock_of_length_eq_16 (b : List (BitVec 8)) (hb : b.length = 16) :
    CBC.blockToBytesLE (CBC.bytesToBlock b) = b := by
  rcases b with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at hb; done)
  have h0 (x : BitVec 8) : ((0 : BitVec 128) <<< 8) ||| x.setWidth 128 = x.setWidth 128 := by simp
  have hs {w : Nat} (x : BitVec w) (y : BitVec 8) :
      ((x.setWidth 128) <<< 8) ||| y.setWidth 128 = (x ++ y).setWidth 128 := by
    ext i hi
    simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getLsbD_append]
    by_cases h8 : i < 8
    · simp [h8]
    · simp [h8, BitVec.getLsbD_of_ge y i (by omega)]
  have hfold :
      CBC.bytesToBlock [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] =
        b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++
        b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 := by
    dsimp only [CBC.bytesToBlock, List.foldr, BitVec.zeroExtend]
    rw [h0]
    repeat rw [hs]
    exact BitVec.setWidth_eq _
  have hlist (v : CBC.Block) :
      CBC.blockToBytesLE v =
        [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
         v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8,
         v.extractLsb' 64 8, v.extractLsb' 72 8, v.extractLsb' 80 8, v.extractLsb' 88 8,
         v.extractLsb' 96 8, v.extractLsb' 104 8, v.extractLsb' 112 8, v.extractLsb' 120 8] := rfl
  rw [hfold, hlist]
  simp only [extractLsb'_append_add8, extractLsb'_append_zero, extractLsb'_self_8]

theorem bytesToKey32_keyToBytes32 (k : BitVec 256) :
    bytesToKey32 (keyToBytes32 k) = k := by
  have h0 (x : BitVec 8) : ((0 : BitVec 256) <<< 8) ||| x.setWidth 256 = x.setWidth 256 := by simp
  have hs {w : Nat} (x : BitVec w) (y : BitVec 8) :
      ((x.setWidth 256) <<< 8) ||| y.setWidth 256 = (x ++ y).setWidth 256 := by
    ext i hi
    simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getLsbD_append]
    by_cases h8 : i < 8
    · simp [h8]
    · simp [h8, BitVec.getLsbD_of_ge y i (by omega)]
  change bytesToKey32
    [k.extractLsb' 0 8, k.extractLsb' 8 8, k.extractLsb' 16 8, k.extractLsb' 24 8,
     k.extractLsb' 32 8, k.extractLsb' 40 8, k.extractLsb' 48 8, k.extractLsb' 56 8,
     k.extractLsb' 64 8, k.extractLsb' 72 8, k.extractLsb' 80 8, k.extractLsb' 88 8,
     k.extractLsb' 96 8, k.extractLsb' 104 8, k.extractLsb' 112 8, k.extractLsb' 120 8,
     k.extractLsb' 128 8, k.extractLsb' 136 8, k.extractLsb' 144 8, k.extractLsb' 152 8,
     k.extractLsb' 160 8, k.extractLsb' 168 8, k.extractLsb' 176 8, k.extractLsb' 184 8,
     k.extractLsb' 192 8, k.extractLsb' 200 8, k.extractLsb' 208 8, k.extractLsb' 216 8,
     k.extractLsb' 224 8, k.extractLsb' 232 8, k.extractLsb' 240 8, k.extractLsb' 248 8] = k
  dsimp only [bytesToKey32, List.foldr, BitVec.zeroExtend]
  rw [h0]
  repeat rw [hs]
  rw [BitVec.setWidth_eq]
  rw [extractLsb'_concat_adj k 248 240 _ 8 rfl, extractLsb'_concat_adj k 240 232 _ 8 rfl,
      extractLsb'_concat_adj k 232 224 _ 8 rfl, extractLsb'_concat_adj k 224 216 _ 8 rfl,
      extractLsb'_concat_adj k 216 208 _ 8 rfl, extractLsb'_concat_adj k 208 200 _ 8 rfl,
      extractLsb'_concat_adj k 200 192 _ 8 rfl, extractLsb'_concat_adj k 192 184 _ 8 rfl,
      extractLsb'_concat_adj k 184 176 _ 8 rfl, extractLsb'_concat_adj k 176 168 _ 8 rfl,
      extractLsb'_concat_adj k 168 160 _ 8 rfl, extractLsb'_concat_adj k 160 152 _ 8 rfl,
      extractLsb'_concat_adj k 152 144 _ 8 rfl, extractLsb'_concat_adj k 144 136 _ 8 rfl,
      extractLsb'_concat_adj k 136 128 _ 8 rfl, extractLsb'_concat_adj k 128 120 _ 8 rfl,
      extractLsb'_concat_adj k 120 112 _ 8 rfl, extractLsb'_concat_adj k 112 104 _ 8 rfl,
      extractLsb'_concat_adj k 104 96 _ 8 rfl, extractLsb'_concat_adj k 96 88 _ 8 rfl,
      extractLsb'_concat_adj k 88 80 _ 8 rfl, extractLsb'_concat_adj k 80 72 _ 8 rfl,
      extractLsb'_concat_adj k 72 64 _ 8 rfl, extractLsb'_concat_adj k 64 56 _ 8 rfl,
      extractLsb'_concat_adj k 56 48 _ 8 rfl, extractLsb'_concat_adj k 48 40 _ 8 rfl,
      extractLsb'_concat_adj k 40 32 _ 8 rfl, extractLsb'_concat_adj k 32 24 _ 8 rfl,
      extractLsb'_concat_adj k 24 16 _ 8 rfl, extractLsb'_concat_adj k 16 8 _ 8 rfl,
      extractLsb'_concat_adj k 8 0 _ 8 rfl]
  ext i hi; simp

theorem hkdf_64_whisperRatchet (F : ShaCompress) (salt : Salt) (ikm : List (BitVec 8)) :
    let prk := hkdfExtract F salt ikm
    let t1 := hmacWith F prk ([] ++ Ratchet.whisperRatchetInfo ++ [1#8])
    let t2 := hmacWith F prk (t1 ++ Ratchet.whisperRatchetInfo ++ [2#8])
    hkdf F salt ikm Ratchet.whisperRatchetInfo 64 = t1 ++ t2 ∧
    (hkdf F salt ikm Ratchet.whisperRatchetInfo 64).take 32 = t1 ∧
    ((hkdf F salt ikm Ratchet.whisperRatchetInfo 64).drop 32).take 32 = t2 := by
  intro prk t1 t2
  have h2 : (64 + 31) / 32 = 2 := rfl
  have hblocks : (hkdfBlocks F prk Ratchet.whisperRatchetInfo 2).flatten = t1 ++ t2 := by
    simp [hkdfBlocks, t1, t2, List.append_assoc]
  have ht1_len : t1.length = 32 := nck_length_hmacWith F _ _
  have ht2_len : t2.length = 32 := nck_length_hmacWith F _ _
  have h64 : hkdf F salt ikm Ratchet.whisperRatchetInfo 64 = t1 ++ t2 := by
    dsimp only [hkdf, hkdfExpand]
    rw [h2, hblocks, List.take_of_length_le (by simp [ht1_len, ht2_len])]
  refine ⟨h64, ?_, ?_⟩
  · rw [h64, List.take_left' ht1_len]
  · rw [h64, List.drop_left' ht1_len, List.take_of_length_le (by omega)]

private theorem clampScalar_toList_cons32
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
     b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8)
    (hl : [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
           b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31].length = 32) :
    (Ratchet.clampScalar ⟨[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
      b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], hl⟩).toList =
      [b0 &&& 0xf8#8, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
       b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
       (b31 &&& 0x7f#8) ||| 0x40#8] := rfl

private theorem clamp_cons32
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
     b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8) :
    clamp [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
           b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] =
      [b0 &&& 0xf8#8, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
       b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
       (b31 &&& 0x7f#8) ||| 0x40#8] := by
  simp [clamp, clampByte]

theorem clampScalar_toList_eq_clamp_toList (v : List.Vector (BitVec 8) 32) :
    (Ratchet.clampScalar v).toList = clamp v.toList := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at hl; done)
  change (Ratchet.clampScalar ⟨[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
    b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], hl⟩).toList =
    clamp [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
      b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]
  rw [clampScalar_toList_cons32, clamp_cons32]

theorem clampScalar_idem (v : List.Vector (BitVec 8) 32) :
    Ratchet.clampScalar (Ratchet.clampScalar v) = Ratchet.clampScalar v := by
  apply Subtype.ext
  change (Ratchet.clampScalar (Ratchet.clampScalar v)).toList = (Ratchet.clampScalar v).toList
  rw [clampScalar_toList_eq_clamp_toList, clampScalar_toList_eq_clamp_toList, clamp_clamp]

theorem clampScalar_toList_eq_clamp (b : List (BitVec 8)) (hb : b.length = 32) :
    (Ratchet.clampScalar (vec32 b)).toList = clamp b := by
  rw [clampScalar_toList_eq_clamp_toList, vec32_toList_of_length_eq_32 b hb]

theorem rootCreateChain_of_rel_lowOrder
    (interpretation : ExternInterpretation)
    (E D : CBC.AesKey → CBC.Block → CBC.Block)
    (rk : RootKey) (their : PublicKey) (our : PrivateKey)
    (hzero : ((cryptoOf' interpretation E D).X (Ratchet.clampScalar our.bytes) their.bytes).toList =
      List.replicate 32 0#8) :
    rootCreateChain (cryptoOf' interpretation E D) rk their our =
      .error .invalidKeyAgreement := by
  unfold rootCreateChain Ratchet.createChain
  simp [hzero]

end Proofs.libsignal.RngG.CliPure.DecCrypto
