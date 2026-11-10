/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhModelLink -- shake: keep
public import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.InitFacts -- shake: keep
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto -- shake: keep
public import Computational.Specifications.Session.StatementComposed -- shake: keep
public import Computational.Specifications.Game.StatementBinaryHarnessCore -- shake: keep
public import Computational.Proofs.SpecLemmas.Game.StatementBinaryHarnessCore -- shake: keep
public import Computational.Proofs.SpecLemmas.Session.StatementComposed -- shake: keep
public import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect -- shake: keep
public import Computational.Proofs.SpecLemmas.SignalPqxdh.Assumptions -- shake: keep
import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs -- shake: keep
import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDec -- shake: keep
import VCVio.EvalDist.Monad.Basic -- shake: keep

/-!
# Well-formedness and dependence witnesses for `modelPrims X W`

**Checked by Lean.**

Proves the definitional, clamping, CBC, and DH laws of `modelPrims X W`, assembles
`CryptoWellFormedPrimitivesδ (modelPrims X W)` from `ModelPrimsCryptoAssumptions`, and gives
dependence witnesses showing that each external assumption can fail on unconstrained `(X, W, Dh)`.
-/

@[expose] public section

set_option autoImplicit false

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM CKA
open CryptoGames.LibsignalSM.Proofs.Correctness

theorem toU8_ofU8 (bs : List UInt8) : toU8 (ofU8 bs) = bs := by
  induction bs with
  | nil => rfl | cons _ _ ih => simp only [toU8, ofU8, List.map_cons] at *; rw [ih]

theorem ofU8_toU8 (bs : List (BitVec 8)) : ofU8 (toU8 bs) = bs := by
  induction bs with
  | nil => rfl | cons _ _ ih => simp only [toU8, ofU8, List.map_cons] at *; rw [ih]

@[simp] theorem toU8_length (bs : List (BitVec 8)) : (toU8 bs).length = bs.length := by simp [toU8]
@[simp] theorem ofU8_length (bs : List UInt8) : (ofU8 bs).length = bs.length := by simp [ofU8]
@[simp] theorem vecU8_length {n : Nat} (v : List.Vector (BitVec 8) n) : (vecU8 v).length = n := by
  simp [vecU8, List.Vector.toList_length]

theorem u8Vec_vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) : u8Vec n (vecU8 v) = v := by
  apply List.Vector.eq; rcases v with ⟨l, hl⟩
  simp [u8Vec, vecU8, ofU8_toU8, fitVec, List.Vector.toList, hl]

theorem vecU8_u8Vec_of_length {n : Nat} (bs : List UInt8) (h : bs.length = n) :
    vecU8 (u8Vec n bs) = bs := by
  have hlen : (ofU8 bs).length = n := by simp [h]
  simp [vecU8, u8Vec, fitVec, List.Vector.toList, hlen, toU8_ofU8]

theorem vecU8_inj {n : Nat} {v₁ v₂ : List.Vector (BitVec 8) n} (h : vecU8 v₁ = vecU8 v₂) :
    v₁ = v₂ := by rw [← u8Vec_vecU8 v₁, ← u8Vec_vecU8 v₂, h]

theorem vecU8_replicate_zero (n : Nat) :
    vecU8 (List.Vector.replicate n 0#8) = List.replicate n 0 := by
  simp [vecU8, toU8, List.Vector.replicate, List.Vector.toList]

/-! ## AES-256-CBC block and stream roundtrip -/

private theorem blockToBytesLE_eq_list (b : CBC.Block) :
    CBC.blockToBytesLE b =
      [b.extractLsb' 0 8, b.extractLsb' 8 8, b.extractLsb' 16 8, b.extractLsb' 24 8,
       b.extractLsb' 32 8, b.extractLsb' 40 8, b.extractLsb' 48 8, b.extractLsb' 56 8,
       b.extractLsb' 64 8, b.extractLsb' 72 8, b.extractLsb' 80 8, b.extractLsb' 88 8,
       b.extractLsb' 96 8, b.extractLsb' 104 8, b.extractLsb' 112 8, b.extractLsb' 120 8] :=
  rfl

private theorem extractLsb'_append_right {w1 w2 : Nat} (x : BitVec w1) (y : BitVec w2) :
    (x ++ y).extractLsb' 0 w2 = y := by
  ext i hi; simp [BitVec.getElem_extractLsb', BitVec.getLsbD_append, hi]

private theorem extractLsb'_append_left {w1 w2 : Nat} (x : BitVec w1) (y : BitVec w2)
    (s n : Nat) : (x ++ y).extractLsb' (w2 + s) n = x.extractLsb' s n := by
  ext i hi; simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  have h1 : ¬ (w2 + s + i < w2) := by omega
  have h2 : w2 + s + i - w2 = s + i := by omega
  simp [h1, h2]

private theorem extractLsb'_8_self (b : BitVec 8) : b.extractLsb' 0 8 = b := by
  ext i hi; simp

theorem blockToBytesLE_bytesToBlock' (bs : List (BitVec 8)) (h : bs.length = 16) :
    CBC.blockToBytesLE (CBC.bytesToBlock bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14,
    _ | ⟨b15, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at h)
  rw [blockToBytesLE_eq_list, CBC.bytesToBlock_16_eq]
  have step {w : Nat} (x : BitVec w) (y : BitVec 8) (s k : Nat) (hk : k = 8 + s) :
      (x ++ y).extractLsb' k 8 = x.extractLsb' s 8 := by
    subst hk; exact extractLsb'_append_left x y s 8
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact extractLsb'_append_right _ b0
  · rw [step _ _ 0 8 rfl]; exact extractLsb'_append_right _ b1
  · rw [step _ _ 8 16 rfl, step _ _ 0 8 rfl]; exact extractLsb'_append_right _ b2
  · rw [step _ _ 16 24 rfl, step _ _ 8 16 rfl, step _ _ 0 8 rfl]
    exact extractLsb'_append_right _ b3
  · rw [step _ _ 24 32 rfl, step _ _ 16 24 rfl, step _ _ 8 16 rfl, step _ _ 0 8 rfl]
    exact extractLsb'_append_right _ b4
  · rw [step _ _ 32 40 rfl, step _ _ 24 32 rfl, step _ _ 16 24 rfl, step _ _ 8 16 rfl,
      step _ _ 0 8 rfl]; exact extractLsb'_append_right _ b5
  · rw [step _ _ 40 48 rfl, step _ _ 32 40 rfl, step _ _ 24 32 rfl, step _ _ 16 24 rfl,
      step _ _ 8 16 rfl, step _ _ 0 8 rfl]; exact extractLsb'_append_right _ b6
  · rw [step _ _ 48 56 rfl, step _ _ 40 48 rfl, step _ _ 32 40 rfl, step _ _ 24 32 rfl,
      step _ _ 16 24 rfl, step _ _ 8 16 rfl, step _ _ 0 8 rfl]; exact extractLsb'_append_right _ b7
  · rw [step _ _ 56 64 rfl, step _ _ 48 56 rfl, step _ _ 40 48 rfl, step _ _ 32 40 rfl,
      step _ _ 24 32 rfl, step _ _ 16 24 rfl, step _ _ 8 16 rfl, step _ _ 0 8 rfl]
    exact extractLsb'_append_right _ b8
  · rw [step _ _ 64 72 rfl, step _ _ 56 64 rfl, step _ _ 48 56 rfl, step _ _ 40 48 rfl,
      step _ _ 32 40 rfl, step _ _ 24 32 rfl, step _ _ 16 24 rfl, step _ _ 8 16 rfl,
      step _ _ 0 8 rfl]; exact extractLsb'_append_right _ b9
  · rw [step _ _ 72 80 rfl, step _ _ 64 72 rfl, step _ _ 56 64 rfl, step _ _ 48 56 rfl,
      step _ _ 40 48 rfl, step _ _ 32 40 rfl, step _ _ 24 32 rfl, step _ _ 16 24 rfl,
      step _ _ 8 16 rfl, step _ _ 0 8 rfl]; exact extractLsb'_append_right _ b10
  · rw [step _ _ 80 88 rfl, step _ _ 72 80 rfl, step _ _ 64 72 rfl, step _ _ 56 64 rfl,
      step _ _ 48 56 rfl, step _ _ 40 48 rfl, step _ _ 32 40 rfl, step _ _ 24 32 rfl,
      step _ _ 16 24 rfl, step _ _ 8 16 rfl, step _ _ 0 8 rfl]
    exact extractLsb'_append_right _ b11
  · rw [step _ _ 88 96 rfl, step _ _ 80 88 rfl, step _ _ 72 80 rfl, step _ _ 64 72 rfl,
      step _ _ 56 64 rfl, step _ _ 48 56 rfl, step _ _ 40 48 rfl, step _ _ 32 40 rfl,
      step _ _ 24 32 rfl, step _ _ 16 24 rfl, step _ _ 8 16 rfl, step _ _ 0 8 rfl]
    exact extractLsb'_append_right _ b12
  · rw [step _ _ 96 104 rfl, step _ _ 88 96 rfl, step _ _ 80 88 rfl, step _ _ 72 80 rfl,
      step _ _ 64 72 rfl, step _ _ 56 64 rfl, step _ _ 48 56 rfl, step _ _ 40 48 rfl,
      step _ _ 32 40 rfl, step _ _ 24 32 rfl, step _ _ 16 24 rfl, step _ _ 8 16 rfl,
      step _ _ 0 8 rfl]; exact extractLsb'_append_right _ b13
  · rw [step _ _ 104 112 rfl, step _ _ 96 104 rfl, step _ _ 88 96 rfl, step _ _ 80 88 rfl,
      step _ _ 72 80 rfl, step _ _ 64 72 rfl, step _ _ 56 64 rfl, step _ _ 48 56 rfl,
      step _ _ 40 48 rfl, step _ _ 32 40 rfl, step _ _ 24 32 rfl, step _ _ 16 24 rfl,
      step _ _ 8 16 rfl, step _ _ 0 8 rfl]; exact extractLsb'_append_right _ b14
  · rw [step _ _ 112 120 rfl, step _ _ 104 112 rfl, step _ _ 96 104 rfl, step _ _ 88 96 rfl,
      step _ _ 80 88 rfl, step _ _ 72 80 rfl, step _ _ 64 72 rfl, step _ _ 56 64 rfl,
      step _ _ 48 56 rfl, step _ _ 40 48 rfl, step _ _ 32 40 rfl, step _ _ 24 32 rfl,
      step _ _ 16 24 rfl, step _ _ 8 16 rfl, step _ _ 0 8 rfl]
    exact extractLsb'_8_self b15

theorem modelPrims_aesEncBlock_len (X : UnreachedPqxdhPrimitives) (W : PEParams) (k blk : List UInt8) :
    ((modelPrims X W).aesEncBlock k blk).length = 16 := by
  simp [modelPrims, blockLevelPrims, LibsignalAesCbc.blockToBytes, LibsignalAesCbc.toLEBytes]

theorem modelPrims_aesBlock_corr (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hAes : ∀ key blk, W.C.D key (W.C.E key blk) = blk)
    (k blk : List UInt8) (_hk : k.length = 32) (hblk : blk.length = 16) :
    (modelPrims X W).aesDecBlock k ((modelPrims X W).aesEncBlock k blk) = blk := by
  have hblk_eq : LibsignalAesCbc.blockToBytes = CBC.blockToBytesLE := rfl
  dsimp only [modelPrims, blockLevelPrims]; rw [hblk_eq]
  set key' := LibsignalAesCbc.bytesToKey (ofU8 (SignalPqxdh.fitBytesRef 32 k))
  set encBlk := W.C.E key' (CBC.bytesToBlock (ofU8 (SignalPqxdh.fitBytesRef 16 blk)))
  have hlen1 : (toU8 (CBC.blockToBytesLE encBlk)).length = 16 := by simp [CBC.blockToBytesLE]
  rw [SignalPqxdh.fitBytesRef_of_length_eq hlen1, ofU8_toU8, CBC.bytesToBlock_blockToBytesLE,
    hAes, SignalPqxdh.fitBytesRef_of_length_eq hblk,
    blockToBytesLE_bytesToBlock' (ofU8 blk) (by simp [hblk]), toU8_ofU8]

theorem modelPrims_aead_roundtrip (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hAes : ∀ key blk, W.C.D key (W.C.E key blk) = blk)
    (mk : SignalPqxdh.MessageKeys) (ad pt : List UInt8) :
    (modelPrims X W).aeadDec mk ad ((modelPrims X W).aeadEnc mk ad pt) = some pt :=
  SignalPqxdh.aes256CbcHmac_roundtrip (modelPrims X W)
    (modelPrims_aesEncBlock_len X W) (modelPrims_aesBlock_corr X W hAes) mk ad pt

private theorem uint8_ofNat_shift_toBitVec_eq_extractLsb' (w : BitVec 256) (j : ℕ) :
    (UInt8.ofNat ((w.toNat >>> (8 * j)) % 256)).toBitVec = w.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_toNat_eq; simp [UInt8.ofNat, BitVec.extractLsb'_toNat]

@[simp] theorem ofU8_word256ToBytes (w : BitVec 256) :
    ofU8 (SignalPqxdh.word256ToBytes w) = HMAC.keyToBytes32 w := by
  refine List.ext_getElem (by simp [ofU8, SignalPqxdh.word256ToBytes, HMAC.keyToBytes32])
    fun j h1 h2 => ?_
  simp only [ofU8, SignalPqxdh.word256ToBytes, HMAC.keyToBytes32, List.getElem_map,
    List.getElem_ofFn]
  exact uint8_ofNat_shift_toBitVec_eq_extractLsb' w j

theorem word256ToBytes_eq_toU8_keyToBytes32 (w : BitVec 256) :
    SignalPqxdh.word256ToBytes w = toU8 (HMAC.keyToBytes32 w) := by
  rw [← toU8_ofU8 (SignalPqxdh.word256ToBytes w), ofU8_word256ToBytes]

@[simp] theorem length_word256ToBytes (w : BitVec 256) :
    (SignalPqxdh.word256ToBytes w).length = 32 := by simp [SignalPqxdh.word256ToBytes]

@[simp] theorem length_keyToBytes32 (k : BitVec 256) :
    (HMAC.keyToBytes32 k).length = 32 := by simp [HMAC.keyToBytes32]

private theorem extractLsb'_zero_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) (j : ℕ)
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

private theorem extractLsb'_bytesToKey32 (bs : List (BitVec 8)) (j : ℕ)
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

@[simp] theorem bytesToKey32_keyToBytes32 (k : BitVec 256) :
    HKDF.bytesToKey32 (HMAC.keyToBytes32 k) = k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hj : i / 8 < 32 := by omega
  have hr : i % 8 < 8 := by omega
  have hbyte := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8))
    (extractLsb'_bytesToKey32 (HMAC.keyToBytes32 k) (i / 8) (by simp [HMAC.keyToBytes32, hj]) hj)
  simp only [HMAC.keyToBytes32, List.getElem_ofFn, BitVec.getLsbD_extractLsb', hr, decide_true,
    Bool.true_and, Nat.div_add_mod] at hbyte
  exact hbyte

theorem keyToBytes32_bytesToKey32 (bs : List (BitVec 8)) (h : bs.length = 32) :
    HMAC.keyToBytes32 (HKDF.bytesToKey32 bs) = bs := by
  refine List.ext_getElem (by simp [HMAC.keyToBytes32, h]) fun j h1 h2 => ?_
  simp only [HMAC.keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32 bs j h2 (by omega)

theorem modelPrims_x25519_comm (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hXcomm : ∀ a b, W.C.X (Ratchet.clampScalar a) (W.C.pubKey (Ratchet.clampScalar b)) =
      W.C.X (Ratchet.clampScalar b) (W.C.pubKey (Ratchet.clampScalar a)))
    (a b : List UInt8) :
    (modelPrims X W).x25519 a ((modelPrims X W).x25519Base b) =
      (modelPrims X W).x25519 b ((modelPrims X W).x25519Base a) := by
  dsimp only [modelPrims, blockLevelPrims]; rw [u8Vec_vecU8, u8Vec_vecU8, hXcomm]

theorem modelPrims_x25519Base_ne_zero (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hXnz : ∀ a b, W.C.X (Ratchet.clampScalar a) (W.C.pubKey (Ratchet.clampScalar b)) ≠
      List.Vector.replicate 32 0#8)
    (a b : List UInt8) :
    (modelPrims X W).x25519 a ((modelPrims X W).x25519Base b) ≠ List.replicate 32 0 := by
  dsimp only [modelPrims, blockLevelPrims]; rw [u8Vec_vecU8, ← vecU8_replicate_zero 32]
  intro h; exact hXnz (u8Vec 32 a) (u8Vec 32 b) (vecU8_inj h)

private theorem vec32_keyToBytes32 (x : BitVec 256) :
    LibsignalInst.vec32 (HMAC.keyToBytes32 x) = Ratchet.keyToBytesVec32 x :=
  vec32_toList (Ratchet.keyToBytesVec32 x)

@[simp]
theorem u8Vec_word256ToBytes (sk : BitVec 256) :
    u8Vec 32 (SignalPqxdh.word256ToBytes sk) = Ratchet.keyToBytesVec32 sk := by
  apply Subtype.ext; dsimp only [u8Vec, fitVec, Ratchet.keyToBytesVec32]
  rw [ofU8_word256ToBytes, List.take_append_of_le_length (by simp [length_keyToBytes32]),
    List.take_of_length_le (by simp [length_keyToBytes32])]

/-! ## Scalar clamping and `modelPrims` field lemmas -/

private theorem take_append_replicate_eq (n : Nat) (bs : List (BitVec 8)) :
    bs.take n ++ List.replicate (n - bs.length) 0#8 =
      (bs ++ List.replicate n 0#8).take n := by
  by_cases h : n ≤ bs.length
  · rw [Nat.sub_eq_zero_of_le h, List.replicate_zero, List.append_nil,
      List.take_append_of_le_length h]
  · rw [List.take_of_length_le (by omega), List.take_append, List.take_of_length_le (by omega),
      List.take_replicate, Nat.min_eq_left (by omega)]

theorem ofU8_fitBytesRef_eq_u8Vec_toList (n : Nat) (sk : List UInt8) :
    ofU8 (SignalPqxdh.fitBytesRef n sk) = (u8Vec n sk).toList := by
  dsimp only [SignalPqxdh.fitBytesRef, u8Vec, fitVec, ofU8, List.Vector.toList]
  rw [List.map_append, List.map_take, List.map_replicate,
    show (0 : UInt8).toBitVec = 0#8 from rfl]
  have hlen := take_append_replicate_eq n (sk.map UInt8.toBitVec)
  rw [List.length_map] at hlen; exact hlen

theorem fitBytesRef_eq_vecU8_u8Vec (n : Nat) (sk : List UInt8) :
    SignalPqxdh.fitBytesRef n sk = vecU8 (u8Vec n sk) := by
  rw [← toU8_ofU8 (SignalPqxdh.fitBytesRef n sk), ofU8_fitBytesRef_eq_u8Vec_toList, vecU8]

theorem u8Vec_clampScalar25519 (sk : List UInt8) :
    u8Vec 32 (SignalPqxdh.clampScalar25519 sk) = Ratchet.clampScalar (u8Vec 32 sk) := by
  unfold SignalPqxdh.clampScalar25519; rw [fitBytesRef_eq_vecU8_u8Vec 32 sk]
  generalize u8Vec 32 sk = v; rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
    _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at hl; done)
  apply Subtype.ext; rfl

@[simp]
theorem clampScalar_u8Vec_clampScalar25519 (sk : List UInt8) :
    Ratchet.clampScalar (u8Vec 32 (SignalPqxdh.clampScalar25519 sk)) =
      Ratchet.clampScalar (u8Vec 32 sk) := by
  rw [u8Vec_clampScalar25519, clampScalar_idem]

theorem modelPrims_x25519_clamp (X : UnreachedPqxdhPrimitives) (W : PEParams) (sk pk : List UInt8) :
    (modelPrims X W).x25519 (SignalPqxdh.clampScalar25519 sk) pk =
      (modelPrims X W).x25519 sk pk := by
  dsimp only [modelPrims, blockLevelPrims]; rw [clampScalar_u8Vec_clampScalar25519]

theorem modelPrims_x25519Base_clamp (X : UnreachedPqxdhPrimitives) (W : PEParams) (sk : List UInt8) :
    (modelPrims X W).x25519Base (SignalPqxdh.clampScalar25519 sk) =
      (modelPrims X W).x25519Base sk := by
  dsimp only [modelPrims, blockLevelPrims]; rw [clampScalar_u8Vec_clampScalar25519]

private theorem flatMap_toBEBytes_length {w : Nat} (n : Nat) :
    ∀ l : List (BitVec w), (l.flatMap (HMAC.toBEBytes n)).length = n * l.length
  | [] => by simp
  | x :: xs => by
    have hx : (HMAC.toBEBytes n x).length = n := by simp [HMAC.toBEBytes]
    simp only [List.flatMap_cons, List.length_append, hx, flatMap_toBEBytes_length n xs,
      List.length_cons, Nat.mul_succ]; omega

theorem modelPrims_sha256Compress_len (X : UnreachedPqxdhPrimitives) (W : PEParams) (st blk : List UInt8) :
    ((modelPrims X W).sha256Compress st blk).length = 32 := by
  change (toU8 _).length = 32
  rw [toU8_length, flatMap_toBEBytes_length 4, List.Vector.toList_length]

theorem modelPrims_sha512Compress_len (X : UnreachedPqxdhPrimitives) (W : PEParams) (st blk : List UInt8) :
    ((modelPrims X W).sha512Compress st blk).length = 64 := by
  change (toU8 _).length = 64
  rw [toU8_length, flatMap_toBEBytes_length 8, List.Vector.toList_length]

theorem modelPrims_aesDecBlock_len (X : UnreachedPqxdhPrimitives) (W : PEParams) (k blk : List UInt8) :
    ((modelPrims X W).aesDecBlock k blk).length = 16 := by
  simp [modelPrims, blockLevelPrims, LibsignalAesCbc.blockToBytes, LibsignalAesCbc.toLEBytes]

theorem modelPrims_x25519_len (X : UnreachedPqxdhPrimitives) (W : PEParams) (k p : List UInt8) :
    ((modelPrims X W).x25519 k p).length = 32 := by simp [modelPrims, blockLevelPrims]

theorem modelPrims_x25519Base_len (X : UnreachedPqxdhPrimitives) (W : PEParams) (k : List UInt8) :
    ((modelPrims X W).x25519Base k).length = 32 := by simp [modelPrims, blockLevelPrims]

theorem modelPrims_sha512_len (X : UnreachedPqxdhPrimitives) (W : PEParams) (m : List UInt8) :
    ((modelPrims X W).sha512 m).length = 64 := SignalPqxdh.sha512Ref_length (blockLevelPrims X W) m

theorem modelPrims_scalarFromBytesModOrder_len (X : UnreachedPqxdhPrimitives) (W : PEParams) (b : List UInt8) :
    ((modelPrims X W).scalarFromBytesModOrder b).length = 32 := by simp [modelPrims, blockLevelPrims]

theorem modelPrims_scalarFromWide_len (X : UnreachedPqxdhPrimitives) (W : PEParams) (b : List UInt8) :
    ((modelPrims X W).scalarFromWide b).length = 32 := by simp [modelPrims, blockLevelPrims]

theorem modelPrims_montToEd_len (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (u : List UInt8) (s : UInt8) (pt : List UInt8) (h : (modelPrims X W).montToEd u s = some pt) :
    pt.length = 160 := by
  dsimp only [modelPrims, blockLevelPrims] at h
  rcases h1 : W.Q.montToEd (u8Vec 32 u) s.toBitVec with _ | v <;> simp [h1] at h
  subst h; simp

theorem modelPrims_edNeg_len (X : UnreachedPqxdhPrimitives) (W : PEParams) (pt : List UInt8) :
    ((modelPrims X W).edNeg pt).length = 160 := by simp [modelPrims, blockLevelPrims]

theorem modelPrims_doubleScalarMulBasepoint_len (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (h a s : List UInt8) :
    ((modelPrims X W).doubleScalarMulBasepoint h a s).length = 160 := by
  simp [modelPrims, blockLevelPrims]

theorem modelPrims_compress_len (X : UnreachedPqxdhPrimitives) (W : PEParams) (pt : List UInt8) :
    ((modelPrims X W).compress pt).length = 32 := by simp [modelPrims, blockLevelPrims]

theorem modelPrims_kemEncaps_isSome (X : UnreachedPqxdhPrimitives) (W : PEParams) (pk r : List UInt8)
    (hpk : pk.length = SignalPqxdh.kyberPkLen) :
    ((modelPrims X W).kemEncaps pk r).isSome = true := by
  simp [modelPrims, blockLevelPrims, hpk]

theorem modelPrims_kemDecaps_isSome (X : UnreachedPqxdhPrimitives) (W : PEParams) (sk ct : List UInt8)
    (hct : ct.length = SignalPqxdh.kyberCtLen) :
    ((modelPrims X W).kemDecaps sk ct).isSome = true := by
  simp [modelPrims, blockLevelPrims, hct]

theorem modelPrims_kemEncaps_len (X : UnreachedPqxdhPrimitives) (W : PEParams) (pk r ss ct : List UInt8)
    (h : (modelPrims X W).kemEncaps pk r = some (ss, ct)) :
    ss.length = 32 ∧ ct.length = 1568 := by
  dsimp only [modelPrims, blockLevelPrims] at h
  split at h
  · injection h with hpair; injection hpair with hss hct; subst hss hct; simp
  · cases h

theorem modelPrims_kemDecaps_len (X : UnreachedPqxdhPrimitives) (W : PEParams) (sk ct ss : List UInt8)
    (h : (modelPrims X W).kemDecaps sk ct = some ss) : ss.length = 32 := by
  dsimp only [modelPrims, blockLevelPrims] at h
  split at h
  · injection h with hss; subst hss; simp
  · cases h

theorem modelPrims_kemDecaps_len_reject (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (sk ct : List UInt8) (h : ct.length ≠ SignalPqxdh.kyberCtLen) :
    (modelPrims X W).kemDecaps sk ct = none := by
  simp [modelPrims, blockLevelPrims, h]

theorem modelPrims_kemEncaps_len_reject (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (pk r : List UInt8) (h : pk.length ≠ SignalPqxdh.kyberPkLen) :
    (modelPrims X W).kemEncaps pk r = none := by
  simp [modelPrims, blockLevelPrims, h]

theorem modelPrims_spqrInitSend_some (X : UnreachedPqxdhPrimitives) (W : PEParams) (k r : List UInt8) :
    ((modelPrims X W).spqrInitSend k r).isSome = true := rfl

theorem modelPrims_spqr_corr (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (pqrKey coins stA : List UInt8) (salt? : Option (List UInt8)) (pqMsg : List UInt8)
    (h : (modelPrims X W).spqrInitSend pqrKey coins = some (stA, salt?, pqMsg)) :
    ∃ stB, (modelPrims X W).spqrInitRecv pqrKey pqMsg = some (stB, salt?) := by
  dsimp only [modelPrims, blockLevelPrims] at h ⊢; injection h with htuple
  rcases Prod.mk.inj htuple with ⟨_, hrest⟩; rcases Prod.mk.inj hrest with ⟨rfl, _⟩; exact ⟨[], rfl⟩

theorem modelPrims_spqrInitRecv_salt_len (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (pqrKey pqMsg stB salt : List UInt8)
    (h : (modelPrims X W).spqrInitRecv pqrKey pqMsg = some (stB, some salt)) :
    salt.length ≤ 32 := by
  dsimp only [modelPrims, blockLevelPrims] at h; injection h with htuple
  rcases Prod.mk.inj htuple with ⟨_, hsalt⟩; cases hsalt

private theorem keyVec_bytesToKey32 (v : List.Vector (BitVec 8) 32) :
    Ratchet.keyToBytesVec32 (HKDF.bytesToKey32 v.toList) = v := by
  apply Subtype.ext
  exact keyToBytes32_bytesToKey32 v.toList v.toList_length

theorem pubKey_clampScalar_toList_of_libX25519Rel
    {Pt : Type} [Zero Pt] {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh C Dh encPt encT) (v : List.Vector (BitVec 8) 32) :
    (C.pubKey (Ratchet.clampScalar v)).toList =
      encPt (Dh.dh (HKDF.bytesToKey32 v.toList) Dh.base) := by
  have hv := keyVec_bytesToKey32 v
  conv_lhs => rw [← hv, Proofs.Correctness.clampScalar_keyVec, ← vec32_keyToBytes32]
  rw [hX.1.pubKey_hook, hX.1.dh_clamp]

theorem x25519_clampScalar_encPt_toList_of_libX25519Rel
    {Pt : Type} [Zero Pt] {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh C Dh encPt encT) (a : List.Vector (BitVec 8) 32) (P : Pt) :
    (C.X (Ratchet.clampScalar a) (vec32 (encPt P))).toList =
      encPt (Dh.dh (HKDF.bytesToKey32 a.toList) P) := by
  have ha := keyVec_bytesToKey32 a
  conv_lhs => rw [← ha, Proofs.Correctness.clampScalar_keyVec, ← vec32_keyToBytes32]
  rw [hX.1.hook, hX.1.dh_clamp]

theorem x25519_clampScalar_pubKey_toList_of_libX25519Rel
    {Pt : Type} [Zero Pt] {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh C Dh encPt encT) (a b : List.Vector (BitVec 8) 32) :
    (C.X (Ratchet.clampScalar a) (C.pubKey (Ratchet.clampScalar b))).toList =
      encPt (Dh.dh (HKDF.bytesToKey32 a.toList)
        (Dh.dh (HKDF.bytesToKey32 b.toList) Dh.base)) := by
  have hpub : C.pubKey (Ratchet.clampScalar b) =
      vec32 (encPt (Dh.dh (HKDF.bytesToKey32 b.toList) Dh.base)) := by
    rw [← pubKey_clampScalar_toList_of_libX25519Rel hX b,
      vec32_toList (C.pubKey (Ratchet.clampScalar b))]
  rw [hpub, x25519_clampScalar_encPt_toList_of_libX25519Rel hX]

theorem x25519_comm_of_libX25519Rel
    {Pt : Type} [Zero Pt] {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey}
    (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT) (a b : List.Vector (BitVec 8) 32) :
    C.X (Ratchet.clampScalar a) (C.pubKey (Ratchet.clampScalar b)) =
      C.X (Ratchet.clampScalar b) (C.pubKey (Ratchet.clampScalar a)) := by
  apply List.Vector.eq
  rw [x25519_clampScalar_pubKey_toList_of_libX25519Rel hX a b,
    x25519_clampScalar_pubKey_toList_of_libX25519Rel hX b a,
    hDh (HKDF.bytesToKey32 a.toList) (HKDF.bytesToKey32 b.toList)]

theorem x25519_ne_zero_of_libX25519Rel
    {Pt : Type} [Zero Pt] {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh C Dh encPt encT) (a b : List.Vector (BitVec 8) 32) :
    C.X (Ratchet.clampScalar a) (C.pubKey (Ratchet.clampScalar b)) ≠
      List.Vector.replicate 32 0#8 := by
  intro heq
  have hlist : (C.X (Ratchet.clampScalar a) (C.pubKey (Ratchet.clampScalar b))).toList =
      List.replicate 32 0#8 := by rw [heq]; simp [List.Vector.replicate, List.Vector.toList]
  rw [x25519_clampScalar_pubKey_toList_of_libX25519Rel hX a b] at hlist
  have h0 := hX.1.enc_injective (hlist.trans hX.1.enc_zero.symm)
  exact hX.1.dh_ne_zero (HKDF.bytesToKey32 a.toList)
    (Dh.dh (HKDF.bytesToKey32 b.toList) Dh.base)
    (hX.1.dh_ne_zero (HKDF.bytesToKey32 b.toList) Dh.base hX.1.base_ne_zero) h0

theorem modelPrims_x25519_comm_of_libX25519Rel
    {Pt : Type} [Zero Pt] (X : UnreachedPqxdhPrimitives) (W : PEParams)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {encT : Pt → PublicKey}
    (hDh : Dh.Commutes) (hX : X25519RealizesDh W.C Dh encPt encT) (a b : List UInt8) :
    (modelPrims X W).x25519 a ((modelPrims X W).x25519Base b) =
      (modelPrims X W).x25519 b ((modelPrims X W).x25519Base a) :=
  modelPrims_x25519_comm X W (x25519_comm_of_libX25519Rel hDh hX) a b

theorem modelPrims_x25519_base_ne_zero_of_libX25519Rel
    {Pt : Type} [Zero Pt] (X : UnreachedPqxdhPrimitives) (W : PEParams)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh W.C Dh encPt encT) (a b : List UInt8) :
    (modelPrims X W).x25519 a ((modelPrims X W).x25519Base b) ≠ List.replicate 32 0 :=
  modelPrims_x25519Base_ne_zero X W (x25519_ne_zero_of_libX25519Rel hX) a b

theorem modelPrims_pow8_x25519_comm_of_libX25519Rel
    {Pt : Type} [Zero Pt] (X : UnreachedPqxdhPrimitives) (W : PEParams)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {encT : Pt → PublicKey}
    (hDh : Dh.Commutes) (hX : X25519RealizesDh W.C Dh encPt encT) (a b : List UInt8) :
    (modelPrims X W).pow8 ((modelPrims X W).x25519 a ((modelPrims X W).x25519Base b)) =
      (modelPrims X W).pow8 ((modelPrims X W).x25519 b ((modelPrims X W).x25519Base a)) :=
  congrArg (modelPrims X W).pow8 (modelPrims_x25519_comm_of_libX25519Rel X W hDh hX a b)

theorem modelPrims_kem_corr_of_decaps (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hkem : ∀ seed r : List UInt8,
      W.Q.decaps (u8Vec 3168 (X.kemKeyGen seed).2)
        (W.Q.encaps (u8Vec 1568 (X.kemKeyGen seed).1) (u8Vec 32 r)).1 =
      (W.Q.encaps (u8Vec 1568 (X.kemKeyGen seed).1) (u8Vec 32 r)).2)
    (seed r ss ct : List UInt8)
    (hEnc : (modelPrims X W).kemEncaps ((modelPrims X W).kemKeyGen seed).1 r = some (ss, ct)) :
    (modelPrims X W).kemDecaps ((modelPrims X W).kemKeyGen seed).2 ct = some ss := by
  dsimp only [modelPrims, blockLevelPrims] at hEnc ⊢
  split at hEnc
  · injection hEnc with hpair; injection hpair with hss hct
    rw [← hct, ← hss]
    simp only [vecU8_length, SignalPqxdh.kyberCtLen, SignalPqxdh.kyberPkLen,
      beq_self_eq_true, ↓reduceIte]
    rw [u8Vec_vecU8, hkem seed r]
  · cases hEnc

/-! ## Well-formedness of `modelPrims X W` -/

theorem modelPrims_canon_base_of_len32 (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hcanon : ∀ e : List UInt8, e.length = 32 →
      (modelPrims X W).isCanonical ((modelPrims X W).x25519Base e) = true)
    (e : List UInt8) :
    (modelPrims X W).isCanonical ((modelPrims X W).x25519Base e) = true := by
  rw [← modelPrims_x25519Base_clamp X W e]
  exact hcanon (SignalPqxdh.clampScalar25519 e) (SignalPqxdh.clampScalar25519_length e)

theorem modelPrims_x25519_pow8_congr_of_len32 (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hcongr : ∀ a pk1 pk2 : List UInt8, a.length = 32 → pk1.length = 32 → pk2.length = 32 →
      X.pow8 pk1 = X.pow8 pk2 → (modelPrims X W).x25519 a pk1 = (modelPrims X W).x25519 a pk2)
    (a pk1 pk2 : List UInt8) (h1 : pk1.length = 32) (h2 : pk2.length = 32)
    (hpow : X.pow8 pk1 = X.pow8 pk2) :
    (modelPrims X W).x25519 a pk1 = (modelPrims X W).x25519 a pk2 := by
  rw [← modelPrims_x25519_clamp X W a pk1, ← modelPrims_x25519_clamp X W a pk2]
  exact hcongr (SignalPqxdh.clampScalar25519 a) pk1 pk2
    (SignalPqxdh.clampScalar25519_length a) h1 h2 hpow

theorem modelPrims_pow8_base_len_of_len32 (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hlen : ∀ p e : List UInt8, e.length = 32 →
      X.pow8 p = X.pow8 ((modelPrims X W).x25519Base e) → p.length = 32)
    (p e : List UInt8) (hpow : X.pow8 p = X.pow8 ((modelPrims X W).x25519Base e)) :
    p.length = 32 := by
  rw [← modelPrims_x25519Base_clamp X W e] at hpow
  exact hlen p (SignalPqxdh.clampScalar25519 e) (SignalPqxdh.clampScalar25519_length e) hpow

theorem modelPrims_onCurveKey_x25519Base (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (a : List UInt8) :
    SignalPqxdh.onCurveKey (modelPrims X W) ((modelPrims X W).x25519Base a) :=
  Or.inr ⟨SignalPqxdh.clampScalar25519 a, SignalPqxdh.clampScalar25519_length a,
    by rw [modelPrims_x25519Base_clamp]⟩

theorem modelPrims_ddh_symm (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hisValid : ∀ A B Z : List UInt8,
      X.isValidDhTriple A B Z = true ↔ SignalPqxdh.isValidDhTripleRef (modelPrims X W) A B Z)
    (pk1 pk2 z : List UInt8) :
    (modelPrims X W).isValidDhTriple pk1 pk2 z = (modelPrims X W).isValidDhTriple pk2 pk1 z := by
  dsimp only [modelPrims, blockLevelPrims]
  rw [Bool.eq_iff_iff, hisValid, hisValid]
  exact ⟨fun ⟨h1, h2, h⟩ => ⟨h2, h1, h.symm⟩, fun ⟨h2, h1, h⟩ => ⟨h1, h2, h.symm⟩⟩

theorem modelPrims_ddh_consistent (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hisValid : ∀ A B Z : List UInt8,
      X.isValidDhTriple A B Z = true ↔ SignalPqxdh.isValidDhTripleRef (modelPrims X W) A B Z)
    (hcomm : ∀ a b : List UInt8,
      (modelPrims X W).x25519 a ((modelPrims X W).x25519Base b) =
        (modelPrims X W).x25519 b ((modelPrims X W).x25519Base a))
    (a b z : List UInt8) :
    (modelPrims X W).isValidDhTriple
        ((modelPrims X W).x25519Base a) ((modelPrims X W).x25519Base b) z = true ↔
      (modelPrims X W).pow8 z =
        (modelPrims X W).pow8 ((modelPrims X W).x25519 a ((modelPrims X W).x25519Base b)) := by
  change X.isValidDhTriple
    ((modelPrims X W).x25519Base a) ((modelPrims X W).x25519Base b) z = true ↔ _
  rw [hisValid]
  constructor
  · rintro ⟨_, _, ⟨a', hbase, hpow⟩ | ⟨b', hbase, hpow⟩⟩
    · rw [hpow, hcomm a' b, ← hbase, ← hcomm a b]
    · rw [hpow, hcomm b' a, ← hbase]
  · intro hpow
    exact ⟨modelPrims_onCurveKey_x25519Base X W a, modelPrims_onCurveKey_x25519Base X W b,
      Or.inl ⟨a, rfl, hpow⟩⟩

theorem modelPrims_ddh_consistent_left (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hisValid : ∀ A B Z : List UInt8,
      X.isValidDhTriple A B Z = true ↔ SignalPqxdh.isValidDhTripleRef (modelPrims X W) A B Z)
    (hcongr : ∀ a1 a2 pk : List UInt8, a1.length = 32 → a2.length = 32 →
      SignalPqxdh.onCurveKey (modelPrims X W) pk →
      (modelPrims X W).x25519Base a1 = (modelPrims X W).x25519Base a2 →
      (modelPrims X W).x25519 a1 pk = (modelPrims X W).x25519 a2 pk)
    (hcomm : ∀ a b : List UInt8,
      (modelPrims X W).x25519 a ((modelPrims X W).x25519Base b) =
        (modelPrims X W).x25519 b ((modelPrims X W).x25519Base a))
    (a pk z : List UInt8) (honCurve : SignalPqxdh.onCurveKey (modelPrims X W) pk) :
    (modelPrims X W).isValidDhTriple ((modelPrims X W).x25519Base a) pk z = true ↔
      (modelPrims X W).pow8 z = (modelPrims X W).pow8 ((modelPrims X W).x25519 a pk) := by
  change X.isValidDhTriple ((modelPrims X W).x25519Base a) pk z = true ↔ _
  rw [hisValid]
  constructor
  · rintro ⟨_, _, ⟨a', hbase, hpow⟩ | ⟨b, rfl, hpow⟩⟩
    · have hbase' :
          (modelPrims X W).x25519Base (SignalPqxdh.clampScalar25519 a) =
            (modelPrims X W).x25519Base (SignalPqxdh.clampScalar25519 a') := by
        rw [modelPrims_x25519Base_clamp, modelPrims_x25519Base_clamp, hbase]
      have hx := hcongr (SignalPqxdh.clampScalar25519 a) (SignalPqxdh.clampScalar25519 a') pk
        (SignalPqxdh.clampScalar25519_length a) (SignalPqxdh.clampScalar25519_length a')
        honCurve hbase'
      rw [modelPrims_x25519_clamp, modelPrims_x25519_clamp] at hx
      rw [hpow, ← hx]
    · rw [hpow, ← hcomm a b]
  · intro hpow
    exact ⟨modelPrims_onCurveKey_x25519Base X W a, honCurve, Or.inl ⟨a, rfl, hpow⟩⟩

theorem modelPrims_x25519_congr_of_base_eq_of_canon (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hcanon : ∀ a1 a2 pk : List UInt8, a1.length = 32 → a2.length = 32 →
      (modelPrims X W).isCanonical pk = true →
      (modelPrims X W).x25519Base a1 = (modelPrims X W).x25519Base a2 →
      (modelPrims X W).x25519 a1 pk = (modelPrims X W).x25519 a2 pk)
    (hpow8_congr : ∀ a pk1 pk2 : List UInt8, pk1.length = 32 → pk2.length = 32 →
      X.pow8 pk1 = X.pow8 pk2 →
      (modelPrims X W).x25519 a pk1 = (modelPrims X W).x25519 a pk2)
    (hpow8_len : ∀ p e : List UInt8,
      X.pow8 p = X.pow8 ((modelPrims X W).x25519Base e) → p.length = 32)
    (hcomm : ∀ a b : List UInt8,
      (modelPrims X W).x25519 a ((modelPrims X W).x25519Base b) =
        (modelPrims X W).x25519 b ((modelPrims X W).x25519Base a))
    (a1 a2 pk : List UInt8) (ha1 : a1.length = 32) (ha2 : a2.length = 32)
    (hon : SignalPqxdh.onCurveKey (modelPrims X W) pk)
    (hbase : (modelPrims X W).x25519Base a1 = (modelPrims X W).x25519Base a2) :
    (modelPrims X W).x25519 a1 pk = (modelPrims X W).x25519 a2 pk := by
  rcases hon with hcan | ⟨e, _he, hpow⟩
  · exact hcanon a1 a2 pk ha1 ha2 hcan hbase
  · have hpk_len : pk.length = 32 := hpow8_len pk e hpow
    have hbase_len : ((modelPrims X W).x25519Base e).length = 32 :=
      modelPrims_x25519Base_len X W e
    rw [hpow8_congr a1 pk ((modelPrims X W).x25519Base e) hpk_len hbase_len hpow,
      hpow8_congr a2 pk ((modelPrims X W).x25519Base e) hpk_len hbase_len hpow,
      hcomm a1 e, hcomm a2 e, hbase]

/-- Assembles `SignalPqxdh.WellFormedPrimitivesδ (modelPrims X W)` from
`ModelPrimsCryptoAssumptions X W` and the underlying X25519 and AES block assumptions. -/
theorem wellFormedPrimitivesδ_modelPrims
    {Pt : Type} [Zero Pt] (X : UnreachedPqxdhPrimitives) (W : PEParams)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {encT : Pt → PublicKey}
    (hAssump : ModelPrimsCryptoAssumptions X W)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh W.C Dh encPt encT)
    (hD : ∀ k x, W.C.D k (W.C.E k x) = x) :
    SignalPqxdh.WellFormedPrimitivesδ (modelPrims X W) where
  sha256Compress_len := modelPrims_sha256Compress_len X W
  sha512Compress_len := modelPrims_sha512Compress_len X W
  aesEncBlock_len := modelPrims_aesEncBlock_len X W
  aesDecBlock_len := modelPrims_aesDecBlock_len X W
  aesBlock_corr := modelPrims_aesBlock_corr X W hD
  sha512_eq_ref := modelPrims_sha512_eq_ref X W
  hkdfDerive96_eq_ref := modelPrims_hkdfDerive96_eq_ref X W
  rootCreateChain_eq_ref := modelPrims_rootCreateChain_eq_ref X W
  chainKdfSeed_eq_ref := modelPrims_chainKdfSeed_eq_ref X W
  chainKdfNext_eq_ref := modelPrims_chainKdfNext_eq_ref X W
  deriveMsgKeys_eq_ref := modelPrims_deriveMsgKeys_eq_ref X W
  aeadEnc_eq_ref := modelPrims_aeadEnc_eq_ref X W
  aeadDec_eq_ref := modelPrims_aeadDec_eq_ref X W
  x25519_clamp := modelPrims_x25519_clamp X W
  x25519Base_clamp := modelPrims_x25519Base_clamp X W
  x25519_base_ne_zero := fun a b _ _ => modelPrims_x25519_base_ne_zero_of_libX25519Rel X W hX a b
  x25519_zero_iff := hAssump.x25519_zero_iff
  kemDecaps_isSome := fun sk ct _ hct => modelPrims_kemDecaps_isSome X W sk ct hct
  kemEncaps_isSome := fun pk r hpk _ => modelPrims_kemEncaps_isSome X W pk r hpk
  x25519_comm := modelPrims_x25519_comm_of_libX25519Rel X W hDh hX
  canon_base := modelPrims_canon_base_of_len32 X W hAssump.canon_base
  canon_x25519 := hAssump.canon_x25519
  sigPkGen_eq_x25519Base := hAssump.sigPkGen_eq_x25519Base
  pow8_idemp := hAssump.pow8_idemp
  pow8_x25519_comm := modelPrims_pow8_x25519_comm_of_libX25519Rel X W hDh hX
  ddh_consistent :=
    modelPrims_ddh_consistent X W hAssump.isValidDhTriple_eq_ref
      (modelPrims_x25519_comm_of_libX25519Rel X W hDh hX)
  ddh_consistent_left :=
    modelPrims_ddh_consistent_left X W hAssump.isValidDhTriple_eq_ref
      (modelPrims_x25519_congr_of_base_eq_of_canon X W hAssump.x25519_congr_of_base_eq
        (modelPrims_x25519_pow8_congr_of_len32 X W hAssump.x25519_pow8_congr)
        (modelPrims_pow8_base_len_of_len32 X W hAssump.pow8_base_len)
        (modelPrims_x25519_comm_of_libX25519Rel X W hDh hX))
      (modelPrims_x25519_comm_of_libX25519Rel X W hDh hX)
  ddh_symm := modelPrims_ddh_symm X W hAssump.isValidDhTriple_eq_ref
  isValidDhTriple_eq_ref := hAssump.isValidDhTriple_eq_ref
  x25519_pow8_congr := modelPrims_x25519_pow8_congr_of_len32 X W hAssump.x25519_pow8_congr
  x25519_congr_of_base_eq :=
    modelPrims_x25519_congr_of_base_eq_of_canon X W hAssump.x25519_congr_of_base_eq
      (modelPrims_x25519_pow8_congr_of_len32 X W hAssump.x25519_pow8_congr)
      (modelPrims_pow8_base_len_of_len32 X W hAssump.pow8_base_len)
      (modelPrims_x25519_comm_of_libX25519Rel X W hDh hX)
  canon_pow8_inj := hAssump.canon_pow8_inj
  x25519_len := modelPrims_x25519_len X W
  x25519Base_len := modelPrims_x25519Base_len X W
  pow8_len := hAssump.pow8_len
  sha512_len := modelPrims_sha512_len X W
  scalarMul_len := hAssump.scalarMul_len
  scalarAdd_len := hAssump.scalarAdd_len
  scalarFromBytesModOrder_len := modelPrims_scalarFromBytesModOrder_len X W
  scalarFromWide_len := modelPrims_scalarFromWide_len X W
  montToEd_len := modelPrims_montToEd_len X W
  edNeg_len := modelPrims_edNeg_len X W
  doubleScalarMulBasepoint_len := modelPrims_doubleScalarMulBasepoint_len X W
  compress_len := modelPrims_compress_len X W
  sigVerify_eq_xeddsaVerifyRef := modelPrims_sigVerify_eq_ref X W
  isCanonical_eq_isCanonicalRef := modelPrims_isCanonical_eq_ref X W
  kemKeyGen_valid := hAssump.kemKeyGen_len
  kemEncaps_len := modelPrims_kemEncaps_len X W
  kemDecaps_len := modelPrims_kemDecaps_len X W
  spqrInitSend_some := modelPrims_spqrInitSend_some X W
  aead_corr := modelPrims_aead_roundtrip X W hD
  sig_corr := hAssump.sig_corr
  spqr_corr := modelPrims_spqr_corr X W
  spqrInitRecv_salt_len := modelPrims_spqrInitRecv_salt_len X W

/-- Assembles `SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W)` from
`ModelPrimsCryptoAssumptions X W` and the underlying X25519 and AES block assumptions. -/
theorem cryptoWellFormedPrimitivesδ_modelPrims
    {Pt : Type} [Zero Pt] (X : UnreachedPqxdhPrimitives) (W : PEParams)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {encT : Pt → PublicKey}
    (hAssump : ModelPrimsCryptoAssumptions X W)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh W.C Dh encPt encT)
    (hD : ∀ k x, W.C.D k (W.C.E k x) = x) :
    SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W) where
  toWellFormedPrimitivesδ := wellFormedPrimitivesδ_modelPrims X W hAssump hDh hX hD
  ec_coll_bound := fun pk => SignalPqxdh.prob_le_one_div_two_pow_of_toReal (hAssump.ec_coll_bound pk)
  kem_coll_bound := fun pk => SignalPqxdh.prob_le_one_div_two_pow_of_toReal (hAssump.kem_coll_bound pk)
  x25519_inj_pow8 := hAssump.x25519_inj_pow8
  pow8_base_len := modelPrims_pow8_base_len_of_len32 X W hAssump.pow8_base_len
  kemDecaps_len_reject := modelPrims_kemDecaps_len_reject X W
  kemEncaps_len_reject := modelPrims_kemEncaps_len_reject X W

/-! ## Dependence witnesses for external hypotheses -/

theorem not_kemKeyGen_valid_of_bad_len (X : UnreachedPqxdhPrimitives) (W : PEParams) (seed : List UInt8)
    (h : (X.kemKeyGen seed).1.length ≠ SignalPqxdh.kyberPkLen) :
    ¬ (((modelPrims X W).kemKeyGen seed).1.length = SignalPqxdh.kyberPkLen ∧
      ((modelPrims X W).kemKeyGen seed).2.length = 3168) :=
  fun hvalid => h hvalid.1

theorem not_sig_corr_of_short_sig (X : UnreachedPqxdhPrimitives) (W : PEParams) (sk msg r : List UInt8)
    (h : (X.sigSign sk msg r).length ≠ 64) :
    (modelPrims X W).sigVerify (X.sigPkGen sk) msg (X.sigSign sk msg r) = false := by
  dsimp only [modelPrims, SignalPqxdh.xeddsaVerifyRef]; simp [h]

theorem not_canon_base_of_montToEd_none (X : UnreachedPqxdhPrimitives) (W : PEParams) (e : List UInt8)
    (h : W.Q.montToEd (u8Vec 32 ((modelPrims X W).x25519Base e)) 0 = none) :
    (modelPrims X W).isCanonical ((modelPrims X W).x25519Base e) = false := by
  change SignalPqxdh.isCanonicalRef (blockLevelPrims X W) ((modelPrims X W).x25519Base e) = false
  unfold SignalPqxdh.isCanonicalRef
  have hm : (blockLevelPrims X W).montToEd ((modelPrims X W).x25519Base e) 0 = none := by
    change Option.map vecU8 (W.Q.montToEd (u8Vec 32 ((modelPrims X W).x25519Base e)) 0) = none
    rw [h]; rfl
  rw [hm]; split <;> rfl

theorem not_pow8_idemp_of_ne (X : UnreachedPqxdhPrimitives) (p : List UInt8) (h : X.pow8 (X.pow8 p) ≠ X.pow8 p) :
    ¬ (∀ q : List UInt8, X.pow8 (X.pow8 q) = X.pow8 q) := fun hall => h (hall p)

theorem not_isValidDhTriple_eq_ref_of_false (X : UnreachedPqxdhPrimitives) (W : PEParams) (a b : List UInt8)
    (h : X.isValidDhTriple ((modelPrims X W).x25519Base a) ((modelPrims X W).x25519Base b)
      ((modelPrims X W).x25519 a ((modelPrims X W).x25519Base b)) = false) :
    ¬ (∀ A B Z : List UInt8,
      X.isValidDhTriple A B Z = true ↔ SignalPqxdh.isValidDhTripleRef (modelPrims X W) A B Z) := by
  intro hall
  have href : SignalPqxdh.isValidDhTripleRef (modelPrims X W)
      ((modelPrims X W).x25519Base a) ((modelPrims X W).x25519Base b)
      ((modelPrims X W).x25519 a ((modelPrims X W).x25519Base b)) :=
    ⟨modelPrims_onCurveKey_x25519Base X W a, modelPrims_onCurveKey_x25519Base X W b,
      Or.inl ⟨a, rfl, rfl⟩⟩
  have htrue := (hall _ _ _).mpr href; rw [h] at htrue; exact Bool.noConfusion htrue

theorem not_pow8_base_len_of_eq_empty (X : UnreachedPqxdhPrimitives) (W : PEParams) (e : List UInt8)
    (h : X.pow8 [] = X.pow8 ((modelPrims X W).x25519Base e)) :
    ¬ (∀ p e' : List UInt8,
      X.pow8 p = X.pow8 ((modelPrims X W).x25519Base e') → p.length = 32) := by
  intro hall; have hlen := hall [] e h; revert hlen; decide

theorem not_x25519_pow8_congr_of_const_pow8 (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (a pk1 pk2 : List UInt8) (h1 : pk1.length = 32) (h2 : pk2.length = 32)
    (hpow : X.pow8 pk1 = X.pow8 pk2)
    (hne : (modelPrims X W).x25519 a pk1 ≠ (modelPrims X W).x25519 a pk2) :
    ¬ (∀ a' p1 p2 : List UInt8, p1.length = 32 → p2.length = 32 →
      X.pow8 p1 = X.pow8 p2 →
      (modelPrims X W).x25519 a' p1 = (modelPrims X W).x25519 a' p2) :=
  fun hall => hne (hall a pk1 pk2 h1 h2 hpow)

theorem not_canon_pow8_inj_of_const_pow8 (X : UnreachedPqxdhPrimitives) (W : PEParams) (pk1 pk2 : List UInt8)
    (hc1 : (modelPrims X W).isCanonical pk1 = true) (hc2 : (modelPrims X W).isCanonical pk2 = true)
    (hpow : X.pow8 pk1 = X.pow8 pk2) (hne : pk1 ≠ pk2) :
    ¬ (∀ p1 p2 : List UInt8,
      (modelPrims X W).isCanonical p1 = true → (modelPrims X W).isCanonical p2 = true →
      X.pow8 p1 = X.pow8 p2 → p1 = p2) :=
  fun hall => hne (hall pk1 pk2 hc1 hc2 hpow)

theorem not_x25519_inj_pow8_of_id_pow8 (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (a pk1 pk2 : List UInt8) (ha : a.length = 32) (h1 : pk1.length = 32) (h2 : pk2.length = 32)
    (hx : (modelPrims X W).x25519 a pk1 = (modelPrims X W).x25519 a pk2)
    (hne : X.pow8 pk1 ≠ X.pow8 pk2) :
    ¬ (∀ a' p1 p2 : List UInt8, a'.length = 32 → p1.length = 32 → p2.length = 32 →
      (modelPrims X W).x25519 a' p1 = (modelPrims X W).x25519 a' p2 → X.pow8 p1 = X.pow8 p2) :=
  fun hall => hne (hall a pk1 pk2 ha h1 h2 hx)

theorem not_x25519_zero_iff_of_witness (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (a1 a2 pk : List UInt8) (ha1 : a1.length = 32) (ha2 : a2.length = 32) (hpk : pk.length = 32)
    (h1 : (modelPrims X W).x25519 a1 pk = List.replicate 32 0)
    (h2 : (modelPrims X W).x25519 a2 pk ≠ List.replicate 32 0) :
    ¬ (∀ b1 b2 p : List UInt8, b1.length = 32 → b2.length = 32 → p.length = 32 →
      ((modelPrims X W).x25519 b1 p = List.replicate 32 0 ↔
        (modelPrims X W).x25519 b2 p = List.replicate 32 0)) :=
  fun hall => h2 ((hall a1 a2 pk ha1 ha2 hpk).mp h1)

theorem not_aesBlock_corr_of_const_zero (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hD0 : ∀ k x, W.C.D k x = 0#128) :
    (modelPrims X W).aesDecBlock (List.replicate 32 0)
      ((modelPrims X W).aesEncBlock (List.replicate 32 0) (List.replicate 16 1)) ≠
      List.replicate 16 1 := by
  dsimp only [modelPrims, blockLevelPrims]; rw [hD0]; decide

theorem not_aead_corr_of_const_zero (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hD0 : ∀ k x, W.C.D k x = 0#128) :
    (modelPrims X W).aeadDec ⟨List.replicate 32 0, List.replicate 32 0, List.replicate 16 0⟩ []
      ((modelPrims X W).aeadEnc ⟨List.replicate 32 0, List.replicate 32 0, List.replicate 16 0⟩
        [] []) = none := by
  have hdec0 : ∀ k b : List UInt8, (modelPrims X W).aesDecBlock k b = List.replicate 16 0 := by
    intro k b; dsimp only [modelPrims, blockLevelPrims]; rw [hD0]; decide
  rw [modelPrims_aeadEnc_eq_ref, modelPrims_aeadDec_eq_ref]
  set P := modelPrims X W
  have hpad : SignalPqxdh.pkcs7Pad16 [] = List.replicate 16 16 := rfl
  have hblk_pad : SignalPqxdh.toBlocks16 (List.replicate 16 16) = [List.replicate 16 16] := by
    have h1 := SignalPqxdh.toBlocks16_append_of_len16
      (List.length_replicate (n := 16) (a := (16 : UInt8))) []
    rw [List.append_nil] at h1; rw [h1, SignalPqxdh.toBlocks16]; rfl
  have henc_len :
      (SignalPqxdh.aes256CbcEncRef P (List.replicate 32 0) (List.replicate 16 0) []).length =
        16 := by
    unfold SignalPqxdh.aes256CbcEncRef; rw [hpad, hblk_pad]
    simp [SignalPqxdh.cbcEncBlocks, SignalPqxdh.cbcEncBlocksWith, SignalPqxdh.fromBlocks16,
      SignalPqxdh.fitBytesRef_length]
  set ct := SignalPqxdh.aes256CbcEncRef P (List.replicate 32 0) (List.replicate 16 0) []
  set mac := (SignalPqxdh.hmacSha256Ref P (List.replicate 32 0)
    (SignalPqxdh.aeadMacInput [] ct)).take 8
  have hmac_len : mac.length = 8 := by simp [mac, SignalPqxdh.hmacSha256Ref_length]
  have htot : (ct ++ mac).length ≥ 24 := by simp [henc_len, hmac_len]
  have hsub : (ct ++ mac).length - 8 = ct.length := by simp [hmac_len]
  have hblk_ct : SignalPqxdh.toBlocks16 ct = [ct] := by
    have h1 := SignalPqxdh.toBlocks16_append_of_len16 henc_len []
    rw [List.append_nil] at h1; rw [h1, SignalPqxdh.toBlocks16]; rfl
  have hdec_ct :
      SignalPqxdh.aes256CbcDecRef P (List.replicate 32 0) (List.replicate 16 0) ct = none := by
    unfold SignalPqxdh.aes256CbcDecRef; rw [henc_len, hblk_ct]
    dsimp only [SignalPqxdh.cbcDecBlocks, SignalPqxdh.cbcDecBlocksWith,
      SignalPqxdh.fromBlocks16, List.foldr]
    rw [hdec0]; decide
  change SignalPqxdh.aes256CbcHmacDecRef P
    ⟨List.replicate 32 0, List.replicate 32 0, List.replicate 16 0⟩ [] (ct ++ mac) = none
  unfold SignalPqxdh.aes256CbcHmacDecRef
  rw [ite_eq_left_iff.mpr fun h => absurd htot h]; dsimp only
  rw [hsub, List.take_left' rfl, List.drop_left' rfl, beq_self_eq_true,
    ite_eq_left_iff.mpr fun h => absurd rfl h]
  exact hdec_ct

theorem kemHonestFail_modelPrims_eq_true_of_ne (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (seed r : List UInt8) (hpk : (X.kemKeyGen seed).1.length = SignalPqxdh.kyberPkLen)
    (hne : W.Q.decaps (u8Vec 3168 (X.kemKeyGen seed).2)
        (W.Q.encaps (u8Vec 1568 (X.kemKeyGen seed).1) (u8Vec 32 r)).1 ≠
      (W.Q.encaps (u8Vec 1568 (X.kemKeyGen seed).1) (u8Vec 32 r)).2) :
    SignalPqxdh.kemHonestExchangeFails (modelPrims X W) seed r = true := by
  unfold SignalPqxdh.kemHonestExchangeFails
  have henc : (modelPrims X W).kemEncaps ((modelPrims X W).kemKeyGen seed).1 r =
      some (vecU8 (W.Q.encaps (u8Vec 1568 (X.kemKeyGen seed).1) (u8Vec 32 r)).2,
            vecU8 (W.Q.encaps (u8Vec 1568 (X.kemKeyGen seed).1) (u8Vec 32 r)).1) := by
    dsimp only [modelPrims, blockLevelPrims]
    simp [hpk, SignalPqxdh.kyberPkLen]
  rw [henc, decide_eq_true_eq]
  dsimp only [modelPrims, blockLevelPrims]
  simp only [vecU8_length, SignalPqxdh.kyberCtLen, beq_self_eq_true, ↓reduceIte, u8Vec_vecU8]
  intro heq; injection heq with hvec; exact hne (vecU8_inj hvec)

theorem not_ec_coll_bound_of_const_pow8 (X : UnreachedPqxdhPrimitives) (W : PEParams) (targetPk : List UInt8)
    (hconst : ∀ sk : List UInt8, X.pow8 ((modelPrims X W).x25519Base sk) = X.pow8 targetPk) :
    ¬ (∀ t : List UInt8,
      (𝒟[do
        let sk ← SignalPqxdh.sampleScalar32
        pure ((modelPrims X W).pow8 ((modelPrims X W).x25519Base sk) ==
          (modelPrims X W).pow8 t)] {true}).toReal ≤ 1 / (2 : ℝ) ^ 250) := by
  intro hall; have hbound := hall targetPk
  have hbeq : ∀ sk : List UInt8,
      ((modelPrims X W).pow8 ((modelPrims X W).x25519Base sk) ==
        (modelPrims X W).pow8 targetPk) = true := by
    intro sk; change (X.pow8 ((modelPrims X W).x25519Base sk) == X.pow8 targetPk) = true
    rw [hconst sk, beq_self_eq_true]
  simp only [hbeq, OracleComp.evalDist_bind_const, evalDist_pure,
    Measure.dirac_apply' _ (measurableSet_singleton _), Set.mem_singleton_iff, Set.indicator_of_mem,
    Pi.one_apply, ENNReal.toReal_one] at hbound
  norm_num at hbound

theorem not_kem_coll_bound_of_const_kemKeyGen (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (targetPk : List UInt8) (hconst : ∀ seed : List UInt8, (X.kemKeyGen seed).1 = targetPk) :
    ¬ (∀ t : List UInt8,
      (𝒟[do
        let (pk, _) ← SignalPqxdh.sampleKemKeyGen (modelPrims X W)
        pure (pk == t)] {true}).toReal ≤ 1 / (2 : ℝ) ^ 255) := by
  intro hall; have hbound := hall targetPk
  have hbeq : ∀ seed : List UInt8, (((modelPrims X W).kemKeyGen seed).1 == targetPk) = true := by
    intro seed; change ((X.kemKeyGen seed).1 == targetPk) = true; rw [hconst seed, beq_self_eq_true]
  simp only [SignalPqxdh.sampleKemKeyGen, bind_assoc, pure_bind, hbeq,
    OracleComp.evalDist_bind_const, evalDist_pure,
    Measure.dirac_apply' _ (measurableSet_singleton _), Set.mem_singleton_iff, Set.indicator_of_mem,
    Pi.one_apply, ENNReal.toReal_one] at hbound
  norm_num at hbound

theorem not_encaps1Total_of_none (K : LibsignalSpqrV1.MlKem)
    (hdr : Bytes) (rand : List.Vector (BitVec 8) 32) (hlen : hdr.length = 64)
    (hnone : K.encaps1 hdr rand = none) : ¬ Encaps1Total K := by
  intro htot; have hsome := htot hdr rand hlen; rw [hnone] at hsome; exact Bool.noConfusion hsome

theorem not_dhKerUniform_of_witness {Pt : Type} (Dh : DHFun (BitVec 256) Pt)
    (s x : BitVec 256) (Q Q' : Pt) (hx : Dh.dh x Q = Dh.dh x Q') (hs : Dh.dh s Q ≠ Dh.dh s Q') :
    ¬ DhKerUniform Dh :=
  fun hker => hs ((hker s x Q Q').mp hx)

end CryptoVerification.E2E
