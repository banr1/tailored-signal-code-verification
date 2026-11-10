/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
public import LibsignalBinary.Specifications.RecordCodecsBinary
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom

/-!
# `IdentityKey::decode` Stack Frame and Result Repacking

Model case splits, 96-byte stack frame (`sub sp, sp, #0x60`) decomposition, and 32-byte key-chunk
repacking from `pkTryFromResultAt` (`40` B) into `identityKeyDecodeResultAt` (`48` B).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.RecordCodecsBinary.IdentityKeyDecode.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.RecordCodecs

/-! ## 1. Model case split & pure BitVec facts -/

theorem publicKey_deserialize_cases (bs : List (BitVec 8)) :
    (∃ pk, PublicKey.deserialize bs = .ok pk ∧ decodeIdentityKey bs = .ok ⟨pk⟩) ∨
    (PublicKey.deserialize bs = .error .noKeyTypeIdentifier ∧
      decodeIdentityKey bs = .error .noKeyTypeIdentifier) ∨
    (∃ t, PublicKey.deserialize bs = .error (.badKeyType t) ∧
      decodeIdentityKey bs = .error (.badKeyType t)) ∨
    (∃ n, PublicKey.deserialize bs = .error (.badKeyLength n) ∧
      decodeIdentityKey bs = .error (.badKeyLength n)) := by
  unfold decodeIdentityKey
  rcases bs with _ | ⟨b0, rest⟩
  · right; left
    rw [PublicKeyTryFrom.publicKey_deserialize_nil]; exact ⟨rfl, rfl⟩
  · by_cases hb0 : b0 = 5#8
    · subst hb0
      by_cases hlen : rest.length < 32
      · right; right; right
        refine ⟨rest.length + 1, ?_, ?_⟩
        · rw [PublicKeyTryFrom.publicKey_deserialize_badKeyLength rest hlen]
        · rw [PublicKeyTryFrom.publicKey_deserialize_badKeyLength rest hlen]; rfl
      · left
        have hge : 32 ≤ rest.length := by omega
        refine ⟨_, PublicKeyTryFrom.publicKey_deserialize_ok_of_ge32 rest hge, ?_⟩
        rw [PublicKeyTryFrom.publicKey_deserialize_ok_of_ge32 rest hge]; rfl
    · right; right; left
      refine ⟨b0, ?_, ?_⟩
      · rw [PublicKeyTryFrom.publicKey_deserialize_badKeyType rest hb0]
      · rw [PublicKeyTryFrom.publicKey_deserialize_badKeyType rest hb0]; rfl

theorem le_of_eq32 {n k : Nat} (h : n = 32) (hk : k ≤ 32) : k ≤ n := h ▸ hk

theorem extractLsb'_append_lo {w1 w2 : Nat} (hi : BitVec w1) (lo : BitVec w2)
    (s k : Nat) (h : s + k ≤ w2) :
    (hi ++ lo).extractLsb' s k = lo.extractLsb' s k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  have hlt : s + i < w2 := by omega
  simp [BitVec.getLsbD_append, hi', hlt]

theorem extractLsb'_append_hi {w1 w2 : Nat} (hi : BitVec w1) (lo : BitVec w2)
    (s k : Nat) (h : w2 ≤ s) :
    (hi ++ lo).extractLsb' s k = hi.extractLsb' (s - w2) k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  have hnot : ¬(s + i < w2) := by omega
  have hsub : s - w2 + i = s + i - w2 := by omega
  simp [BitVec.getLsbD_append, hi', hnot, hsub]

theorem truncate16_zeroExtend32 (v : BitVec 16) :
    BitVec.truncate 16 (BitVec.zeroExtend 32 v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem truncate8_zeroExtend32 (v : BitVec 8) :
    BitVec.truncate 8 (BitVec.zeroExtend 32 v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem mask_split_64 (v : BitVec 64) :
    (v &&& (-256#64)) ||| (v &&& 255#64) = v := by
  bv_bits

theorem zero_orr_zext8_mask (t : BitVec 8) :
    0#64 ||| ((BitVec.zeroExtend 64 (BitVec.zeroExtend 32 t)) &&& 255#64) = t.zeroExtend 64 := by
  bv_bits

theorem sub_add_ofNat_eq_sub (sp a b : BitVec 64) (n : Nat)
    (h : 0#64 - b = 0#64 - a + BitVec.ofNat 64 n) :
    sp - b = sp - a + BitVec.ofNat 64 n := by
  have h0 : ∀ x : BitVec 64, 0#64 - x = -x := BitVec.zero_sub
  rw [h0, h0] at h
  rw [BitVec.sub_eq_add_neg, h, ← BitVec.add_assoc, ← BitVec.sub_eq_add_neg]

theorem sub_add_eq_sub (sp a b k : BitVec 64)
    (h : 0#64 - a + k = 0#64 - b) :
    sp - a + k = sp - b := by
  have h0 : ∀ x : BitVec 64, 0#64 - x = -x := BitVec.zero_sub
  rw [h0, h0] at h
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, h, ← BitVec.sub_eq_add_neg]

theorem add_add_ofNat_eq_add (ret a b : BitVec 64) (n : Nat)
    (h : b = a + BitVec.ofNat 64 n) :
    ret + b = ret + a + BitVec.ofNat 64 n := by
  rw [h, BitVec.add_assoc]

theorem add_ofNat_eq_add (ret b : BitVec 64) (n : Nat)
    (h : b = BitVec.ofNat 64 n) :
    ret + b = ret + BitVec.ofNat 64 n := by
  rw [h]

theorem add_add_eq_add (ret a b k : BitVec 64)
    (h : a + k = b) :
    ret + a + k = ret + b := by
  rw [BitVec.add_assoc, h]

/-! ## 2. Stack split (`stackAt sp 0x60`) & normalized `pkTryFromResultAt` -/

theorem stackAt_ikDec_split (sp : BitVec 64) :
    stackAt sp 0x60 =
      memRegion (sp - 96#64) 8 ∗
      memRegion (sp - 88#64) 40 ∗
      (∃∗ s48 : BitVec 64, (sp - 48#64) ↦₆₄ s48) ∗
      (∃∗ s40 : BitVec 8, (sp - 40#64) ↦₈ s40) ∗
      memRegion (sp - 39#64) 7 ∗
      (∃∗ s32 : BitVec 64, (sp - 32#64) ↦₆₄ s32) ∗
      (∃∗ s24 : BitVec 64, (sp - 24#64) ↦₆₄ s24) ∗
      (∃∗ s16 : BitVec 64, (sp - 16#64) ↦₆₄ s16) ∗
      (∃∗ s8 : BitVec 32, (sp - 8#64) ↦₃₂ s8) ∗
      (∃∗ s4 : BitVec 16, (sp - 4#64) ↦₁₆ s4) ∗
      memRegion (sp - 2#64) 2 := by
  simp only [stackAt]
  rw [show BitVec.ofNat 64 96 = 96#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 8) (k := 88)
        (b' := sp - 88#64) rfl (sub_add_ofNat_eq_sub sp 96#64 88#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 40) (k := 48)
        (b' := sp - 48#64) rfl (sub_add_ofNat_eq_sub sp 88#64 48#64 40 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 48#64) (n := 8) (k := 40)
        (b' := sp - 40#64) rfl (sub_add_ofNat_eq_sub sp 48#64 40#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 40#64) (n := 1) (k := 39)
        (b' := sp - 39#64) rfl (sub_add_ofNat_eq_sub sp 40#64 39#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 39#64) (n := 7) (k := 32)
        (b' := sp - 32#64) rfl (sub_add_ofNat_eq_sub sp 39#64 32#64 7 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
        (b' := sp - 24#64) rfl (sub_add_ofNat_eq_sub sp 32#64 24#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
        (b' := sp - 16#64) rfl (sub_add_ofNat_eq_sub sp 24#64 16#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
        (b' := sp - 8#64) rfl (sub_add_ofNat_eq_sub sp 16#64 8#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 8#64) (n := 4) (k := 4)
        (b' := sp - 4#64) rfl (sub_add_ofNat_eq_sub sp 8#64 4#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 4#64) (n := 2) (k := 2)
        (b' := sp - 2#64) rfl (sub_add_ofNat_eq_sub sp 4#64 2#64 2 rfl) (by decide),
      ProofLib.memRegion_eight (sp - 48#64), memRegion_one (sp - 40#64),
      ProofLib.memRegion_eight (sp - 32#64), ProofLib.memRegion_eight (sp - 24#64),
      ProofLib.memRegion_eight (sp - 16#64),
      memRegion_four (sp - 8#64), memRegion_two (sp - 4#64)]

theorem pkTryFrom_sp_88_ok (sp : BitVec 64) (pk : PublicKey) :
    pkTryFromResultAt (sp - 88#64) (.ok pk) =
      ((sp - 88#64) ↦₈ 0#8) ∗ ((sp - 87#64) ↦ₛ pk.bytes.toList) ∗ memRegion (sp - 55#64) 7 := by
  dsimp only [pkTryFromResultAt]
  rw [sub_add_eq_sub sp 88#64 87#64 1#64 rfl, sub_add_eq_sub sp 88#64 55#64 33#64 rfl]

theorem pkTryFrom_sp_88_nil (sp : BitVec 64) :
    pkTryFromResultAt (sp - 88#64) (.error .noKeyTypeIdentifier) =
      ((sp - 88#64) ↦₈ 1#8) ∗ memRegion (sp - 87#64) 7 ∗
        ((sp - 80#64) ↦₈ 0#8) ∗ memRegion (sp - 79#64) 31 := by
  dsimp only [pkTryFromResultAt]
  rw [sub_add_eq_sub sp 88#64 87#64 1#64 rfl, sub_add_eq_sub sp 88#64 80#64 8#64 rfl,
      sub_add_eq_sub sp 88#64 79#64 9#64 rfl]

theorem pkTryFrom_sp_88_badType (sp : BitVec 64) (t : BitVec 8) :
    pkTryFromResultAt (sp - 88#64) (.error (.badKeyType t)) =
      ((sp - 88#64) ↦₈ 1#8) ∗ memRegion (sp - 87#64) 7 ∗
        ((sp - 80#64) ↦₈ 1#8) ∗ ((sp - 79#64) ↦₈ t) ∗ memRegion (sp - 78#64) 30 := by
  dsimp only [pkTryFromResultAt]
  rw [sub_add_eq_sub sp 88#64 87#64 1#64 rfl, sub_add_eq_sub sp 88#64 80#64 8#64 rfl,
      sub_add_eq_sub sp 88#64 79#64 9#64 rfl, sub_add_eq_sub sp 88#64 78#64 10#64 rfl]

theorem pkTryFrom_sp_88_badLen (sp : BitVec 64) (n : Nat) :
    pkTryFromResultAt (sp - 88#64) (.error (.badKeyLength n)) =
      ((sp - 88#64) ↦₈ 1#8) ∗ memRegion (sp - 87#64) 7 ∗
        ((sp - 80#64) ↦₈ 2#8) ∗ memRegion (sp - 79#64) 7 ∗
        ((sp - 72#64) ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (sp - 64#64) 16 := by
  dsimp only [pkTryFromResultAt]
  rw [sub_add_eq_sub sp 88#64 87#64 1#64 rfl, sub_add_eq_sub sp 88#64 80#64 8#64 rfl,
      sub_add_eq_sub sp 88#64 79#64 9#64 rfl, sub_add_eq_sub sp 88#64 72#64 16#64 rfl,
      sub_add_eq_sub sp 88#64 64#64 24#64 rfl]

/-! ## 3. Key chunks (`Ok` path) -/

def ikKeyChunks (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) : SepProp :=
  (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
  ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
  ((a + 7#64) ↦₁₆ v7) ∗ ((a + 9#64) ↦₃₂ v9) ∗ ((a + 13#64) ↦₁₆ v13) ∗
  ((a + 15#64) ↦₆₄ v15) ∗ ((a + 23#64) ↦₆₄ v23) ∗ ((a + 31#64) ↦₈ v31)

private theorem pointsToBytes_drop_split (a : BitVec 64) (bs : List (BitVec 8)) (off k : Nat)
    (h : off + k ≤ bs.length) :
    (a ↦ₛ bs.drop off) =
      (a ↦ₛ (bs.drop off).take k) ∗ ((a + BitVec.ofNat 64 k) ↦ₛ bs.drop (off + k)) := by
  conv => lhs; rw [← List.take_append_drop k (bs.drop off)]
  have hlen : ((bs.drop off).take k).length = k := by
    simp [List.length_take, List.length_drop]
    omega
  rw [pointsToBytes_append, hlen, List.drop_drop]

theorem exists_ikKeyChunks_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
      (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
      (v15 v23 : BitVec 64) (v31 : BitVec 8),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) = ikKeyChunks a b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 := by
  refine ⟨bs.getD 0 0#8, bs.getD 1 0#8, bs.getD 2 0#8, bs.getD 3 0#8,
    bs.getD 4 0#8, bs.getD 5 0#8, bs.getD 6 0#8,
    pack16 (bs.getD 7 0#8) (bs.getD 8 0#8),
    pack32 (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8) (bs.getD 12 0#8),
    pack16 (bs.getD 13 0#8) (bs.getD 14 0#8),
    pack64 (bs.getD 15 0#8) (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8)
      (bs.getD 19 0#8) (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8),
    pack64 (bs.getD 23 0#8) (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8)
      (bs.getD 27 0#8) (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8),
    bs.getD 31 0#8, fun a => ?_⟩
  change (a ↦ₛ bs.drop 0) = _
  rw [pointsToBytes_drop_split a bs 0 4 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 4 1 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 5 1 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 6 1 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 7 2 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 9 4 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 13 2 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 15 8 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 23 8 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 31 1 (le_of_eq32 h (by decide))]
  have hdrop32 : bs.drop 32 = [] := by simp [h]
  rw [hdrop32, pointsToBytes_nil, sepConj_emp,
      pointsToBytes_take4_eq_pointsTo32 _ bs 0 (le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 4 (le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 5 (le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 6 (le_of_eq32 h (by decide)),
      pointsToBytes_take2_eq_pointsTo16 _ bs 7 (le_of_eq32 h (by decide)),
      pointsToBytes_take4_eq_pointsTo32 _ bs 9 (le_of_eq32 h (by decide)),
      pointsToBytes_take2_eq_pointsTo16 _ bs 13 (le_of_eq32 h (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 15 (le_of_eq32 h (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 23 (le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 31 (le_of_eq32 h (by decide))]
  have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
  have h1 : BitVec.ofNat 64 1 = 1#64 := rfl
  have h4 : BitVec.ofNat 64 4 = 4#64 := rfl
  have h2 : BitVec.ofNat 64 2 = 2#64 := rfl
  rw [h8, h1, h4, h2]
  simp only [ikKeyChunks, pack32, BitVec.add_assoc, BitVec.reduceAdd]

theorem ikKeyChunks_sp_87 (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) :
    ikKeyChunks (sp - 87#64) b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 =
      ((sp - 87#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((sp - 83#64) ↦₈ b4) ∗ ((sp - 82#64) ↦₈ b5) ∗ ((sp - 81#64) ↦₈ b6) ∗
      ((sp - 80#64) ↦₁₆ v7) ∗ ((sp - 78#64) ↦₃₂ v9) ∗ ((sp - 74#64) ↦₁₆ v13) ∗
      ((sp - 72#64) ↦₆₄ v15) ∗ ((sp - 64#64) ↦₆₄ v23) ∗ ((sp - 56#64) ↦₈ v31) := by
  dsimp only [ikKeyChunks]
  have h83 : sp - 87#64 + 4#64 = sp - 83#64 := sub_add_eq_sub sp 87#64 83#64 4#64 rfl
  have h82 : sp - 87#64 + 5#64 = sp - 82#64 := sub_add_eq_sub sp 87#64 82#64 5#64 rfl
  have h81 : sp - 87#64 + 6#64 = sp - 81#64 := sub_add_eq_sub sp 87#64 81#64 6#64 rfl
  have h80 : sp - 87#64 + 7#64 = sp - 80#64 := sub_add_eq_sub sp 87#64 80#64 7#64 rfl
  have h78 : sp - 87#64 + 9#64 = sp - 78#64 := sub_add_eq_sub sp 87#64 78#64 9#64 rfl
  have h74 : sp - 87#64 + 13#64 = sp - 74#64 := sub_add_eq_sub sp 87#64 74#64 13#64 rfl
  have h72 : sp - 87#64 + 15#64 = sp - 72#64 := sub_add_eq_sub sp 87#64 72#64 15#64 rfl
  have h64 : sp - 87#64 + 23#64 = sp - 64#64 := sub_add_eq_sub sp 87#64 64#64 23#64 rfl
  have h56 : sp - 87#64 + 31#64 = sp - 56#64 := sub_add_eq_sub sp 87#64 56#64 31#64 rfl
  rw [h83, h82, h81, h80, h78, h74, h72, h64, h56]

theorem ikKeyChunks_ret_8 (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) :
    ikKeyChunks (ret + 8#64) b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 =
      ((ret + 8#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((ret + 12#64) ↦₈ b4) ∗ ((ret + 13#64) ↦₈ b5) ∗ ((ret + 14#64) ↦₈ b6) ∗
      ((ret + 15#64) ↦₁₆ v7) ∗ ((ret + 17#64) ↦₃₂ v9) ∗ ((ret + 21#64) ↦₁₆ v13) ∗
      ((ret + 23#64) ↦₆₄ v15) ∗ ((ret + 31#64) ↦₆₄ v23) ∗ ((ret + 39#64) ↦₈ v31) := by
  dsimp only [ikKeyChunks]
  have hr12 : ret + 8#64 + 4#64 = ret + 12#64 := add_add_eq_add ret 8#64 12#64 4#64 rfl
  have hr13 : ret + 8#64 + 5#64 = ret + 13#64 := add_add_eq_add ret 8#64 13#64 5#64 rfl
  have hr14 : ret + 8#64 + 6#64 = ret + 14#64 := add_add_eq_add ret 8#64 14#64 6#64 rfl
  have hr15 : ret + 8#64 + 7#64 = ret + 15#64 := add_add_eq_add ret 8#64 15#64 7#64 rfl
  have hr17 : ret + 8#64 + 9#64 = ret + 17#64 := add_add_eq_add ret 8#64 17#64 9#64 rfl
  have hr21 : ret + 8#64 + 13#64 = ret + 21#64 := add_add_eq_add ret 8#64 21#64 13#64 rfl
  have hr23 : ret + 8#64 + 15#64 = ret + 23#64 := add_add_eq_add ret 8#64 23#64 15#64 rfl
  have hr31 : ret + 8#64 + 23#64 = ret + 31#64 := add_add_eq_add ret 8#64 31#64 23#64 rfl
  have hr39 : ret + 8#64 + 31#64 = ret + 39#64 := add_add_eq_add ret 8#64 39#64 31#64 rfl
  rw [hr12, hr13, hr14, hr15, hr17, hr21, hr23, hr31, hr39]

private theorem sevenLo_eq_sevenHi (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6)) =
      ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3))) := by
  rw [← pointsToBytes4_eq_pointsTo32, ← pointsToBytes4_eq_pointsTo32]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem sevenLo_eq_sevenHi' (a a1 a2 a3 a4 a5 a6 : BitVec 64)
    (h1 : a + 1#64 = a1) (h2 : a + 2#64 = a2) (h3 : a + 3#64 = a3)
    (h4 : a + 4#64 = a4) (h5 : a + 5#64 = a5) (h6 : a + 6#64 = a6)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ (a4 ↦₈ b4) ∗ (a5 ↦₈ b5) ∗ (a6 ↦₈ b6) ∗ rest) =
      ((a ↦₈ b0) ∗ (a1 ↦₈ b1) ∗ (a2 ↦₈ b2) ∗ (a3 ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) := by
  subst h1 h2 h3 h4 h5 h6
  simpa only [sepConj_assoc] using
    congrArg (· ∗ rest) (sevenLo_eq_sevenHi a b0 b1 b2 b3 b4 b5 b6)

theorem sevenLo_sp_87 (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 87#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((sp - 83#64) ↦₈ b4) ∗ ((sp - 82#64) ↦₈ b5) ∗ ((sp - 81#64) ↦₈ b6) ∗ rest) =
      (((sp - 87#64) ↦₈ b0) ∗ ((sp - 86#64) ↦₈ b1) ∗ ((sp - 85#64) ↦₈ b2) ∗
       ((sp - 84#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (sp - 87#64) (sp - 86#64) (sp - 85#64) (sp - 84#64)
    (sp - 83#64) (sp - 82#64) (sp - 81#64)
    (sub_add_eq_sub sp 87#64 86#64 1#64 rfl)
    (sub_add_eq_sub sp 87#64 85#64 2#64 rfl)
    (sub_add_eq_sub sp 87#64 84#64 3#64 rfl)
    (sub_add_eq_sub sp 87#64 83#64 4#64 rfl)
    (sub_add_eq_sub sp 87#64 82#64 5#64 rfl)
    (sub_add_eq_sub sp 87#64 81#64 6#64 rfl)
    b0 b1 b2 b3 b4 b5 b6 rest

theorem sevenLo_ret_8 (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((ret + 8#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((ret + 12#64) ↦₈ b4) ∗ ((ret + 13#64) ↦₈ b5) ∗ ((ret + 14#64) ↦₈ b6) ∗ rest) =
      (((ret + 8#64) ↦₈ b0) ∗ ((ret + 9#64) ↦₈ b1) ∗ ((ret + 10#64) ↦₈ b2) ∗
       ((ret + 11#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (ret + 8#64) (ret + 9#64) (ret + 10#64) (ret + 11#64)
    (ret + 12#64) (ret + 13#64) (ret + 14#64)
    (add_add_eq_add ret 8#64 9#64 1#64 rfl)
    (add_add_eq_add ret 8#64 10#64 2#64 rfl)
    (add_add_eq_add ret 8#64 11#64 3#64 rfl)
    (add_add_eq_add ret 8#64 12#64 4#64 rfl)
    (add_add_eq_add ret 8#64 13#64 5#64 rfl)
    (add_add_eq_add ret 8#64 14#64 6#64 rfl)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem pointsTo16_pair_eq_pointsTo32 (a : BitVec 64) (lo hi : BitVec 16) :
    ((a ↦₁₆ lo) ∗ ((a + 2#64) ↦₁₆ hi)) = (a ↦₃₂ (hi ++ lo)) := by
  simp only [pointsTo16, pointsTo32, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  have e0 : lo.extractLsb' 0 8 = (hi ++ lo).extractLsb' 0 8 :=
    (extractLsb'_append_lo hi lo 0 8 (by decide)).symm
  have e1 : lo.extractLsb' 8 8 = (hi ++ lo).extractLsb' 8 8 :=
    (extractLsb'_append_lo hi lo 8 8 (by decide)).symm
  have e2 : hi.extractLsb' 0 8 = (hi ++ lo).extractLsb' 16 8 :=
    (extractLsb'_append_hi hi lo 16 8 (by decide)).symm
  have e3 : hi.extractLsb' 8 8 = (hi ++ lo).extractLsb' 24 8 :=
    (extractLsb'_append_hi hi lo 24 8 (by decide)).symm
  rw [e0, e1, e2, e3]

theorem sp_88_repack (sp : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 88#64) ↦₈ 0#8) ∗ ((sp - 87#64) ↦₈ b0) ∗ ((sp - 86#64) ↦₈ b1) ∗
     ((sp - 85#64) ↦₈ b2) ∗ ((sp - 84#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) =
    (((sp - 88#64) ↦₃₂ (b2 ++ b1 ++ b0 ++ 0#8)) ∗
     ((sp - 84#64) ↦₁₆ (b4 ++ b3)) ∗ ((sp - 82#64) ↦₁₆ (b6 ++ b5)) ∗ rest) := by
  have h87 : sp - 88#64 + 1#64 = sp - 87#64 := sub_add_eq_sub sp 88#64 87#64 1#64 rfl
  have h86 : sp - 88#64 + 2#64 = sp - 86#64 := sub_add_eq_sub sp 88#64 86#64 2#64 rfl
  have h85 : sp - 88#64 + 3#64 = sp - 85#64 := sub_add_eq_sub sp 88#64 85#64 3#64 rfl
  have h82 : sp - 84#64 + 2#64 = sp - 82#64 := sub_add_eq_sub sp 84#64 82#64 2#64 rfl
  have hlo : (((sp - 88#64) ↦₈ 0#8) ∗ ((sp - 87#64) ↦₈ b0) ∗
      ((sp - 86#64) ↦₈ b1) ∗ ((sp - 85#64) ↦₈ b2)) =
      ((sp - 88#64) ↦₃₂ (b2 ++ b1 ++ b0 ++ 0#8)) := by
    rw [← pointsToBytes4_eq_pointsTo32]
    simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
      BitVec.add_assoc, BitVec.reduceAdd]
    rw [h87, h86, h85]
  have hhi : ((sp - 84#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) =
      (((sp - 84#64) ↦₁₆ (b4 ++ b3)) ∗ ((sp - 82#64) ↦₁₆ (b6 ++ b5))) := by
    rw [← h82, pointsTo16_pair_eq_pointsTo32]
    congr 1; bv_bits
  calc (((sp - 88#64) ↦₈ 0#8) ∗ ((sp - 87#64) ↦₈ b0) ∗ ((sp - 86#64) ↦₈ b1) ∗
         ((sp - 85#64) ↦₈ b2) ∗ ((sp - 84#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest)
      = ((((sp - 88#64) ↦₈ 0#8) ∗ ((sp - 87#64) ↦₈ b0) ∗ ((sp - 86#64) ↦₈ b1) ∗
          ((sp - 85#64) ↦₈ b2)) ∗ ((sp - 84#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) := by
        simp only [sepConj_assoc]
    _ = (((sp - 88#64) ↦₃₂ (b2 ++ b1 ++ b0 ++ 0#8)) ∗
          (((sp - 84#64) ↦₁₆ (b4 ++ b3)) ∗ ((sp - 82#64) ↦₁₆ (b6 ++ b5))) ∗ rest) := by
        rw [hlo, hhi]
    _ = _ := by simp only [sepConj_assoc]

theorem memRegion_48_ok_split (ret : BitVec 64) :
    memRegion ret 48 =
      (∃∗ r0 : BitVec 64, ret ↦₆₄ r0) ∗
      (∃∗ r8 : BitVec 32, (ret + 8#64) ↦₃₂ r8) ∗
      (∃∗ r12 : BitVec 8, (ret + 12#64) ↦₈ r12) ∗
      (∃∗ r13 : BitVec 8, (ret + 13#64) ↦₈ r13) ∗
      (∃∗ r14 : BitVec 8, (ret + 14#64) ↦₈ r14) ∗
      (∃∗ r15 : BitVec 16, (ret + 15#64) ↦₁₆ r15) ∗
      (∃∗ r17 : BitVec 32, (ret + 17#64) ↦₃₂ r17) ∗
      (∃∗ r21 : BitVec 16, (ret + 21#64) ↦₁₆ r21) ∗
      (∃∗ r23 : BitVec 64, (ret + 23#64) ↦₆₄ r23) ∗
      (∃∗ r31 : BitVec 64, (ret + 31#64) ↦₆₄ r31) ∗
      (∃∗ r39 : BitVec 8, (ret + 39#64) ↦₈ r39) ∗
      memRegion (ret + 40#64) 8 := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 8) (k := 40)
        (b' := ret + 8#64) rfl (add_ofNat_eq_add ret 8#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 8#64) (n := 4) (k := 36)
        (b' := ret + 12#64) rfl (add_add_ofNat_eq_add ret 8#64 12#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 12#64) (n := 1) (k := 35)
        (b' := ret + 13#64) rfl (add_add_ofNat_eq_add ret 12#64 13#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 13#64) (n := 1) (k := 34)
        (b' := ret + 14#64) rfl (add_add_ofNat_eq_add ret 13#64 14#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 14#64) (n := 1) (k := 33)
        (b' := ret + 15#64) rfl (add_add_ofNat_eq_add ret 14#64 15#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 15#64) (n := 2) (k := 31)
        (b' := ret + 17#64) rfl (add_add_ofNat_eq_add ret 15#64 17#64 2 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 17#64) (n := 4) (k := 27)
        (b' := ret + 21#64) rfl (add_add_ofNat_eq_add ret 17#64 21#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 21#64) (n := 2) (k := 25)
        (b' := ret + 23#64) rfl (add_add_ofNat_eq_add ret 21#64 23#64 2 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 23#64) (n := 8) (k := 17)
        (b' := ret + 31#64) rfl (add_add_ofNat_eq_add ret 23#64 31#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 31#64) (n := 8) (k := 9)
        (b' := ret + 39#64) rfl (add_add_ofNat_eq_add ret 31#64 39#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 39#64) (n := 1) (k := 8)
        (b' := ret + 40#64) rfl (add_add_ofNat_eq_add ret 39#64 40#64 1 rfl) (by decide),
      ProofLib.memRegion_eight ret, memRegion_four (ret + 8#64),
      memRegion_one (ret + 12#64), memRegion_one (ret + 13#64), memRegion_one (ret + 14#64),
      memRegion_two (ret + 15#64), memRegion_four (ret + 17#64), memRegion_two (ret + 21#64),
      ProofLib.memRegion_eight (ret + 23#64), ProofLib.memRegion_eight (ret + 31#64),
      memRegion_one (ret + 39#64)]

/-! ## 4. Pure-equality postcondition splits for `wp_done` -/

theorem memRegion_sp_88_ok_post (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      (∃∗ w88 : BitVec 32, (sp - 88#64) ↦₃₂ w88) ∗
      (∃∗ w84 : BitVec 16, (sp - 84#64) ↦₁₆ w84) ∗
      (∃∗ w82 : BitVec 16, (sp - 82#64) ↦₁₆ w82) ∗
      (∃∗ v7 : BitVec 16, (sp - 80#64) ↦₁₆ v7) ∗
      (∃∗ v9 : BitVec 32, (sp - 78#64) ↦₃₂ v9) ∗
      (∃∗ v13 : BitVec 16, (sp - 74#64) ↦₁₆ v13) ∗
      (∃∗ v15 : BitVec 64, (sp - 72#64) ↦₆₄ v15) ∗
      (∃∗ v23 : BitVec 64, (sp - 64#64) ↦₆₄ v23) ∗
      (∃∗ v31 : BitVec 8, (sp - 56#64) ↦₈ v31) ∗
      memRegion (sp - 55#64) 7 := by
  rw [ProofLib.memRegion_split' (b := sp - 88#64) (n := 4) (k := 36)
        (b' := sp - 84#64) rfl (sub_add_ofNat_eq_sub sp 88#64 84#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 84#64) (n := 2) (k := 34)
        (b' := sp - 82#64) rfl (sub_add_ofNat_eq_sub sp 84#64 82#64 2 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 82#64) (n := 2) (k := 32)
        (b' := sp - 80#64) rfl (sub_add_ofNat_eq_sub sp 82#64 80#64 2 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 2) (k := 30)
        (b' := sp - 78#64) rfl (sub_add_ofNat_eq_sub sp 80#64 78#64 2 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 78#64) (n := 4) (k := 26)
        (b' := sp - 74#64) rfl (sub_add_ofNat_eq_sub sp 78#64 74#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 74#64) (n := 2) (k := 24)
        (b' := sp - 72#64) rfl (sub_add_ofNat_eq_sub sp 74#64 72#64 2 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 8) (k := 16)
        (b' := sp - 64#64) rfl (sub_add_ofNat_eq_sub sp 72#64 64#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 8)
        (b' := sp - 56#64) rfl (sub_add_ofNat_eq_sub sp 64#64 56#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 1) (k := 7)
        (b' := sp - 55#64) rfl (sub_add_ofNat_eq_sub sp 56#64 55#64 1 rfl) (by decide),
      memRegion_four (sp - 88#64), memRegion_two (sp - 84#64), memRegion_two (sp - 82#64),
      memRegion_two (sp - 80#64), memRegion_four (sp - 78#64), memRegion_two (sp - 74#64),
      ProofLib.memRegion_eight (sp - 72#64), ProofLib.memRegion_eight (sp - 64#64),
      memRegion_one (sp - 56#64)]

theorem memRegion_sp_88_nil_post (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      (∃∗ u88 : BitVec 8, (sp - 88#64) ↦₈ u88) ∗
      memRegion (sp - 87#64) 7 ∗
      (∃∗ u80 : BitVec 8, (sp - 80#64) ↦₈ u80) ∗
      memRegion (sp - 79#64) 31 := by
  rw [ProofLib.memRegion_split' (b := sp - 88#64) (n := 1) (k := 39)
        (b' := sp - 87#64) rfl (sub_add_ofNat_eq_sub sp 88#64 87#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 87#64) (n := 7) (k := 32)
        (b' := sp - 80#64) rfl (sub_add_ofNat_eq_sub sp 87#64 80#64 7 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 1) (k := 31)
        (b' := sp - 79#64) rfl (sub_add_ofNat_eq_sub sp 80#64 79#64 1 rfl) (by decide),
      memRegion_one (sp - 88#64), memRegion_one (sp - 80#64)]

theorem memRegion_sp_88_badType_post (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      (∃∗ u88 : BitVec 8, (sp - 88#64) ↦₈ u88) ∗
      memRegion (sp - 87#64) 7 ∗
      (∃∗ u80 : BitVec 8, (sp - 80#64) ↦₈ u80) ∗
      (∃∗ u79 : BitVec 8, (sp - 79#64) ↦₈ u79) ∗
      memRegion (sp - 78#64) 30 := by
  rw [ProofLib.memRegion_split' (b := sp - 88#64) (n := 1) (k := 39)
        (b' := sp - 87#64) rfl (sub_add_ofNat_eq_sub sp 88#64 87#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 87#64) (n := 7) (k := 32)
        (b' := sp - 80#64) rfl (sub_add_ofNat_eq_sub sp 87#64 80#64 7 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 1) (k := 31)
        (b' := sp - 79#64) rfl (sub_add_ofNat_eq_sub sp 80#64 79#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 79#64) (n := 1) (k := 30)
        (b' := sp - 78#64) rfl (sub_add_ofNat_eq_sub sp 79#64 78#64 1 rfl) (by decide),
      memRegion_one (sp - 88#64), memRegion_one (sp - 80#64), memRegion_one (sp - 79#64)]

theorem memRegion_sp_88_badLen_post (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      (∃∗ u88 : BitVec 8, (sp - 88#64) ↦₈ u88) ∗
      memRegion (sp - 87#64) 7 ∗
      (∃∗ u80 : BitVec 8, (sp - 80#64) ↦₈ u80) ∗
      memRegion (sp - 79#64) 7 ∗
      (∃∗ u72 : BitVec 64, (sp - 72#64) ↦₆₄ u72) ∗
      memRegion (sp - 64#64) 16 := by
  rw [ProofLib.memRegion_split' (b := sp - 88#64) (n := 1) (k := 39)
        (b' := sp - 87#64) rfl (sub_add_ofNat_eq_sub sp 88#64 87#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 87#64) (n := 7) (k := 32)
        (b' := sp - 80#64) rfl (sub_add_ofNat_eq_sub sp 87#64 80#64 7 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 1) (k := 31)
        (b' := sp - 79#64) rfl (sub_add_ofNat_eq_sub sp 80#64 79#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 79#64) (n := 7) (k := 24)
        (b' := sp - 72#64) rfl (sub_add_ofNat_eq_sub sp 79#64 72#64 7 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 8) (k := 16)
        (b' := sp - 64#64) rfl (sub_add_ofNat_eq_sub sp 72#64 64#64 8 rfl) (by decide),
      memRegion_one (sp - 88#64), memRegion_one (sp - 80#64),
      ProofLib.memRegion_eight (sp - 72#64)]

theorem memRegion_48_err_split (ret : BitVec 64) :
    memRegion ret 48 =
      (∃∗ r0 : BitVec 64, ret ↦₆₄ r0) ∗
      (∃∗ r8 : BitVec 64, (ret + 8#64) ↦₆₄ r8) ∗
      memRegion (ret + 16#64) 32 := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 8) (k := 40)
        (b' := ret + 8#64) rfl (add_ofNat_eq_add ret 8#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 8#64) (n := 8) (k := 32)
        (b' := ret + 16#64) rfl (add_add_ofNat_eq_add ret 8#64 16#64 8 rfl) (by decide),
      ProofLib.memRegion_eight ret, ProofLib.memRegion_eight (ret + 8#64)]

theorem spe_noKeyType_post (A : RustAlloc) (ret : BitVec 64) :
    identityKeyResultAt A ret (.error .noKeyTypeIdentifier) =
      (ret ↦₆₄ speWord 7) ∗
      (∃∗ r8 : BitVec 64, (ret + 8#64) ↦₆₄ r8) ∗
      memRegion (ret + 16#64) 32 := by
  dsimp only [identityKeyResultAt, speAt]
  rw [ProofLib.memRegion_split' (b := ret + 8#64) (n := 8) (k := 32)
        (b' := ret + 16#64) rfl (add_add_ofNat_eq_add ret 8#64 16#64 8 rfl) (by decide),
      ProofLib.memRegion_eight (ret + 8#64)]

theorem pointsTo64_zext8_split (ret : BitVec 64) (t : BitVec 8) :
    ((ret + 8#64) ↦₆₄ t.zeroExtend 64) =
      ((ret + 8#64) ↦₈ t) ∗
      ((ret + 9#64) ↦₈ 0#8) ∗ ((ret + 10#64) ↦₈ 0#8) ∗ ((ret + 11#64) ↦₈ 0#8) ∗
      ((ret + 12#64) ↦₈ 0#8) ∗ ((ret + 13#64) ↦₈ 0#8) ∗ ((ret + 14#64) ↦₈ 0#8) ∗
      ((ret + 15#64) ↦₈ 0#8) := by
  rw [pointsTo64_eq_pointsToBytes]
  dsimp only [unpack64]
  have e0 : (t.zeroExtend 64).extractLsb' 0 8 = t := by bv_bits
  have e1 : (t.zeroExtend 64).extractLsb' 8 8 = 0#8 := by bv_bits
  have e2 : (t.zeroExtend 64).extractLsb' 16 8 = 0#8 := by bv_bits
  have e3 : (t.zeroExtend 64).extractLsb' 24 8 = 0#8 := by bv_bits
  have e4 : (t.zeroExtend 64).extractLsb' 32 8 = 0#8 := by bv_bits
  have e5 : (t.zeroExtend 64).extractLsb' 40 8 = 0#8 := by bv_bits
  have e6 : (t.zeroExtend 64).extractLsb' 48 8 = 0#8 := by bv_bits
  have e7 : (t.zeroExtend 64).extractLsb' 56 8 = 0#8 := by bv_bits
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem spe_badKeyType_post (A : RustAlloc) (ret : BitVec 64) (t : BitVec 8) :
    identityKeyResultAt A ret (.error (.badKeyType t)) =
      (ret ↦₆₄ speWord 8) ∗
      ((ret + 8#64) ↦₈ t) ∗
      (∃∗ z9 : BitVec 8, (ret + 9#64) ↦₈ z9) ∗
      (∃∗ z10 : BitVec 8, (ret + 10#64) ↦₈ z10) ∗
      (∃∗ z11 : BitVec 8, (ret + 11#64) ↦₈ z11) ∗
      (∃∗ z12 : BitVec 8, (ret + 12#64) ↦₈ z12) ∗
      (∃∗ z13 : BitVec 8, (ret + 13#64) ↦₈ z13) ∗
      (∃∗ z14 : BitVec 8, (ret + 14#64) ↦₈ z14) ∗
      (∃∗ z15 : BitVec 8, (ret + 15#64) ↦₈ z15) ∗
      memRegion (ret + 16#64) 32 := by
  dsimp only [identityKeyResultAt, speAt]
  rw [ProofLib.memRegion_split' (b := ret + 9#64) (n := 1) (k := 38)
        (b' := ret + 10#64) rfl (add_add_ofNat_eq_add ret 9#64 10#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 10#64) (n := 1) (k := 37)
        (b' := ret + 11#64) rfl (add_add_ofNat_eq_add ret 10#64 11#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 11#64) (n := 1) (k := 36)
        (b' := ret + 12#64) rfl (add_add_ofNat_eq_add ret 11#64 12#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 12#64) (n := 1) (k := 35)
        (b' := ret + 13#64) rfl (add_add_ofNat_eq_add ret 12#64 13#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 13#64) (n := 1) (k := 34)
        (b' := ret + 14#64) rfl (add_add_ofNat_eq_add ret 13#64 14#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 14#64) (n := 1) (k := 33)
        (b' := ret + 15#64) rfl (add_add_ofNat_eq_add ret 14#64 15#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 15#64) (n := 1) (k := 32)
        (b' := ret + 16#64) rfl (add_add_ofNat_eq_add ret 15#64 16#64 1 rfl) (by decide),
      memRegion_one (ret + 9#64), memRegion_one (ret + 10#64), memRegion_one (ret + 11#64),
      memRegion_one (ret + 12#64), memRegion_one (ret + 13#64), memRegion_one (ret + 14#64),
      memRegion_one (ret + 15#64)]

end CryptoVerification.RecordCodecsBinary.IdentityKeyDecode.Helpers
