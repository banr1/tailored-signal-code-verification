/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Hmac.Defs
import ProofLib.SepLogic.WP.StateNorm

/-!
# Merkle–Damgård block decompositions for `MacEnv`

Pure list and `BitVec` lemmas relating the `MacEnv` intermediates (`innerMsg`, `hState`,
`innerPadded`, `innerHash`, `outerMsg`) to `sha256With` and `hmacSha256Trunc8` for 32-byte keys.
-/

@[expose] public section


namespace CryptoVerification
namespace LibsignalHmac
namespace MD

open Arm64 CryptoGames CryptoGames.HMAC

variable (e : MacEnv) (F : ShaState → List (BitVec 8) → ShaState)

@[simp] private theorem chunks64_length (bs : List (BitVec 8)) :
    (chunks64 bs).length = bs.length / 64 := by
  simp [chunks64]

@[simp] private theorem chunks64_getElem (bs : List (BitVec 8)) (i : ℕ)
    (hi : i < (chunks64 bs).length) :
    (chunks64 bs)[i] = (bs.drop (64 * i)).take 64 := by
  simp [chunks64]

private theorem chunks64_of_lt {bs : List (BitVec 8)} (h : bs.length < 64) :
    chunks64 bs = [] := by
  rw [← List.length_eq_zero_iff, chunks64_length]
  omega

private theorem chunks64_append_64 {a b : List (BitVec 8)} (ha : a.length = 64) :
    chunks64 (a ++ b) = a :: chunks64 b := by
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · simp [ha]
  · cases i with
    | zero =>
      simp [ha]
    | succ j =>
      simp only [chunks64_getElem, List.getElem_cons_succ]
      have hdrop : 64 * (j + 1) = a.length + 64 * j := by omega
      rw [hdrop, ← List.drop_drop, List.drop_left]

private theorem chunks64_single {a : List (BitVec 8)} (ha : a.length = 64) :
    chunks64 a = [a] := by
  conv_lhs => rw [← List.append_nil a]
  rw [chunks64_append_64 ha, chunks64_of_lt (by simp)]

private theorem chunks64_append_mul {a b : List (BitVec 8)} (k : ℕ) (ha : a.length = 64 * k) :
    chunks64 (a ++ b) = chunks64 a ++ chunks64 b := by
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · simp [ha]; omega
  · rw [chunks64_getElem]
    by_cases hi : i < (chunks64 a).length
    · rw [List.getElem_append_left hi, chunks64_getElem]
      have hle : 64 * i + 64 ≤ a.length := by
        simp only [chunks64_length] at hi
        omega
      rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
    · rw [List.getElem_append_right (by omega), chunks64_getElem]
      simp only [chunks64_length] at hi ⊢
      have hdrop : 64 * i = a.length + 64 * (i - a.length / 64) := by omega
      rw [hdrop, ← List.drop_drop, List.drop_left]

private theorem chunks64_eq_take_mul (bs : List (BitVec 8)) :
    chunks64 bs = chunks64 (bs.take (64 * (bs.length / 64))) := by
  have h1 : (bs.take (64 * (bs.length / 64))).length = 64 * (bs.length / 64) := by
    rw [List.length_take]; omega
  have h2 : (bs.drop (64 * (bs.length / 64))).length < 64 := by
    rw [List.length_drop]; omega
  conv_lhs =>
    rw [← List.take_append_drop (64 * (bs.length / 64)) bs,
      chunks64_append_mul (bs.length / 64) h1, chunks64_of_lt h2, List.append_nil]

private theorem ipadKey_length (hk : e.vkey.length = 32) : e.ipadKey.length = 64 := by
  simp [MacEnv.ipadKey, MacEnv.k0, hk]

private theorem opadKey_length (hk : e.vkey.length = 32) : e.opadKey.length = 64 := by
  simp [MacEnv.opadKey, MacEnv.k0, hk]

@[simp] private theorem toBEBytes_length (n : ℕ) {w : ℕ} (x : BitVec w) :
    (toBEBytes n x).length = n := by
  simp [toBEBytes]

@[simp] private theorem sha256With_length (m : List (BitVec 8)) :
    (sha256With F m).length = 32 := by
  unfold sha256With
  generalize ((chunks64 (sha256Pad m)).foldl F sha256IV) = st
  rcases st with ⟨l, hl⟩
  simp [List.length_flatMap, hl]

theorem innerMsg_length (hk : e.vkey.length = 32) : e.innerMsg.length = 130 + e.vmsg.length := by
  simp [MacEnv.innerMsg, hk]
  omega

private theorem innerMsg_split2 :
    e.innerMsg =
      e.ipadKey ++ ((e.vsik.toList ++ e.vrik.toList.take 31) ++
        (e.vrik.toList.drop 31 ++ e.vmsg)) := by
  unfold MacEnv.innerMsg
  conv_lhs => rw [← List.take_append_drop 31 e.vrik.toList]
  simp only [List.append_assoc]

private theorem blk2_length : (e.vsik.toList ++ e.vrik.toList.take 31).length = 64 := by
  simp

private theorem chunks64_innerMsg (hk : e.vkey.length = 32) :
    chunks64 e.innerMsg =
      e.ipadKey :: (e.vsik.toList ++ e.vrik.toList.take 31) ::
        chunks64 (e.vrik.toList.drop 31 ++ e.vmsg) := by
  rw [innerMsg_split2 e, chunks64_append_64 (ipadKey_length e hk),
    chunks64_append_64 (blk2_length e)]

/-- Block 1 of `innerMsg` is `k ⊕ ipad` (compress #1). -/
theorem hState_one (hk : e.vkey.length = 32) : e.hState F 1 = F sha256IV e.ipadKey := by
  unfold MacEnv.hState
  rw [chunks64_innerMsg e hk]
  rfl

/-- Block 2 is `sik ‖ rik[..31]` (compress #3). -/
theorem hState_two (hk : e.vkey.length = 32) :
    e.hState F 2 = F (e.hState F 1) (e.vsik.toList ++ e.vrik.toList.take 31) := by
  unfold MacEnv.hState
  rw [chunks64_innerMsg e hk]
  rfl

/-- Short path (`L ≤ 61`): two whole blocks, `rik[31..] ‖ msg` buffered. -/
theorem short (hk : e.vkey.length = 32) (hL : e.vmsg.length ≤ 61) :
    e.innerB = 2 ∧ e.innerPos = e.vmsg.length + 2 ∧
      e.innerTail = e.vrik.toList.drop 31 ++ e.vmsg := by
  have hlen := innerMsg_length e hk
  have hb : e.innerB = 2 := by unfold MacEnv.innerB; omega
  have hp : e.innerPos = e.vmsg.length + 2 := by unfold MacEnv.innerPos; omega
  refine ⟨hb, hp, ?_⟩
  unfold MacEnv.innerTail
  rw [hb, innerMsg_split2 e, ← List.append_assoc]
  have h128 : (e.ipadKey ++ (e.vsik.toList ++ e.vrik.toList.take 31)).length = 64 * 2 := by
    simp [hk]
  rw [← h128, List.drop_left]

/-- Long path (`L ≥ 62`): block 3 is `rik[31..] ‖ msg[..62]` (compress #4), then the `n` blocks
`msg[62 .. 62 + 64n]` (compress #5, in place), and `msg[62 + 64n ..]` is buffered. -/
theorem long (hk : e.vkey.length = 32) (hL : 62 ≤ e.vmsg.length) :
    e.hState F 3 = F (e.hState F 2) (e.vrik.toList.drop 31 ++ e.vmsg.take 62) ∧
      e.innerB = 3 + e.nFull ∧ e.innerPos = (e.vmsg.length - 62) % 64 ∧
      e.hState F (3 + e.nFull) =
        (chunks64 ((e.vmsg.drop 62).take (64 * e.nFull))).foldl F (e.hState F 3) ∧
      e.innerTail = e.vmsg.drop (62 + 64 * e.nFull) := by
  have hlen := innerMsg_length e hk
  have hb3_len : (e.vrik.toList.drop 31 ++ e.vmsg.take 62).length = 64 := by simp; omega
  have hrest : e.vrik.toList.drop 31 ++ e.vmsg =
      (e.vrik.toList.drop 31 ++ e.vmsg.take 62) ++ e.vmsg.drop 62 := by
    conv_lhs => rw [← List.take_append_drop 62 e.vmsg]
    rw [List.append_assoc]
  have hchunks : chunks64 e.innerMsg =
      e.ipadKey :: (e.vsik.toList ++ e.vrik.toList.take 31) ::
        (e.vrik.toList.drop 31 ++ e.vmsg.take 62) :: chunks64 (e.vmsg.drop 62) := by
    rw [chunks64_innerMsg e hk, hrest, chunks64_append_64 hb3_len]
  have hh3 : e.hState F 3 = F (e.hState F 2) (e.vrik.toList.drop 31 ++ e.vmsg.take 62) := by
    unfold MacEnv.hState
    rw [hchunks]
    rfl
  have hb : e.innerB = 3 + e.nFull := by
    unfold MacEnv.innerB MacEnv.nFull MacEnv.L; omega
  have hp : e.innerPos = (e.vmsg.length - 62) % 64 := by
    unfold MacEnv.innerPos; omega
  refine ⟨hh3, hb, hp, ?_, ?_⟩
  · rw [hh3, hState_two e F hk, hState_one e F hk]
    unfold MacEnv.hState
    rw [hchunks, show 3 + e.nFull = e.nFull + 1 + 1 + 1 by omega]
    have htake : (chunks64 (e.vmsg.drop 62)).take e.nFull =
        chunks64 ((e.vmsg.drop 62).take (64 * e.nFull)) := by
      have hlen_c : (chunks64 (e.vmsg.drop 62)).length ≤ e.nFull := by
        simp [MacEnv.nFull, MacEnv.L]
      rw [List.take_of_length_le hlen_c, chunks64_eq_take_mul, List.length_drop]
    simp [htake]
  · unfold MacEnv.innerTail
    rw [hb, innerMsg_split2 e, hrest]
    have h192 : (e.ipadKey ++ (e.vsik.toList ++ e.vrik.toList.take 31) ++
        (e.vrik.toList.drop 31 ++ e.vmsg.take 62)).length = 192 := by
      simp [hk]; omega
    have hsplit : e.ipadKey ++ ((e.vsik.toList ++ e.vrik.toList.take 31) ++
        ((e.vrik.toList.drop 31 ++ e.vmsg.take 62) ++ e.vmsg.drop 62)) =
        (e.ipadKey ++ (e.vsik.toList ++ e.vrik.toList.take 31) ++
          (e.vrik.toList.drop 31 ++ e.vmsg.take 62)) ++ e.vmsg.drop 62 := by
      simp only [List.append_assoc]
    rw [hsplit, show 64 * (3 + e.nFull) = 192 + 64 * e.nFull by omega,
      ← List.drop_drop, ← h192, List.drop_left, List.drop_drop]

private theorem bitlen_and_zero (b p : ℕ) (hp : p < 64) :
    ((BitVec.ofNat 64 b <<< 9) &&& (BitVec.ofNat 64 p <<< 3)) = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    hi, decide_true, Bool.true_and]
  by_cases h9 : i < 9
  · simp [h9]
  · have hpow : 2 ^ 6 ≤ 2 ^ (i - 3) := Nat.pow_le_pow_right (by decide) (by omega)
    have hlt : p < 2 ^ (i - 3) := by omega
    simp [Nat.testBit_lt_two_pow hlt]

/-- The bit length as the binary computes it (`lsl x8, x25, #9; orr x8, x8, x23, lsl #3` at
`cm+0x860`): `B · 512 | pos · 8 = 8 · |innerMsg| mod 2⁶⁴` (the length field of `sha256Pad`). -/
theorem bitlen (hk : e.vkey.length = 32) :
    (BitVec.ofNat 64 e.innerB <<< 9) ||| (BitVec.ofNat 64 e.innerPos <<< 3) =
      BitVec.ofNat 64 (8 * e.innerMsg.length) := by
  let _ := hk
  have hp : e.innerPos < 64 := Nat.mod_lt _ (by decide)
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ (bitlen_and_zero e.innerB e.innerPos hp),
    BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow]
  have hdiv : 8 * e.innerMsg.length = e.innerB * 512 + e.innerPos * 8 := by
    unfold MacEnv.innerB MacEnv.innerPos
    omega
  rw [hdiv, BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_mul]
  rfl

private theorem innerMsg_head_eq :
    (chunks64 (e.innerMsg.take (64 * e.innerB))).foldl F sha256IV = e.hState F e.innerB := by
  unfold MacEnv.hState
  have h1 : chunks64 e.innerMsg = chunks64 (e.innerMsg.take (64 * e.innerB)) :=
    chunks64_eq_take_mul e.innerMsg
  have h2 : (chunks64 (e.innerMsg.take (64 * e.innerB))).length ≤ e.innerB := by
    simp [MacEnv.innerB]; omega
  rw [h1, List.take_of_length_le h2]

/-- `pos < 56`: one padding block, `tail ‖ 0x80 ‖ 0… ‖ BE64(bitlen)`; the blocks before it are the
`B` whole blocks of `innerMsg`. -/
theorem pad_lt (hk : e.vkey.length = 32) (hp : e.innerPos < 56) :
    e.innerPadded.drop (e.innerPadded.length - 64) =
        e.innerTail ++ [0x80#8] ++ List.replicate (55 - e.innerPos) 0#8 ++
          toBEBytes 8 (BitVec.ofNat 64 (8 * e.innerMsg.length)) ∧
      (chunks64 (e.innerPadded.take (e.innerPadded.length - 64))).foldl F sha256IV =
        e.hState F e.innerB := by
  let _ := hk
  set head := e.innerMsg.take (64 * e.innerB)
  set blk := e.innerTail ++ [0x80#8] ++ List.replicate (55 - e.innerPos) 0#8 ++
    toBEBytes 8 (BitVec.ofNat 64 (8 * e.innerMsg.length))
  have hhead_len : head.length = 64 * e.innerB := by
    simp [head, MacEnv.innerB]; omega
  have htail_len : e.innerTail.length = e.innerPos := by
    simp [MacEnv.innerTail, MacEnv.innerB, MacEnv.innerPos]; omega
  have hblk_len : blk.length = 64 := by
    simp [blk, htail_len]; omega
  have hz : (119 - e.innerMsg.length % 64) % 64 = 55 - e.innerPos := by
    unfold MacEnv.innerPos at hp ⊢; omega
  have hpad : e.innerPadded = head ++ blk := by
    unfold MacEnv.innerPadded sha256Pad
    rw [hz]
    dsimp only [head, blk, MacEnv.innerTail]
    simp only [← List.append_assoc, List.take_append_drop]
    rfl
  have hsub : e.innerPadded.length - 64 = head.length := by
    rw [hpad, List.length_append, hblk_len, Nat.add_sub_cancel]
  rw [hsub, hpad, List.drop_left, List.take_left]
  exact ⟨rfl, innerMsg_head_eq e F⟩

/-- `pos ≥ 56`: two padding blocks, `tail ‖ 0x80 ‖ 0…` (compress #6) and
`0…0 ‖ BE64(bitlen)` (compress #7). -/
theorem pad_ge (hk : e.vkey.length = 32) (hp : 56 ≤ e.innerPos) :
    e.innerPadded.drop (e.innerPadded.length - 64) =
        List.replicate 56 0#8 ++ toBEBytes 8 (BitVec.ofNat 64 (8 * e.innerMsg.length)) ∧
      (chunks64 (e.innerPadded.take (e.innerPadded.length - 64))).foldl F sha256IV =
        F (e.hState F e.innerB) (e.innerTail ++ [0x80#8] ++ List.replicate (63 - e.innerPos) 0#8) := by
  let _ := hk
  set head := e.innerMsg.take (64 * e.innerB)
  set blk1 := e.innerTail ++ [0x80#8] ++ List.replicate (63 - e.innerPos) 0#8
  set blk2 := List.replicate 56 0#8 ++ toBEBytes 8 (BitVec.ofNat 64 (8 * e.innerMsg.length))
  have hpos_lt : e.innerPos < 64 := Nat.mod_lt _ (by decide)
  have hhead_len : head.length = 64 * e.innerB := by
    simp [head, MacEnv.innerB]; omega
  have htail_len : e.innerTail.length = e.innerPos := by
    simp [MacEnv.innerTail, MacEnv.innerB, MacEnv.innerPos]; omega
  have hblk1_len : blk1.length = 64 := by
    simp [blk1, htail_len]; omega
  have hblk2_len : blk2.length = 64 := by
    simp [blk2]
  have hz : (119 - e.innerMsg.length % 64) % 64 = (63 - e.innerPos) + 56 := by
    unfold MacEnv.innerPos at hp ⊢; omega
  have hpad : e.innerPadded = (head ++ blk1) ++ blk2 := by
    unfold MacEnv.innerPadded sha256Pad
    rw [hz, List.replicate_add]
    dsimp only [head, blk1, blk2, MacEnv.innerTail]
    simp only [← List.append_assoc, List.take_append_drop]
    rfl
  have hsub : e.innerPadded.length - 64 = (head ++ blk1).length := by
    rw [hpad, List.length_append, hblk2_len, Nat.add_sub_cancel]
  rw [hsub, hpad, List.drop_left, List.take_left]
  refine ⟨rfl, ?_⟩
  rw [chunks64_append_mul e.innerB hhead_len, chunks64_single hblk1_len,
    List.foldl_append, List.foldl_cons, List.foldl_nil, innerMsg_head_eq e F]

private theorem sha256Pad_length_exists (m : List (BitVec 8)) :
    ∃ k, (sha256Pad m).length = 64 * (k + 1) := by
  unfold sha256Pad
  simp only [List.length_append, List.length_singleton, List.length_replicate, toBEBytes_length]
  by_cases hp : m.length % 64 < 56
  · exact ⟨m.length / 64, by omega⟩
  · exact ⟨m.length / 64 + 1, by omega⟩

/-- The inner digest is the BE bytes of the state after the last padding block (compress #7). -/
theorem innerHash_eq (hk : e.vkey.length = 32) :
    e.innerHash F =
      (F ((chunks64 (e.innerPadded.take (e.innerPadded.length - 64))).foldl F sha256IV)
        (e.innerPadded.drop (e.innerPadded.length - 64))).toList.flatMap (toBEBytes 4) := by
  let _ := hk
  unfold MacEnv.innerHash sha256With
  change ((chunks64 e.innerPadded).foldl F sha256IV).toList.flatMap (toBEBytes 4) = _
  rcases sha256Pad_length_exists e.innerMsg with ⟨k, hk_len⟩
  have hk_len' : e.innerPadded.length = 64 * (k + 1) := hk_len
  have hsplit : e.innerPadded =
      e.innerPadded.take (e.innerPadded.length - 64) ++
        e.innerPadded.drop (e.innerPadded.length - 64) :=
    (List.take_append_drop _ _).symm
  have htake_len : (e.innerPadded.take (e.innerPadded.length - 64)).length = 64 * k := by
    rw [List.length_take, hk_len']; omega
  have hdrop_len : (e.innerPadded.drop (e.innerPadded.length - 64)).length = 64 := by
    rw [List.length_drop, hk_len']; omega
  conv_lhs => rw [hsplit]
  rw [chunks64_append_mul k htake_len, chunks64_single hdrop_len,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The second block of `sha256Pad outerMsg` (96 bytes): `innerHash ‖ 0x80 ‖ 0×23 ‖ BE64(768)`. -/
theorem outer_block (hk : e.vkey.length = 32) :
    (sha256Pad (e.outerMsg F)).drop 64 =
      e.innerHash F ++ [0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 (768#64) := by
  have hopad := opadKey_length e hk
  have hih : (e.innerHash F).length = 32 := sha256With_length F e.innerMsg
  have hout : (e.outerMsg F).length = 96 := by
    rw [List.length_append, hopad, hih]
  unfold sha256Pad
  rw [hout]
  change (e.opadKey ++ e.innerHash F ++ [0x80#8] ++ List.replicate 23 0#8 ++
    toBEBytes 8 768#64).drop 64 = _
  simp only [List.append_assoc]
  rw [← hopad, List.drop_left]

/-- The tag: the first 8 BE bytes of the state after the second outer block (compress #8). -/
theorem hmac8_eq (hk : e.vkey.length = 32) :
    hmacSha256Trunc8 F e.vkey (e.vsik.toList ++ e.vrik.toList ++ e.vmsg) =
      ((F (e.oState1 F) ((sha256Pad (e.outerMsg F)).drop 64)).toList.flatMap (toBEBytes 4)).take 8 := by
  unfold hmacSha256Trunc8 hmacWith
  have hk_not_gt : ¬ (64 < e.vkey.length) := by omega
  simp only [hk_not_gt, ↓reduceIte]
  have hinner_eq : e.k0.map (· ^^^ 0x36) ++ (e.vsik.toList ++ e.vrik.toList ++ e.vmsg) =
      e.innerMsg := by
    simp [MacEnv.innerMsg, MacEnv.ipadKey, List.append_assoc]
  rw [hinner_eq]
  change (sha256With F (e.outerMsg F)).take 8 = _
  unfold sha256With
  have hopad := opadKey_length e hk
  have hih : (e.innerHash F).length = 32 := sha256With_length F e.innerMsg
  have hout : (e.outerMsg F).length = 96 := by
    rw [List.length_append, hopad, hih]
  have hout_pad_len : (sha256Pad (e.outerMsg F)).length = 128 := by
    unfold sha256Pad
    rw [List.length_append, List.length_append, List.length_append,
      hout, List.length_singleton, List.length_replicate, toBEBytes_length]
  have htake64 : (sha256Pad (e.outerMsg F)).take 64 = e.opadKey := by
    unfold sha256Pad MacEnv.outerMsg
    simp only [List.append_assoc]
    rw [← hopad, List.take_left]
  have hdrop64_len : ((sha256Pad (e.outerMsg F)).drop 64).length = 64 := by
    rw [List.length_drop, hout_pad_len]
  conv_lhs => rw [← List.take_append_drop 64 (sha256Pad (e.outerMsg F))]
  rw [htake64, chunks64_append_64 hopad, chunks64_single hdrop64_len]
  rfl

end MD
end LibsignalHmac
end CryptoVerification
