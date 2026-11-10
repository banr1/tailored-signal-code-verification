/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupStage5
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupHelpers3
public import VerifiedLibraries.Mallocng.Proofs.EnframeUserHelpers

/-!
# Placed `alloc_group` Post-Call `enframe` and Zero-Loop

Symbolic execution of the nested `alloc_group` post-call `enframe` header load, parent slot offset
calculation, and zero-initialization loop (`+0x6ec .. +0x8bc`) in `blk08`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-- Replace `[off, off + sub.length)` inside `bs` with `sub`. -/
def replaceSlice (bs : List (BitVec 8)) (off : Nat) (sub : List (BitVec 8)) : List (BitVec 8) :=
  bs.take off ++ (sub ++ bs.drop (off + sub.length))

theorem replaceSlice_length {bs sub : List (BitVec 8)} {off : Nat}
    (h : off + sub.length ≤ bs.length) :
    (replaceSlice bs off sub).length = bs.length := by
  simp [replaceSlice, List.length_take, List.length_drop]
  omega

theorem replaceSlice_getD_out {bs sub : List (BitVec 8)} {off idx : Nat}
    (h : off + sub.length ≤ bs.length)
    (hout : idx < off ∨ off + sub.length ≤ idx) :
    (replaceSlice bs off sub).getD idx 0#8 = bs.getD idx 0#8 := by
  unfold replaceSlice
  have htake_len : (bs.take off).length = off := by simp [List.length_take]; omega
  rcases hout with hlt | hge
  · have hi1 : idx < (bs.take off ++ (sub ++ bs.drop (off + sub.length))).length := by
      simp [List.length_take, List.length_drop]; omega
    have hi2 : idx < bs.length := by omega
    simp only [List.getD, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2, Option.getD]
    rw [List.getElem_append_left (by omega), List.getElem_take]
  · by_cases hi_bs : idx < bs.length
    · have hi1 : idx < (bs.take off ++ (sub ++ bs.drop (off + sub.length))).length := by
        simp [List.length_take, List.length_drop]; omega
      simp only [List.getD, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi_bs, Option.getD]
      rw [List.getElem_append_right (by omega)]
      simp only [htake_len]
      rw [List.getElem_append_right (by omega), List.getElem_drop]
      congr 1; omega
    · have hi1 : (bs.take off ++ (sub ++ bs.drop (off + sub.length))).length ≤ idx := by
        simp [List.length_take, List.length_drop]; omega
      have hi2 : bs.length ≤ idx := by omega
      simp [List.getD, List.getElem?_eq_none hi1, List.getElem?_eq_none hi2]

theorem replaceSlice_getD_in {bs sub : List (BitVec 8)} {off j : Nat}
    (h : off + sub.length ≤ bs.length) (hj : j < sub.length) :
    (replaceSlice bs off sub).getD (off + j) 0#8 = sub.getD j 0#8 := by
  unfold replaceSlice
  have htake_len : (bs.take off).length = off := by simp [List.length_take]; omega
  have hi1 : off + j < (bs.take off ++ (sub ++ bs.drop (off + sub.length))).length := by
    simp [List.length_take, List.length_drop]; omega
  simp only [List.getD, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hj, Option.getD]
  rw [List.getElem_append_right (by omega)]
  simp only [htake_len, show off + j - off = j by omega]
  rw [List.getElem_append_left hj]

theorem writeBytesToMap_getD (val : BitVec 64 → BitVec 8) (base : BitVec 64)
    (bs : List (BitVec 8)) {i : Nat} (hi : i < bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    writeBytesToMap val base bs (base + BitVec.ofNat 64 i) = bs.getD i 0#8 := by
  rw [writeBytesToMap_in val base bs hi hlen]
  simp [List.getD, List.getElem?_eq_getElem hi]

theorem readBytesFromMap_sub_writeBytesToMap (val : BitVec 64 → BitVec 8) (base : BitVec 64)
    (bs sub : List (BitVec 8)) {off : Nat}
    (hoff : off + sub.length ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hsub : ∀ j < sub.length, bs.getD (off + j) 0#8 = sub.getD j 0#8) :
    readBytesFromMap (writeBytesToMap val base bs) (base + BitVec.ofNat 64 off) sub.length = sub := by
  apply List.ext_getElem (by simp)
  intro j hj1 hj2
  rw [readBytesFromMap_getElem _ _ _ _ hj1]
  have haddr : base + BitVec.ofNat 64 off + BitVec.ofNat 64 j =
      base + BitVec.ofNat 64 (off + j) := by bv_omega
  rw [haddr, writeBytesToMap_getD val base bs (by omega) hlen, hsub j hj2]
  simp [List.getD, List.getElem?_eq_getElem hj2]

theorem split_slot_sub (base : BitVec 64) (bs : List (BitVec 8)) (off w : Nat)
    (h : off + w ≤ bs.length) :
    (base ↦ₛ bs) =
      (((base + BitVec.ofNat 64 off) ↦ₛ (bs.drop off).take w) ∗
       (base ↦ₛ bs.take off) ∗
       ((base + BitVec.ofNat 64 (off + w)) ↦ₛ bs.drop (off + w))) := by
  have hbs : bs = bs.take off ++ ((bs.drop off).take w ++ bs.drop (off + w)) := by
    have hd : (bs.drop off).take w ++ bs.drop (off + w) = bs.drop off := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [hd, List.take_append_drop]
  have htl : (bs.take off).length = off := by simp [List.length_take]; omega
  have hml : ((bs.drop off).take w).length = w := by simp [List.length_take, List.length_drop]; omega
  have hadd : base + BitVec.ofNat 64 off + BitVec.ofNat 64 w =
      base + BitVec.ofNat 64 (off + w) := by bv_omega
  conv => lhs; rw [hbs]
  rw [pointsToBytes_append, pointsToBytes_append, htl, hml, hadd]
  ac_rfl

theorem fold_slot_sub (base : BitVec 64) (bs sub : List (BitVec 8)) (off : Nat)
    (h : off + sub.length ≤ bs.length) :
    (((base + BitVec.ofNat 64 off) ↦ₛ sub) ∗
     (base ↦ₛ bs.take off) ∗
     ((base + BitVec.ofNat 64 (off + sub.length)) ↦ₛ bs.drop (off + sub.length))) =
      (base ↦ₛ replaceSlice bs off sub) := by
  unfold replaceSlice
  have htl : (bs.take off).length = off := by simp [List.length_take]; omega
  have hadd : base + BitVec.ofNat 64 off + BitVec.ofNat 64 sub.length =
      base + BitVec.ofNat 64 (off + sub.length) := by bv_omega
  rw [pointsToBytes_append, pointsToBytes_append, htl, hadd]
  ac_rfl

theorem split_slot_u8 (base : BitVec 64) (bs : List (BitVec 8)) {off : Nat}
    (h : off + 1 ≤ bs.length) :
    (base ↦ₛ bs) =
      (((base + BitVec.ofNat 64 off) ↦₈ bs.getD off 0#8) ∗
       (base ↦ₛ bs.take off) ∗
       ((base + BitVec.ofNat 64 (off + 1)) ↦ₛ bs.drop (off + 1))) := by
  rw [split_slot_sub base bs off 1 h]
  have ht1 : (bs.drop off).take 1 = [bs.getD off 0#8] := by
    have hi : off < bs.length := by omega
    apply List.ext_getElem (by simp [List.length_drop]; omega)
    intro i _ hi2
    have hi0 : i = 0 := by simpa using hi2
    subst hi0
    simp [List.getD, List.getElem?_eq_getElem hi]
  rw [ht1, pointsToBytes_singleton]

theorem fold_slot_u8 (base : BitVec 64) (bs : List (BitVec 8)) {off : Nat}
    (h : off + 1 ≤ bs.length) (v : BitVec 8) :
    (((base + BitVec.ofNat 64 off) ↦₈ v) ∗
     (base ↦ₛ bs.take off) ∗
     ((base + BitVec.ofNat 64 (off + 1)) ↦ₛ bs.drop (off + 1))) =
      (base ↦ₛ replaceSlice bs off [v]) := by
  rw [← pointsToBytes_singleton]
  exact fold_slot_sub base bs [v] off h

theorem split_slot_u16 (base : BitVec 64) (bs : List (BitVec 8)) {off : Nat}
    (h : off + 2 ≤ bs.length) :
    (base ↦ₛ bs) =
      (((base + BitVec.ofNat 64 off) ↦₁₆ pack16 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)) ∗
       (base ↦ₛ bs.take off) ∗
       ((base + BitVec.ofNat 64 (off + 2)) ↦ₛ bs.drop (off + 2))) := by
  rw [split_slot_sub base bs off 2 h, pointsToBytes_take2_eq_pointsTo16 _ _ _ h]

theorem fold_slot_u16 (base : BitVec 64) (bs : List (BitVec 8)) {off : Nat}
    (h : off + 2 ≤ bs.length) (v : BitVec 16) :
    (((base + BitVec.ofNat 64 off) ↦₁₆ v) ∗
     (base ↦ₛ bs.take off) ∗
     ((base + BitVec.ofNat 64 (off + 2)) ↦ₛ bs.drop (off + 2))) =
      (base ↦ₛ replaceSlice bs off (unpack16 v)) := by
  have hl : (unpack16 v).length = 2 := rfl
  rw [pointsTo16_eq_pointsToBytes]
  simpa only [hl] using fold_slot_sub base bs (unpack16 v) off (by rw [hl]; exact h)

theorem split_slot_u32 (base : BitVec 64) (bs : List (BitVec 8)) {off : Nat}
    (h : off + 4 ≤ bs.length) :
    ∃ v : BitVec 32,
      (base ↦ₛ bs) =
        (((base + BitVec.ofNat 64 off) ↦₃₂ v) ∗
         (base ↦ₛ bs.take off) ∗
         ((base + BitVec.ofNat 64 (off + 4)) ↦ₛ bs.drop (off + 4))) := by
  have htake4 : (bs.drop off).take 4 =
      (bs.drop off).take 2 ++ (bs.drop (off + 2)).take 2 := by
    have h1 : (bs.drop off).drop 2 = bs.drop (off + 2) := List.drop_drop
    rw [← h1]
    exact List.take_add (i := 2) (j := 2)
  let lo := pack16 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
  let hi := pack16 (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)
  refine ⟨hi ++ lo, ?_⟩
  rw [split_slot_sub base bs off 4 h, htake4, pointsToBytes_append]
  have hl2 : ((bs.drop off).take 2).length = 2 := by simp [List.length_take, List.length_drop]; omega
  rw [hl2, pointsToBytes_take2_eq_pointsTo16 _ bs off (by omega),
      pointsToBytes_take2_eq_pointsTo16 _ bs (off + 2) (by omega),
      ← sepConj_assoc, pointsTo16_pair]
  simp only [lo, hi, sepConj_assoc]

theorem fold_slot_u32 (base : BitVec 64) (bs : List (BitVec 8)) {off : Nat}
    (h : off + 4 ≤ bs.length) (v : BitVec 32) :
    (((base + BitVec.ofNat 64 off) ↦₃₂ v) ∗
     (base ↦ₛ bs.take off) ∗
     ((base + BitVec.ofNat 64 (off + 4)) ↦ₛ bs.drop (off + 4))) =
      (base ↦ₛ replaceSlice bs off (unpack32 v)) := by
  have hl : (unpack32 v).length = 4 := unpack32_length v
  rw [pointsTo32_eq_pointsToBytes]
  simpa only [hl] using fold_slot_sub base bs (unpack32 v) off (by rw [hl]; exact h)

theorem split_slot_hdr9 (base : BitVec 64) (bs : List (BitVec 8)) {off : Nat}
    (h : off + 9 ≤ bs.length) :
    ∃ (mb0 : BitVec 64) (b8Old : BitVec 8),
      (base ↦ₛ bs) =
        (((base + BitVec.ofNat 64 off) ↦₆₄ mb0) ∗
         ((base + BitVec.ofNat 64 off + 8#64) ↦₈ b8Old) ∗
         (base ↦ₛ bs.take off) ∗
         ((base + BitVec.ofNat 64 (off + 9)) ↦ₛ bs.drop (off + 9))) := by
  obtain ⟨v0, hv0⟩ := split_slot_u32 base bs (off := off) (by omega)
  obtain ⟨v1, hv1⟩ := split_slot_u32 (base + BitVec.ofNat 64 (off + 4)) (bs.drop (off + 4))
    (off := 0) (by simp [List.length_drop]; omega)
  have hdrop4 : (bs.drop (off + 4)).drop 4 = bs.drop (off + 8) := List.drop_drop
  have hdrop8_1 : (bs.drop (off + 8)).drop 1 = bs.drop (off + 9) := List.drop_drop
  have ha4 : base + BitVec.ofNat 64 (off + 4) + BitVec.ofNat 64 0 =
      base + BitVec.ofNat 64 off + 4#64 := by bv_omega
  have ha8 : base + BitVec.ofNat 64 (off + 4) + BitVec.ofNat 64 4 =
      base + BitVec.ofNat 64 (off + 8) := by bv_omega
  have ha8b : base + BitVec.ofNat 64 (off + 8) + BitVec.ofNat 64 0 =
      base + BitVec.ofNat 64 off + 8#64 := by bv_omega
  have ha9 : base + BitVec.ofNat 64 (off + 8) + BitVec.ofNat 64 1 =
      base + BitVec.ofNat 64 (off + 9) := by bv_omega
  refine ⟨v1 ++ v0, (bs.drop (off + 8)).getD 0 0#8, ?_⟩
  rw [hv0, hv1]
  simp only [List.take_zero, pointsToBytes_nil, emp_sepConj, hdrop4, ha4, ha8]
  have h8 : ((base + BitVec.ofNat 64 (off + 8)) ↦ₛ bs.drop (off + 8)) =
      (((base + BitVec.ofNat 64 off + 8#64) ↦₈ (bs.drop (off + 8)).getD 0 0#8) ∗
       ((base + BitVec.ofNat 64 (off + 9)) ↦ₛ bs.drop (off + 9))) := by
    rw [split_slot_u8 (base + BitVec.ofNat 64 (off + 8)) (bs.drop (off + 8))
      (off := 0) (by simp [List.length_drop]; omega)]
    simp only [List.take_zero, pointsToBytes_nil, emp_sepConj, Nat.zero_add, ha8b, ha9, hdrop8_1]
  rw [h8, pointsTo64_split32 (base + BitVec.ofNat 64 off) (v1 ++ v0)]
  have hex0 : (v1 ++ v0).extractLsb' 0 32 = v0 := by bv_bits
  have hex1 : (v1 ++ v0).extractLsb' 32 32 = v1 := by bv_bits
  rw [hex0, hex1]
  ac_rfl

theorem fold_slot_hdr9 (base : BitVec 64) (bs : List (BitVec 8)) {off : Nat}
    (h : off + 9 ≤ bs.length) (m : BitVec 64) (actB : BitVec 8) :
    (((base + BitVec.ofNat 64 off) ↦₆₄ m) ∗
     ((base + BitVec.ofNat 64 off + 8#64) ↦₈ actB) ∗
     (base ↦ₛ bs.take off) ∗
     ((base + BitVec.ofNat 64 (off + 9)) ↦ₛ bs.drop (off + 9))) =
      (base ↦ₛ replaceSlice bs off (unpack64 m ++ [actB])) := by
  have hl : (unpack64 m ++ [actB]).length = 9 := by simp [unpack64_length]
  have hpair : (((base + BitVec.ofNat 64 off) ↦₆₄ m) ∗
      ((base + BitVec.ofNat 64 off + 8#64) ↦₈ actB)) =
      ((base + BitVec.ofNat 64 off) ↦ₛ (unpack64 m ++ [actB])) := by
    rw [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes, pointsToBytes_singleton]
  rw [← sepConj_assoc, hpair]
  simpa only [hl, sepConj_assoc] using fold_slot_sub base bs (unpack64 m ++ [actB]) off (by rw [hl]; exact h)

private theorem split_m32_b0 (m v : BitVec 64) (R : SepProp) :
    (((m + 32#64) ↦₆₄ v) ∗ R) =
      (((m + 32#64) ↦₈ v.extractLsb' 0 8) ∗
       ((m + 33#64) ↦₈ v.extractLsb' 8 8) ∗
       ((m + 34#64) ↦₁₆ v.extractLsb' 16 16) ∗
       ((m + 36#64) ↦₃₂ v.extractLsb' 32 32) ∗ R) := by
  have h33 : m + 32#64 + 1#64 = m + 33#64 := by bv_omega
  have he0 : (v.extractLsb' 0 16).extractLsb' 0 8 = v.extractLsb' 0 8 := by bv_bits
  have he1 : (v.extractLsb' 0 16).extractLsb' 8 8 = v.extractLsb' 8 8 := by bv_bits
  rw [split_m32 m v R, pointsTo16_split8 (m + 32#64), h33, he0, he1]
  simp only [sepConj_assoc]

private theorem pIdx_bit31_false {pIdx : Nat} (h : pIdx ≤ 31) (x0 : BitVec 64)
    (hw0 : BitVec.setWidth 32 x0 = BitVec.ofNat 32 pIdx) :
    x0.getLsbD 31 = false := by
  have h1 : x0.getLsbD 31 = (BitVec.setWidth 32 x0).getLsbD 31 := by bv_bits
  have h2 : (BitVec.ofNat 32 pIdx).ult (1#32 <<< 31) = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
    change pIdx % (2 ^ 32) < 2 ^ 31
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have h3 : (BitVec.ofNat 32 pIdx).getLsbD 31 = false := by revert h2; bv_robdd
  rw [h1, hw0, h3]

private theorem sxtw_ofNat_lt31 {n : Nat} (h : n ≤ 65536) :
    BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hlt : (BitVec.ofNat 32 n).ult (1#32 <<< 31) = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
    change n % (2 ^ 32) < 2 ^ 31
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hse : BitVec.signExtend 64 (BitVec.ofNat 32 n) =
      BitVec.zeroExtend 64 (BitVec.ofNat 32 n) := by revert hlt; bv_robdd
  rw [hse]; bv_omega

private theorem sbfm_sxtw_eq (v : BitVec 64) :
    (v >>> 0 &&& 0xffffffff#64 |||
      (if v.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) =
      BitVec.signExtend 64 (BitVec.setWidth 32 v) := by
  bv_robdd

private theorem sbfm_sxtw_ofNat {n : Nat} (h : n ≤ 65536) (v : BitVec 64)
    (hw : BitVec.setWidth 32 v = BitVec.ofNat 32 n) :
    (v >>> 0 &&& 0xffffffff#64 |||
      (if v.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) = BitVec.ofNat 64 n := by
  rw [sbfm_sxtw_eq, hw]
  exact sxtw_ofNat_lt31 h

private theorem sbfm_sxtw_simp (v : BitVec 64) :
    (v &&& 0xffffffff#64 |||
      (if v.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) =
      BitVec.signExtend 64 (BitVec.setWidth 32 v) := by
  bv_robdd

private theorem zext64_mask31_eq_zext32 (b : BitVec 8) :
    BitVec.zeroExtend 64 b &&& 31#64 =
      BitVec.zeroExtend 64 (BitVec.zeroExtend 32 b &&& 0x1f#32) := by
  bv_robdd

private theorem mask_f000_shr12 (w : BitVec 64) :
    (w &&& 0xfffffffffffff000#64) >>> 12 = w >>> 12 := by
  bv_robdd

private theorem w5_sub4_eq {sc : Nat} (hsc : sc ≤ 24) :
    (BitVec.setWidth 32 (BitVec.ofNat 16 (sizeClass sc)) <<< 4) - 4#32 =
      BitVec.ofNat 32 (slotStride sc - 4) := by
  have ⟨hlo, _⟩ := sizeClass_bounds (by omega : sc < 48)
  have hhi := slotStride_le_2336_of_le_24 hsc
  have hstr : slotStride sc = 16 * sizeClass sc := rfl
  bv_omega

private theorem ubfiz_stride_eq {sc : Nat} (hsc : sc ≤ 24) :
    (BitVec.setWidth 64 (BitVec.ofNat 16 (sizeClass sc)) &&& 65535#64) <<< 4 =
      BitVec.ofNat 64 (slotStride sc) := by
  have hmask : ∀ x : BitVec 16, BitVec.setWidth 64 x &&& 65535#64 = BitVec.zeroExtend 64 x := by
    intro x; bv_robdd
  rw [hmask]
  have ⟨hlo, _⟩ := sizeClass_bounds (by omega : sc < 48)
  have hhi := slotStride_le_2336_of_le_24 hsc
  have hstr : slotStride sc = 16 * sizeClass sc := rfl
  bv_omega

private theorem zext32_ofNat_lt32 {n : Nat} (h : n ≤ 65536) :
    BitVec.zeroExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  bv_omega

private theorem maplen_stride_calc {pg : GroupDesc}
    (hLast : pg.lastIdx ≤ 31) (hSc : pg.sc < 64) (hMap : pg.maplen < 2 ^ 52)
    (hMapPos : 0 < pg.maplen) (hMapBound : pg.maplen * 4096 ≤ 2 ^ 48) :
    (pg.packedWord &&& 0xfffffffffffff000#64) - 16#64 =
      BitVec.ofNat 64 (pg.maplen * 4096 - 16) := by
  have ⟨_, _, hm, _⟩ := GroupDesc.packedWord_fields pg hLast hSc hMap
  have hmask : pg.packedWord &&& 0xfffffffffffff000#64 = (pg.packedWord >>> 12) <<< 12 := by
    bv_bits
  have hsh : BitVec.ofNat 64 pg.maplen <<< 12 = BitVec.ofNat 64 (pg.maplen * 4096) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : pg.maplen < 2 ^ 64),
        Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (by omega : pg.maplen * 2 ^ 12 < 2 ^ 64),
        BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : pg.maplen * 4096 < 2 ^ 64)]
  rw [hmask, hm, hsh]
  bv_omega

arm64_proof_prelude

set_option maxHeartbeats 800000 in
theorem wp_nested_enframe_load [MallocngMultiPlacement]
    (s : State) (mmapCnt : BitVec 32) (pSc pIdx : Nat) (pg : GroupDesc) (Frame : SepProp)
    (_hw768 : Blk08HasWords768 mallocngFaultSvc) (_hr768 : Blk08Range768)
    (hpSc24 : pSc ≤ 24) (hpIdx31 : pIdx ≤ 31)
    (hpgSc : pg.sc = pSc) (hpgLast : pg.lastIdx ≤ 31) (hpgMap : pg.maplen < 2 ^ 52)
    (hpgNested : pg.maplen = 0 → 1 ≤ pg.lastIdx)
    (hpgMapBound : 0 < pg.maplen → pg.maplen * 4096 ≤ 2 ^ 48)
    (hpc : s.pc = mbase 8 + allocSlotOff_after_self) (hrun : s.status = .Running)
    (hw0 : s.readReg32 .x0 = BitVec.ofNat 32 pIdx)
    (hw25 : s.readReg32 .x25 = BitVec.ofNat 32 pSc)
    (hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx)
    (hx26 : s.readReg64 .x26 = Obj.pageOf maddrs.sizeClasses) :
    let Pre :=
      ((maddrs.ctx + 12#64) ↦₃₂ mmapCnt) ∗
      ((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * pSc)) ↦₆₄ pg.metaPtr) ∗
      (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗
      (pg.metaPtr ↦ₛ pg.metaBytes) ∗ Frame
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_enframe_hdr) s Pre
      (fun sf P_f =>
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧
        sf.readReg64 .x1 = BitVec.ofNat 64 pIdx ∧
        sf.readReg64 .x2 = BitVec.zeroExtend 64 mmapCnt ∧
        sf.readReg64 .x3 = BitVec.ofNat 64 (slotStride pSc - 4) ∧
        sf.readReg32 .x5 = BitVec.ofNat 32 (slotStride pSc - 4) ∧
        sf.readReg64 .x6 = BitVec.ofNat 64 pg.stride ∧
        sf.readReg64 .x7 = pg.metaPtr ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → r ≠ .x6 →
          r ≠ .x7 → r ≠ .x25 → r ≠ .x26 → sf.readReg64 r = s.readReg64 r) ∧
        P_f = Pre)
      (fun _ => ⌜False⌝) := by
  intro Pre
  have hpSc48 : pSc < 48 := by omega
  have hpStrHi := slotStride_le_2336_of_le_24 hpSc24
  have hbit31 : (s.readReg64 (Reg.gpr 0#5)).getLsbD 31 = false :=
    pIdx_bit31_false hpIdx31 (s.readReg64 .x0) hw0
  have hsx25 := sbfm_sxtw_ofNat (by omega : pSc ≤ 65536) (s.readReg64 (Reg.gpr 25#5)) hw25
  have hActAddr := ctx_off_active (ctxAddr := maddrs.ctx) hpSc48
  have hScAddr : maddrs.sizeClasses + (BitVec.ofNat 64 pSc <<< 1) =
      maddrs.sizeClasses + BitVec.ofNat 64 (2 * pSc) := by
    have : BitVec.ofNat 64 pSc <<< 1 = BitVec.ofNat 64 (2 * pSc) := by bv_omega
    rw [this]
  obtain ⟨RestSc, hSplitSc⟩ := split_sizeClass_ro maddrs.sizeClasses hpSc48
    ((pg.metaPtr ↦ₛ pg.metaBytes) ∗ Frame)
  have hMetaSplit : ((pg.metaPtr ↦ₛ pg.metaBytes) ∗ Frame) =
      ((pg.metaPtr ↦₆₄ pg.prev) ∗ ((pg.metaPtr + 8#64) ↦₆₄ pg.next) ∗
       ((pg.metaPtr + 16#64) ↦₆₄ pg.mem) ∗ ((pg.metaPtr + 24#64) ↦₃₂ pg.availMask) ∗
       ((pg.metaPtr + 28#64) ↦₃₂ pg.freedMask) ∗
       ((pg.metaPtr + 32#64) ↦₆₄ pg.packedWord) ∗ Frame) := by
    rw [GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]
  have ⟨_, hb0_last⟩ := GroupDesc.packedWord_byte0 pg hpgLast
  have ⟨_, _, hpf_map, hpf_sc16⟩ :=
    GroupDesc.packedWord_fields pg hpgLast (by omega) hpgMap
  dsimp only [allocSlotOff_after_self, allocSlotOff_enframe_hdr] at hpc ⊢
  refine SepWP.seq (mid := mbase 8 + (words_insn_off% blk08Words 0x540002c1#32))
    (Mid := fun s1 P1 =>
      (s1.sp = s.sp ∧ s1.spAligned = s.spAligned ∧ PureStatePres s s1 ∧
        s1.readReg64 .x1 = BitVec.ofNat 64 pIdx ∧
        s1.readReg64 .x2 = BitVec.zeroExtend 64 mmapCnt ∧
        s1.readReg64 .x3 = BitVec.ofNat 64 (slotStride pSc - 4) ∧
        s1.readReg32 .x5 = BitVec.ofNat 32 (slotStride pSc - 4) ∧
        s1.readReg64 .x7 = pg.metaPtr ∧
        s1.readReg64 .x26 = Obj.pageOf maddrs.sizeClasses ∧
        s1.pstate.z = decide (pg.lastIdx = 0) ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 →
          r ≠ .x7 → r ≠ .x25 → s1.readReg64 r = s.readReg64 r)) ∧
      P1 = Pre) ?_ ?_
  · conv =>
      arg 4; dsimp only [Pre]
      rw [hSplitSc, hMetaSplit, split_m32_b0 pg.metaPtr pg.packedWord Frame]
    wp_sym_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨⟨by simp, by simp [State.spAligned], psp_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp; change BitVec.zeroExtend 64 (s.readReg32 .x0) = _
      rw [hw0]; exact zext32_ofNat_lt32 (by omega)
    · simp
    · rw [State.readReg64_setPC, State.readReg64_setPState,
        State.readReg64_writeReg64_same _ _ _ (by decide) (by decide), sbfm_sxtw_eq]
      simp [w5_sub4_eq hpSc24]
      exact sxtw_ofNat_lt31 (by omega)
    · simp [State.readReg32, w5_sub4_eq hpSc24]
    · simp
    · simp [hx26]
    · simp
      have hb0_64 : BitVec.zeroExtend 64 (pg.packedWord.extractLsb' 0 8) &&& 31#64 =
          BitVec.ofNat 64 pg.lastIdx := by
        rw [zext64_mask31_eq_zext32, hb0_last]
        exact zext32_ofNat_lt32 (by omega)
      rw [hb0_64]
      by_cases h0 : pg.lastIdx = 0
      · rw [h0]; rfl
      · simp only [h0, decide_false, beq_eq_false_iff_ne]
        intro h; have ht := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pg.lastIdx < 2 ^ 64)] at ht
        exact h0 ht
    · intro r hr0 hr1 hr2 hr3 hr4 hr5 hr7 hr25
      simp only [State.readReg64_setPC, State.readReg64_setPState,
        State.readReg64_writeReg64_ne _ _ _ _ hr0, State.readReg64_writeReg64_ne _ _ _ _ hr1,
        State.readReg64_writeReg64_ne _ _ _ _ hr2, State.readReg64_writeReg64_ne _ _ _ _ hr3,
        State.readReg64_writeReg64_ne _ _ _ _ hr4, State.readReg64_writeReg64_ne _ _ _ _ hr5,
        State.readReg64_writeReg64_ne _ _ _ _ hr7, State.readReg64_writeReg64_ne _ _ _ _ hr25]
    · dsimp only [Pre]
      rw [← split_m32_b0 pg.metaPtr pg.packedWord Frame, ← hMetaSplit]
      have hRew : (((maddrs.sizeClasses + BitVec.ofNat 64 (2 * pSc)) ↦₁₆ᵣ
            BitVec.ofNat 16 (sizeClass pSc)) ∗ RestSc ∗ (pg.metaPtr ↦ₛ pg.metaBytes) ∗ Frame) =
          ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (pg.metaPtr ↦ₛ pg.metaBytes) ∗ Frame) := by
        simpa only [sepConj_assoc] using hSplitSc.symm
      exact congrArg (_ ∗ ·) (congrArg (_ ∗ ·) hRew)
  · intro s1 P1 hpc1 hrun1
      ⟨⟨hsp1, hal1, hpsp1, hx1_1, hx2_1, hx3_1, hw5_1, hx7_1, hx26_1, hz1, hregs1⟩, hP1⟩
    subst hP1
    by_cases hLast0 : pg.lastIdx = 0
    · have hMapPos : 0 < pg.maplen :=
        Nat.pos_of_ne_zero fun hm0 => by have := hpgNested hm0; omega
      have hcond_ne : ConditionHolds CondCode.NE s1.pstate = false := by
        simp [ConditionHolds, hz1, hLast0]
      have htst_map : (pg.packedWord &&& 0xfffffffffffff000#64 == 0#64) = false := by
        rw [beq_eq_false_iff_ne]
        intro h0
        have hsh := mask_f000_shr12 pg.packedWord
        rw [h0] at hsh
        have hm0 : BitVec.ofNat 64 pg.maplen = 0#64 := hpf_map.symm.trans hsh.symm
        have ht := congrArg BitVec.toNat hm0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pg.maplen < 2 ^ 64)] at ht
        change pg.maplen = 0 at ht
        omega
      have hStrEq : pg.stride = pg.maplen * 4096 - 16 := by
        simp [GroupDesc.stride, hLast0, hMapPos]
      conv => arg 4; dsimp only [Pre]; rw [hMetaSplit]
      wp_sym_steps
      refine SepWP.done rfl (by simp [hrun1])
        ⟨by simp [hrun1], hsp1, by simpa [State.spAligned] using hal1, hpsp1,
         by simp [hx1_1], by simp [hx2_1], by simp [hx3_1],
         by simp [State.readReg32]; exact hw5_1,
         ?_, by simp [hx7_1], ?_, ?_⟩
      · simp [hStrEq, maplen_stride_calc hpgLast (by omega) hpgMap hMapPos (hpgMapBound hMapPos)]
      · intro r hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr25 _
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ hr0, State.readReg64_writeReg64_ne _ _ _ _ hr6]
        exact hregs1 r hr0 hr1 hr2 hr3 hr4 hr5 hr7 hr25
      · dsimp only [Pre]; rw [← hMetaSplit]
    · have hcond_ne : ConditionHolds CondCode.NE s1.pstate = true := by
        simp [ConditionHolds, hz1, hLast0]
      have hStrEq : pg.stride = slotStride pSc := by
        simp [GroupDesc.stride, hLast0, hpgSc]
      have hubfx : (BitVec.zeroExtend 64 (pg.packedWord.extractLsb' 0 16) >>> 6) &&& 63#64 =
          BitVec.ofNat 64 pSc := by
        rw [← hpgSc]; exact hpf_sc16
      conv =>
        arg 4; dsimp only [Pre]
        rw [hSplitSc, hMetaSplit, split_m32 pg.metaPtr pg.packedWord Frame]
      wp_sym_steps
      refine SepWP.done rfl (by simp [hrun1])
        ⟨by simp [hrun1], hsp1, by simpa [State.spAligned] using hal1, hpsp1,
         by simp [hx1_1], by simp [hx2_1], by simp [hx3_1],
         by simp [State.readReg32]; exact hw5_1,
         ?_, by simp [hx7_1], ?_, ?_⟩
      · simp [hStrEq]; exact ubfiz_stride_eq hpSc24
      · intro r hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr25 hr26
        simp only [State.readReg64_setPC,
          State.readReg64_writeReg64_ne _ _ _ _ hr0, State.readReg64_writeReg64_ne _ _ _ _ hr6,
          State.readReg64_writeReg64_ne _ _ _ _ hr26]
        exact hregs1 r hr0 hr1 hr2 hr3 hr4 hr5 hr7 hr25
      · dsimp only [Pre]
        rw [← split_m32 pg.metaPtr pg.packedWord Frame, ← hMetaSplit]
        have hRew : (((maddrs.sizeClasses + BitVec.ofNat 64 (2 * pSc)) ↦₁₆ᵣ
              BitVec.ofNat 16 (sizeClass pSc)) ∗ RestSc ∗ (pg.metaPtr ↦ₛ pg.metaBytes) ∗ Frame) =
            ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (pg.metaPtr ↦ₛ pg.metaBytes) ∗ Frame) := by
          simpa only [sepConj_assoc] using hSplitSc.symm
        exact congrArg (_ ∗ ·) (congrArg (_ ∗ ·) hRew)

abbrev allocSlotOff_enframe_off_done : BitVec 64 := words_insn_off% blk08Words 0x34000122#32

theorem split_slot_first4 (start : BitVec 64) (bs : List (BitVec 8))
    (hlen : 4 ≤ bs.length) (hb0 : bs.getD 0 0#8 = 0#8) (R : SepProp) :
    ∃ u2 : BitVec 16,
      (((start - 4#64) ↦ₛ bs) ∗ R) =
        (((start - 4#64) ↦₈ 0#8) ∗ ((start - 3#64) ↦₈ bs.getD 1 0#8) ∗
         ((start - 2#64) ↦₁₆ u2) ∗ (start ↦ₛ bs.drop 4) ∗ R) := by
  let base := start - 4#64
  have hu2 := split_slot_u16 (base + 2#64) (bs.drop 2) (off := 0) (by simp; omega)
  have h0 := split_slot_u8 base bs (off := 0) (by omega)
  have h1 := split_slot_u8 (base + 1#64) (bs.drop 1) (off := 0) (by simp; omega)
  have hd12 : (bs.drop 1).drop 1 = bs.drop 2 := List.drop_drop
  have hd22 : (bs.drop 2).drop 2 = bs.drop 4 := List.drop_drop
  have hget1 : (bs.drop 1).getD 0 0#8 = bs.getD 1 0#8 := by simp [List.getD]
  have ha0 : base + BitVec.ofNat 64 0 = start - 4#64 := by dsimp [base]; bv_robdd
  have ha1 : base + BitVec.ofNat 64 1 = base + 1#64 := rfl
  have ha10 : base + 1#64 + BitVec.ofNat 64 0 = start - 3#64 := by dsimp [base]; bv_robdd
  have ha11 : base + 1#64 + BitVec.ofNat 64 1 = base + 2#64 := by bv_robdd
  have ha20 : base + 2#64 + 0#64 = start - 2#64 := by dsimp [base]; bv_robdd
  have ha22 : base + 2#64 + BitVec.ofNat 64 (0 + 2) = start := by dsimp [base]; bv_robdd
  refine ⟨pack16 ((bs.drop 2).getD 0 0#8) ((bs.drop 2).getD (0 + 1) 0#8), ?_⟩
  change ((base ↦ₛ bs) ∗ R) = _
  rw [h0, ha1, h1, ha11, hd12, hu2]
  simp only [List.take_zero, pointsToBytes_nil, emp_sepConj,
    hb0, hget1, hd22, ha0, ha10, ha20, ha22, sepConj_assoc]

private theorem enframe_slack_eq {stride pStride : Nat}
    (hlo : 16 ≤ pStride) (hle : pStride ≤ stride) (hhi : stride ≤ 65524) :
    BitVec.ofNat 64 stride - BitVec.ofNat 64 (pStride - 4) - 4#64 =
      BitVec.ofNat 64 (stride - pStride) := by
  bv_omega

private theorem enframe_slotStart_eq (pg : GroupDesc) (pIdx : Nat) :
    pg.mem + 16#64 + BitVec.ofNat 64 pIdx * BitVec.ofNat 64 pg.stride = pg.slotStart pIdx := by
  unfold GroupDesc.slotStart GroupDesc.storage
  rw [← BitVec.ofNat_mul]

private theorem enframe_slotEnd_eq (pg : GroupDesc) (pIdx : Nat)
    (hlo : 16 ≤ pg.stride) (hhi : pg.stride ≤ 65524) :
    pg.slotStart pIdx + (BitVec.ofNat 64 pg.stride - 4#64) = pg.slotEnd pIdx := by
  unfold GroupDesc.slotEnd
  congr 1
  bv_omega

private theorem setWidth32_ofNat64 {n : Nat} (_hn : n ≤ 65536) :
    BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  bv_omega

private theorem and255_idem (w : BitVec 32) :
    (w &&& 255#32) &&& 255#32 = w &&& 255#32 := by
  bv_robdd

private theorem mvn32_eq (x : BitVec 64) :
    BitVec.setWidth 32 (~~~BitVec.setWidth 64 (BitVec.setWidth 32 x)) = ~~~(x.truncate 32) := by
  bv_robdd

private theorem enframeMaskReduce_eval (x3 : BitVec 64) (w2 : BitVec 32)
    (hw2 : w2 &&& 255#32 = w2)
    (hgt : (x3 >>> 4).ult (BitVec.signExtend 64 w2) = true) :
    let x5 := x3 >>> 4
    let w7 := BitVec.setWidth 32 (~~~BitVec.setWidth 64 (BitVec.setWidth 32 x5))
    let x3_3 := ((x5 ||| (x3 >>> 5)) ||| ((x5 ||| (x3 >>> 5)) >>> 2)) |||
      (((x5 ||| (x3 >>> 5)) ||| ((x5 ||| (x3 >>> 5)) >>> 2)) >>> 4)
    let w8 := w2 &&& BitVec.setWidth 32 x3_3
    let w2' := if x5.ult (BitVec.setWidth 64 w8) = true then w8 + w7 else w8
    x5.ult (BitVec.signExtend 64 w2') = false ∧
    w2' &&& 255#32 = w2' := by
  dsimp only
  rw [mvn32_eq (x3 >>> 4)]
  have ⟨h1, h2, _⟩ := enframeMaskReduce_spec x3 w2 hw2 hgt
  exact ⟨h1, h2⟩

private theorem ule_false_of_ult {a b : BitVec 64} (h : a.ult b = true) :
    b.ule a = false := by
  revert h; bv_robdd

private theorem ule_true_of_not_ult {a b : BitVec 64} (h : a.ult b = false) :
    b.ule a = true := by
  revert h; bv_robdd

private theorem mask255_props (w : BitVec 32) (hw : w &&& 255#32 = w) :
    BitVec.signExtend 64 w = BitVec.setWidth 64 w ∧
    BitVec.ofNat 32 w.toNat = w ∧
    w.toNat < 256 := by
  have hse : BitVec.signExtend 64 w = BitVec.setWidth 64 w := by revert hw; bv_robdd
  have hlt : w.ult 256#32 = true := by revert hw; bv_robdd
  rw [BitVec.ult, decide_eq_true_eq] at hlt
  exact ⟨hse, by simp, hlt⟩

private theorem off_le_of_not_ult {n : Nat} (hn : n ≤ 65524) (w : BitVec 32)
    (hw : w &&& 255#32 = w)
    (hnlt : (BitVec.ofNat 64 n >>> 4).ult (BitVec.signExtend 64 w) = false) :
    w.toNat ≤ n / 16 := by
  have ⟨hse, _, _⟩ := mask255_props w hw
  rw [hse, BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (by have := w.isLt; omega),
      BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.shiftRight_eq_div_pow] at hnlt
  change ¬ (n / 16 < w.toNat) at hnlt
  omega

private theorem cbz8_false_of_ne {b : BitVec 8} (hb : b ≠ 0#8) :
    (BitVec.setWidth 32 (BitVec.zeroExtend 64 b) == 0#32) = false ∧
    (BitVec.zeroExtend 32 b == 0#32) = false ∧
    (b == 0#8) = false := by
  have h0 : (b == 0#8) = false := beq_eq_false_iff_ne.mpr hb
  refine ⟨by revert h0; bv_robdd, by revert h0; bv_robdd, h0⟩

set_option maxHeartbeats 800000 in
theorem wp_nested_enframe_off [MallocngMultiPlacement]
    (s : State) (pSc pIdx : Nat) (pg : GroupDesc) (bs : List (BitVec 8)) (Frame : SepProp)
    (_hw768 : Blk08HasWords768 mallocngFaultSvc) (_hr768 : Blk08Range768)
    (hpIdx31 : pIdx ≤ 31)
    (hpStrLo : 16 ≤ slotStride pSc) (hStrLe : slotStride pSc ≤ pg.stride)
    (hStrHi : pg.stride ≤ 65524)
    (hbsLen : bs.length = pg.stride + 1) (hbs0 : bs.getD 0 0#8 = 0#8)
    (hpc : s.pc = mbase 8 + allocSlotOff_enframe_hdr) (hrun : s.status = .Running)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 pIdx)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 (slotStride pSc - 4))
    (hw5 : s.readReg32 .x5 = BitVec.ofNat 32 (slotStride pSc - 4))
    (hx6 : s.readReg64 .x6 = BitVec.ofNat 64 pg.stride)
    (hx7 : s.readReg64 .x7 = pg.metaPtr) :
    let slotBase := pg.slotStart pIdx - 4#64
    let Pre := (pg.metaPtr ↦ₛ pg.metaBytes) ∗ (slotBase ↦ₛ bs) ∗ Frame
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_enframe_off_done) s Pre
      (fun sf P_f =>
        ∃ off : Nat, off ≤ (pg.stride - slotStride pSc) / 16 ∧
          sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
          PureStatePres s sf ∧
          sf.readReg64 .x0 = pg.slotStart pIdx ∧
          sf.readReg64 .x1 = BitVec.ofNat 64 pIdx ∧
          sf.readReg64 .x2 = BitVec.ofNat 64 off ∧
          sf.readReg64 .x4 = pg.storage ∧
          sf.readReg32 .x5 = BitVec.ofNat 32 (slotStride pSc - 4) ∧
          sf.readReg64 .x6 = 0#64 ∧
          sf.readReg64 .x7 = pg.metaPtr ∧
          sf.readReg64 .x8 = pg.slotEnd pIdx ∧
          (∀ r, r ≠ .x0 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x8 →
            r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → sf.readReg64 r = s.readReg64 r) ∧
          P_f = Pre)
      (fun _ => ⌜False⌝) := by
  intro slotBase Pre
  have hsx1 := sbfm_sxtw_ofNat (by omega : pIdx ≤ 65536) (BitVec.ofNat 64 pIdx)
    (setWidth32_ofNat64 (by omega))
  have hSlack := enframe_slack_eq hpStrLo hStrLe hStrHi
  have hStart := enframe_slotStart_eq pg pIdx
  have hEnd := enframe_slotEnd_eq pg pIdx (by omega) hStrHi
  refine (split_slot_first4 (pg.slotStart pIdx) bs (by omega) hbs0 Frame).elim fun u2 hSlotSplit => ?_
  have hMetaSplit : ((pg.metaPtr ↦ₛ pg.metaBytes) ∗ (slotBase ↦ₛ bs) ∗ Frame) =
      ((pg.metaPtr ↦₆₄ pg.prev) ∗ ((pg.metaPtr + 8#64) ↦₆₄ pg.next) ∗
       ((pg.metaPtr + 16#64) ↦₆₄ pg.mem) ∗ ((pg.metaPtr + 24#64) ↦₃₂ pg.availMask) ∗
       ((pg.metaPtr + 28#64) ↦₃₂ pg.freedMask) ∗ ((pg.metaPtr + 32#64) ↦₆₄ pg.packedWord) ∗
       ((pg.slotStart pIdx - 4#64) ↦₈ 0#8) ∗ ((pg.slotStart pIdx - 3#64) ↦₈ bs.getD 1 0#8) ∗
       ((pg.slotStart pIdx - 2#64) ↦₁₆ u2) ∗ (pg.slotStart pIdx ↦ₛ bs.drop 4) ∗ Frame) := by
    dsimp only [slotBase]
    rw [GroupDesc.metaBytes_pointsTo, hSlotSplit]; simp only [sepConj_assoc]
  let slack := BitVec.ofNat 64 (pg.stride - slotStride pSc)
  dsimp only [allocSlotOff_enframe_hdr, allocSlotOff_enframe_off_done] at hpc ⊢
  refine SepWP.seq (mid := mbase 8 + (words_insn_off% blk08Words 0x385fc006#32))
    (Mid := fun s1 P1 =>
      (∃ w2 : BitVec 32, w2 &&& 255#32 = w2 ∧
        s1.sp = s.sp ∧ s1.spAligned = s.spAligned ∧ PureStatePres s s1 ∧
        s1.readReg64 .x0 = pg.slotStart pIdx ∧
        s1.readReg64 .x1 = BitVec.ofNat 64 pIdx ∧
        s1.readReg64 .x2 = BitVec.zeroExtend 64 w2 ∧
        s1.readReg64 .x3 = slack ∧
        s1.readReg64 .x4 = pg.storage ∧
        s1.readReg32 .x5 = BitVec.ofNat 32 (slotStride pSc - 4) ∧
        s1.readReg64 .x7 = pg.metaPtr ∧
        s1.readReg64 .x8 = pg.slotEnd pIdx ∧
        s1.readReg64 .x9 = slack >>> 4 ∧
        (∀ r, r ≠ .x0 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x8 →
          r ≠ .x9 → s1.readReg64 r = s.readReg64 r)) ∧
      P1 = Pre) ?_ ?_
  · by_cases hb1 : bs.getD 1 0#8 = 0#8
    · conv => arg 4; dsimp only [Pre]; rw [hMetaSplit]
      wp_sym_steps
      refine SepWP.done rfl (by simp [hrun])
        ⟨⟨s.readReg32 .x2 &&& 255#32, and255_idem _, by simp, by simp [State.spAligned], psp_rfl,
          by simp, by simp [hx1], by simp [State.readReg32], by simp [slack],
          by simp [GroupDesc.storage], by simp [State.readReg32]; exact hw5, by simp [hx7],
          by simp, by simp [slack], ?_⟩,
         by dsimp only [Pre]; rw [hMetaSplit]⟩
      intro r hr0 hr2 hr3 hr4 hr6 hr8 hr9
      simp only [State.readReg64_setPC,
        State.readReg64_writeReg64_ne _ _ _ _ hr0, State.readReg64_writeReg64_ne _ _ _ _ hr2,
        State.readReg64_writeReg64_ne _ _ _ _ hr3, State.readReg64_writeReg64_ne _ _ _ _ hr4,
        State.readReg64_writeReg64_ne _ _ _ _ hr6, State.readReg64_writeReg64_ne _ _ _ _ hr8,
        State.readReg64_writeReg64_ne _ _ _ _ hr9]
    · have ⟨hcbz1, hcbz2, hcbz3⟩ := cbz8_false_of_ne hb1
      conv => arg 4; dsimp only [Pre]; rw [hMetaSplit]
      wp_sym_steps
      refine SepWP.done rfl (by simp [hrun])
        ⟨⟨(u2.zeroExtend 32 + 1#32) &&& 255#32, and255_idem _, by simp,
          by simp [State.spAligned], psp_rfl,
          by simp, by simp [hx1], by simp, by simp [slack], by simp [GroupDesc.storage],
          by simp [State.readReg32]; exact hw5, by simp [hx7],
          by simp, by simp [slack], ?_⟩,
         by dsimp only [Pre]; rw [hMetaSplit]⟩
      intro r hr0 hr2 hr3 hr4 hr6 hr8 hr9
      simp only [State.readReg64_setPC,
        State.readReg64_writeReg64_ne _ _ _ _ hr0, State.readReg64_writeReg64_ne _ _ _ _ hr2,
        State.readReg64_writeReg64_ne _ _ _ _ hr3, State.readReg64_writeReg64_ne _ _ _ _ hr4,
        State.readReg64_writeReg64_ne _ _ _ _ hr6, State.readReg64_writeReg64_ne _ _ _ _ hr8,
        State.readReg64_writeReg64_ne _ _ _ _ hr9]
  · intro s1 P1 hpc1 hrun1
      ⟨⟨w2, hw2, hsp1, hal1, hpsp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hw5_1,
        hx7_1, hx8_1, hx9_1, hregs1⟩, hP1⟩
    subst hP1
    have ⟨hse_w2, _, _⟩ := mask255_props w2 hw2
    by_cases hgt : (slack >>> 4).ult (BitVec.signExtend 64 w2) = true
    · have ⟨hult2, hw2'_mask⟩ := enframeMaskReduce_eval slack w2 hw2 hgt
      have hule_neg := ule_false_of_ult hgt
      have hule_neg_z : (BitVec.setWidth 64 w2).ule (slack >>> 4) = false := by
        rw [← hse_w2]; exact hule_neg
      let x5 := slack >>> 4
      let w7 := BitVec.setWidth 32 (~~~BitVec.setWidth 64 (BitVec.setWidth 32 x5))
      let x3_3 := ((x5 ||| (slack >>> 5)) ||| ((x5 ||| (slack >>> 5)) >>> 2)) |||
        (((x5 ||| (slack >>> 5)) ||| ((x5 ||| (slack >>> 5)) >>> 2)) >>> 4)
      let w8 := w2 &&& BitVec.setWidth 32 x3_3
      let w2' := if x5.ult (BitVec.setWidth 64 w8) = true then w8 + w7 else w8
      have hoff_le := off_le_of_not_ult (by omega) w2' hw2'_mask hult2
      conv => arg 4; dsimp only [Pre]; rw [hMetaSplit]
      wp_sym_steps
      refine SepWP.done rfl (by simp [hrun1])
        ⟨w2'.toNat, hoff_le, by simp [hrun1], hsp1, by simpa [State.spAligned] using hal1,
         hpsp1, by simp [hx0_1], by simp [hx1_1], by simp [w2', w8, w7, x3_3, x5, slack],
         by simp [hx4_1], by simp [State.readReg32]; exact hw5_1, by simp,
         by simp [hx7_1], by simp [hx8_1], ?_, by dsimp only [Pre]; rw [hMetaSplit]⟩
      intro r hr0 hr2 hr3 hr4 hr6 hr8 hr9 hr10 hr11
      simp only [State.readReg64_setPC, State.readReg64_setPState,
        State.readReg64_writeReg64_ne _ _ _ _ hr2, State.readReg64_writeReg64_ne _ _ _ _ hr3,
        State.readReg64_writeReg64_ne _ _ _ _ hr6, State.readReg64_writeReg64_ne _ _ _ _ hr10,
        State.readReg64_writeReg64_ne _ _ _ _ hr11]
      exact hregs1 r hr0 hr2 hr3 hr4 hr6 hr8 hr9
    · have hnlt : (slack >>> 4).ult (BitVec.signExtend 64 w2) = false := Bool.eq_false_iff.mpr hgt
      have hule := ule_true_of_not_ult hnlt
      have hule_z : (BitVec.setWidth 64 w2).ule (slack >>> 4) = true := by rw [← hse_w2]; exact hule
      have hoff_le := off_le_of_not_ult (by omega) w2 hw2 hnlt
      conv => arg 4; dsimp only [Pre]; rw [hMetaSplit]
      wp_sym_steps
      refine SepWP.done rfl (by simp [hrun1])
        ⟨w2.toNat, hoff_le, by simp [hrun1], hsp1, by simpa [State.spAligned] using hal1,
         hpsp1, by simp [hx0_1], by simp [hx1_1], by simp [hx2_1], by simp [hx4_1],
         by simp [State.readReg32]; exact hw5_1, by simp, by simp [hx7_1], by simp [hx8_1],
         ?_, by dsimp only [Pre]; rw [hMetaSplit]⟩
      intro r hr0 hr2 hr3 hr4 hr6 hr8 hr9 _ _
      simp only [State.readReg64_setPC, State.readReg64_setPState,
        State.readReg64_writeReg64_ne _ _ _ _ hr6]
      exact hregs1 r hr0 hr2 hr3 hr4 hr6 hr8 hr9

end VerifiedLibraries.Mallocng.Proofs
