/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupStage6

/-!
# Multi-Block Placed `alloc_group`: Enframe Tail and Zero Loop

Symbolic execution of the nested `alloc_group` `enframe` header writes and zero-loop
(`+0x808 .. +0x8bc`) in `blk08`, establishing `wp_enframe_step_off`, `wp_enframe_step_rsv`, and
`wp_enframe_step_fin`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Sub-Slice Split/Fold and Scalar Helpers -/

private theorem eq_of_length_of_getD {xs ys : List (BitVec 8)}
    (hlen : xs.length = ys.length)
    (hget : ∀ i < xs.length, xs.getD i 0#8 = ys.getD i 0#8) : xs = ys := by
  apply List.ext_getElem hlen
  intro i hi1 hi2
  have h := hget i hi1
  simpa [List.getD, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] using h

private theorem getD_take_lt {bs : List (BitVec 8)} {k i : Nat} (hi : i < k) (hk : k ≤ bs.length) :
    (bs.take k).getD i 0#8 = bs.getD i 0#8 := by
  have hi1 : i < (bs.take k).length := by simp [List.length_take]; omega
  have hi2 : i < bs.length := by omega
  simp [List.getD, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2]

private theorem getD_drop_eq {bs : List (BitVec 8)} {k i : Nat} (hi : k + i < bs.length) :
    (bs.drop k).getD i 0#8 = bs.getD (k + i) 0#8 := by
  have hi1 : i < (bs.drop k).length := by simp [List.length_drop]; omega
  simp [List.getD, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi]

private theorem replaceSlice_take_ge {bs sub : List (BitVec 8)} {off k : Nat}
    (h1 : off + sub.length ≤ k) (h2 : k ≤ bs.length) :
    (replaceSlice bs off sub).take k = replaceSlice (bs.take k) off sub := by
  have hlen1 : ((replaceSlice bs off sub).take k).length = k := by
    rw [List.length_take, replaceSlice_length (by omega)]; omega
  have hlen2 : (replaceSlice (bs.take k) off sub).length = k := by
    rw [replaceSlice_length (by simp [List.length_take]; omega), List.length_take]; omega
  apply eq_of_length_of_getD (hlen1.trans hlen2.symm)
  intro i hi
  rw [hlen1] at hi
  rw [getD_take_lt hi (by rw [replaceSlice_length (by omega)]; exact h2)]
  by_cases hmid : off ≤ i ∧ i < off + sub.length
  · obtain ⟨hlo, hhi⟩ := hmid
    have heq : i = off + (i - off) := by omega
    rw [heq, replaceSlice_getD_in (by omega) (by omega),
        replaceSlice_getD_in (by simp [List.length_take]; omega) (by omega)]
  · have hout : i < off ∨ off + sub.length ≤ i := by omega
    rw [replaceSlice_getD_out (by omega) hout,
        replaceSlice_getD_out (by simp [List.length_take]; omega) hout,
        getD_take_lt hi h2]

private theorem replaceSlice_drop_ge {bs sub : List (BitVec 8)} {off k : Nat}
    (h1 : off + sub.length ≤ k) (h2 : k ≤ bs.length) :
    (replaceSlice bs off sub).drop k = bs.drop k := by
  have hlenL : (replaceSlice bs off sub).length = bs.length := replaceSlice_length (by omega)
  have hlen1 : ((replaceSlice bs off sub).drop k).length = bs.length - k := by
    simp [List.length_drop, hlenL]
  apply eq_of_length_of_getD (by simp [List.length_drop, hlenL])
  intro i hi
  rw [hlen1] at hi
  rw [getD_drop_eq (by rw [hlenL]; omega), getD_drop_eq (by omega)]
  exact replaceSlice_getD_out (by omega) (Or.inr (by omega))

theorem split_fold_two_sub (base : BitVec 64) (bs sub1 sub2 : List (BitVec 8))
    (off1 off2 : Nat)
    (h12 : off1 + sub1.length ≤ off2) (h2 : off2 + sub2.length ≤ bs.length) :
    ∃ Rest : SepProp,
      ((base ↦ₛ bs) =
        (((base + BitVec.ofNat 64 off1) ↦ₛ (bs.drop off1).take sub1.length) ∗
         ((base + BitVec.ofNat 64 off2) ↦ₛ (bs.drop off2).take sub2.length) ∗ Rest)) ∧
      ((((base + BitVec.ofNat 64 off1) ↦ₛ sub1) ∗
        ((base + BitVec.ofNat 64 off2) ↦ₛ sub2) ∗ Rest) =
        (base ↦ₛ replaceSlice (replaceSlice bs off1 sub1) off2 sub2)) := by
  let n1 := sub1.length
  let n2 := sub2.length
  have htk_len : (bs.take off2).length = off2 := by simp [List.length_take]; omega
  have hsub_eq : ((bs.take off2).drop off1).take n1 = (bs.drop off1).take n1 := by
    apply eq_of_length_of_getD (by simp [List.length_take, List.length_drop]; omega)
    intro i hi
    have hi_n1 : i < n1 := by simp [List.length_take, List.length_drop] at hi; omega
    rw [getD_take_lt hi_n1 (by simp [List.length_drop]; omega),
        getD_take_lt hi_n1 (by simp [List.length_drop]; omega),
        getD_drop_eq (by rw [htk_len]; omega),
        getD_drop_eq (by omega), getD_take_lt (by omega) (by omega)]
  refine ⟨(base ↦ₛ (bs.take off2).take off1) ∗
    ((base + BitVec.ofNat 64 (off1 + n1)) ↦ₛ (bs.take off2).drop (off1 + n1)) ∗
    ((base + BitVec.ofNat 64 (off2 + n2)) ↦ₛ bs.drop (off2 + n2)), ?_, ?_⟩
  · rw [split_slot_sub base bs off2 n2 h2,
        split_slot_sub base (bs.take off2) off1 n1 (by rw [htk_len]; exact h12), hsub_eq]
    ac_rfl
  · have hf1 := fold_slot_sub base (bs.take off2) sub1 off1 (by rw [htk_len]; exact h12)
    have hf2 := fold_slot_sub base (replaceSlice bs off1 sub1) sub2 off2
      (by rw [replaceSlice_length (by omega)]; exact h2)
    rw [replaceSlice_take_ge h12 (by omega),
        replaceSlice_drop_ge (k := off2 + n2) (by omega) (by omega)] at hf2
    calc (((base + BitVec.ofNat 64 off1) ↦ₛ sub1) ∗
          ((base + BitVec.ofNat 64 off2) ↦ₛ sub2) ∗
          ((base ↦ₛ (bs.take off2).take off1) ∗
           ((base + BitVec.ofNat 64 (off1 + n1)) ↦ₛ (bs.take off2).drop (off1 + n1)) ∗
           ((base + BitVec.ofNat 64 (off2 + n2)) ↦ₛ bs.drop (off2 + n2))))
      _ = (((base + BitVec.ofNat 64 off2) ↦ₛ sub2) ∗
           (((base + BitVec.ofNat 64 off1) ↦ₛ sub1) ∗
            (base ↦ₛ (bs.take off2).take off1) ∗
            ((base + BitVec.ofNat 64 (off1 + n1)) ↦ₛ (bs.take off2).drop (off1 + n1))) ∗
           ((base + BitVec.ofNat 64 (off2 + n2)) ↦ₛ bs.drop (off2 + n2))) := by ac_rfl
      _ = _ := by rw [hf1, hf2]

private theorem sub3_split_u8_u16 (addr : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 3 ≤ bs.length) :
    ∃ (b0 : BitVec 8) (u1 : BitVec 16),
      (addr ↦ₛ (bs.drop off).take 3) =
        ((addr ↦₈ b0) ∗ ((addr + 1#64) ↦₁₆ u1)) := by
  have ht3 : (bs.drop off).take 3 = [(bs.drop off).getD 0 0#8] ++ ((bs.drop (off + 1)).take 2) := by
    apply eq_of_length_of_getD (by simp [List.length_take, List.length_drop]; omega)
    intro i hi
    have hi3 : i < 3 := by simp [List.length_take, List.length_drop] at hi; omega
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rw [getD_take_lt (by omega) (by simp [List.length_drop]; omega)]; rfl
    · rw [getD_take_lt (by omega) (by simp [List.length_drop]; omega), getD_drop_eq (by omega)]
      change _ = ((bs.drop (off + 1)).take 2).getD 0 0#8
      rw [getD_take_lt (by omega) (by simp [List.length_drop]; omega), getD_drop_eq (by omega)]
    · rw [getD_take_lt (by omega) (by simp [List.length_drop]; omega), getD_drop_eq (by omega)]
      change _ = ((bs.drop (off + 1)).take 2).getD 1 0#8
      rw [getD_take_lt (by omega) (by simp [List.length_drop]; omega), getD_drop_eq (by omega)]
  refine ⟨(bs.drop off).getD 0 0#8, pack16 (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8), ?_⟩
  rw [ht3, pointsToBytes_append, List.length_singleton, pointsToBytes_singleton,
      pointsToBytes_take2_eq_pointsTo16 (addr + BitVec.ofNat 64 1) bs (off + 1) (by omega)]

private theorem sub3_fold_u8_u16 (addr : BitVec 64) (b0 : BitVec 8) (u1 : BitVec 16) :
    ((addr ↦₈ b0) ∗ ((addr + 1#64) ↦₁₆ u1)) = (addr ↦ₛ ([b0] ++ unpack16 u1)) := by
  rw [← pointsToBytes_singleton, pointsTo16_eq_pointsToBytes, pointsToBytes_append]
  rfl

private theorem sub5_split_u8_u32 (addr : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 5 ≤ bs.length) :
    ∃ (b0 : BitVec 8) (u1 : BitVec 32),
      (addr ↦ₛ (bs.drop off).take 5) = ((addr ↦₈ b0) ∗ ((addr + 1#64) ↦₃₂ u1)) := by
  obtain ⟨v32, hv32⟩ := split_slot_u32 (addr + 1#64) ((bs.drop (off + 1)).take 4) (off := 0)
    (by simp [List.length_take, List.length_drop]; omega)
  have ht5 : (bs.drop off).take 5 = [(bs.drop off).getD 0 0#8] ++ ((bs.drop (off + 1)).take 4) := by
    apply eq_of_length_of_getD (by simp [List.length_take, List.length_drop]; omega)
    intro i hi; have hi5 : i < 5 := by simp [List.length_take, List.length_drop] at hi; omega
    by_cases hi0 : i = 0
    · subst hi0; rw [getD_take_lt (by omega) (by simp [List.length_drop]; omega)]; rfl
    · rw [getD_take_lt hi5 (by simp [List.length_drop]; omega), getD_drop_eq (by omega)]
      have hidx : ([((bs.drop off).getD 0 0#8)] ++ (bs.drop (off + 1)).take 4).getD i 0#8 =
          ((bs.drop (off + 1)).take 4).getD (i - 1) 0#8 := by
        rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> rfl
      rw [hidx, getD_take_lt (by omega) (by simp [List.length_drop]; omega), getD_drop_eq (by omega)]
      congr 1; omega
  refine ⟨(bs.drop off).getD 0 0#8, v32, ?_⟩
  have hdr4 : (((bs.drop (off + 1)).take 4).drop 4) = [] := by simp
  have ha0 : addr + 1#64 + BitVec.ofNat 64 0 = addr + 1#64 := by bv_robdd
  rw [ht5, pointsToBytes_append, List.length_singleton, pointsToBytes_singleton]
  change ((addr ↦₈ _) ∗ ((addr + 1#64) ↦ₛ _)) = _; rw [hv32]
  simp only [List.take_zero, hdr4, pointsToBytes_nil, sepConj_emp, ha0]

private theorem sub5_fold_u8_u32 (addr : BitVec 64) (b0 : BitVec 8) (u1 : BitVec 32) :
    ((addr ↦₈ b0) ∗ ((addr + 1#64) ↦₃₂ u1)) = (addr ↦ₛ ([b0] ++ unpack32 u1)) := by
  rw [← pointsToBytes_singleton, pointsTo32_eq_pointsToBytes, pointsToBytes_append]; rfl

/-! ## Offset Header Step (`wp_enframe_step_off`, `+0x808 .. +0x82c`) -/

private theorem step_off_scalars {off : Nat} (hoff1 : 1 ≤ off) (hoffHi : off ≤ 4095) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 off) == 0#32) = false ∧
    BitVec.truncate 16 (BitVec.truncate 32 (BitVec.ofNat 64 off)) = BitVec.ofNat 16 off ∧
    BitVec.signExtend 64
      (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 off)) <<< 4)) =
      BitVec.ofNat 64 (16 * off) := by
  have h1 : (BitVec.setWidth 32 (BitVec.ofNat 64 off) == 0#32) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have ht := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt (by omega : off < 2 ^ 32)] at ht; omega
  have h4 : BitVec.signExtend 64 (BitVec.ofNat 32 off <<< 4) = BitVec.ofNat 64 (16 * off) := by
    have hlt : (BitVec.ofNat 32 off <<< 4).ult (1#32 <<< 31) = true := by
      have hsh : BitVec.ofNat 32 off <<< 4 = BitVec.ofNat 32 (16 * off) := by bv_omega
      rw [hsh, BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
      change (16 * off) % (2 ^ 32) < 2 ^ 31; rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [(by revert hlt; bv_robdd : BitVec.signExtend 64 (BitVec.ofNat 32 off <<< 4) =
      BitVec.zeroExtend 64 (BitVec.ofNat 32 off <<< 4))]; bv_omega
  exact ⟨h1, by bv_omega, by simpa using h4⟩

private theorem split_fold_step_off (start : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (hoff1 : 1 ≤ off) (hoffHi : off ≤ 4095) (hlen : 16 * off + 2 ≤ bs.length) :
    let base := start - 4#64; let mb := start + BitVec.ofNat 64 (16 * off)
    let sub1 := [224#8] ++ unpack16 (BitVec.ofNat 16 off)
    let bs1 := replaceSlice (replaceSlice bs 1 sub1) (16 * off) [0#8]
    ∃ (b1 bOff : BitVec 8) (u2 : BitVec 16) (Rest : SepProp),
      ((base ↦ₛ bs) = (((start - 3#64) ↦₈ b1) ∗ ((start - 2#64) ↦₁₆ u2) ∗ ((mb - 4#64) ↦₈ bOff) ∗ Rest)) ∧
      ((((start - 3#64) ↦₈ 224#8) ∗ ((start - 2#64) ↦₁₆ BitVec.ofNat 16 off) ∗
        ((mb - 4#64) ↦₈ 0#8) ∗ Rest) = (base ↦ₛ bs1)) ∧
      bs1.length = bs.length ∧ bs1.getD 0 0#8 = bs.getD 0 0#8 ∧
      bs1.getD (16 * off) 0#8 = 0#8 ∧ bs1.getD (bs.length - 1) 0#8 = bs.getD (bs.length - 1) 0#8 := by
  intro base mb sub1 bs1
  have hsub1_len : sub1.length = 3 := rfl
  obtain ⟨Rest, hSp, hFd⟩ := split_fold_two_sub base bs sub1 [0#8] 1 (16 * off)
    (by rw [hsub1_len]; omega) (by simp; omega)
  obtain ⟨b1, u2, hSub3⟩ := sub3_split_u8_u16 (base + BitVec.ofNat 64 1) bs 1 (by omega)
  have ht1 : (bs.drop (16 * off)).take 1 = [bs.getD (16 * off) 0#8] := by
    apply eq_of_length_of_getD (by simp [List.length_take, List.length_drop]; omega)
    intro i hi; have hi0 : i = 0 := by simp [List.length_take, List.length_drop] at hi; omega
    subst hi0; rw [getD_take_lt (by omega) (by simp [List.length_drop]; omega), getD_drop_eq (by omega)]; simp
  have ha1 : base + BitVec.ofNat 64 1 = start - 3#64 := by dsimp [base]; bv_robdd
  have ha2 : start - 3#64 + 1#64 = start - 2#64 := by bv_robdd
  have haOff : base + BitVec.ofNat 64 (16 * off) = mb - 4#64 := by dsimp [base, mb]; bv_omega
  refine ⟨b1, bs.getD (16 * off) 0#8, u2, Rest,
    by rw [hsub1_len] at hSp
       rw [hSp, hSub3, List.length_singleton, ht1, pointsToBytes_singleton, ha1, ha2, haOff]; ac_rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hFold3 := sub3_fold_u8_u16 (start - 3#64) 224#8 (BitVec.ofNat 16 off); rw [ha2] at hFold3
    rw [← ha1, ← haOff, ← pointsToBytes_singleton (a := base + BitVec.ofNat 64 (16 * off)) (b := 0#8)]
    have hAssoc : (((base + BitVec.ofNat 64 1) ↦₈ 224#8) ∗ ((start - 2#64) ↦₁₆ BitVec.ofNat 16 off) ∗
        ((base + BitVec.ofNat 64 (16 * off)) ↦ₛ [0#8]) ∗ Rest) =
        ((((start - 3#64) ↦₈ 224#8) ∗ ((start - 2#64) ↦₁₆ BitVec.ofNat 16 off)) ∗
         ((base + BitVec.ofNat 64 (16 * off)) ↦ₛ [0#8]) ∗ Rest) := by rw [ha1]; ac_rfl
    rw [hAssoc, hFold3, ← ha1]; exact hFd
  · dsimp [bs1]; rw [replaceSlice_length (by rw [replaceSlice_length (by rw [hsub1_len]; omega)]; simp; omega),
      replaceSlice_length (by rw [hsub1_len]; omega)]
  · dsimp [bs1]; rw [replaceSlice_getD_out (by rw [replaceSlice_length (by rw [hsub1_len]; omega)]; simp; omega)
      (Or.inl (by omega)), replaceSlice_getD_out (by rw [hsub1_len]; omega) (Or.inl (by omega))]
  · dsimp [bs1]; simpa using replaceSlice_getD_in (bs := replaceSlice bs 1 sub1) (sub := [0#8]) (off := 16 * off)
      (j := 0) (by rw [replaceSlice_length (by rw [hsub1_len]; omega)]; simp; omega) (by simp)
  · dsimp [bs1]; rw [replaceSlice_getD_out (by rw [replaceSlice_length (by rw [hsub1_len]; omega)]; simp; omega)
      (Or.inr (by simp; omega)), replaceSlice_getD_out (by rw [hsub1_len]; omega) (Or.inr (by rw [hsub1_len]; omega))]

arm64_proof_prelude

set_option maxHeartbeats 600000 in
theorem wp_enframe_step_off [MallocngMultiPlacement]
    (s : State) (pSc pIdx off : Nat) (pg : GroupDesc) (bs : List (BitVec 8)) (Frame : SepProp)
    (_hw768 : Blk08HasWords768 mallocngFaultSvc) (_hr768 : Blk08Range768)
    (hpStrLo : 16 ≤ slotStride pSc) (hStrLe : slotStride pSc ≤ pg.stride)
    (hStrHi : pg.stride ≤ 65524) (hoffLe : off ≤ (pg.stride - slotStride pSc) / 16)
    (hbsLen : bs.length = pg.stride + 1)
    (hbs0 : bs.getD 0 0#8 = 0#8) (hbsEnd : bs.getD pg.stride 0#8 = 0#8)
    (hpc : s.pc = mbase 8 + allocSlotOff_enframe_off_done) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = pg.slotStart pIdx)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 pIdx)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 off)
    (hx4 : s.readReg64 .x4 = pg.storage)
    (hw5 : s.readReg32 .x5 = BitVec.ofNat 32 (slotStride pSc - 4))
    (hx6 : s.readReg64 .x6 = 0#64)
    (hx7 : s.readReg64 .x7 = pg.metaPtr)
    (hx8 : s.readReg64 .x8 = pg.slotEnd pIdx) :
    let slotBase := pg.slotStart pIdx - 4#64
    let mb := pg.slotStart pIdx + BitVec.ofNat 64 (16 * off)
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_enframe_idx) s
      ((pg.metaPtr ↦ₛ pg.metaBytes) ∗ (slotBase ↦ₛ bs) ∗ Frame)
      (fun sf P_f =>
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧
        sf.readReg64 .x0 = mb ∧
        sf.readReg64 .x1 = BitVec.ofNat 64 pIdx ∧
        sf.readReg64 .x4 = pg.storage ∧
        sf.readReg32 .x5 = BitVec.ofNat 32 (slotStride pSc - 4) ∧
        sf.readReg64 .x6 = 0#64 ∧
        sf.readReg64 .x8 = pg.slotEnd pIdx ∧
        (∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x4 → sf.readReg64 r = s.readReg64 r) ∧
        ∃ bs1 : List (BitVec 8),
          bs1.length = pg.stride + 1 ∧
          bs1.getD 0 0#8 = 0#8 ∧
          bs1.getD (16 * off) 0#8 = 0#8 ∧
          bs1.getD pg.stride 0#8 = 0#8 ∧
          P_f = ((pg.metaPtr ↦ₛ pg.metaBytes) ∗ (slotBase ↦ₛ bs1) ∗ Frame))
      (fun _ => ⌜False⌝) := by
  intro slotBase mb
  dsimp only [allocSlotOff_enframe_off_done, allocSlotOff_enframe_idx] at hpc ⊢
  rcases Nat.eq_or_lt_of_le (Nat.zero_le off) with rfl | hoffPos
  · wp_sym_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hrun], by simp, by simp [State.spAligned], psp_rfl,
       by simp [hx0, mb], by simp [hx1], by simp [hx4],
       by simp [State.readReg32]; exact hw5, by simp [hx6], by simp [hx8],
       fun r _ _ _ => by simp, bs, hbsLen, hbs0, by simpa using hbs0, hbsEnd, rfl⟩
  · have ⟨hcbz, htr16, hsx1⟩ := step_off_scalars hoffPos (by omega)
    refine (split_fold_step_off (pg.slotStart pIdx) bs off hoffPos (by omega) (by omega)).elim
      fun b1 h => h.elim fun bOff h => h.elim fun u2 h => h.elim fun Rest
        ⟨hSp, hFd, hLen1, hG0, hGOff, hGEnd⟩ => ?_
    have hsx2 : BitVec.signExtend 64 (BitVec.ofNat 32 off <<< 4) = BitVec.ofNat 64 (16 * off) := by
      simpa using hsx1
    have hPreEq : ((pg.metaPtr ↦ₛ pg.metaBytes) ∗ (slotBase ↦ₛ bs) ∗ Frame) =
        ((pg.metaPtr ↦₆₄ pg.prev) ∗ ((pg.metaPtr + 8#64) ↦₆₄ pg.next) ∗
         ((pg.metaPtr + 16#64) ↦₆₄ pg.mem) ∗ ((pg.metaPtr + 24#64) ↦₃₂ pg.availMask) ∗
         ((pg.metaPtr + 28#64) ↦₃₂ pg.freedMask) ∗ ((pg.metaPtr + 32#64) ↦₆₄ pg.packedWord) ∗
         ((pg.slotStart pIdx - 3#64) ↦₈ b1) ∗ ((pg.slotStart pIdx - 2#64) ↦₁₆ u2) ∗
         ((pg.slotStart pIdx + BitVec.ofNat 64 (16 * off) - 4#64) ↦₈ bOff) ∗ Rest ∗ Frame) := by
      dsimp only [slotBase, mb] at hSp ⊢
      rw [GroupDesc.metaBytes_pointsTo, hSp]; ac_rfl
    conv => arg 4; rw [hPreEq]
    wp_sym_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hrun], by simp, by simp [State.spAligned], psp_rfl,
       by dsimp [mb]; simp [hsx2], by simp [hx1], by simp [GroupDesc.storage],
       by simp [State.readReg32]; exact hw5, by simp [hx6], by simp [hx8], ?_,
       _, by omega, by rw [hG0, hbs0], hGOff,
       by have hsi : bs.length - 1 = pg.stride := by omega
          rw [← hsi, hGEnd, hsi, hbsEnd], ?_⟩
    · intro r hr0 hr3 hr4
      simp only [State.readReg64_setPC, State.readReg64_setMem,
        State.readReg64_writeReg64_ne _ _ _ _ hr0,
        State.readReg64_writeReg64_ne _ _ _ _ hr3,
        State.readReg64_writeReg64_ne _ _ _ _ hr4]
    · rw [GroupDesc.metaBytes_pointsTo]
      dsimp only [slotBase, mb] at hFd ⊢
      rw [← hFd]; ac_rfl

/-! ## Parent Slot Index and Reserve Footer Step (`wp_enframe_step_rsv`, `+0x82c .. +0x86c`) -/

private theorem rsv_idx_scalars {pIdx : Nat} (hp : pIdx ≤ 31) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 pIdx)) &&& 255#64) =
      BitVec.ofNat 8 pIdx ∧
    (BitVec.ofNat 32 pIdx &&& 255#32) = BitVec.ofNat 32 pIdx ∧
    BitVec.setWidth 64 (BitVec.ofNat 8 pIdx) = BitVec.setWidth 64 (BitVec.ofNat 32 pIdx) := by
  refine ⟨?_, ?_, by bv_omega⟩ <;> apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_setWidth,
    BitVec.toNat_and, BitVec.toNat_ofNat]
  · change (((pIdx % 2 ^ 64 % 2 ^ 32 % 2 ^ 64) &&& (2 ^ 8 - 1)) % 256) = pIdx % 256
    rw [Nat.and_two_pow_sub_one_eq_mod _ 8]; omega
  · change ((pIdx % 2 ^ 32) &&& (2 ^ 8 - 1)) = pIdx % 2 ^ 32
    rw [Nat.and_two_pow_sub_one_eq_mod _ 8]; omega

private theorem rsv_u16_scalar (storage : BitVec 64) (prod off : Nat)
    (hNoWrap : storage.toNat + prod + 16 * off < 2 ^ 64) :
    let mb := (storage + BitVec.ofNat 64 prod) + BitVec.ofNat 64 (16 * off)
    BitVec.truncate 16 (BitVec.truncate 32 ((mb - storage) >>> 4)) =
      BitVec.ofNat 16 ((mb.toNat - storage.toNat) / 16) := by
  intro mb
  have hMbEq : mb = storage + BitVec.ofNat 64 (prod + 16 * off) := by dsimp [mb]; bv_omega
  have hToNat : mb.toNat = storage.toNat + (prod + 16 * off) := by
    rw [hMbEq]; exact bv64_add_toNat (by omega)
  have hSub : mb - storage = BitVec.ofNat 64 (prod + 16 * off) := by rw [hMbEq]; bv_omega
  have hDiff : mb.toNat - storage.toNat = prod + 16 * off := by omega
  rw [hSub, hDiff]; bv_omega

private theorem sext_neg_u16 (u : BitVec 16) (hu : u ≠ 0#16) :
    BitVec.signExtend 64 (-(u.zeroExtend 32)) = -(u.zeroExtend 64) := by
  have hne : (u == 0#16) = false := beq_eq_false_iff_ne.mpr hu
  revert hne; bv_robdd

private theorem rsv_sub_scalars (start : BitVec 64) (stride off pStr : Nat)
    (hpLo : 16 ≤ pStr) (hSum : pStr + 16 * off ≤ stride) (hHi : stride ≤ 65524) :
    let mb := start + BitVec.ofNat 64 (16 * off)
    let slotEnd := start + BitVec.ofNat 64 (stride - 4)
    let rsv := stride - pStr - 16 * off
    slotEnd - mb = BitVec.ofNat 64 (stride - 4 - 16 * off) ∧
    BitVec.setWidth 32 (BitVec.ofNat 64 (stride - 4 - 16 * off)) - BitVec.ofNat 32 (pStr - 4) =
      BitVec.ofNat 32 rsv ∧
    (rsv = 0 →
      (BitVec.setWidth 32 (BitVec.ofNat 64 (stride - 4 - 16 * off)) ==
        BitVec.ofNat 32 (pStr - 4)) = true) ∧
    (16 ≤ rsv →
      (BitVec.setWidth 32 (BitVec.ofNat 64 (stride - 4 - 16 * off)) ==
        BitVec.ofNat 32 (pStr - 4)) = false ∧
      (BitVec.ofNat 32 rsv).sle 4#32 = false ∧
      slotEnd +
        BitVec.signExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (-BitVec.ofNat 32 rsv))) =
        (start - 4#64) + BitVec.ofNat 64 (stride - rsv)) := by
  intro mb slotEnd rsv
  have hEndSub : slotEnd - mb = BitVec.ofNat 64 (stride - 4 - 16 * off) := by
    have hN : stride - 4 = (stride - 4 - 16 * off) + 16 * off := by omega
    have hB := congrArg (BitVec.ofNat 64) hN; rw [BitVec.ofNat_add] at hB
    dsimp [slotEnd, mb]; rw [hB]; bv_arith
  have hTr32 : ∀ k : Nat, BitVec.setWidth 32 (BitVec.ofNat 64 k) = BitVec.ofNat 32 k := fun k => by
    apply BitVec.eq_of_toNat_eq; simp
  have hSub32 : BitVec.setWidth 32 (BitVec.ofNat 64 (stride - 4 - 16 * off)) -
      BitVec.ofNat 32 (pStr - 4) = BitVec.ofNat 32 rsv := by
    have hN : stride - 4 - 16 * off = rsv + (pStr - 4) := by dsimp [rsv]; omega
    have hB := congrArg (BitVec.ofNat 32) hN; rw [BitVec.ofNat_add] at hB
    rw [hTr32, hB]; bv_arith
  refine ⟨hEndSub, hSub32,
    fun hr0 => by
      have hEq : stride - 4 - 16 * off = pStr - 4 := by dsimp [rsv] at hr0; omega
      rw [beq_iff_eq, hEq, hTr32],
    fun hr16 => ?_⟩
  have hBeqF : (BitVec.setWidth 32 (BitVec.ofNat 64 (stride - 4 - 16 * off)) ==
      BitVec.ofNat 32 (pStr - 4)) = false := by
    rw [beq_eq_false_iff_ne]; intro h
    have h0 : BitVec.ofNat 32 rsv = 0#32 := by rw [← hSub32, h]; simp
    have ht := congrArg BitVec.toNat h0
    simp [Nat.mod_eq_of_lt (by omega : rsv < 2 ^ 32)] at ht; omega
  have hu16 : BitVec.ofNat 32 rsv = (BitVec.ofNat 16 rsv).zeroExtend 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (by omega : rsv < 2 ^ 16), Nat.mod_eq_of_lt (by omega : rsv < 2 ^ 32)]
  have hSleF : (BitVec.ofNat 32 rsv).sle 4#32 = false := by
    have hge16 : (16#16).ule (BitVec.ofNat 16 rsv) = true := by
      rw [BitVec.ule, decide_eq_true_eq]; change 16 ≤ rsv % (2 ^ 16)
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [hu16]; exact (fun u (hu : (16#16).ule u = true) => by revert hu; bv_robdd) _ hge16
  have hAddr : slotEnd +
      BitVec.signExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (-BitVec.ofNat 32 rsv))) =
      (start - 4#64) + BitVec.ofNat 64 (stride - rsv) := by
    have ht0 : ∀ w : BitVec 32, BitVec.truncate 32 (BitVec.zeroExtend 64 w) = w := fun _ => by bv_bits
    have ht : BitVec.truncate 32 (BitVec.zeroExtend 64 (-BitVec.ofNat 32 rsv)) =
        -(BitVec.ofNat 16 rsv).zeroExtend 32 := by rw [ht0, hu16]
    have hne : BitVec.ofNat 16 rsv ≠ 0#16 := fun h => by
      have ht1 := congrArg BitVec.toNat h
      simp [Nat.mod_eq_of_lt (by omega : rsv < 2 ^ 16)] at ht1; omega
    have h64 : (BitVec.ofNat 16 rsv).zeroExtend 64 = BitVec.ofNat 64 rsv := by
      apply BitVec.eq_of_toNat_eq
      simp [Nat.mod_eq_of_lt (by omega : rsv < 2 ^ 16), Nat.mod_eq_of_lt (by omega : rsv < 2 ^ 64)]
    have hN : stride - 4 + 4 = (stride - rsv) + rsv := by dsimp [rsv] at hr16 ⊢; omega
    have hB := congrArg (BitVec.ofNat 64) hN
    rw [BitVec.ofNat_add, BitVec.ofNat_add] at hB
    rw [ht, sext_neg_u16 _ hne, h64]; dsimp [slotEnd]
    change (start + BitVec.ofNat 64 (stride - 4)) + (-BitVec.ofNat 64 rsv) = _
    have hEq64 : BitVec.ofNat 64 (stride - 4) + BitVec.ofNat 64 4 =
        BitVec.ofNat 64 (stride - rsv) + BitVec.ofNat 64 rsv := hB
    bv_arith
  exact ⟨hBeqF, hSleF, hAddr⟩

private theorem split_fold_rsv_hdr (start : BitVec 64) (bs : List (BitVec 8))
    (off : Nat) (bIdx : BitVec 8) (u16Off : BitVec 16) (hlen : 16 * off + 5 ≤ bs.length) :
    let base := start - 4#64
    let mb := start + BitVec.ofNat 64 (16 * off)
    let bs_a := replaceSlice bs (16 * off + 1) ([bIdx] ++ unpack16 u16Off)
    ∃ (bOld : BitVec 8) (uOld : BitVec 16) (Rest : SepProp),
      ((base ↦ₛ bs) = (((mb - 3#64) ↦₈ bOld) ∗ ((mb - 2#64) ↦₁₆ uOld) ∗ Rest)) ∧
      ((((mb - 3#64) ↦₈ bIdx) ∗ ((mb - 2#64) ↦₁₆ u16Off) ∗ Rest) = (base ↦ₛ bs_a)) ∧
      bs_a.length = bs.length ∧ bs_a.getD 0 0#8 = bs.getD 0 0#8 ∧
      bs_a.getD (16 * off) 0#8 = bs.getD (16 * off) 0#8 ∧
      bs_a.getD (16 * off + 1) 0#8 = bIdx ∧
      bs_a.getD (16 * off + 2) 0#8 = (unpack16 u16Off).getD 0 0#8 ∧
      bs_a.getD (16 * off + 3) 0#8 = (unpack16 u16Off).getD 1 0#8 ∧
      bs_a.getD (bs.length - 1) 0#8 = bs.getD (bs.length - 1) 0#8 := by
  intro base mb bs_a
  let sub := [bIdx] ++ unpack16 u16Off
  have hsub_len : sub.length = 3 := rfl
  have h13 : 16 * off + 1 + 3 = 16 * off + 4 := by omega
  have hSp0 := split_slot_sub base bs (16 * off + 1) 3 (by omega)
  have hFd0 := fold_slot_sub base bs sub (16 * off + 1) (by rw [hsub_len]; omega)
  rw [h13] at hSp0; rw [hsub_len, h13] at hFd0
  obtain ⟨bOld, uOld, hSub3⟩ := sub3_split_u8_u16 (base + BitVec.ofNat 64 (16 * off + 1)) bs
    (16 * off + 1) (by omega)
  have ha3 : base + BitVec.ofNat 64 (16 * off + 1) = mb - 3#64 := by dsimp [base, mb]; bv_omega
  have ha2 : mb - 3#64 + 1#64 = mb - 2#64 := by bv_robdd
  refine ⟨bOld, uOld, (base ↦ₛ bs.take (16 * off + 1)) ∗
    ((base + BitVec.ofNat 64 (16 * off + 4)) ↦ₛ bs.drop (16 * off + 4)),
    by rw [hSp0, hSub3, ha3, ha2]; ac_rfl, ?_,
    replaceSlice_length (by rw [hsub_len]; omega),
    replaceSlice_getD_out (by rw [hsub_len]; omega) (Or.inl (by omega)),
    replaceSlice_getD_out (by rw [hsub_len]; omega) (Or.inl (by omega)), ?_, ?_, ?_,
    replaceSlice_getD_out (by rw [hsub_len]; omega) (Or.inr (by rw [hsub_len]; omega))⟩
  · have hFold3 := sub3_fold_u8_u16 (mb - 3#64) bIdx u16Off; rw [ha2] at hFold3
    have hAssoc : (((mb - 3#64) ↦₈ bIdx) ∗ ((mb - 2#64) ↦₁₆ u16Off) ∗
        ((base ↦ₛ bs.take (16 * off + 1)) ∗
         ((base + BitVec.ofNat 64 (16 * off + 4)) ↦ₛ bs.drop (16 * off + 4)))) =
        ((((mb - 3#64) ↦₈ bIdx) ∗ ((mb - 2#64) ↦₁₆ u16Off)) ∗
         (base ↦ₛ bs.take (16 * off + 1)) ∗
         ((base + BitVec.ofNat 64 (16 * off + 4)) ↦ₛ bs.drop (16 * off + 4))) := by ac_rfl
    rw [hAssoc, hFold3, ← ha3]; exact hFd0
  · dsimp [bs_a]
    exact (replaceSlice_getD_in (bs := bs) (sub := sub) (off := 16 * off + 1) (j := 0)
      (by rw [hsub_len]; omega) (by rw [hsub_len]; omega)).trans rfl
  · dsimp [bs_a]; have h := replaceSlice_getD_in (bs := bs) (sub := sub) (off := 16 * off + 1)
      (j := 1) (by rw [hsub_len]; omega) (by rw [hsub_len]; omega)
    simpa [Nat.add_assoc, sub] using h
  · dsimp [bs_a]; have h := replaceSlice_getD_in (bs := bs) (sub := sub) (off := 16 * off + 1)
      (j := 2) (by rw [hsub_len]; omega) (by rw [hsub_len]; omega)
    simpa [Nat.add_assoc, sub] using h

private theorem split_fold_rsv_tail (start : BitVec 64) (stride off rsv : Nat) (bs : List (BitVec 8))
    (hr16 : 16 ≤ rsv) (hLow : 16 * off + 16 ≤ stride - rsv) (hHi : stride ≤ 65524)
    (hlen : bs.length = stride + 1) :
    let base := start - 4#64
    let slotEnd := start + BitVec.ofNat 64 (stride - 4)
    let rsvAddr := base + BitVec.ofNat 64 (stride - rsv)
    let sub2 := [0#8] ++ unpack32 (BitVec.ofNat 32 rsv)
    let bs2 := replaceSlice (replaceSlice bs (stride - rsv) [0#8]) (stride - 5) sub2
    ∃ (bRsv bEnd5 : BitVec 8) (uEnd4 : BitVec 32) (Rest : SepProp),
      ((base ↦ₛ bs) = ((rsvAddr ↦₈ bRsv) ∗ ((slotEnd - 5#64) ↦₈ bEnd5) ∗
         ((slotEnd - 4#64) ↦₃₂ uEnd4) ∗ Rest)) ∧
      (((rsvAddr ↦₈ 0#8) ∗ ((slotEnd - 5#64) ↦₈ 0#8) ∗
        ((slotEnd - 4#64) ↦₃₂ BitVec.ofNat 32 rsv) ∗ Rest) = (base ↦ₛ bs2)) ∧
      bs2.length = stride + 1 ∧
      (∀ idx, idx < 16 * off + 4 → bs2.getD idx 0#8 = bs.getD idx 0#8) ∧
      bs2.getD stride 0#8 = bs.getD stride 0#8 := by
  intro base slotEnd rsvAddr sub2 bs2
  have hsub2_len : sub2.length = 5 := by simp [sub2, unpack32_length]
  obtain ⟨Rest, hSp, hFd⟩ := split_fold_two_sub base bs [0#8] sub2 (stride - rsv) (stride - 5)
    (by simp; omega) (by rw [hsub2_len]; omega)
  obtain ⟨bEnd5, uEnd4, hSub5⟩ := sub5_split_u8_u32 (base + BitVec.ofNat 64 (stride - 5)) bs
    (stride - 5) (by omega)
  have ht1 : (bs.drop (stride - rsv)).take 1 = [bs.getD (stride - rsv) 0#8] := by
    apply eq_of_length_of_getD (by simp [List.length_take, List.length_drop]; omega)
    intro i hi; have hi0 : i = 0 := by simp [List.length_take, List.length_drop] at hi; omega
    subst hi0; rw [getD_take_lt (by omega) (by simp [List.length_drop]; omega), getD_drop_eq (by omega)]; simp
  have ha5 : base + BitVec.ofNat 64 (stride - 5) = slotEnd - 5#64 := by
    dsimp [base, slotEnd]; bv_omega
  have ha4 : slotEnd - 5#64 + 1#64 = slotEnd - 4#64 := by bv_robdd
  refine ⟨bs.getD (stride - rsv) 0#8, bEnd5, uEnd4, Rest,
    by rw [hsub2_len] at hSp
       rw [hSp, List.length_singleton, ht1, pointsToBytes_singleton, hSub5, ha5, ha4]; ac_rfl,
    ?_, ?_, ?_, ?_⟩
  · have hFold5 := sub5_fold_u8_u32 (slotEnd - 5#64) 0#8 (BitVec.ofNat 32 rsv)
    rw [ha4] at hFold5; rw [← pointsToBytes_singleton (a := rsvAddr) (b := 0#8)]
    have hAssoc : ((rsvAddr ↦ₛ [0#8]) ∗ ((slotEnd - 5#64) ↦₈ 0#8) ∗
        ((slotEnd - 4#64) ↦₃₂ BitVec.ofNat 32 rsv) ∗ Rest) =
        ((rsvAddr ↦ₛ [0#8]) ∗
         (((slotEnd - 5#64) ↦₈ 0#8) ∗ ((slotEnd - 4#64) ↦₃₂ BitVec.ofNat 32 rsv)) ∗
         Rest) := by ac_rfl
    rw [hAssoc, hFold5, ← ha5]; exact hFd
  · dsimp [bs2]; rw [replaceSlice_length (by rw [replaceSlice_length (by simp; omega), hsub2_len]; omega),
      replaceSlice_length (by simp; omega), hlen]
  · intro idx _; dsimp [bs2]
    rw [replaceSlice_getD_out (by rw [replaceSlice_length (by simp; omega), hsub2_len]; omega) (Or.inl (by omega)),
        replaceSlice_getD_out (by simp; omega) (Or.inl (by omega))]
  · dsimp [bs2]
    rw [replaceSlice_getD_out (by rw [replaceSlice_length (by simp; omega), hsub2_len]; omega)
          (Or.inr (by rw [hsub2_len]; omega)),
        replaceSlice_getD_out (by simp; omega) (Or.inr (by simp; omega))]

private theorem split_fold_mb3 (start : BitVec 64) (bs : List (BitVec 8))
    (off : Nat) (bNew : BitVec 8) (hlen : 16 * off + 2 ≤ bs.length) :
    let base := start - 4#64; let mb := start + BitVec.ofNat 64 (16 * off)
    let bs' := replaceSlice bs (16 * off + 1) [bNew]
    ∃ Rest : SepProp,
      ((base ↦ₛ bs) = (((mb - 3#64) ↦₈ bs.getD (16 * off + 1) 0#8) ∗ Rest)) ∧
      ((((mb - 3#64) ↦₈ bNew) ∗ Rest) = (base ↦ₛ bs')) ∧
      bs'.length = bs.length ∧ bs'.getD (16 * off + 1) 0#8 = bNew ∧
      (∀ idx, idx ≠ 16 * off + 1 → bs'.getD idx 0#8 = bs.getD idx 0#8) := by
  intro base mb bs'
  have hSp := split_slot_u8 base bs (off := 16 * off + 1) hlen
  have hFd := fold_slot_u8 base bs (off := 16 * off + 1) hlen bNew
  have ha : base + BitVec.ofNat 64 (16 * off + 1) = mb - 3#64 := by dsimp [base, mb]; bv_omega
  refine ⟨(base ↦ₛ bs.take (16 * off + 1)) ∗
    ((base + BitVec.ofNat 64 (16 * off + 1 + 1)) ↦ₛ bs.drop (16 * off + 1 + 1)),
    by rw [hSp, ha], ?_, replaceSlice_length (by simp; omega),
    by simpa using replaceSlice_getD_in (bs := bs) (sub := [bNew]) (off := 16 * off + 1) (j := 0)
         (by simp; omega) (by simp),
    fun _ _ => replaceSlice_getD_out (by simp; omega) (by simp; omega)⟩
  have hAssoc : (((mb - 3#64) ↦₈ bNew) ∗
      ((base ↦ₛ bs.take (16 * off + 1)) ∗
       ((base + BitVec.ofNat 64 (16 * off + 1 + 1)) ↦ₛ bs.drop (16 * off + 1 + 1)))) =
      (((base + BitVec.ofNat 64 (16 * off + 1)) ↦₈ bNew) ∗
       (base ↦ₛ bs.take (16 * off + 1)) ∗
       ((base + BitVec.ofNat 64 (16 * off + 1 + 1)) ↦ₛ bs.drop (16 * off + 1 + 1))) := by
    rw [ha]
  rw [hAssoc]; exact hFd

private abbrev allocSlotOff_rsv_neg : BitVec 64 := words_insn_off% blk08Words 0x4b0503e1#32
private abbrev allocSlotOff_rsv_ldb : BitVec 64 := words_insn_off% blk08Words 0x385fd001#32

set_option maxHeartbeats 800000 in
theorem wp_enframe_step_rsv [MallocngMultiPlacement]
    (s : State) (pSc pIdx off : Nat) (pg : GroupDesc) (bs1 : List (BitVec 8)) (Frame : SepProp)
    (_hw768 : Blk08HasWords768 mallocngFaultSvc) (_hr768 : Blk08Range768)
    (hpIdx31 : pIdx ≤ 31) (hpStrLo : 16 ≤ slotStride pSc) (hpStrDiv : slotStride pSc % 16 = 0)
    (hStrHi : pg.stride ≤ 65524) (hStrDiv : pg.stride % 16 = 0)
    (hoffLe : off ≤ (pg.stride - slotStride pSc) / 16) (hStrLe : slotStride pSc ≤ pg.stride)
    (hNoWrap : pg.storage.toNat + pIdx * pg.stride + 16 * off < 2 ^ 64)
    (hbsLen : bs1.length = pg.stride + 1) (hbs0 : bs1.getD 0 0#8 = 0#8)
    (hbsOff : bs1.getD (16 * off) 0#8 = 0#8) (hbsEnd : bs1.getD pg.stride 0#8 = 0#8)
    (hpc : s.pc = mbase 8 + allocSlotOff_enframe_idx) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = pg.slotStart pIdx + BitVec.ofNat 64 (16 * off))
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 pIdx) (hx4 : s.readReg64 .x4 = pg.storage)
    (hw5 : s.readReg32 .x5 = BitVec.ofNat 32 (slotStride pSc - 4))
    (hx6 : s.readReg64 .x6 = 0#64) (hx8 : s.readReg64 .x8 = pg.slotEnd pIdx) :
    let slotBase := pg.slotStart pIdx - 4#64
    let mb := pg.slotStart pIdx + BitVec.ofNat 64 (16 * off)
    let u16Off := BitVec.ofNat 16 ((mb.toNat - pg.storage.toNat) / 16)
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_enframe_fin) s ((slotBase ↦ₛ bs1) ∗ Frame)
      (fun sf P_f =>
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ PureStatePres s sf ∧
        sf.readReg64 .x0 = mb ∧ sf.readReg32 .x1 = BitVec.ofNat 32 pIdx ∧
        (sf.readReg32 .x6 &&& 0x1f#32 = 0#32) ∧
        (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → sf.readReg64 r = s.readReg64 r) ∧
        ∃ bs2 : List (BitVec 8),
          bs2.length = pg.stride + 1 ∧ bs2.getD 0 0#8 = 0#8 ∧ bs2.getD (16 * off) 0#8 = 0#8 ∧
          bs2.getD (16 * off + 1) 0#8 = BitVec.ofNat 8 pIdx ∧
          bs2.getD (16 * off + 2) 0#8 = (unpack16 u16Off).getD 0 0#8 ∧
          bs2.getD (16 * off + 3) 0#8 = (unpack16 u16Off).getD 1 0#8 ∧
          bs2.getD pg.stride 0#8 = 0#8 ∧ P_f = ((slotBase ↦ₛ bs2) ∗ Frame))
      (fun _ => ⌜False⌝) := by
  intro slotBase mb u16Off
  have hSumLe : slotStride pSc + 16 * off ≤ pg.stride := by omega
  let rsv := pg.stride - slotStride pSc - 16 * off
  have hSlotEndEq : pg.slotEnd pIdx = pg.slotStart pIdx + BitVec.ofNat 64 (pg.stride - 4) := rfl
  obtain ⟨hIdx8, hIdx32, hLdIdx32⟩ := rsv_idx_scalars hpIdx31
  have hU16 : BitVec.setWidth 16 (BitVec.setWidth 32 ((mb - pg.storage) >>> 4)) = u16Off :=
    rsv_u16_scalar pg.storage (pIdx * pg.stride) off hNoWrap
  have ⟨hEndSub, hSub32, hRsvZero, hRsvPos⟩ :=
    rsv_sub_scalars (pg.slotStart pIdx) pg.stride off (slotStride pSc) hpStrLo hSumLe hStrHi
  rw [← hSlotEndEq] at hEndSub hRsvPos
  refine (split_fold_rsv_hdr (pg.slotStart pIdx) bs1 off (BitVec.ofNat 8 pIdx) u16Off
    (by omega)).elim fun bOld h => h.elim fun uOld h => h.elim fun RestHdr
      ⟨hSpHdr, hFdHdr, hLenA, hGA0, hGAOff, hGA1, hGA2, hGA3, hGAEnd⟩ => ?_
  let bs_a := replaceSlice bs1 (16 * off + 1) ([BitVec.ofNat 8 pIdx] ++ unpack16 u16Off)
  have hLenA' : bs_a.length = pg.stride + 1 := hLenA.trans hbsLen
  have hsi : bs1.length - 1 = pg.stride := by omega
  have hHdrFold : (((mb - 3#64) ↦₈ BitVec.ofNat 8 pIdx) ∗
      ((mb - 2#64) ↦₁₆ BitVec.setWidth 16 (BitVec.setWidth 32 ((mb - pg.storage) >>> 4))) ∗
      RestHdr ∗ Frame) = ((slotBase ↦ₛ bs_a) ∗ Frame) := by
    rw [hU16]
    have hAssoc : (((mb - 3#64) ↦₈ BitVec.ofNat 8 pIdx) ∗ ((mb - 2#64) ↦₁₆ u16Off) ∗ RestHdr ∗ Frame) =
        ((((mb - 3#64) ↦₈ BitVec.ofNat 8 pIdx) ∗ ((mb - 2#64) ↦₁₆ u16Off) ∗ RestHdr) ∗ Frame) := by ac_rfl
    rw [hAssoc]; exact congrArg (· ∗ Frame) hFdHdr
  dsimp only [allocSlotOff_enframe_idx, allocSlotOff_enframe_fin] at hpc ⊢
  conv => arg 4; dsimp only [slotBase]; rw [hSpHdr]; simp only [sepConj_assoc]
  wp_sym_steps 8
  wp_if hbeq
  · refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hrun], by simp, by simp [State.spAligned], psp_rfl,
       by dsimp [mb]; simp [hx0], by simp [State.readReg32]; exact hIdx32, by simp [State.readReg32, hx6],
       fun r hr1 hr3 hr4 hr5 _ => by
         simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_setMem,
           State.readReg64_writeReg64_ne _ _ _ _ hr1, State.readReg64_writeReg64_ne _ _ _ _ hr3,
           State.readReg64_writeReg64_ne _ _ _ _ hr4, State.readReg64_writeReg64_ne _ _ _ _ hr5],
       bs_a, hLenA', by rw [hGA0, hbs0], by rw [hGAOff, hbsOff], hGA1, hGA2, hGA3,
       by rw [← hsi, hGAEnd, hsi, hbsEnd], by simpa only [mb] using hHdrFold⟩
  · refine SepWP.seq (mid := mbase 8 + allocSlotOff_rsv_neg)
      (Mid := fun s1 P1 =>
        (rsv ≠ 0 ∧ s1.sp = s.sp ∧ s1.spAligned = s.spAligned ∧ PureStatePres s s1 ∧
          s1.readReg64 .x0 = mb ∧ s1.readReg64 .x5 = BitVec.zeroExtend 64 (BitVec.ofNat 32 rsv) ∧
          s1.readReg64 .x8 = pg.slotEnd pIdx ∧
          (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → s1.readReg64 r = s.readReg64 r)) ∧
        P1 = ((slotBase ↦ₛ bs_a) ∗ Frame)) ?_ ?_
    · refine SepWP.done rfl (by simp [hrun])
        ⟨⟨fun hr0 => ?_, by simp, by simp [State.spAligned], psp_rfl, by dsimp [mb]; simp [hx0],
          by simp only [State.readReg32, BitVec.truncate] at hw5 ⊢
             simp [show pg.slotStart pIdx + BitVec.ofNat 64 (pg.stride - 4) = pg.slotEnd pIdx from rfl,
               hEndSub, hw5]
             exact congrArg (BitVec.setWidth 64) (by simpa using hSub32),
          by simp [hx8],
          fun r hr1 hr3 hr4 hr5 => by
            simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_setMem,
              State.readReg64_writeReg64_ne _ _ _ _ hr1, State.readReg64_writeReg64_ne _ _ _ _ hr3,
              State.readReg64_writeReg64_ne _ _ _ _ hr4, State.readReg64_writeReg64_ne _ _ _ _ hr5]⟩,
         by simpa only [mb] using hHdrFold⟩
      apply hbeq; simp only [State.readReg32, BitVec.truncate] at hw5
      rw [show pg.slotStart pIdx + BitVec.ofNat 64 (pg.stride - 4) = pg.slotEnd pIdx from rfl,
          hEndSub, show Reg.gpr 5#5 = Reg.x5 from rfl, hw5]
      exact beq_iff_eq.mp (hRsvZero hr0)
    · intro s1 P1 hpc1 hrun1 ⟨⟨hr0, hsp1, hal1, hpsp1, hx0_1, hx5_1, hx8_1, hregs1⟩, hP1⟩
      dsimp only [allocSlotOff_rsv_neg] at hpc1
      have hr16 : 16 ≤ rsv := by dsimp [rsv] at hr0 ⊢; omega
      have ⟨_, hSleF, hRsvAddr⟩ := hRsvPos hr16; subst hP1
      refine (split_fold_rsv_tail (pg.slotStart pIdx) pg.stride off rsv bs_a hr16
        (by dsimp [rsv]; omega) hStrHi (by omega)).elim fun bRsv h => h.elim fun bEnd5 h =>
          h.elim fun uEnd4 h => h.elim fun RestTail ⟨hSpTail, hFdTail, hLen2, hG2Low, hG2End⟩ => ?_
      let bs2 := replaceSlice (replaceSlice bs_a (pg.stride - rsv) [0#8])
        (pg.stride - 5) ([0#8] ++ unpack32 (BitVec.ofNat 32 rsv))
      let endP := pg.slotStart pIdx + BitVec.ofNat 64 (pg.stride - 4)
      let rsvEval := endP +
        BitVec.signExtend 64 (0#32 - BitVec.ofNat 32 (pg.stride - slotStride pSc - 16 * off))
      have hRsvEvalEq : rsvEval = pg.slotStart pIdx - 4#64 + BitVec.ofNat 64 (pg.stride - rsv) := by
        dsimp only [rsvEval, endP, rsv] at hRsvAddr ⊢
        simpa [GroupDesc.slotEnd, BitVec.zero_sub] using hRsvAddr
      have hTailPre : ((slotBase ↦ₛ bs_a) ∗ Frame) =
          ((rsvEval ↦₈ bRsv) ∗ ((endP - 5#64) ↦₈ bEnd5) ∗
           ((endP - 4#64) ↦₃₂ uEnd4) ∗ RestTail ∗ Frame) := by
        dsimp only [slotBase, endP]; rw [hRsvEvalEq, hSpTail]; simp only [sepConj_assoc]
      refine SepWP.seq (mid := mbase 8 + allocSlotOff_rsv_ldb)
        (Mid := fun s2 P2 =>
          (s2.sp = s.sp ∧ s2.spAligned = s.spAligned ∧ PureStatePres s s2 ∧
            s2.readReg64 .x0 = mb ∧ s2.readReg64 .x6 = 160#64 ∧
            (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → s2.readReg64 r = s.readReg64 r)) ∧
          P2 = ((slotBase ↦ₛ bs2) ∗ Frame)) ?_ ?_
      · dsimp only [allocSlotOff_rsv_ldb]
        conv => arg 4; rw [hTailPre]; dsimp only [endP]
        wp_sym_steps 7
        refine SepWP.done rfl (by simp [hrun1])
          ⟨⟨hsp1, by simpa [State.spAligned] using hal1, hpsp1, by simp [hx0_1], by simp,
            fun r hr1 hr3 hr4 hr5 hr6 => by
              simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_setMem,
                State.readReg64_writeReg64_ne _ _ _ _ hr6, State.readReg64_writeReg64_ne _ _ _ _ hr1]
              exact hregs1 r hr1 hr3 hr4 hr5⟩, ?_⟩
        change ((rsvEval ↦₈ 0#8) ∗ ((endP - 5#64) ↦₈ 0#8) ∗
          ((endP - 4#64) ↦₃₂ BitVec.ofNat 32 rsv) ∗ RestTail ∗ Frame) = _
        dsimp only [slotBase, endP]; rw [hRsvEvalEq]
        have hAssoc : (((pg.slotStart pIdx - 4#64 + BitVec.ofNat 64 (pg.stride - rsv)) ↦₈ 0#8) ∗
            ((pg.slotStart pIdx + BitVec.ofNat 64 (pg.stride - 4) - 5#64) ↦₈ 0#8) ∗
            ((pg.slotStart pIdx + BitVec.ofNat 64 (pg.stride - 4) - 4#64) ↦₃₂ BitVec.ofNat 32 rsv) ∗
            RestTail ∗ Frame) =
            ((((pg.slotStart pIdx - 4#64 + BitVec.ofNat 64 (pg.stride - rsv)) ↦₈ 0#8) ∗
              ((pg.slotStart pIdx + BitVec.ofNat 64 (pg.stride - 4) - 5#64) ↦₈ 0#8) ∗
              ((pg.slotStart pIdx + BitVec.ofNat 64 (pg.stride - 4) - 4#64) ↦₃₂ BitVec.ofNat 32 rsv) ∗
              RestTail) ∗ Frame) := by ac_rfl
        rw [hAssoc]; exact congrArg (· ∗ Frame) hFdTail
      · intro s2 P2 hpc2 hrun2 ⟨⟨hsp2, hal2, hpsp2, hx0_2, hx6_2, hregs2⟩, hP2⟩
        dsimp only [allocSlotOff_rsv_ldb] at hpc2; subst hP2
        have hB2Idx : bs2.getD (16 * off + 1) 0#8 = BitVec.ofNat 8 pIdx := by
          rw [hG2Low _ (by omega), hGA1]
        refine (split_fold_mb3 (pg.slotStart pIdx) bs2 off (BitVec.ofNat 8 pIdx)
          (by rw [show bs2.length = pg.stride + 1 from hLen2]; omega)).elim fun Rest3 ⟨hSp3, _, _, _, _⟩ => ?_
        conv => arg 4; dsimp only [slotBase]; rw [hSp3, hB2Idx]; simp only [sepConj_assoc]
        wp_sym_steps 1
        refine SepWP.done rfl (by simp [hrun2])
          ⟨by simp [hrun2], hsp2, by simpa [State.spAligned] using hal2, hpsp2,
           by simp [hx0_2], by simp [State.readReg32], by simp [State.readReg32, hx6_2],
           fun r hr1 hr3 hr4 hr5 hr6 => by
             simp only [State.readReg64_setPC, State.readReg64_writeReg64_ne _ _ _ _ hr1]
             exact hregs2 r hr1 hr3 hr4 hr5 hr6,
           bs2, hLen2, by rw [hG2Low _ (by omega), hGA0, hbs0], by rw [hG2Low _ (by omega), hGAOff, hbsOff],
           hB2Idx, by rw [hG2Low _ (by omega), hGA2], by rw [hG2Low _ (by omega), hGA3],
           by rw [hG2End, ← hsi, hGAEnd, hsi, hbsEnd],
           by dsimp only [slotBase]; rw [hSp3, hB2Idx]; simp only [sepConj_assoc]⟩

/-! ## Final Header Tag and Meta Clear (`wp_enframe_step_fin`, `+0x86c .. +0x8a0`) -/

private theorem fin_b3_scalars {pIdx : Nat} {m31 mC0 : BitVec 64} (hp : pIdx ≤ 31) (x1 x6 : BitVec 64)
    (hx1 : BitVec.setWidth 32 x1 = BitVec.ofNat 32 pIdx)
    (hx6 : BitVec.setWidth 32 x6 &&& 0x1f#32 = 0#32)
    (hm31 : BitVec.setWidth 8 m31 = 0x1f#8) (hmC0 : BitVec.setWidth 8 mC0 = 0xc0#8) :
    BitVec.zeroExtend 8
      (BitVec.zeroExtend 64
        (BitVec.zeroExtend 8 x6 +
         BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 x1) &&& m31)) &&&
        m31 ||| mC0) = BitVec.ofNat 8 ((6 <<< 5) ||| pIdx) := by
  have h8_or : ∀ a b : BitVec 64, BitVec.setWidth 8 (a ||| b) =
      BitVec.setWidth 8 a ||| BitVec.setWidth 8 b := fun _ _ => by ext i hi; simp
  have h8_and : ∀ a b : BitVec 64, BitVec.setWidth 8 (a &&& b) =
      BitVec.setWidth 8 a &&& BitVec.setWidth 8 b := fun _ _ => by ext i hi; simp
  have h8_64 : ∀ b : BitVec 8, BitVec.setWidth 8 (BitVec.setWidth 64 b) = b := fun _ => by ext i hi; simp
  have h8_32 : ∀ v : BitVec 32, BitVec.setWidth 8 (BitVec.setWidth 64 v) =
      BitVec.setWidth 8 v := fun _ => by ext i hi; simp
  have hx6_8 : BitVec.setWidth 8 x6 &&& 0x1f#8 = 0#8 :=
    (fun x : BitVec 64 => fun h : BitVec.setWidth 32 x &&& 0x1f#32 = 0#32 => by revert h; bv_robdd) x6 hx6
  have hAdd8 : ∀ b6 b1 : BitVec 8, b6 &&& 0x1f#8 = 0#8 →
      ((b6 + (b1 &&& 0x1f#8)) &&& 0x1f#8) ||| 0xc0#8 = 0xc0#8 ||| (b1 &&& 0x1f#8) := by
    intro b6 b1 h; revert h; bv_robdd
  have hp8 : BitVec.setWidth 8 (BitVec.ofNat 32 pIdx) &&& 0x1f#8 = 0#8 ||| BitVec.ofNat 8 pIdx := by
    have htr : BitVec.setWidth 8 (BitVec.ofNat 32 pIdx) = BitVec.ofNat 8 pIdx := by bv_omega
    have hlt : (BitVec.ofNat 8 pIdx).ult 32#8 = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
      change pIdx % 256 < 32; rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [htr]; exact (fun b : BitVec 8 => fun h : b.ult 32#8 = true => by revert h; bv_robdd) _ hlt
  simp only [BitVec.zeroExtend, h8_or, h8_and, h8_64, h8_32, hx1, hm31, hmC0]
  rw [hAdd8 _ _ hx6_8, hp8, BitVec.zero_or]
  change BitVec.ofNat 8 (6 <<< 5) ||| BitVec.ofNat 8 pIdx = _
  exact BitVec.ofNat_or.symm

set_option maxHeartbeats 600000 in
theorem wp_enframe_step_fin [MallocngMultiPlacement]
    (s : State) (pIdx off cnt' : Nat) (m : BitVec 64) (pg : GroupDesc)
    (bs2 : List (BitVec 8)) (Frame : SepProp)
    (_hw768 : Blk08HasWords768 mallocngFaultSvc) (_hr768 : Blk08Range768)
    (hpIdx31 : pIdx ≤ 31) (_hcnt32 : cnt' ≤ 32) (hlen : 16 * off + 2 ≤ bs2.length)
    (hpc : s.pc = mbase 8 + allocSlotOff_enframe_fin) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = pg.slotStart pIdx + BitVec.ofNat 64 (16 * off))
    (hw1 : s.readReg32 .x1 = BitVec.ofNat 32 pIdx)
    (hw6 : s.readReg32 .x6 &&& 0x1f#32 = 0#32)
    (hx19 : s.readReg64 .x19 = m)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt') :
    let slotBase := pg.slotStart pIdx - 4#64
    let mb := pg.slotStart pIdx + BitVec.ofNat 64 (16 * off)
    let bTag := BitVec.ofNat 8 ((6 <<< 5) ||| pIdx)
    let bs3 := replaceSlice bs2 (16 * off + 1) [bTag]
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_zero_loop) s
      (((m + 32#64) ↦₆₄ 0#64) ∗ (slotBase ↦ₛ bs2) ∗ Frame)
      (fun sf P_f =>
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ PureStatePres s sf ∧
        sf.readReg64 .x0 = mb ∧ sf.readReg64 .x1 = mb + 12#64 ∧
        sf.readReg32 .x2 = 0#32 ∧ sf.readReg32 .x3 = BitVec.ofNat 32 (cnt' + 1) ∧
        (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → sf.readReg64 r = s.readReg64 r) ∧
        bs3.length = bs2.length ∧ bs3.getD (16 * off + 1) 0#8 = bTag ∧
        (∀ idx, idx ≠ 16 * off + 1 → bs3.getD idx 0#8 = bs2.getD idx 0#8) ∧
        P_f = (((m + 32#64) ↦₆₄ 0#64) ∗ (slotBase ↦ₛ bs3) ∗ Frame))
      (fun _ => ⌜False⌝) := by
  intro slotBase mb bTag bs3
  refine (split_fold_mb3 (pg.slotStart pIdx) bs2 off bTag hlen).elim
    fun Rest3 ⟨hSp3, hFd3, hLen3, hGTag, hGOut⟩ => ?_
  dsimp only [allocSlotOff_enframe_fin, allocSlotOff_zero_loop] at hpc ⊢
  conv => arg 4; dsimp only [slotBase]; rw [hSp3]; simp only [sepConj_assoc]
  wp_sym_steps
  refine SepWP.done rfl (by simp [hrun])
    ⟨by simp [hrun], by simp, by simp [State.spAligned], psp_rfl,
     by dsimp [mb]; simp [hx0], by dsimp [mb]; simp, by simp [State.readReg32], by simp [State.readReg32]; bv_omega,
     fun r hr1 hr2 hr3 hr4 => by
       simp only [State.readReg64_setPC, State.readReg64_setMem,
         State.readReg64_writeReg64_ne _ _ _ _ hr1, State.readReg64_writeReg64_ne _ _ _ _ hr2,
         State.readReg64_writeReg64_ne _ _ _ _ hr3, State.readReg64_writeReg64_ne _ _ _ _ hr4],
     hLen3, hGTag, hGOut, ?_⟩
  dsimp only [bTag] at hFd3 ⊢
  rw [fin_b3_scalars hpIdx31 (s.readReg64 (Reg.gpr 1#5)) (s.readReg64 (Reg.gpr 6#5)) hw1 hw6 rfl rfl]
  dsimp only [slotBase, mb] at hFd3 ⊢
  have hAssoc : (((m + 32#64) ↦₆₄ 0#64) ∗ ((mb - 3#64) ↦₈ bTag) ∗ Rest3 ∗ Frame) =
      (((m + 32#64) ↦₆₄ 0#64) ∗ (((mb - 3#64) ↦₈ bTag) ∗ Rest3) ∗ Frame) := by ac_rfl
  rw [hAssoc, hFd3]

end VerifiedLibraries.Mallocng.Proofs
