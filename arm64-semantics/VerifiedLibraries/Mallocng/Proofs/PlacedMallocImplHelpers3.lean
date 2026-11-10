/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplHelpers2
public import VerifiedLibraries.Mallocng.Proofs.SizeClasses

/-!
# Enframing, Byte-Slice, and Frame Helpers for `__libc_malloc_impl`

Proves data-structure, bitvector, byte-slice, and separation-logic framing lemmas for
`__libc_malloc_impl` slot enframing (`+0x1a4..+0x1c4` and `+0x32c..+0x454`) and prologue/epilogue
stack frames (`704 = 80 + 624` bytes).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib SepLogic

/-! ## `enframeClaimed_slotWf` and `enframeClaimed_absorb` -/

private theorem sizeClass_ge_292_of_ge_28 {sc : Nat} (h48 : sc < 48) (h28 : 28 ≤ sc) :
    292 ≤ sizeClass sc := by
  have hAll : (List.range 48).all (fun s => !(decide (28 ≤ s)) || decide (292 ≤ sizeClass s)) = true := by decide
  have h := List.all_eq_true.mp hAll sc (List.mem_range.mpr h48)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at h
  rcases h with hNot | hOk
  · exact False.elim (hNot h28)
  · exact hOk

private theorem checkCoarseSc24_27 :
    nominalSlotCap 23 = 2028 ∧
    nominalSlotCap 24 = 2332 ∧
    pageAlignUp (slotStride 24 + 16) = 4096 ∧ 146 ≤ sizeClass 24 ∧
    pageAlignUp (slotStride 25 + 16) = 4096 ∧ 146 ≤ sizeClass 25 ∧
    pageAlignUp (slotStride 26 + 16) = 4096 ∧ 146 ≤ sizeClass 26 ∧
    pageAlignUp (slotStride 27 + 16) = 4096 ∧ sizeClass 27 = 255 := by decide

private theorem enframe_totalOff_lt_sizeClass
    (g : GroupDesc) (idx req off pNat : Nat)
    (hScLt : g.sc < 48) (hStr16 : 16 ≤ g.stride) (hIdxCnt : idx < g.cnt)
    (hStorNat : g.storage.toNat = g.mem.toNat + 16)
    (hStartNat : (g.slotStart idx).toNat = g.mem.toNat + 16 + idx * g.stride)
    (hPNat : pNat = (g.slotStart idx).toNat + 16 * off)
    (hOff255 : off ≤ 255) (hFit : 16 * off + req ≤ g.stride - 4)
    (hSc24_26 : 24 ≤ g.sc ∧ g.sc ≤ 26 → nominalSlotCap 23 < req)
    (hCoarse : 0 < g.maplen → g.lastIdx = 0 →
      g.stride ≤ slotStride g.sc ∨
      (24 ≤ g.sc ∧ g.maplen * 4096 = pageAlignUp (slotStride g.sc + 16))) :
    (pNat - g.storage.toNat) / 16 < (idx + 1) * sizeClass g.sc := by
  obtain ⟨hCap23, _, hP24, hS24, hP25, hS25, hP26, hS26, hP27, hS27⟩ := checkCoarseSc24_27
  by_cases hZ : (g.lastIdx == 0 && 0 < g.maplen) = true
  · have hZ' : g.lastIdx = 0 ∧ 0 < g.maplen := by simpa using hZ
    have hIdx0 : idx = 0 := by dsimp [GroupDesc.cnt] at hIdxCnt; omega
    subst hIdx0
    rcases hCoarse hZ'.2 hZ'.1 with hStrLe | ⟨h24, hMapAlign⟩
    · dsimp only [slotStride] at hStrLe; omega
    · have hStrVal : g.stride = g.maplen * 4096 - 16 := by simp [GroupDesc.stride, hZ'.1, hZ'.2]
      by_cases hLe26 : g.sc ≤ 26
      · have hNom23 : nominalSlotCap 23 < req := hSc24_26 ⟨h24, hLe26⟩
        rcases (by omega : g.sc = 24 ∨ g.sc = 25 ∨ g.sc = 26) with hsc | hsc | hsc
        · rw [hsc, hP24] at hMapAlign; rw [hsc] at *; omega
        · rw [hsc, hP25] at hMapAlign; rw [hsc] at *; omega
        · rw [hsc, hP26] at hMapAlign; rw [hsc] at *; omega
      · by_cases hEq27 : g.sc = 27
        · rw [hEq27, hP27] at hMapAlign; rw [hEq27, hS27]; omega
        · have h292 := sizeClass_ge_292_of_ge_28 hScLt (by omega)
          omega
  · have hZFalse : (g.lastIdx == 0 && decide (0 < g.maplen)) = false := by
      cases hB : (g.lastIdx == 0 && decide (0 < g.maplen)) <;> simp_all
    have hStrEq : g.stride = 16 * sizeClass g.sc := by
      unfold GroupDesc.stride; rw [ite_eq_right (by simp [hZFalse])]; rfl
    have hIdxStr : idx * g.stride = 16 * (idx * sizeClass g.sc) := by
      rw [hStrEq, ← Nat.mul_assoc, Nat.mul_comm idx 16, Nat.mul_assoc]
    have hMulIdx : (idx + 1) * sizeClass g.sc = idx * sizeClass g.sc + sizeClass g.sc :=
      Nat.succ_mul idx (sizeClass g.sc)
    have hPS : pNat - g.storage.toNat = 16 * (idx * sizeClass g.sc + off) := by omega
    rw [hPS, Nat.mul_div_right _ (by decide)]
    omega

set_option maxHeartbeats 400000 in
private theorem enframeClaimed_arith
    (g : GroupDesc) (idx req off : Nat) (p : BitVec 64)
    (hp : p = g.slotStart idx + BitVec.ofNat 64 (16 * off))
    (hStrPos : 0 < g.stride) (hStrAl : g.stride % 16 = 0)
    (hIdxCnt : idx < g.cnt)
    (hStorNat : g.storage.toNat = g.mem.toNat + 16)
    (hStartNat : (g.slotStart idx).toNat = g.mem.toNat + 16 + idx * g.stride)
    (hEndNat : (g.slotEnd idx).toNat = g.mem.toNat + 12 + (idx + 1) * g.stride)
    (hEnd48 : (g.slotEnd idx).toNat ≤ g.mem.toNat + g.totalBytes)
    (hScCases : g.sc < 48 ∨ g.sc = 63)
    (hMemGe : 4096 ≤ g.mem.toNat) (hMemAl : g.mem.toNat % 16 = 0)
    (hTot48 : g.mem.toNat + g.totalBytes ≤ 2 ^ 48)
    (hTotLe48 : g.sc < 48 → g.totalBytes ≤ 1048576)
    (hCoarse : 0 < g.maplen → g.lastIdx = 0 → g.sc < 48 →
      g.stride ≤ slotStride g.sc ∨
      (24 ≤ g.sc ∧ g.maplen * 4096 = pageAlignUp (slotStride g.sc + 16)))
    (hSc63Info : g.sc = 63 → g.lastIdx = 0 ∧ 0 < g.maplen)
    (hReqMax : req ≤ MallocngMaxAllocSize)
    (hOff255 : off ≤ 255) (hFit : 16 * off + req ≤ g.stride - 4)
    (hSc2 : 2 ≤ g.sc ∧ g.sc < 48 → nominalSlotCap (g.sc - 2) < max req 16)
    (hSc24 : g.sc = 24 → nominalSlotCap 23 < req)
    (hSc63 : g.sc = 63 → g.maplen * 4096 ≤ max req MallocngMinBlockCost + 8195) :
    p.toNat = (g.slotStart idx).toNat + 16 * off ∧
    MallocngBlockWf p req ∧
    (g.slotStart idx).toNat ≤ p.toNat ∧
    p.toNat + req ≤ (g.slotEnd idx).toNat ∧
    (p.toNat - (g.slotStart idx).toNat) % 16 = 0 ∧
    (24 ≤ g.sc ∧ g.sc ≤ 26 → nominalSlotCap 23 < req) ∧
    (g.sc < 48 → (p.toNat - g.storage.toNat) / 16 < (idx + 1) * sizeClass g.sc) ∧
    (p.toNat - g.storage.toNat) / 16 ≤ 0xffff ∧
    (g.slotEnd idx).toNat - (p.toNat + req) < 2 ^ 31 ∧
    (2 ≤ g.sc ∧ g.sc < 48 → nominalSlotCap (g.sc - 2) < max req MallocngMinBlockCost) := by
  have hStr16 : 16 ≤ g.stride := by clear hMemAl; omega
  have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hPNat : p.toNat = (g.slotStart idx).toNat + 16 * off := by
    clear hMemAl hStrAl
    have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by decide
    rw [hp, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hSc24_26 : 24 ≤ g.sc ∧ g.sc ≤ 26 → nominalSlotCap 23 < req := by
    clear hMemAl hStrAl hp
    obtain ⟨hCap23, hCap24, _⟩ := checkCoarseSc24_27
    rintro ⟨h24, h26⟩
    rcases (by omega : g.sc = 24 ∨ g.sc = 25 ∨ g.sc = 26) with hEq | hEq | hEq
    · exact hSc24 hEq
    · have h := hSc2 ⟨by omega, by omega⟩
      have hSub : g.sc - 2 = 23 := by omega
      rw [hSub] at h; omega
    · have h := hSc2 ⟨by omega, by omega⟩
      have hSub : g.sc - 2 = 24 := by omega
      rw [hSub] at h; omega
  have hTotOffSc : g.sc < 48 → (p.toNat - g.storage.toNat) / 16 < (idx + 1) * sizeClass g.sc :=
    fun hScLt => enframe_totalOff_lt_sizeClass g idx req off p.toNat
      hScLt hStr16 hIdxCnt hStorNat hStartNat hPNat hOff255 hFit hSc24_26
      (fun hMp hLast => hCoarse hMp hLast hScLt)
  clear hp hCoarse
  generalize (g.slotStart idx).toNat = startNat at hStartNat hPNat ⊢
  generalize (g.slotEnd idx).toNat = endNat at hEndNat hEnd48 ⊢
  generalize g.storage.toNat = storNat at hStorNat hTotOffSc ⊢
  generalize g.mem.toNat = memNat at hStorNat hStartNat hEndNat hEnd48 hMemGe hMemAl hTot48
  generalize g.totalBytes = totBytes at hEnd48 hTot48 hTotLe48
  have hDvdP : 16 ∣ p.toNat := by
    rw [hPNat, hStartNat]
    exact Nat.dvd_add
      (Nat.dvd_add
        (Nat.dvd_add (Nat.dvd_of_mod_eq_zero hMemAl) (Nat.dvd_refl 16))
        (Nat.dvd_mul_left_of_dvd (Nat.dvd_of_mod_eq_zero hStrAl) idx))
      (Nat.dvd_mul_right 16 off)
  clear hMemAl hStrAl
  have hDiff16 : (p.toNat - startNat) % 16 = 0 := by
    rw [hPNat, Nat.add_sub_cancel_left]
    exact Nat.mul_mod_right 16 off
  have hBlkWf : MallocngBlockWf p req := by
    clear hDiff16 hTotOffSc
    have hPNe : p ≠ 0#64 := fun h0 => by
      rw [h0] at hPNat; simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hPNat; omega
    exact ⟨hPNe, hDvdP, by clear hDvdP; omega, hReqMax⟩
  clear hDvdP
  have hTotOffLe : (p.toNat - storNat) / 16 ≤ 0xffff := by
    clear hBlkWf hDiff16 hTotOffSc
    have hSubLe : p.toNat - storNat ≤ 1048560 := by
      rcases hScCases with hScLt | hScEq63
      · have := hTotLe48 hScLt; omega
      · have hLast0 := (hSc63Info hScEq63).1
        have hIdx0 : idx = 0 := by dsimp [GroupDesc.cnt] at hIdxCnt; omega
        have hMul0 : idx * g.stride = 0 := by rw [hIdx0, Nat.zero_mul]
        rw [hMul0] at hStartNat
        omega
    exact Nat.le_trans (Nat.div_le_div_right hSubLe) (by decide)
  have hResLt31 : endNat - (p.toNat + req) < 2 ^ 31 := by
    clear hBlkWf hDiff16 hTotOffSc hTotOffLe
    have h2_31 : (2 : Nat) ^ 31 = 2147483648 := by decide
    rw [h2_31]
    rcases hScCases with hScLt | hScEq63
    · have := hTotLe48 hScLt; omega
    · obtain ⟨hLast0, hMpPos⟩ := hSc63Info hScEq63
      have h63 := hSc63 hScEq63
      change g.maplen * 4096 ≤ max req 65536 + 8195 at h63
      have hIdx0 : idx = 0 := by dsimp [GroupDesc.cnt] at hIdxCnt; omega
      have hStrEq : g.stride = g.maplen * 4096 - 16 := by
        simp only [GroupDesc.stride, hLast0, beq_self_eq_true, hMpPos, decide_true, Bool.and_self, ↓reduceIte]
      have hMul0 : idx * g.stride = 0 := by rw [hIdx0, Nat.zero_mul]
      have hMul1 : (idx + 1) * g.stride = g.maplen * 4096 - 16 := by
        rw [hIdx0, Nat.zero_add, Nat.one_mul, hStrEq]
      rw [hMul0] at hStartNat
      rw [hMul1] at hEndNat
      omega
  have hSc2Min : 2 ≤ g.sc ∧ g.sc < 48 → nominalSlotCap (g.sc - 2) < max req MallocngMinBlockCost :=
    fun h => Nat.lt_of_lt_of_le (hSc2 h) (Nat.max_le.mpr
      ⟨Nat.le_max_left _ _, Nat.le_trans (by decide : 16 ≤ MallocngMinBlockCost) (Nat.le_max_right _ _)⟩)
  exact ⟨hPNat, hBlkWf, by clear hBlkWf hDiff16 hTotOffSc hTotOffLe; omega,
    by clear hBlkWf hDiff16 hTotOffSc hTotOffLe; omega,
    hDiff16, hSc24_26, hTotOffSc, hTotOffLe, hResLt31, hSc2Min⟩

set_option maxHeartbeats 400000 in
theorem enframeClaimed_slotWf {base brkStart brk : BitVec 64}
    {liveCost peakCost req off : Nat} {st1 : MallocngSt}
    (hwf1 : MallocngWFInflight 1 base brkStart brk liveCost peakCost st1)
    {g : GroupDesc} (hg : g ∈ st1.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hReqMax : req ≤ MallocngMaxAllocSize)
    (hOff255 : off ≤ 255) (hFit : 16 * off + req ≤ g.stride - 4)
    (hSc2 : 2 ≤ g.sc ∧ g.sc < 48 → nominalSlotCap (g.sc - 2) < max req 16)
    (hSc24 : g.sc = 24 → nominalSlotCap 23 < req)
    (hSc63 : g.sc = 63 → g.maplen * 4096 ≤ max req MallocngMinBlockCost + 8195)
    {val' : BitVec 64 → BitVec 8} {liveMap' : MallocngLiveMap}
    (hByteStart4 : val' (g.slotStart idx - 4#64) = 0#8)
    (hByteP4 : val' (g.slotStart idx + BitVec.ofNat 64 (16 * off) - 4#64) = 0#8)
    (hByteP3 : val' (g.slotStart idx + BitVec.ofNat 64 (16 * off) - 3#64) =
      BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat -
        ((g.slotStart idx + BitVec.ofNat 64 (16 * off)).toNat + req)) 5 <<< 5) ||| idx))
    (hByteP2 : readBytesFromMap val' (g.slotStart idx + BitVec.ofNat 64 (16 * off) - 2#64) 2 =
      unpack16 (BitVec.ofNat 16 (((g.slotStart idx + BitVec.ofNat 64 (16 * off)).toNat -
        g.storage.toNat) / 16)))
    (hByteRes1 : 1 ≤ (g.slotEnd idx).toNat -
        ((g.slotStart idx + BitVec.ofNat 64 (16 * off)).toNat + req) →
      val' (g.slotStart idx + BitVec.ofNat 64 (16 * off) + BitVec.ofNat 64 req) = 0#8)
    (hByteRes5 : 5 ≤ (g.slotEnd idx).toNat -
        ((g.slotStart idx + BitVec.ofNat 64 (16 * off)).toNat + req) →
      val' (g.slotEnd idx - 5#64) = 0#8 ∧
      readBytesFromMap val' (g.slotEnd idx - 4#64) 4 = unpack32 (BitVec.ofNat 32
        ((g.slotEnd idx).toNat - ((g.slotStart idx + BitVec.ofNat 64 (16 * off)).toNat + req)))) :
    let p := g.slotStart idx + BitVec.ofNat 64 (16 * off)
    let sNew := SlotState.liveUser p req (max req MallocngMinBlockCost)
    MallocngBlockWf p req ∧
    st1.liveMap p = none ∧
    p.toNat = (g.slotStart idx).toNat + 16 * off ∧
    (24 ≤ g.sc ∧ g.sc ≤ 26 → nominalSlotCap 23 < req) ∧
    SlotWf (mkReplaceSlotSt st1 g idx g.availMask sNew val' liveMap')
      (mkReplaceSlotGroup g idx g.availMask sNew) idx sNew := by
  intro p sNew
  have hgw0 := hwf1.groups_wf g hg
  obtain ⟨hStrPos, hStrAl⟩ := group_stride_pos_and_align hgw0
  have hsb := group_slot_bounds hgw0 hIdx
  have hgw := hgw0
  dsimp only [GroupWf] at hgw
  clear hgw0
  have hTotLe48 : g.sc < 48 → g.totalBytes ≤ 1048576 := fun hScLt => by
    by_cases hMp : 0 < g.maplen
    · simpa only [GroupDesc.totalBytes, hMp, ↓reduceIte] using
        ((hgw.2.2.2.2.2.2.2.2.2.2.2.1 hMp).2.2.2 hScLt).1
    · have hMp0 : g.maplen = 0 := Nat.eq_zero_of_not_pos hMp
      obtain ⟨_, pg, _, _, _, _, hPg48, _, _, _, _, _, hCap⟩ := hgw.2.2.2.2.2.2.2.2.2.2.2.2.1 hMp0
      clear hwf1 hgw hsb
      have hPgSc := (sizeClass_bounds hPg48).2.1
      simp only [GroupDesc.totalBytes, hMp0, Nat.lt_irrefl, ↓reduceIte, hCap, slotStride]; omega
  have hsw := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx
  have hAvF : g.availMask.getLsbD idx = false := by
    cases hB : g.availMask.getLsbD idx with
    | false => rfl
    | true => have h := hsw.2.1.mp hB; rw [hClaimed] at h; cases h
  have hFrF : g.freedMask.getLsbD idx = false := by
    cases hB : g.freedMask.getLsbD idx with
    | false => rfl
    | true => have h := hsw.2.2.1.mp hB; rw [hClaimed] at h; cases h
  have hActGe : ¬ g.activeIdx < idx := fun hLt => by
    have h := hsw.2.2.2.1 hLt; rw [hClaimed] at h; cases h
  obtain ⟨hPNat, hBlkWf, hLe1, hLe2, _, hSc24_26, hTotOffSc, hTotOffLe, hResLt31, hSc2Min⟩ :=
    enframeClaimed_arith g idx req off p rfl (Nat.lt_of_lt_of_le (by decide : 0 < 16) hStrPos) hStrAl
      hsb.1 hsb.2.1 hsb.2.2.1 hsb.2.2.2.2.1 hsb.2.2.2.2.2.1
      hgw.1 hgw.2.2.2.2.1 hgw.2.2.2.2.2.1 hgw.2.2.2.2.2.2.1 hTotLe48
      (fun hMp hLast hScLt => ((hgw.2.2.2.2.2.2.2.2.2.2.2.1 hMp).2.2.2 hScLt).2 hLast)
      (fun h63 => ⟨(hgw.2.2.2.1 h63).1, (hgw.2.2.2.1 h63).2.1⟩)
      hReqMax hOff255 hFit hSc2 hSc24 hSc63
  have hPEnd : p.toNat ≤ (g.slotEnd idx).toNat := Nat.le_trans (Nat.le_add_right _ _) hLe2
  have hFresh : st1.liveMap p = none :=
    liveMap_fresh_of_claimed hwf1 hg hIdx hClaimed hBlkWf.2.1 hLe1 hPEnd
  clear hwf1 hg hClaimed hgw hsb hsw
  have hOffBnd : p.toNat - (g.slotStart idx).toNat ≤
      max req MallocngMinBlockCost - max req MallocngMinBlockCost + 255 * 16 := by
    rw [Nat.sub_self, Nat.zero_add, hPNat, Nat.add_sub_cancel_left, Nat.mul_comm 255 16]
    exact Nat.mul_le_mul_left 16 hOff255
  refine ⟨hBlkWf, hFresh, hPNat, hSc24_26, ?_⟩
  let g' := mkReplaceSlotGroup g idx g.availMask sNew
  dsimp only [SlotWf]
  have hStartEq : g'.slotStart idx = g.slotStart idx := rfl
  have hEndEq : g'.slotEnd idx = g.slotEnd idx := rfl
  have hStorEq : g'.storage = g.storage := rfl
  have hScEq : g'.sc = g.sc := rfl
  have hMpEq' : g'.maplen = g.maplen := rfl
  have hActEq : g'.activeIdx = g.activeIdx := rfl
  rw [hStartEq, hEndEq, hStorEq, hScEq, hMpEq', hActEq]
  exact ⟨hByteStart4,
    ⟨fun h => False.elim (by change g.availMask.getLsbD idx = true at h; rw [hAvF] at h; cases h),
      fun h => nomatch h⟩,
    ⟨fun h => False.elim (by change g.freedMask.getLsbD idx = true at h; rw [hFrF] at h; cases h),
      fun h => nomatch h⟩,
    fun hLt => False.elim (hActGe hLt),
    hBlkWf, hLe1, hLe2, Nat.le_refl _,
    ⟨hOffBnd, by simp [MaxAlignedAllocAlign], by simp⟩,
    hResLt31, ⟨hSc2Min, hTotOffSc⟩, hSc63, hByteP3,
    (by
      split
      · exact ⟨hByteP4, hByteP2⟩
      · rename_i hN; exact False.elim (hN hTotOffLe)),
    hByteRes1, hByteRes5⟩

set_option maxHeartbeats 400000 in
theorem enframeClaimed_absorb
    {base brkStart brk : BitVec 64} {b : MallocngBudget} {req off : Nat} {st1 : MallocngSt}
    (hwf1 : MallocngWFInflight 1 base brkStart brk b.liveCost b.peakCost st1)
    {g : GroupDesc} (hg : g ∈ st1.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hReqMax : req ≤ MallocngMaxAllocSize)
    (hOff255 : off ≤ 255) (hFit : 16 * off + req ≤ g.stride - 4)
    (hSc2 : 2 ≤ g.sc ∧ g.sc < 48 → nominalSlotCap (g.sc - 2) < max req 16)
    (hSc24 : g.sc = 24 → nominalSlotCap 23 < req)
    (hSc63 : g.sc = 63 → g.maplen * 4096 ≤ max req MallocngMinBlockCost + 8195)
    {newSlotBytes : List (BitVec 8)} (hLen : newSlotBytes.length = g.stride)
    (hByteStart4 : writeBytesToMap st1.byteVal (g.slotStart idx - 4#64) newSlotBytes
      (g.slotStart idx - 4#64) = 0#8)
    (hByteP4 : writeBytesToMap st1.byteVal (g.slotStart idx - 4#64) newSlotBytes
      (g.slotStart idx + BitVec.ofNat 64 (16 * off) - 4#64) = 0#8)
    (hByteP3 : writeBytesToMap st1.byteVal (g.slotStart idx - 4#64) newSlotBytes
      (g.slotStart idx + BitVec.ofNat 64 (16 * off) - 3#64) =
      BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat -
        ((g.slotStart idx + BitVec.ofNat 64 (16 * off)).toNat + req)) 5 <<< 5) ||| idx))
    (hByteP2 : readBytesFromMap (writeBytesToMap st1.byteVal (g.slotStart idx - 4#64) newSlotBytes)
      (g.slotStart idx + BitVec.ofNat 64 (16 * off) - 2#64) 2 =
      unpack16 (BitVec.ofNat 16 (((g.slotStart idx + BitVec.ofNat 64 (16 * off)).toNat -
        g.storage.toNat) / 16)))
    (hByteRes1 : 1 ≤ (g.slotEnd idx).toNat -
        ((g.slotStart idx + BitVec.ofNat 64 (16 * off)).toNat + req) →
      writeBytesToMap st1.byteVal (g.slotStart idx - 4#64) newSlotBytes
        (g.slotStart idx + BitVec.ofNat 64 (16 * off) + BitVec.ofNat 64 req) = 0#8)
    (hByteRes5 : 5 ≤ (g.slotEnd idx).toNat -
        ((g.slotStart idx + BitVec.ofNat 64 (16 * off)).toNat + req) →
      writeBytesToMap st1.byteVal (g.slotStart idx - 4#64) newSlotBytes (g.slotEnd idx - 5#64) = 0#8 ∧
      readBytesFromMap (writeBytesToMap st1.byteVal (g.slotStart idx - 4#64) newSlotBytes)
        (g.slotEnd idx - 4#64) 4 = unpack32 (BitVec.ofNat 32
        ((g.slotEnd idx).toNat - ((g.slotStart idx + BitVec.ofNat 64 (16 * off)).toNat + req)))) :
    let start := g.slotStart idx
    let p := start + BitVec.ofNat 64 (16 * off)
    let effCost := max req MallocngMinBlockCost
    let val' := writeBytesToMap st1.byteVal (start - 4#64) newSlotBytes
    let liveMap' := st1.liveMap.insert p req 0
    let g' := mkReplaceSlotGroup g idx g.availMask (.liveUser p req effCost)
    let st2 := mkReplaceSlotSt st1 g idx g.availMask (.liveUser p req effCost) val' liveMap'
    let bf := mallocngAllocBudget true req b
    MallocngBlockWf p req ∧
    st1.liveMap p = none ∧
    p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
    (24 ≤ g'.sc ∧ g'.sc ≤ 26 → nominalSlotCap 23 < req) ∧
    MallocngWF base brkStart brk bf.liveCost bf.peakCost st2 ∧
    g' ∈ st2.groups ∧
    totalLiveCount st2 = totalLiveCount st1 + 1 ∧
    dynamicRootRegions st2 = dynamicRootRegions st1 ∧
    ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal =
      (((start - 4#64) ↦ₛ readBytesFromMap st1.byteVal (start - 4#64) g.stride) ∗
        ByteMap st1.masterDom (fun a => OwnedRwByte st1 a ∧ ¬ InRegion (start - 4#64) g.stride a) st1.byteVal) ∧
    (((start - 4#64) ↦ₛ newSlotBytes) ∗
      ByteMap st1.masterDom (fun a => OwnedRwByte st1 a ∧ ¬ InRegion (start - 4#64) g.stride a) st1.byteVal) =
      ((p ↦ₛ readBytesFromMap val' p req) ∗ ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal) ∧
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
      ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal ∧
    MappedSet st1.masterDom (OwnedMappedByte st1) =
      MappedSet st2.masterDom (OwnedMappedByte st2) := by
  intro start p effCost val' liveMap' g' st2 bf
  obtain ⟨hBlkWf, hFresh, hPNat, hSc24_26, hTargetSw⟩ := enframeClaimed_slotWf hwf1 hg hIdx
    hClaimed hReqMax hOff255 hFit hSc2 hSc24 hSc63 (liveMap' := liveMap')
    hByteStart4 hByteP4 hByteP3 hByteP2 hByteRes1 hByteRes5
  clear hSc2 hSc24 hSc63 hByteP4 hByteP3 hByteP2 hByteRes1 hByteRes5
  change p.toNat = start.toNat + 16 * off at hPNat
  have hSw1 : st1.byteVal (start - 4#64) = 0#8 :=
    ((hwf1.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx).1
  have hMaskAnd := (hwf1.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMaskOr := (hwf1.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMetaBytes0 := (hwf1.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTot48 : g.mem.toNat + g.totalBytes ≤ 2 ^ 48 := (hwf1.groups_wf g hg).2.2.2.2.2.2.1
  have hStrPos := (group_stride_pos_and_align (hwf1.groups_wf g hg)).1
  have hStartNat : start.toNat = g.mem.toNat + 16 + idx * g.stride :=
    (group_slot_bounds (hwf1.groups_wf g hg) hIdx).2.2.1
  have hSub4Nat : (start - 4#64).toNat = g.mem.toNat + 12 + idx * g.stride :=
    (group_slot_bounds (hwf1.groups_wf g hg) hIdx).2.2.2.1
  have hEndNat : (g.slotEnd idx).toNat = g.mem.toNat + 12 + (idx + 1) * g.stride :=
    (group_slot_bounds (hwf1.groups_wf g hg) hIdx).2.2.2.2.1
  have hEnd48 : (g.slotEnd idx).toNat ≤ g.mem.toNat + g.totalBytes :=
    (group_slot_bounds (hwf1.groups_wf g hg) hIdx).2.2.2.2.2.1
  have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hRes0 : st1.reservedMetas = [] := by
    have hInf := hwf1.inflight_wf
    have hSetCl := (list_set_slot_props g.slots idx hIdx .freeAvail).1
    have hSumCl := (replaceGroup_props st1.groups g (mkReplaceSlotGroup g idx g.availMask .freeAvail)
      hg hwf1.groups_nodup.1 rfl rfl rfl rfl rfl rfl rfl).2.2.2.2.2.2.2.2
      (fun x => (x.slots.filter SlotState.isClaimed).length)
    rw [hClaimed] at hSetCl
    simp only [SlotState.isClaimed, mkReplaceSlotGroup, Bool.false_eq_true, ↓reduceIte] at hSetCl hSumCl
    unfold totalClaimedSlots at hInf
    cases hR : st1.reservedMetas with
    | nil => rfl
    | cons _ _ => simp only [hR, List.length_cons] at hInf; omega
  have hNotN : ∀ cm, g.slots[idx]'hIdx ≠ .liveNested cm := by rw [hClaimed]; intro _ h; cases h
  have hNotU : ∀ u r c, g.slots[idx]'hIdx ≠ .liveUser u r c := by rw [hClaimed]; intro _ _ _ h; cases h
  obtain ⟨_, hSlotOwn⟩ := group_meta_and_claimed_ownedRw hwf1 hRes0 hg
  obtain ⟨hwf2, hg'Mem, _, hCntEq, hDynEq, hMpIff, hCarvIff⟩ := replaceSlot_wf_core (inflight' := 0)
    (liveCost' := bf.liveCost) (peakCost' := bf.peakCost)
    hwf1 hg hIdx hNotN hNotU (fun _ h => by cases h) rfl
    hMaskAnd hMaskOr
    (fun _ _ => rfl) (Or.inl rfl)
    (fun a hNotMod => by
      by_cases hEq4 : a = start - 4#64
      · subst hEq4; exact hByteStart4.trans hSw1.symm
      · exact writeBytesToMap_out _ _ _ (fun hIn => hNotMod (Or.inr ⟨by rwa [hLen] at hIn, hEq4⟩)))
    ((readBytesFromMap_congr_pred (W := InRegion (start - 4#64) g.stride) (by omega)
      (fun a ha hSl => (hSlotOwn idx hIdx hNotN hNotU a hSl).2.2 ha)
      (fun a hOut => writeBytesToMap_out st1.byteVal (start - 4#64) newSlotBytes (by rwa [hLen]))).trans
      hMetaBytes0)
    hTargetSw
    (by have := hwf1.inflight_wf; rw [hClaimed]
        change st1.reservedMetas.length + totalClaimedSlots st1 + (if false = true then 1 else 0) ≤
          0 + (if true = true then 1 else 0)
        simp only [Bool.false_eq_true, ↓reduceIte]; omega)
    (fun q n => by
      dsimp only [liveMap']; rw [MallocngLiveMap.insert_req]; constructor
      · intro h; by_cases hqp : q = p
        · subst hqp; simp only [↓reduceIte, Option.some.injEq] at h; subst h; exact Or.inl ⟨effCost, rfl⟩
        · simp only [hqp, ↓reduceIte] at h; exact Or.inr h
      · rintro (⟨ef, hE⟩ | hOld)
        · cases hE; exact ite_eq_left rfl
        · have hqp : q ≠ p := fun hEq => by
            subst hEq; change st1.liveMap p = none at hFresh; rw [hFresh] at hOld; cases hOld
          simp only [hqp, ↓reduceIte, hOld])
    (fun u r hU => by
      have hup : u ≠ p := fun hEq => by
        have hF : st1.liveMap p = none := hFresh; rw [hEq, hF] at hU; cases hU
      dsimp only [liveMap']; rw [MallocngLiveMap.insert_ov]; simp only [hup, ↓reduceIte])
    (by simp only [bf, mallocngAllocBudget, ↓reduceIte]; omega)
    (by have := hwf1.effCost_le_live; simp only [bf, mallocngAllocBudget, slotEffCost, ↓reduceIte]; omega)
    (by simp only [bf, mallocngAllocBudget, ↓reduceIte]; omega)
  have hStride64 : g.stride ≤ 2 ^ 64 := by omega
  have hExtSlot := ByteMap_extract_slice hwf1.masterDom_wf.1 (keep := OwnedRwByte st1)
    st1.byteVal (start - 4#64) (n := g.stride) hStride64
    (fun a ha => (hSlotOwn idx hIdx hNotN hNotU a ha).2.1)
    (fun a ha => (hSlotOwn idx hIdx hNotN hNotU a ha).1)
  have hAbsSlot := ByteMap_absorb_slice hwf1.masterDom_wf.1
    (keep := fun a => OwnedRwByte st1 a ∧ ¬ InRegion (start - 4#64) g.stride a)
    st1.byteVal (start - 4#64) newSlotBytes (by rw [hLen]; exact hStride64)
    (fun a ha => (hSlotOwn idx hIdx hNotN hNotU a (by rwa [hLen] at ha)).2.1)
    (fun a ha hK => hK.2 (by rwa [hLen] at ha))
  have hAbsEqRw1 : ByteMap st1.masterDom
      (fun a => (OwnedRwByte st1 a ∧ ¬ InRegion (start - 4#64) g.stride a) ∨
        InRegion (start - 4#64) newSlotBytes.length a) val' =
      ByteMap st1.masterDom (OwnedRwByte st1) val' := by
    unfold ByteMap; refine SetSep_congr (fun a _ => ?_) (fun _ _ _ => rfl)
    rw [hLen]
    exact ⟨fun h => h.elim (fun h1 => h1.1) (fun h2 => (hSlotOwn idx hIdx hNotN hNotU a h2).1),
      fun h => (Classical.em (InRegion (start - 4#64) g.stride a)).elim Or.inr (fun hS => Or.inl ⟨h, hS⟩)⟩
  have hPInSlot : ∀ a, InRegion p req a → InRegion (start - 4#64) g.stride a := fun a ha => by
    have haN := (inRegion_iff_toNat (base := p) (n := req) (by omega) a).mp ha
    exact (inRegion_iff_toNat (base := start - 4#64) (n := g.stride) (by omega) a).mpr ⟨by omega, by omega⟩
  have hCarveP := ByteMap_extract_slice hwf1.masterDom_wf.1 (keep := OwnedRwByte st1)
    val' p (n := req) (by omega)
    (fun a ha => (hSlotOwn idx hIdx hNotN hNotU a (hPInSlot a ha)).2.1)
    (fun a ha => (hSlotOwn idx hIdx hNotN hNotU a (hPInSlot a ha)).1)
  have hRwRestEq : ByteMap st1.masterDom (fun a => OwnedRwByte st1 a ∧ ¬ InRegion p req a) val' =
      ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal := by
    unfold ByteMap; refine SetSep_congr (fun a _ => ?_) (fun _ _ _ => rfl)
    obtain ⟨_, hGsCases, hGsKeep, _, _, _, _, _, _⟩ :=
      replaceGroup_props st1.groups g g' hg hwf1.groups_nodup.1 rfl rfl rfl rfl rfl rfl rfl
    unfold OwnedRwByte
    constructor
    · rintro ⟨⟨hD, hNC, hNM⟩, hNP⟩
      refine ⟨?_, fun hc => ?_, hNM⟩
      · exact hD.elim Or.inl (fun ⟨x, hx, hp, hi⟩ =>
          if hE : x.metaPtr = g.metaPtr then
            by have rflX := mem_groups_eq_of_metaPtr hwf1.groups_nodup.1 hx hg hE
               subst rflX; exact Or.inr ⟨g', hg'Mem, hp, hi⟩
          else Or.inr ⟨x, hGsKeep x hx hE, hp, hi⟩)
      · rcases (hCarvIff a).mp hc with ⟨u, r, c, hEq, hIn⟩ | hc1
        · cases hEq; exact hNP hIn
        · exact hNC hc1
    · rintro ⟨hD, hNC, hNM⟩
      refine ⟨⟨?_, fun hc1 => hNC ((hCarvIff a).mpr (Or.inr hc1)), hNM⟩,
        fun hIn => hNC ((hCarvIff a).mpr (Or.inl ⟨p, req, effCost, rfl, hIn⟩))⟩
      exact hD.elim Or.inl (fun ⟨x, hx, hp, hi⟩ => (hGsCases x hx).elim
        (fun ⟨_, hE⟩ => by subst hE; exact Or.inr ⟨g, hg, hp, hi⟩)
        (fun ⟨_, hxO⟩ => Or.inr ⟨x, hxO, hp, hi⟩))
  have hPnEq : ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
      ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal := by
    unfold ProtNoneByteMap; refine SetSep_congr (fun _ _ => Iff.rfl) (fun a _ hPn => ?_)
    congr 1
    by_cases hEq4 : a = start - 4#64
    · subst hEq4; exact (hByteStart4.trans hSw1.symm).symm
    · obtain ⟨hDisjAp, hDisjGp⟩ := protNone_disjoint_slotWriteMod hwf1 hg hIdx
      have hOut : ¬ InRegion (start - 4#64) g.stride a := fun hS =>
        hPn.elim (fun ⟨gp, hgp, ha⟩ => hDisjGp gp hgp a ha (Or.inr ⟨hS, hEq4⟩))
          (fun ⟨ap, hap, ha⟩ => hDisjAp ap hap a ha (Or.inr ⟨hS, hEq4⟩))
      exact (writeBytesToMap_out st1.byteVal (start - 4#64) newSlotBytes (by rwa [hLen])).symm
  have hMpEq : MappedSet st1.masterDom (OwnedMappedByte st1) =
      MappedSet st2.masterDom (OwnedMappedByte st2) := by
    unfold MappedSet; exact SetSep_congr (fun a _ => (hMpIff a).symm) (fun _ _ _ => rfl)
  exact ⟨hBlkWf, hFresh, by change p.toNat - start.toNat ≤ 255 * 16; omega, hSc24_26,
    hwf2, hg'Mem, hCntEq, hDynEq, hExtSlot,
    (hAbsSlot.trans hAbsEqRw1).trans (hCarveP.trans (by rw [hRwRestEq])),
    hPnEq, hMpEq⟩

/-! ## Stack-Frame and `bupd` Framing Helpers -/

theorem sepWP_bupd_focus {prog : Program} {ret : BitVec 64} {s : State}
    {Full T Q F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hUpd : T ⊢ |==> Q)
    (hf : ∀ R : SepProp, (s.mem ⊨ Full ∗ R) → (s.mem ⊨ T ∗ (F ∗ R)) := by sep_frame)
    (h : SepWP prog ret s (Q ∗ F) post oom) :
    SepWP prog ret s Full post oom := by
  apply SepWP.of_reaches_pc
  intro R hm hLoad
  have hm' := Satisfies.of_bupd_frame_left hUpd (hf R hm)
  rw [← sepConj_assoc] at hm'
  exact SepWP.to_reaches_pc h hm' hLoad

def MallocImplSavedRegs (s0 : State) (sp1 : BitVec 64) : SepProp :=
  (sp1 ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
  ((sp1 + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((sp1 + 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
  ((sp1 + 24#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
  ((sp1 + 32#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((sp1 + 40#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
  ((sp1 + 48#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
  ((sp1 + 56#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
  ((sp1 + 64#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
  (∃∗ vPad : BitVec 64, (sp1 + 72#64) ↦₆₄ vPad)

theorem stackFrameAt_624_split (sp1 : BitVec 64) (s : State) (k : Nat)
    (hsp : s.sp = sp1) (hk : k ≤ 624) :
    stackFrameAt sp1 624 = (stackFrame s k ∗ stackFrameAt (sp1 - BitVec.ofNat 64 k) (624 - k)) := by
  have hEq : (624 : Nat) = k + (624 - k) := by omega
  conv => lhs; rw [hEq]
  rw [stackFrameAt_split sp1 k (624 - k), ← hsp, stackFrameAt_eq_memRegion s.sp k]

theorem savedRegs_entails_stackFrame (s0 : State) :
    MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ⊢
      stackFrame s0 704 := by
  let sp1 := s0.sp - 80#64
  have hSplit : stackFrame s0 704 = (memRegion sp1 80 ∗ stackFrameAt sp1 624) := by
    unfold stackFrame
    rw [← stackFrameAt_eq_memRegion s0.sp 704, show (704 : Nat) = 80 + 624 from rfl,
        stackFrameAt_split s0.sp 80 624, stackFrameAt_eq_memRegion s0.sp 80]
  rw [hSplit]
  refine sepConj_mono ?_ (Entails.refl _)
  have h80 : memRegion sp1 80 =
      (memRegion sp1 8 ∗ memRegion (sp1 + 8#64) 8 ∗ memRegion (sp1 + 16#64) 8 ∗
       memRegion (sp1 + 24#64) 8 ∗ memRegion (sp1 + 32#64) 8 ∗ memRegion (sp1 + 40#64) 8 ∗
       memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗ memRegion (sp1 + 64#64) 8 ∗
       memRegion (sp1 + 72#64) 8) := by
    rw [memRegion_split' (b' := sp1 + 8#64) (n := 8) (k := 72) rfl rfl (by decide),
        memRegion_split' (b := sp1 + 8#64) (b' := sp1 + 16#64) (n := 8) (k := 64) rfl (by bv_lin) (by decide),
        memRegion_split' (b := sp1 + 16#64) (b' := sp1 + 24#64) (n := 8) (k := 56) rfl (by bv_lin) (by decide),
        memRegion_split' (b := sp1 + 24#64) (b' := sp1 + 32#64) (n := 8) (k := 48) rfl (by bv_lin) (by decide),
        memRegion_split' (b := sp1 + 32#64) (b' := sp1 + 40#64) (n := 8) (k := 40) rfl (by bv_lin) (by decide),
        memRegion_split' (b := sp1 + 40#64) (b' := sp1 + 48#64) (n := 8) (k := 32) rfl (by bv_lin) (by decide),
        memRegion_split' (b := sp1 + 48#64) (b' := sp1 + 56#64) (n := 8) (k := 24) rfl (by bv_lin) (by decide),
        memRegion_split' (b := sp1 + 56#64) (b' := sp1 + 64#64) (n := 8) (k := 16) rfl (by bv_lin) (by decide),
        memRegion_split' (b := sp1 + 64#64) (b' := sp1 + 72#64) (n := 8) (k := 8) rfl (by bv_lin) (by decide)]
  rw [h80]; unfold MallocImplSavedRegs
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (Entails.sepExists_elim fun _ => pointsTo64_entails_memRegion _ _)))))))))

/-! ## Metadata, Context, and Enframing Byte-Slice Operations -/

private theorem pack64_of_unpack64 (v : BitVec 64) :
    pack64 (v.extractLsb' 0 8) (v.extractLsb' 8 8) (v.extractLsb' 16 8) (v.extractLsb' 24 8)
      (v.extractLsb' 32 8) (v.extractLsb' 40 8) (v.extractLsb' 48 8) (v.extractLsb' 56 8) = v := by
  unfold pack64; bv_bits

private theorem pack32_of_unpack32 (v : BitVec 32) :
    pack32 (v.extractLsb' 0 8) (v.extractLsb' 8 8) (v.extractLsb' 16 8) (v.extractLsb' 24 8) = v := by
  unfold pack32; bv_bits

theorem metaBytes_ops (g : GroupDesc) (idx : Nat) (newAvail : BitVec 32) (sNew : SlotState) :
    let bs := g.metaBytes
    pack64 (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8) (bs.getD 19 0#8)
      (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8) (bs.getD 23 0#8) = g.mem ∧
    pack32 (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8) (bs.getD 27 0#8) = g.availMask ∧
    pack32 (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8) (bs.getD 31 0#8) = g.freedMask ∧
    bs.getD 32 0#8 = g.packedWord.extractLsb' 0 8 ∧
    pack16 (bs.getD 32 0#8) (bs.getD 33 0#8) = g.packedWord.truncate 16 ∧
    pack64 (bs.getD 32 0#8) (bs.getD 33 0#8) (bs.getD 34 0#8) (bs.getD 35 0#8)
      (bs.getD 36 0#8) (bs.getD 37 0#8) (bs.getD 38 0#8) (bs.getD 39 0#8) = g.packedWord ∧
    ByteSlice.write32 bs 24 newAvail = (mkReplaceSlotGroup g idx newAvail sNew).metaBytes := by
  dsimp only [GroupDesc.metaBytes, mkReplaceSlotGroup]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simpa [unpack64, unpack32] using pack64_of_unpack64 g.mem
  · simpa [unpack64, unpack32] using pack32_of_unpack32 g.availMask
  · simpa [unpack64, unpack32] using pack32_of_unpack32 g.freedMask
  · simp [unpack64, unpack32]
  · simp only [unpack64, unpack32, List.cons_append, List.nil_append, List.getD_cons_zero,
      List.getD_cons_succ, pack16]; bv_bits
  · simpa [unpack64, unpack32] using pack64_of_unpack64 g.packedWord

private theorem getD_append_right_eq {α : Type} (xs ys : List α) (n i : Nat) (d : α) (hn : xs.length = n) :
    (xs ++ ys).getD (n + i) d = ys.getD i d := by
  subst hn; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _)]

private theorem flatMap_unpack64_pack64 (xs : List (BitVec 64)) (suf : List (BitVec 8))
    (k : Nat) (hk : k < xs.length) :
    let s := xs.flatMap unpack64 ++ suf
    pack64 (s.getD (8 * k) 0#8) (s.getD (8 * k + 1) 0#8) (s.getD (8 * k + 2) 0#8) (s.getD (8 * k + 3) 0#8)
      (s.getD (8 * k + 4) 0#8) (s.getD (8 * k + 5) 0#8) (s.getD (8 * k + 6) 0#8) (s.getD (8 * k + 7) 0#8) =
      xs[k]'hk := by
  dsimp only
  induction xs generalizing k with
  | nil => cases hk
  | cons hd tl ih =>
    cases k with
    | zero =>
      simp only [List.flatMap_cons, List.append_assoc, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      simpa [unpack64] using pack64_of_unpack64 hd
    | succ k' =>
      have hk' : k' < tl.length := Nat.lt_of_succ_lt_succ hk
      have hStep := ih k' hk'
      simp only [List.flatMap_cons, List.append_assoc, List.getElem_cons_succ]
      have sh0 : 8 * (k' + 1) = 8 + (8 * k' + 0) := by omega
      have sh (j : Nat) : 8 * (k' + 1) + j = 8 + (8 * k' + j) := by omega
      rw [sh 1, sh 2, sh 3, sh 4, sh 5, sh 6, sh 7, sh0]
      repeat rw [getD_append_right_eq (unpack64 hd) _ 8 _ 0#8 rfl]
      simpa only [Nat.add_zero] using hStep

private theorem flatMap_unpack64_len (xs : List (BitVec 64)) :
    (xs.flatMap unpack64).length = 8 * xs.length := by
  induction xs with | nil => rfl | cons _ _ ih => simp [ih]; omega

private theorem write_middle (pre mid newMid suf : List (BitVec 8)) (n : Nat)
    (hPre : pre.length = n) (hMid : mid.length = newMid.length) :
    ByteSlice.write (pre ++ (mid ++ suf)) n newMid = pre ++ (newMid ++ suf) := by
  subst hPre
  simp [ByteSlice.write, List.take_append_of_le_length (Nat.le_refl _),
    List.drop_append, hMid, Nat.add_sub_cancel_left]

theorem ctxBytes_ops (c : CtxFields)
    (hAct : c.active.length = 48) (hUse : c.usageByClass.length = 48)
    (hUnm : c.unmapSeq.length = 32) (hBnc : c.bounces.length = 32) (_hPad : c.seqPad.length = 7) :
    let bs := c.toBytes
    pack32 (bs.getD 12 0#8) (bs.getD 13 0#8) (bs.getD 14 0#8) (bs.getD 15 0#8) = c.mmapCounter ∧
    (∀ v, ByteSlice.write32 bs 12 v = { c with mmapCounter := v }.toBytes) ∧
    (∀ sc (_hsc : sc < 48),
      pack64 (bs.getD (80 + 8 * sc) 0#8) (bs.getD (80 + 8 * sc + 1) 0#8)
        (bs.getD (80 + 8 * sc + 2) 0#8) (bs.getD (80 + 8 * sc + 3) 0#8)
        (bs.getD (80 + 8 * sc + 4) 0#8) (bs.getD (80 + 8 * sc + 5) 0#8)
        (bs.getD (80 + 8 * sc + 6) 0#8) (bs.getD (80 + 8 * sc + 7) 0#8) =
        c.active[sc]'(by omega)) ∧
    (∀ sc (_hsc : sc < 48),
      pack64 (bs.getD (464 + 8 * sc) 0#8) (bs.getD (464 + 8 * sc + 1) 0#8)
        (bs.getD (464 + 8 * sc + 2) 0#8) (bs.getD (464 + 8 * sc + 3) 0#8)
        (bs.getD (464 + 8 * sc + 4) 0#8) (bs.getD (464 + 8 * sc + 5) 0#8)
        (bs.getD (464 + 8 * sc + 6) 0#8) (bs.getD (464 + 8 * sc + 7) 0#8) =
        c.usageByClass[sc]'(by omega)) ∧
    bs.getD 912 0#8 = c.seq ∧
    (∀ v, ByteSlice.write8 bs 912 v = { c with seq := v }.toBytes) := by
  dsimp only
  let pfx := unpack64 c.secret ++ unpack32 c.initDone ++ unpack32 c.mmapCounter ++
    unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
    unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
    unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas
  have hPfxLen : pfx.length = 80 := by simp [pfx]
  have hActLen : (c.active.flatMap unpack64).length = 384 := by rw [flatMap_unpack64_len, hAct]
  have hUseLen : (c.usageByClass.flatMap unpack64).length = 384 := by rw [flatMap_unpack64_len, hUse]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · let p12 := unpack64 c.secret ++ unpack32 c.initDone
    have hEq : c.toBytes = p12 ++ (unpack32 c.mmapCounter ++
        (unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
         unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
         unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas ++ c.active.flatMap unpack64 ++
         c.usageByClass.flatMap unpack64 ++ c.unmapSeq ++ c.bounces ++ [c.seq] ++ c.seqPad ++ unpack64 c.brk)) := by
      simp [CtxFields.toBytes, p12, List.append_assoc]
    have h12 : p12.length = 12 := by simp [p12]
    rw [hEq, show (12 : Nat) = 12 + 0 from rfl, getD_append_right_eq p12 _ 12 0 0#8 h12,
        show (13 : Nat) = 12 + 1 from rfl, getD_append_right_eq p12 _ 12 1 0#8 h12,
        show (14 : Nat) = 12 + 2 from rfl, getD_append_right_eq p12 _ 12 2 0#8 h12,
        show (15 : Nat) = 12 + 3 from rfl, getD_append_right_eq p12 _ 12 3 0#8 h12]
    simpa [unpack32] using pack32_of_unpack32 c.mmapCounter
  · intro v
    let p12 := unpack64 c.secret ++ unpack32 c.initDone
    let suf16 := unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
      unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
      unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas ++ c.active.flatMap unpack64 ++
      c.usageByClass.flatMap unpack64 ++ c.unmapSeq ++ c.bounces ++ [c.seq] ++ c.seqPad ++ unpack64 c.brk
    have hEq1 : c.toBytes = p12 ++ (unpack32 c.mmapCounter ++ suf16) := by
      simp [CtxFields.toBytes, p12, suf16, List.append_assoc]
    have hEq2 : ({ c with mmapCounter := v } : CtxFields).toBytes = p12 ++ (unpack32 v ++ suf16) := by
      simp [CtxFields.toBytes, p12, suf16, List.append_assoc]
    rw [hEq1, hEq2]
    exact write_middle p12 (unpack32 c.mmapCounter) (ByteSlice.unpackLE 4 v) suf16 12 (by simp [p12]) rfl
  · intro sc hsc
    have hEq : c.toBytes = pfx ++ (c.active.flatMap unpack64 ++
        (c.usageByClass.flatMap unpack64 ++ c.unmapSeq ++ c.bounces ++ [c.seq] ++ c.seqPad ++ unpack64 c.brk)) := by
      simp [CtxFields.toBytes, pfx, List.append_assoc]
    rw [hEq]
    have sh0 : 80 + 8 * sc = 80 + (8 * sc + 0) := by omega
    have sh (j : Nat) : 80 + 8 * sc + j = 80 + (8 * sc + j) := by omega
    rw [sh 1, sh 2, sh 3, sh 4, sh 5, sh 6, sh 7, sh0]
    repeat rw [getD_append_right_eq pfx _ 80 _ 0#8 hPfxLen]
    simpa only [Nat.add_zero] using flatMap_unpack64_pack64 c.active _ sc (by omega)
  · intro sc hsc
    let pfx2 := pfx ++ c.active.flatMap unpack64
    have hPfx2Len : pfx2.length = 464 := by simp [pfx2, hPfxLen, hActLen]
    have hEq : c.toBytes = pfx2 ++ (c.usageByClass.flatMap unpack64 ++
        (c.unmapSeq ++ c.bounces ++ [c.seq] ++ c.seqPad ++ unpack64 c.brk)) := by
      simp [CtxFields.toBytes, pfx2, pfx, List.append_assoc]
    rw [hEq]
    have sh0 : 464 + 8 * sc = 464 + (8 * sc + 0) := by omega
    have sh (j : Nat) : 464 + 8 * sc + j = 464 + (8 * sc + j) := by omega
    rw [sh 1, sh 2, sh 3, sh 4, sh 5, sh 6, sh 7, sh0]
    repeat rw [getD_append_right_eq pfx2 _ 464 _ 0#8 hPfx2Len]
    simpa only [Nat.add_zero] using flatMap_unpack64_pack64 c.usageByClass _ sc (by omega)
  · let pfx3 := pfx ++ c.active.flatMap unpack64 ++ c.usageByClass.flatMap unpack64 ++ c.unmapSeq ++ c.bounces
    have hPfx3Len : pfx3.length = 912 := by simp [pfx3, hPfxLen, hActLen, hUseLen, hUnm, hBnc]
    have hEq : c.toBytes = pfx3 ++ ([c.seq] ++ c.seqPad ++ unpack64 c.brk) := by
      simp [CtxFields.toBytes, pfx3, pfx, List.append_assoc]
    rw [hEq, show (912 : Nat) = 912 + 0 from rfl, getD_append_right_eq pfx3 _ 912 0 0#8 hPfx3Len]
    rfl
  · intro v
    let pfx3 := pfx ++ c.active.flatMap unpack64 ++ c.usageByClass.flatMap unpack64 ++ c.unmapSeq ++ c.bounces
    have hPfx3Len : pfx3.length = 912 := by simp [pfx3, hPfxLen, hActLen, hUseLen, hUnm, hBnc]
    have hEq1 : c.toBytes = pfx3 ++ ([c.seq] ++ (c.seqPad ++ unpack64 c.brk)) := by
      simp [CtxFields.toBytes, pfx3, pfx, List.append_assoc]
    have hEq2 : ({ c with seq := v } : CtxFields).toBytes = pfx3 ++ ([v] ++ (c.seqPad ++ unpack64 c.brk)) := by
      simp [CtxFields.toBytes, pfx3, pfx, List.append_assoc]
    rw [hEq1, hEq2]
    exact write_middle pfx3 [c.seq] [v] (c.seqPad ++ unpack64 c.brk) 912 hPfx3Len rfl

end VerifiedLibraries.Mallocng.Proofs

