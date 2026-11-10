/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.LiveUserBandHelpers
public import VerifiedLibraries.Mallocng.Proofs.GetMetaHelpers

/-!
# Alignment and Heap-Invariant Helpers for `aligned_alloc` and `posix_memalign`

Bitvector alignment and overflow equivalences, power-of-two pointer-snapping bounds, and
`MallocngWF` / `SlotWf` / `ByteMap` preservation lemmas for snapping a `.liveUser` allocation up to
`new_p = (p + align - 1) & -align` within a slot.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

/-! ## Alignment and Overflow Bitvector Lemmas -/

theorem bics_neg_eq_zero_iff_alignOk (align : BitVec 64) :
    (align &&& ~~~(0#64 - align) == 0#64) = alignedAllocAlignOk align := by
  unfold alignedAllocAlignOk
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  bv_robdd

theorem neg_and_self_of_alignOk {align : BitVec 64} (h : alignedAllocAlignOk align = true) :
    (0#64 - align) &&& align = align := by
  unfold alignedAllocAlignOk at h
  rw [beq_iff_eq] at h
  revert h
  bv_robdd

theorem alignOk_iff_zero_or_isPow2 (align : BitVec 64) :
    alignedAllocAlignOk align = true ↔ align = 0#64 ∨ IsPow2Align align := by
  unfold alignedAllocAlignOk IsPow2Align
  rw [beq_iff_eq]
  constructor
  · intro h
    by_cases hz : align = 0#64
    · exact Or.inl hz
    · refine Or.inr ⟨hz, ?_⟩
      clear hz
      revert h
      bv_robdd
  · rintro (rfl | ⟨_, hand⟩)
    · rfl
    · revert hand
      bv_robdd

theorem alignOk_eq_isPow2_of_ge8 {align : BitVec 64} (h8 : 8 ≤ align.toNat) :
    alignedAllocAlignOk align = isPow2Align align := by
  have hne : align ≠ 0#64 := by
    intro hz; rw [hz] at h8; simp at h8
  apply Bool.eq_iff_iff.mpr
  rw [alignOk_iff_zero_or_isPow2, isPow2Align, decide_eq_true_eq]
  exact ⟨fun h => h.resolve_left hne, Or.inr⟩

theorem alignedAlloc_ovf_iff {align len : BitVec 64}
    (hMax : align.toNat ≤ MaxAlignedAllocAlign) :
    (BitVec.ult 0x7ffffffff#64 align = false) ∧
    (BitVec.ule len (~~~align) = false ↔ 2 ^ 64 ≤ len.toNat + align.toNat) := by
  have hAlignLt : align.toNat < 2 ^ 64 := align.isLt
  have hLenLt : len.toNat < 2 ^ 64 := len.isLt
  refine ⟨?_, ?_⟩
  · rw [BitVec.ult, decide_eq_false_iff_not]
    unfold MaxAlignedAllocAlign at hMax
    change ¬ (0x7ffffffff < align.toNat)
    omega
  · rw [BitVec.ule, decide_eq_false_iff_not, BitVec.toNat_not]
    omega

theorem alignedAlloc_effReg_toNat {align len : BitVec 64}
    (hNoOvf : len.toNat + align.toNat < 2 ^ 64) :
    let a16 : BitVec 64 :=
      if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64
    a16.toNat = max align.toNat 16 ∧
    ((len - 16#64) + a16).toNat = mallocngAlignedEffSize align.toNat len.toNat := by
  have hCs : ConditionHolds .CS (subsPState64 align 16#64) = decide (16 ≤ align.toNat) := by
    rw [conditionHolds_cs_subsPState64, BitVec.ule]
    rfl
  dsimp only []
  rw [hCs]
  unfold mallocngAlignedEffSize
  have hLenLt : len.toNat < 2 ^ 64 := len.isLt
  have hCancel : (len - 16#64) + 16#64 = len := by bv_robdd
  by_cases h16 : 16 ≤ align.toNat
  · simp only [decide_eq_true h16, ↓reduceIte]
    refine ⟨by omega, ?_⟩
    by_cases hEq16 : align.toNat = 16
    · have ha : align = 16#64 := BitVec.eq_of_toNat_eq hEq16
      subst ha
      rw [hCancel]
      simp
    · have hGt16 : ¬ align.toNat ≤ 16 := by omega
      simp only [hGt16, ↓reduceIte]
      have hSub16 : (align - 16#64).toNat = align.toNat - 16 := by
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (show (16#64).toNat ≤ align.toNat from h16))]
        rfl
      have hAssoc : (len - 16#64) + align = len + (align - 16#64) := by bv_robdd
      rw [hAssoc, BitVec.toNat_add, hSub16, Nat.mod_eq_of_lt (by omega)]
      omega
  · have hLe16 : align.toNat ≤ 16 := by omega
    simp only [decide_eq_false h16, Bool.false_eq_true, ↓reduceIte, hLe16]
    rw [hCancel]
    exact ⟨by simp only [BitVec.toNat_ofNat]; omega, rfl⟩

/-! ## Power-of-Two Characterization and Pointer Snapping -/

private theorem isPow2_bool_eq_any_shift (a : BitVec 64) :
    ((a != 0#64) && (a &&& (a - 1#64) == 0#64)) =
      (List.range 64).any (fun k => a == (1#64 <<< k)) := by
  simp only [List.range_succ, List.range_zero, List.any_append, List.any_cons, List.any_nil,
    Bool.or_false, Bool.false_or]
  bv_robdd

theorem exists_shift_of_isPow2Align {a : BitVec 64} (h : IsPow2Align a) :
    ∃ k < 64, a = 1#64 <<< k ∧ a.toNat = 2 ^ k := by
  have hb : ((a != 0#64) && (a &&& (a - 1#64) == 0#64)) = true := by
    rw [Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
    exact h
  rw [isPow2_bool_eq_any_shift, List.any_eq_true] at hb
  obtain ⟨k, hkMem, hkEq⟩ := hb
  have hkLt : k < 64 := List.mem_range.mp hkMem
  rw [beq_iff_eq] at hkEq
  refine ⟨k, hkLt, hkEq, ?_⟩
  rw [hkEq, BitVec.toNat_shiftLeft]
  have h1 : (1#64).toNat <<< k = 2 ^ k := by
    simp [Nat.shiftLeft_eq]
  have hLt : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hkLt
  rw [h1, Nat.mod_eq_of_lt hLt]

private theorem snap_nat_props {p a16 : BitVec 64} {k : Nat}
    (hkLo : 4 ≤ k) (hkHi : k < 64) (haNat : a16.toNat = 2 ^ k) (hp16Dvd : 16 ∣ p.toNat) :
    let delta := (0#64 - p) &&& (a16 - 1#64)
    16 ∣ delta.toNat ∧
    delta.toNat ≤ 2 ^ k - 16 ∧
    2 ^ k ∣ (p.toNat + delta.toNat) := by
  dsimp only []
  have hkPos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hSubNat : (a16 - 1#64).toNat = 2 ^ k - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (show (1#64).toNat ≤ a16.toNat by
      change 1 ≤ a16.toNat; omega)), haNat]
    rfl
  let delta := (0#64 - p) &&& (a16 - 1#64)
  have hDeltaMod : delta.toNat = (0#64 - p).toNat % (2 ^ k) := by
    dsimp only [delta]
    rw [BitVec.toNat_and, hSubNat, Nat.and_two_pow_sub_one_eq_mod]
  have hDvd2_64 : 2 ^ k ∣ 2 ^ 64 :=
    ⟨2 ^ (64 - k), by rw [← Nat.pow_add, show k + (64 - k) = 64 by omega]⟩
  have h16DvdPow : 16 ∣ 2 ^ k :=
    ⟨2 ^ (k - 4), by rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_add, show 4 + (k - 4) = k by omega]⟩
  have hpLt : p.toNat < 2 ^ 64 := p.isLt
  have hNegNat : (0#64 - p).toNat = (2 ^ 64 - p.toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_sub]
    simp
  have hDeltaEq : delta.toNat = (2 ^ 64 - p.toNat) % 2 ^ k := by
    rw [hDeltaMod, hNegNat, Nat.mod_mod_of_dvd _ hDvd2_64]
  have hDeltaLt : delta.toNat < 2 ^ k := by
    rw [hDeltaEq]
    exact Nat.mod_lt _ (by omega)
  have hSumDvd : 2 ^ k ∣ (p.toNat + delta.toNat) := by
    rw [hDeltaEq]
    have hModSum : (p.toNat + (2 ^ 64 - p.toNat) % 2 ^ k) % 2 ^ k = (2 ^ 64) % 2 ^ k := by
      rw [Nat.add_comm, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
        show 2 ^ 64 - p.toNat + p.toNat = 2 ^ 64 by omega]
    exact Nat.dvd_of_mod_eq_zero (by rw [hModSum, Nat.mod_eq_zero_of_dvd hDvd2_64])
  have hDelta16 : 16 ∣ delta.toNat := by
    have hSum16 : 16 ∣ (p.toNat + delta.toNat) := Nat.dvd_trans h16DvdPow hSumDvd
    exact (Nat.dvd_add_right hp16Dvd).mp hSum16
  have ⟨q, hq⟩ := h16DvdPow
  have ⟨r, hr⟩ := hDelta16
  have hDeltaLe : delta.toNat ≤ 2 ^ k - 16 := by
    dsimp only [delta] at hr hDeltaLt ⊢
    omega
  exact ⟨hDelta16, hDeltaLe, hSumDvd⟩

theorem alignedAlloc_snap_props {p align len : BitVec 64}
    (hAlignOk : alignedAllocAlignOk align = true)
    (hAlignMax : align.toNat ≤ MaxAlignedAllocAlign)
    (hNoOvf : len.toNat + align.toNat < 2 ^ 64)
    (hBlkP : MallocngBlockWf p (mallocngAlignedEffSize align.toNat len.toNat)) :
    let a16 : BitVec 64 :=
      if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64
    let delta : BitVec 64 := (0#64 - p) &&& (a16 - 1#64)
    let new_p : BitVec 64 := p + delta
    let eff : Nat := mallocngAlignedEffSize align.toNat len.toNat
    a16.toNat = max align.toNat 16 ∧
    16 ∣ delta.toNat ∧
    delta.toNat ≤ max align.toNat 16 - 16 ∧
    new_p.toNat = p.toNat + delta.toNat ∧
    new_p.toNat + len.toNat ≤ p.toNat + eff ∧
    max align.toNat 16 ∣ new_p.toNat ∧
    MallocngBlockWf new_p len.toNat ∧
    (align.toNat ≤ 16 → delta = 0#64 ∧ new_p = p) := by
  dsimp only []
  obtain ⟨hpNe0, hp16Dvd, hpFit48, hEffMax⟩ := hBlkP
  have ⟨ha16Nat, _⟩ := alignedAlloc_effReg_toNat (len := len) hNoOvf
  let a16 : BitVec 64 :=
    if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64
  change a16.toNat = max align.toNat 16 at ha16Nat
  have ha16Pow : IsPow2Align a16 := by
    have hCs : ConditionHolds .CS (subsPState64 align 16#64) = decide (16 ≤ align.toNat) := by
      rw [conditionHolds_cs_subsPState64, BitVec.ule]; rfl
    dsimp only [a16]; rw [hCs]
    by_cases h16 : 16 ≤ align.toNat
    · simp only [decide_eq_true h16, ↓reduceIte]
      rcases (alignOk_iff_zero_or_isPow2 align).mp hAlignOk with rfl | hPow
      · simp at h16
      · exact hPow
    · simp only [decide_eq_false h16, Bool.false_eq_true, ↓reduceIte]
      decide
  obtain ⟨k, hk64, _, hkNat⟩ := exists_shift_of_isPow2Align ha16Pow
  have hkGe4 : 4 ≤ k := by
    refine Classical.byContradiction fun hlt => ?_
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  obtain ⟨hDelta16, hDeltaLePow, hPowDvdSum⟩ := snap_nat_props hkGe4 hk64 hkNat hp16Dvd
  let delta : BitVec 64 := (0#64 - p) &&& (a16 - 1#64)
  let new_p : BitVec 64 := p + delta
  have hDeltaLe : delta.toNat ≤ max align.toNat 16 - 16 := by
    change delta.toNat ≤ 2 ^ k - 16 at hDeltaLePow
    omega
  have hEffEq : mallocngAlignedEffSize align.toNat len.toNat =
      len.toNat + (max align.toNat 16 - 16) := by
    unfold mallocngAlignedEffSize
    split <;> omega
  have hMaxVal : MaxAlignedAllocAlign = 2 ^ 31 := rfl
  have hNewNat : new_p.toNat = p.toNat + delta.toNat := by
    dsimp only [new_p]
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hNewFitEff : new_p.toNat + len.toNat ≤
      p.toNat + mallocngAlignedEffSize align.toNat len.toNat := by
    omega
  have ha16DvdNew : max align.toNat 16 ∣ new_p.toNat := by
    rw [← ha16Nat, hkNat, hNewNat]
    exact hPowDvdSum
  have h16DvdNew : 16 ∣ new_p.toNat := by
    rw [hNewNat]
    exact Nat.dvd_add hp16Dvd hDelta16
  have hNewNe0 : new_p ≠ 0#64 := by
    intro hz
    have h0 : new_p.toNat = 0 := by rw [hz]; rfl
    have hpPos : 0 < p.toNat := Nat.pos_of_ne_zero (fun hp0 => hpNe0 (BitVec.eq_of_toNat_eq hp0))
    omega
  have hBlkNew : MallocngBlockWf new_p len.toNat :=
    ⟨hNewNe0, h16DvdNew, by omega, by omega⟩
  refine ⟨ha16Nat, hDelta16, hDeltaLe, hNewNat, hNewFitEff, ha16DvdNew, hBlkNew, ?_⟩
  intro hLe16
  have hDelta0Nat : delta.toNat = 0 := by omega
  have hDelta0 : delta = 0#64 := BitVec.eq_of_toNat_eq hDelta0Nat
  have hNewEqP : new_p = p := by
    dsimp only [new_p]
    rw [hDelta0, BitVec.add_zero]
  exact ⟨hDelta0, hNewEqP⟩

/-! ## `SlotWf` Offset Bound After Snapping -/

theorem snap_le_aligned_bound {p a16 : BitVec 64} {k B : Nat}
    (hkGe4 : 4 ≤ k) (hkLt64 : k < 64) (ha16 : a16.toNat = 2 ^ k)
    (hpLeB : p.toNat ≤ B) (hBDvd : 2 ^ k ∣ B) :
    p.toNat + ((0#64 - p) &&& (a16 - 1#64)).toNat ≤ B := by
  have hkPos : 0 < 2 ^ k := Nat.pow_pos (by omega)
  have h2kLt64 : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hkLt64
  have hMaskNat : (a16 - 1#64).toNat = 2 ^ k - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (show (1#64).toNat ≤ a16.toNat by
      change 1 ≤ a16.toNat; omega)), ha16]
    rfl
  have hDeltaMod : ((0#64 - p) &&& (a16 - 1#64)).toNat = (0#64 - p).toNat % 2 ^ k := by
    rw [BitVec.toNat_and, hMaskNat, Nat.and_two_pow_sub_one_eq_mod]
  have hNegMod : (0#64 - p).toNat % 2 ^ k = (2 ^ k - p.toNat % 2 ^ k) % 2 ^ k := by
    by_cases hp0 : p.toNat = 0
    · have hpz : p = 0#64 := BitVec.eq_of_toNat_eq hp0
      subst hpz; simp
    · have hNegNat : (0#64 - p).toNat = 2 ^ 64 - p.toNat := by
        have hlt := p.isLt
        rw [BitVec.toNat_sub]
        simp only [BitVec.toNat_ofNat, Nat.zero_mod]
        omega
      rw [hNegNat]
      have h64Split : 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k := by
        rw [← Nat.pow_add, show 64 - k + k = 64 by omega]
      have hpSplit := (Nat.div_add_mod p.toNat (2 ^ k)).symm
      have hrLt : p.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt _ hkPos
      have hqLt : p.toNat / 2 ^ k < 2 ^ (64 - k) := by
        have hlt := p.isLt
        rw [h64Split] at hlt
        refine Classical.byContradiction fun hge => ?_
        have h1 : 2 ^ (64 - k) ≤ p.toNat / 2 ^ k := by omega
        have h2 := Nat.mul_le_mul_right (2 ^ k) h1
        have h3 : 2 ^ k * (p.toNat / 2 ^ k) = (p.toNat / 2 ^ k) * 2 ^ k := Nat.mul_comm _ _
        omega
      have hDiffEq :
          2 ^ 64 - p.toNat =
            (2 ^ k - p.toNat % 2 ^ k) + (2 ^ (64 - k) - 1 - p.toNat / 2 ^ k) * (2 ^ k) := by
        have hMulSub :
            (2 ^ (64 - k) - 1 - p.toNat / 2 ^ k) * (2 ^ k) + (p.toNat / 2 ^ k) * (2 ^ k) + 2 ^ k =
              2 ^ (64 - k) * (2 ^ k) := by
          have : (2 ^ (64 - k) - 1 - p.toNat / 2 ^ k) + p.toNat / 2 ^ k + 1 = 2 ^ (64 - k) := by omega
          calc
            (2 ^ (64 - k) - 1 - p.toNat / 2 ^ k) * (2 ^ k) + (p.toNat / 2 ^ k) * (2 ^ k) + 2 ^ k
                = ((2 ^ (64 - k) - 1 - p.toNat / 2 ^ k) + p.toNat / 2 ^ k + 1) * (2 ^ k) := by
                    simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
            _ = 2 ^ (64 - k) * (2 ^ k) := by rw [this]
        have hComm : 2 ^ k * (p.toNat / 2 ^ k) = (p.toNat / 2 ^ k) * 2 ^ k := Nat.mul_comm _ _
        omega
      rw [hDiffEq, Nat.add_mul_mod_self_right]
  rw [hDeltaMod, hNegMod]
  obtain ⟨m, rfl⟩ := hBDvd
  have hpDivMod := Nat.div_add_mod p.toNat (2 ^ k)
  have hrLt : p.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt _ hkPos
  by_cases hr0 : p.toNat % 2 ^ k = 0
  · rw [hr0, Nat.sub_zero, Nat.mod_self]
    omega
  · rw [Nat.mod_eq_of_lt (by omega : 2 ^ k - p.toNat % 2 ^ k < 2 ^ k)]
    have hqLt : p.toNat / 2 ^ k < m := by
      refine Classical.byContradiction fun hge => ?_
      have h1 : m ≤ p.toNat / 2 ^ k := by omega
      have h2 := Nat.mul_le_mul_left (2 ^ k) h1
      omega
    have hqLe : p.toNat / 2 ^ k + 1 ≤ m := by omega
    have hMulLe := Nat.mul_le_mul_left (2 ^ k) hqLe
    rw [Nat.mul_add, Nat.mul_one] at hMulLe
    omega

private def checkSizeClassGe292 : Bool :=
  (List.range 48).all fun sc => !(decide (28 ≤ sc)) || decide (292 ≤ sizeClass sc)

private theorem checkSizeClassGe292_true : checkSizeClassGe292 = true := by decide

private theorem sizeClass_ge_292_of_ge_28 {sc : Nat} (hGe : 28 ≤ sc) (hLt : sc < 48) :
    292 ≤ sizeClass sc := by
  have hAll := (List.all_eq_true.mp checkSizeClassGe292_true) sc (List.mem_range.mpr hLt)
  simpa [hGe] using hAll

private theorem pageAlignUp_le_add_4095 (n : Nat) : pageAlignUp n ≤ n + 4095 := by
  unfold pageAlignUp PAGE_SIZE
  omega

theorem alignedAlloc_totalOff_lt_sizeClass
    {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p align len : BitVec 64}
    (hSlot : g.slots[idx]'hIdx = .liveUser p
      (mallocngAlignedEffSize align.toNat len.toNat)
      (max (mallocngAlignedEffSize align.toNat len.toNat) MallocngMinBlockCost))
    (hOff255 : p.toNat - (g.slotStart idx).toNat ≤ 255 * 16)
    (hSc24_26 : 24 ≤ g.sc ∧ g.sc ≤ 26 →
      nominalSlotCap 23 < mallocngAlignedEffSize align.toNat len.toNat)
    (hAlignOk : alignedAllocAlignOk align = true)
    (hAlignMax : align.toNat ≤ MaxAlignedAllocAlign)
    (hNoOvf : len.toNat + align.toNat < 2 ^ 64)
    (hSc48 : g.sc < 48) :
    let a16 : BitVec 64 :=
      if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64
    let delta : BitVec 64 := (0#64 - p) &&& (a16 - 1#64)
    let new_p : BitVec 64 := p + delta
    (new_p.toNat - g.storage.toNat) / 16 < (idx + 1) * sizeClass g.sc := by
  intro a16 delta new_p
  let eff := mallocngAlignedEffSize align.toNat len.toNat
  have hF := liveUserBlockFacts_of hwf hg hIdx hSlot
  have hBlkP : MallocngBlockWf p eff :=
    ⟨hF.p_ne_zero, Nat.dvd_of_mod_eq_zero hF.p_mod_16, hF.p_add_n_48, hF.n_le_max⟩
  obtain ⟨ha16Nat, _, _, hNewNat, hNewFitEff, _, _, hLe16Eq⟩ :=
    alignedAlloc_snap_props hAlignOk hAlignMax hNoOvf hBlkP
  change a16.toNat = max align.toNat 16 at ha16Nat
  change new_p.toNat = p.toNat + delta.toNat at hNewNat
  change new_p.toNat + len.toNat ≤ p.toNat + eff at hNewFitEff
  by_cases hLe16 : align.toNat ≤ 16
  · obtain ⟨_, hNewEqP⟩ := hLe16Eq hLe16
    change new_p = p at hNewEqP
    rw [hNewEqP]
    exact (hF.sc_lt_48_off hSc48).2
  · have hGt16 : 16 < align.toNat := by omega
    have hPowAlign : IsPow2Align align := by
      rcases (alignOk_iff_zero_or_isPow2 align).mp hAlignOk with rfl | hPow
      · simp at hGt16
      · exact hPow
    obtain ⟨k, hk64, _, hkNat⟩ := exists_shift_of_isPow2Align hPowAlign
    have hkGe5 : 5 ≤ k := by
      refine Classical.byContradiction fun hlt => ?_
      have : 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have ha16Pow : a16.toNat = 2 ^ k := by omega
    have hEffEq : eff = len.toNat + (2 ^ k - 16) := by
      dsimp only [eff, mallocngAlignedEffSize]
      split <;> omega
    have ⟨hScPos, _, _, _⟩ := sizeClass_bounds hSc48
    have hSlotStrideEq : slotStride g.sc = 16 * sizeClass g.sc := rfl
    by_cases hStrLe : g.stride ≤ slotStride g.sc
    ·
      have hEndEq := hF.stride_bounds.2.2.2.2.1
      have hStorEq := hF.stride_bounds.2.2.1
      have hStartLe := hF.start_le_p
      have hStartEq := hF.stride_bounds.2.2.2.1
      have hPEnd : p.toNat + eff ≤ (g.slotEnd idx).toNat := hF.p_add_n_le_end
      have hMulStr : (idx + 1) * g.stride ≤ (idx + 1) * (16 * sizeClass g.sc) :=
        Nat.mul_le_mul_left (idx + 1) (hSlotStrideEq ▸ hStrLe)
      have hMulComm : (idx + 1) * (16 * sizeClass g.sc) = 16 * ((idx + 1) * sizeClass g.sc) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (idx + 1) 16, Nat.mul_assoc]
      have hPosProd : 1 ≤ (idx + 1) * sizeClass g.sc :=
        Nat.mul_le_mul (show 1 ≤ idx + 1 by omega) hScPos
      omega
    ·
      have hgWf := hwf.groups_wf g hg
      have hMpPos : 0 < g.maplen := by
        refine Classical.byContradiction fun h0 => ?_
        have hMp0 : g.maplen = 0 := by omega
        have ⟨_, hLast1⟩ := hF.maplen_zero_sc hMp0
        have hStrEq : g.stride = slotStride g.sc := by
          unfold GroupDesc.stride
          simp [hMp0]
        omega
      have hLast0 : g.lastIdx = 0 := by
        refine Classical.byContradiction fun hne => ?_
        have hStrEq : g.stride = slotStride g.sc := by unfold GroupDesc.stride; simp [hne]
        omega
      have hIdx0 : idx = 0 := by have := hF.idx_le_last; omega
      subst hIdx0
      have hMpWf := hgWf.2.2.2.2.2.2.2.2.2.2.2.1 hMpPos
      have hMem4096 : g.mem.toNat % 4096 = 0 := hMpWf.1
      have ⟨_, hCoarseOr⟩ := hMpWf.2.2.2 hSc48
      rcases hCoarseOr hLast0 with hContra | ⟨hGe24, hMapAlign⟩
      · exact False.elim (hStrLe hContra)
      · have hStrVal : g.stride = g.maplen * 4096 - 16 := by unfold GroupDesc.stride; simp [hLast0, hMpPos]
        have hStorEq := hF.stride_bounds.2.2.1
        have hStartEq : (g.slotStart 0).toNat = g.mem.toNat + 16 := by rw [hF.stride_bounds.2.2.2.1]; simp
        have hEndEq : (g.slotEnd 0).toNat = g.mem.toNat + g.maplen * 4096 - 4 := by
          rw [hF.stride_bounds.2.2.2.2.1, hStrVal]; omega
        have hPLo : g.mem.toNat + 16 ≤ p.toNat := by have := hF.start_le_p; omega
        have hPEnd : p.toNat + eff ≤ g.mem.toNat + g.maplen * 4096 - 4 := by
          have := hF.p_add_n_le_end; change p.toNat + eff ≤ (g.slotEnd 0).toNat at this; omega
        by_cases hLe26 : g.sc ≤ 26
        · have ⟨hPage4096, hSc146⟩ : pageAlignUp (slotStride g.sc + 16) = 4096 ∧ 146 ≤ sizeClass g.sc := by
            rcases (by omega : g.sc = 24 ∨ g.sc = 25 ∨ g.sc = 26) with hsc | hsc | hsc <;>
              exact ⟨by rw [hsc]; decide, by rw [hsc]; decide⟩
          have hNom23 : nominalSlotCap 23 < eff := hSc24_26 ⟨hGe24, hLe26⟩
          have hCap23 : nominalSlotCap 23 = 2028 := by decide
          have hMap4096 : g.maplen * 4096 = 4096 := hMapAlign.trans hPage4096
          have hpMod16 := hF.p_mod_16
          have hkLe11 : k ≤ 11 := Classical.byContradiction fun hgt => by
            have : 2 ^ 12 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega); omega
          have hDvd2048 : 2 ^ k ∣ 2048 := ⟨2 ^ (11 - k), by rw [← Nat.pow_add, show k + (11 - k) = 11 by omega]⟩
          have hDvdMem : 2 ^ k ∣ g.mem.toNat :=
            Nat.dvd_trans (Nat.dvd_trans hDvd2048 ⟨2, rfl⟩) (Nat.dvd_of_mod_eq_zero hMem4096)
          have hNewLe : new_p.toNat ≤ g.mem.toNat + 2048 := by
            rw [hNewNat]; exact snap_le_aligned_bound (by omega) hk64 ha16Pow (by omega) (Nat.dvd_add hDvdMem hDvd2048)
          omega
        · by_cases hEq27 : g.sc = 27
          · have hPage4096 : pageAlignUp (slotStride 27 + 16) = 4096 := by decide
            have hSlot27 : slotStride 27 = 4080 := by decide
            rw [hEq27, hPage4096] at hMapAlign; rw [hEq27, hSlot27] at hStrLe; omega
          · have hSc292 : 292 ≤ sizeClass g.sc := sizeClass_ge_292_of_ge_28 (by omega) hSc48
            by_cases hkLe12 : k ≤ 12
            · have hDvd4096 : 2 ^ k ∣ 4096 := ⟨2 ^ (12 - k), by rw [← Nat.pow_add, show k + (12 - k) = 12 by omega]⟩
              have hDvdMem : 2 ^ k ∣ g.mem.toNat := Nat.dvd_trans hDvd4096 (Nat.dvd_of_mod_eq_zero hMem4096)
              have hNewLe : new_p.toNat ≤ g.mem.toNat + 4096 := by
                rw [hNewNat]; exact snap_le_aligned_bound (by omega) hk64 ha16Pow (by omega) (Nat.dvd_add hDvdMem hDvd4096)
              omega
            · let A := 2 ^ (k - 12)
              have h4096A : 4096 * A = 2 ^ k := by
                change 2 ^ 12 * 2 ^ (k - 12) = 2 ^ k; rw [← Nat.pow_add, show 12 + (k - 12) = k by omega]
              let q := g.mem.toNat / 4096
              have hMemEqQ : g.mem.toNat = 4096 * q := by have := Nat.div_add_mod g.mem.toNat 4096; dsimp only [q]; omega
              let m := (q + A) / A; let B := 2 ^ k * m
              have hAPos : 0 < A := Nat.pow_pos (by omega)
              have hDivMod : A * m + (q + A) % A = q + A := Nat.div_add_mod (q + A) A
              have hModLt : (q + A) % A < A := Nat.mod_lt (q + A) hAPos
              have hAmLo : q + 1 ≤ A * m := by omega
              have hAmHi : A * m ≤ q + A := by omega
              have hBEq : B = 4096 * (A * m) := by dsimp only [B]; rw [← h4096A, Nat.mul_assoc]
              have hBLo : g.mem.toNat + 4096 ≤ B := by have := Nat.mul_le_mul_left 4096 hAmLo; omega
              have hBHi : B ≤ g.mem.toNat + 2 ^ k := by
                have hMul := Nat.mul_le_mul_left 4096 hAmHi; rw [Nat.mul_add] at hMul; omega
              have hNewLeB : new_p.toNat ≤ B := by
                dsimp only [new_p] at hNewNat ⊢; rw [hNewNat]
                exact snap_le_aligned_bound (by omega) hk64 ha16Pow (by omega) ⟨m, rfl⟩
              have hALeMpSub1 : A ≤ g.maplen - 1 := by omega
              have h2kLeSubPage : 2 ^ k ≤ g.maplen * 4096 - 4096 := by
                have := Nat.mul_le_mul_left 4096 hALeMpSub1; omega
              have hPageHi := pageAlignUp_le_add_4095 (slotStride g.sc + 16)
              dsimp only [new_p] at hNewLeB ⊢; omega

/-! ## In-Place Slot Update Combinators -/

namespace AlignedH1
def replaceGroupByMeta (gs : List GroupDesc) (m : BitVec 64) (g1 : GroupDesc) : List GroupDesc :=
  gs.map fun h => if h.metaPtr == m then g1 else h

theorem split_groups_at_mem {gs : List GroupDesc} (hNd : (gs.map (·.metaPtr)).Nodup)
    {g : GroupDesc} (hg : g ∈ gs) :
    ∃ pre post : List GroupDesc, gs = pre ++ g :: post ∧
      (∀ h ∈ pre, h.metaPtr ≠ g.metaPtr) ∧ (∀ h ∈ post, h.metaPtr ≠ g.metaPtr) ∧
      (∀ g1 : GroupDesc, replaceGroupByMeta gs g.metaPtr g1 = pre ++ g1 :: post) := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  rw [List.map_append, List.map_cons, List.nodup_append] at hNd
  obtain ⟨_, hNdCons, hDisj⟩ := hNd; obtain ⟨hNotPost, _⟩ := List.nodup_cons.mp hNdCons
  have hPreNe : ∀ h ∈ pre, h.metaPtr ≠ g.metaPtr := fun h hh hEq =>
    hDisj h.metaPtr (List.mem_map_of_mem hh) g.metaPtr (List.mem_cons_self ..) hEq
  have hPostNe : ∀ h ∈ post, h.metaPtr ≠ g.metaPtr := fun h hh hEq => hNotPost (hEq ▸ List.mem_map_of_mem hh)
  refine ⟨pre, post, rfl, hPreNe, hPostNe, fun g1 => ?_⟩
  unfold replaceGroupByMeta; rw [List.map_append, List.map_cons]
  have h1 : (pre.map fun h => if h.metaPtr == g.metaPtr then g1 else h) = pre := by
    conv => rhs; rw [← List.map_id pre]
    exact List.map_congr_left fun h hh => by simp [hPreNe h hh]
  have h2 : (post.map fun h => if h.metaPtr == g.metaPtr then g1 else h) = post := by
    conv => rhs; rw [← List.map_id post]
    exact List.map_congr_left fun h hh => by simp [hPostNe h hh]
  rw [h1, h2]; simp

theorem replaceGroupByMeta_props {gs : List GroupDesc} (hNd : (gs.map (·.metaPtr)).Nodup)
    {g g1 : GroupDesc} (hg : g ∈ gs)
    (hMeta : g1.metaPtr = g.metaPtr) (hMem : g1.mem = g.mem)
    (hMaplen : g1.maplen = g.maplen) (hSc : g1.sc = g.sc) (hLast : g1.lastIdx = g.lastIdx) :
    let gs' := replaceGroupByMeta gs g.metaPtr g1
    gs'.map (·.metaPtr) = gs.map (·.metaPtr) ∧ gs'.map (·.mem) = gs.map (·.mem) ∧
    (gs'.filter fun h => decide (0 < h.maplen)).map (fun h => (h.mem, h.maplen * 4096)) =
      (gs.filter fun h => decide (0 < h.maplen)).map (fun h => (h.mem, h.maplen * 4096)) ∧
    (∀ sc : Nat, ((gs'.filter (·.sc == sc)).map GroupDesc.cnt).sum =
      ((gs.filter (·.sc == sc)).map GroupDesc.cnt).sum) ∧
    g1 ∈ gs' ∧ (∀ h ∈ gs', h = g1 ∨ (h ∈ gs ∧ h.metaPtr ≠ g.metaPtr)) ∧
    (∀ h ∈ gs, h.metaPtr ≠ g.metaPtr → h ∈ gs') ∧
    (∀ m : BitVec 64, gs'.find? (·.metaPtr == m) =
      if m == g.metaPtr then some g1 else gs.find? (·.metaPtr == m)) := by
  obtain ⟨pre, post, hGsEq, hPreNe, hPostNe, hRep⟩ := split_groups_at_mem hNd hg
  dsimp only []; rw [hRep g1, hGsEq]
  have hCnt : g1.cnt = g.cnt := by simp [GroupDesc.cnt, hLast]
  refine ⟨by simp [List.map_append, hMeta], by simp [List.map_append, hMem],
    by simp only [List.filter_append, List.filter_cons, List.map_append, hMaplen]; split <;> simp [hMem, hMaplen],
    fun sc => by simp only [List.filter_append, List.filter_cons, List.map_append, List.sum_append, hSc]; split <;> simp [hCnt],
    by simp, fun h hh => ?_, fun h hh hNe => ?_, fun m => ?_⟩
  · rcases List.mem_append.mp hh with hPre | hCons
    · exact Or.inr ⟨List.mem_append_left _ hPre, hPreNe h hPre⟩
    · rcases List.mem_cons.mp hCons with rfl | hPost
      · exact Or.inl rfl
      · exact Or.inr ⟨List.mem_append_right _ (List.mem_cons_of_mem _ hPost), hPostNe h hPost⟩
  · rcases List.mem_append.mp hh with hPre | hCons
    · exact List.mem_append_left _ hPre
    · rcases List.mem_cons.mp hCons with rfl | hPost
      · exact False.elim (hNe rfl)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hPost)
  · rw [List.find?_append, List.find?_append, List.find?_cons, List.find?_cons]
    by_cases hmEq : m == g.metaPtr
    · subst_vars; have hmP := beq_iff_eq.mp hmEq; subst hmP
      have hPreNone : pre.find? (·.metaPtr == g.metaPtr) = none := List.find?_eq_none.mpr fun h hh => by simp [hPreNe h hh]
      simp [hPreNone, hMeta]
    · have hBeqG : (g.metaPtr == m) = false := Bool.eq_false_iff.mpr fun hE => hmEq (beq_iff_eq.mpr (beq_iff_eq.mp hE).symm)
      simp [hmEq, hMeta, hBeqG]

theorem replaceGroupByMeta_map_sum {gs : List GroupDesc} (hNd : (gs.map (·.metaPtr)).Nodup)
    {g g1 : GroupDesc} (hg : g ∈ gs) (f : GroupDesc → Nat) :
    ((replaceGroupByMeta gs g.metaPtr g1).map f).sum + f g = (gs.map f).sum + f g1 := by
  obtain ⟨pre, post, hGsEq, _, _, hRep⟩ := split_groups_at_mem hNd hg
  rw [hRep g1, hGsEq]; simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]; omega

theorem list_set_map_sum {α : Type} (xs : List α) {idx : Nat} (hIdx : idx < xs.length) (v : α) (w : α → Nat) :
    ((xs.set idx v).map w).sum + w (xs[idx]'hIdx) = (xs.map w).sum + w v := by
  induction xs generalizing idx with
  | nil => simp at hIdx
  | cons x tl ih =>
    cases idx with
    | zero => simp [Nat.add_comm, Nat.add_left_comm]
    | succ k => have := ih (Nat.lt_of_succ_lt_succ hIdx); simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]; omega

theorem list_set_filter_len {α : Type} (xs : List α) {idx : Nat} (hIdx : idx < xs.length) (v : α) (p : α → Bool) :
    ((xs.set idx v).filter p).length + (if p (xs[idx]'hIdx) then 1 else 0) = (xs.filter p).length + (if p v then 1 else 0) := by
  induction xs generalizing idx with
  | nil => simp at hIdx
  | cons x tl ih =>
    cases idx with
    | zero =>
      simp only [List.set_cons_zero, List.filter_cons, List.getElem_cons_zero]
      by_cases hpv : p v = true <;> by_cases hpx : p x = true <;> simp [hpv, hpx] <;> omega
    | succ k =>
      have := ih (Nat.lt_of_succ_lt_succ hIdx)
      simp only [List.set_cons_succ, List.filter_cons, List.getElem_cons_succ]
      by_cases hpx : p x = true <;> simp [hpx] <;> omega

theorem readBytesFromMap_eq_of_inRegion {v₁ v₂ : BitVec 64 → BitVec 8}
    {b : BitVec 64} {n : Nat} (hn : n ≤ 2 ^ 64) (h : ∀ a : BitVec 64, InRegion b n a → v₁ a = v₂ a) :
    readBytesFromMap v₁ b n = readBytesFromMap v₂ b n :=
  List.map_congr_left fun a ha => h a ((mem_rangeAddrs_iff_inRegion b hn a).mp ha)
end AlignedH1
export AlignedH1 (replaceGroupByMeta split_groups_at_mem replaceGroupByMeta_props
  replaceGroupByMeta_map_sum list_set_map_sum list_set_filter_len readBytesFromMap_eq_of_inRegion)

set_option maxHeartbeats 400000 in
theorem slotWf_other_of_slotSet {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st st' : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hNotNested : ∀ cm, g.slots[idx]'hIdx ≠ .liveNested cm)
    (hBvOut : ∀ a : BitVec 64, ¬ SlotWriteMod g idx a → st'.byteVal a = st.byteVal a)
    (hNestedMap : ∀ cg ∈ st.groups, cg.maplen = 0 →
      ∃ cg' ∈ st'.groups, cg'.metaPtr = cg.metaPtr ∧ cg'.parentMeta = cg.parentMeta ∧
        cg'.mem = cg.mem ∧ cg'.nestedCap = cg.nestedCap)
    {h h' : GroupDesc} (hh : h ∈ st.groups) {j : Nat} (hj : j < h.slots.length)
    (hDiff : h.metaPtr ≠ g.metaPtr ∨ j ≠ idx)
    (hMetaEq : h'.metaPtr = h.metaPtr) (hMemEq : h'.mem = h.mem) (hScEq : h'.sc = h.sc)
    (hLastEq : h'.lastIdx = h.lastIdx) (hMapEq : h'.maplen = h.maplen) (hActEq : h'.activeByte = h.activeByte)
    (hAvailEq : h'.availMask = h.availMask) (hFreedEq : h'.freedMask = h.freedMask)
    {s : SlotState} (hs : h.slots[j]'hj = s)
    (hOv : ∀ u r e, s = .liveUser u r e → st'.liveMap.ov u = st.liveMap.ov u := by intros; rfl) :
    SlotWf st' h' j s := by
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hStrideEq : h'.stride = h.stride := by simp [GroupDesc.stride, hLastEq, hMapEq, hScEq]
  have hStorEq : h'.storage = h.storage := by simp [GroupDesc.storage, hMemEq]
  have hStartEq : h'.slotStart j = h.slotStart j := by simp [GroupDesc.slotStart, hStorEq, hStrideEq]
  have hEndEq : h'.slotEnd j = h.slotEnd j := by simp [GroupDesc.slotEnd, hStartEq, hStrideEq]
  have hActIdxEq : h'.activeIdx = h.activeIdx := by simp [GroupDesc.activeIdx, hActEq]
  have hHWf := hwf.groups_wf h hh
  have ⟨_, hStorNat, hStNat, hSub4Nat, hEnNat, _, hEn48, _, _⟩ := group_slot_bounds hHWf hj
  have ⟨hStrGe16, _⟩ := group_stride_pos_and_align hHWf
  have hSMH : (j + 1) * h.stride = j * h.stride + h.stride := Nat.succ_mul j h.stride
  have hSWf := hHWf.slot_wf j hj; rw [hs] at hSWf
  have hDisj := (slotWriteMod_disjoint hwf hg hIdx hNotNested).2.2.2 h hh j hj hDiff
  dsimp only [SlotWf] at hSWf ⊢
  rw [hStartEq, hEndEq, hAvailEq, hFreedEq, hActIdxEq, hScEq, hStorEq]
  rcases s with _ | _ | _ | cm | ⟨u, r, c⟩
  · rw [hBvOut _ (hDisj.1 (by simp [hs]) _ ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩))]; exact hSWf
  · rw [hBvOut _ (hDisj.1 (by simp [hs]) _ ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩))]; exact hSWf
  · rw [hBvOut _ (hDisj.1 (by simp [hs]) _ ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩))]; exact hSWf
  · obtain ⟨hB0, hAv, hFr, hAc, hSc48, cg, hcg, hCgM, hCgPar, hCgLo, hCgAl, hCgHi, hCgCap, hTot16, hCgM4, hCgM3, hCgM2⟩ := hSWf
    have hCgMap0 : cg.maplen = 0 := Classical.byContradiction fun hP => by
      have hNone := (hwf.groups_wf cg hcg).2.2.2.2.2.2.2.2.2.2.1.mp (by omega); rw [hNone] at hCgPar; cases hCgPar
    have ⟨hN0, hNCg⟩ := hDisj.2 cm cg hs hcg hCgM hCgPar
    obtain ⟨cg', hcg', hM', hP', hMem', hCap'⟩ := hNestedMap cg hcg hCgMap0
    have hCgGe := (hwf.groups_wf cg hcg).2.2.2.2.1
    have hCgSub4 := bv64_sub_toNat (a := cg.mem) (n := 4) (by omega)
    have hCgSub3 := bv64_sub_toNat (a := cg.mem) (n := 3) (by omega)
    have hCgSub2 := bv64_sub_toNat (a := cg.mem) (n := 2) (by omega)
    refine ⟨(hBvOut _ hN0).trans hB0, hAv, hFr, hAc, hSc48, cg', hcg', hM'.trans hCgM,
      hMetaEq ▸ hP'.trans hCgPar, hMem' ▸ hCgLo, hMem' ▸ hCgAl, by rw [hMem', hCap']; exact hCgHi, hCap'.trans hCgCap, ?_⟩
    rw [hMem']
    exact ⟨hTot16, (hBvOut _ (hNCg _ ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩))).trans hCgM4,
      (hBvOut _ (hNCg _ ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩))).trans hCgM3,
      (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
        have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
        exact hBvOut a (hNCg a ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩))).trans hCgM2⟩
  · have hSliceAg : ∀ a : BitVec 64, InRegion (h.slotStart j - 4#64) h.stride a → st'.byteVal a = st.byteVal a :=
      fun a ha => hBvOut a (hDisj.1 (by simp [hs]) a ha)
    obtain ⟨hB0, hAv, hFr, hAc, hBlkWf, hULo, hUHi, hEffLo, hOffB, hRes31, hScProps, hSc63Prop, hUM3, hHdrIte, hRes1, hRes5⟩ := hSWf
    have hUSub3 := bv64_sub_toNat (a := u) (n := 3) (by omega); have hUSub4 := bv64_sub_toNat (a := u) (n := 4) (by omega)
    have hUSub2 := bv64_sub_toNat (a := u) (n := 2) (by omega); have hEndSub5 := bv64_sub_toNat (a := h.slotEnd j) (n := 5) (by omega)
    have hEndSub4 := bv64_sub_toNat (a := h.slotEnd j) (n := 4) (by omega)
    refine ⟨(hSliceAg _ ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩)).trans hB0, hAv, hFr, hAc,
      hBlkWf, hULo, hUHi, hEffLo, ⟨hOffB.1, hOffB.2.1, by rw [hOv u r c rfl]; exact hOffB.2.2⟩,
      hRes31, hScProps, fun h63 => hMapEq ▸ hSc63Prop h63,
      (hSliceAg _ ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩)).trans hUM3, ?_,
      fun hR1 => (hSliceAg _ ((inRegion_iff_toNat (by omega) _).mpr
        ⟨by rw [bv64_add_toNat (by omega)]; omega, by rw [bv64_add_toNat (by omega)]; omega⟩)).trans (hRes1 hR1),
      fun hR5 => ⟨(hSliceAg _ ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩)).trans (hRes5 hR5).1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
          have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
          exact hSliceAg a ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)).trans (hRes5 hR5).2⟩⟩
    by_cases hTotLe : (u.toNat - h.storage.toNat) / 16 ≤ 0xffff
    · simp only [hTotLe, ↓reduceIte] at hHdrIte ⊢
      exact ⟨(hSliceAg _ ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩)).trans hHdrIte.1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
          have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
          exact hSliceAg a ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)).trans hHdrIte.2⟩
    · simp only [hTotLe, ↓reduceIte] at hHdrIte ⊢
      obtain ⟨h63, hj0, hLt27, hM4, hM2, hM8⟩ := hHdrIte
      have hSt0 : (h.slotStart j).toNat = h.storage.toNat := by rw [hj0]; simp [GroupDesc.slotStart]
      have hUGt : (h.slotStart j).toNat + 16 ≤ u.toNat := by rw [hSt0]; omega
      have hUSub8 := bv64_sub_toNat (a := u) (n := 8) (by omega)
      exact ⟨h63, hj0, hLt27, (hSliceAg _ ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩)).trans hM4,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
          have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
          exact hSliceAg a ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)).trans hM2,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
          have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
          exact hSliceAg a ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)).trans hM8⟩

theorem byteMap_absorb_slice_sameKeep {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep] (val : BitVec 64 → BitVec 8)
    (addr : BitVec 64) (bs : List (BitVec 8)) (hn : bs.length ≤ 2 ^ 64)
    (hDom : ∀ a, InRegion addr bs.length a → a ∈ dom) (hKeep : ∀ a, InRegion addr bs.length a → keep a) :
    ((addr ↦ₛ bs) ∗ ByteMap dom (fun a => keep a ∧ ¬ InRegion addr bs.length a) val) =
      ByteMap dom keep (writeBytesToMap val addr bs) := by
  rw [ByteMap_absorb_slice hNodup val addr bs hn hDom (fun _ hIn ⟨_, hN⟩ => hN hIn)]
  exact SetSep_congr (fun a _ => ⟨fun h => h.elim And.left (hKeep a),
    fun hk => if hIn : InRegion addr bs.length a then Or.inr hIn else Or.inl ⟨hk, hIn⟩⟩) (fun _ _ _ => rfl)

theorem byteMap_focus8 {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep] (val : BitVec 64 → BitVec 8) (addr : BitVec 64)
    (hDom : ∀ a, InRegion addr 1 a → a ∈ dom) (hKeep : ∀ a, InRegion addr 1 a → keep a) :
    ByteMap dom keep val = ((addr ↦₈ val addr) ∗ ByteMap dom (fun a => keep a ∧ ¬ InRegion addr 1 a) val) := by
  rw [ByteMap_extract_slice hNodup val addr (by decide) hDom hKeep,
    readBytesFromMap_succ, readBytesFromMap_zero, pointsToBytes_singleton]

theorem byteMap_absorb8 {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep] (val : BitVec 64 → BitVec 8) (addr : BitVec 64) (v : BitVec 8)
    (hDom : ∀ a, InRegion addr 1 a → a ∈ dom) (hKeep : ∀ a, InRegion addr 1 a → keep a) :
    ((addr ↦₈ v) ∗ ByteMap dom (fun a => keep a ∧ ¬ InRegion addr 1 a) val) =
      ByteMap dom keep (writeBytesToMap val addr [v]) := by
  rw [← pointsToBytes_singleton addr v]; exact byteMap_absorb_slice_sameKeep hNodup val addr [v] (by simp) hDom hKeep

theorem byteMap_focus16 {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep] (val : BitVec 64 → BitVec 8) (addr : BitVec 64)
    (hDom : ∀ a, InRegion addr 2 a → a ∈ dom) (hKeep : ∀ a, InRegion addr 2 a → keep a) :
    ByteMap dom keep val = ((addr ↦₁₆ (val (addr + 1#64) ++ val addr)) ∗
      ByteMap dom (fun a => keep a ∧ ¬ InRegion addr 2 a) val) := by
  rw [ByteMap_extract_slice hNodup val addr (by decide) hDom hKeep,
    readBytesFromMap_succ, readBytesFromMap_succ, readBytesFromMap_zero, pointsToBytes2_eq_pointsTo16]

theorem byteMap_absorb16 {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep] (val : BitVec 64 → BitVec 8) (addr : BitVec 64) (w : BitVec 16)
    (hDom : ∀ a, InRegion addr 2 a → a ∈ dom) (hKeep : ∀ a, InRegion addr 2 a → keep a) :
    ((addr ↦₁₆ w) ∗ ByteMap dom (fun a => keep a ∧ ¬ InRegion addr 2 a) val) =
      ByteMap dom keep (writeBytesToMap val addr (unpack16 w)) := by
  rw [pointsTo16_eq_pointsToBytes addr w]
  exact byteMap_absorb_slice_sameKeep hNodup val addr (unpack16 w) (by simp) (by simpa using hDom) (by simpa using hKeep)

theorem byteMap_focus32 {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep] (val : BitVec 64 → BitVec 8) (addr : BitVec 64)
    (hDom : ∀ a, InRegion addr 4 a → a ∈ dom) (hKeep : ∀ a, InRegion addr 4 a → keep a) :
    ByteMap dom keep val = ((addr ↦₃₂ (val (addr + 3#64) ++ val (addr + 2#64) ++ val (addr + 1#64) ++ val addr)) ∗
      ByteMap dom (fun a => keep a ∧ ¬ InRegion addr 4 a) val) := by
  have h2 : addr + 1#64 + 1#64 = addr + 2#64 := by bv_arith
  have h3 : addr + 2#64 + 1#64 = addr + 3#64 := by bv_arith
  rw [ByteMap_extract_slice hNodup val addr (by decide) hDom hKeep, readBytesFromMap_succ,
    readBytesFromMap_succ, h2, readBytesFromMap_succ, h3, readBytesFromMap_succ, readBytesFromMap_zero, pointsToBytes4_eq_pointsTo32]

theorem byteMap_absorb32 {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep] (val : BitVec 64 → BitVec 8) (addr : BitVec 64) (w : BitVec 32)
    (hDom : ∀ a, InRegion addr 4 a → a ∈ dom) (hKeep : ∀ a, InRegion addr 4 a → keep a) :
    ((addr ↦₃₂ w) ∗ ByteMap dom (fun a => keep a ∧ ¬ InRegion addr 4 a) val) =
      ByteMap dom keep (writeBytesToMap val addr (unpack32 w)) := by
  rw [pointsTo32_eq_pointsToBytes addr w]
  exact byteMap_absorb_slice_sameKeep hNodup val addr (unpack32 w) (by simp) (by simpa using hDom) (by simpa using hKeep)

theorem writeBytesToMap_self_one (val : BitVec 64 → BitVec 8) (addr : BitVec 64) (v : BitVec 8) :
    writeBytesToMap val addr [v] addr = v := by
  simpa using writeBytesToMap_in val addr [v] (i := 0) (by simp) (by simp)

end VerifiedLibraries.Mallocng.Proofs
