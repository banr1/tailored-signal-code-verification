/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocStage1

/-!
# Placed `__libc_realloc` Size-Class and Header Helpers

Proves read-only table focus, header-byte bitvector lemmas for `set_size`, and symbolic execution
of `size_to_class(newSz) + 1` in `__libc_realloc` (`realloc_sizeToClass_ok`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## RO Table Split and Bitvector Lemmas for `size_to_class` and `set_size` -/

theorem split_debruijnAlloc_roTablesAt (A : MallocngAddrs) {idx : Nat} (hidx : idx < 32) (R : SepProp) :
    ∃ Rest : SepProp, (MallocngRoTablesAt A ∗ R) =
      (((A.debruijnAlloc + BitVec.ofNat 64 idx) ↦₈ᵣ debruijn32Table.getD idx 0#8) ∗ Rest ∗ R) := by
  refine ⟨(A.debruijnAlloc ↦ᵣ debruijn32Table.take idx) ∗
    ((A.debruijnAlloc + BitVec.ofNat 64 (idx + 1)) ↦ᵣ debruijn32Table.drop (idx + 1)) ∗
    (A.sizeClasses ↦ᵣ sizeClassBytes) ∗ (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
    (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗ (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes), ?_⟩
  unfold MallocngRoTablesAt debruijn32Table
  change ((A.sizeClasses ↦ᵣ sizeClassBytes) ∗ (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
    (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗ (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
    (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table)) ∗ R = _
  rw [pointsToBytesRO_split3 A.debruijnAlloc mallocngDebruijn32Table idx 1
        (by rw [debruijn32Table_length]; omega),
      pointsToBytesRO_take1_eq_pointsTo8RO _ _ _ (by rw [debruijn32Table_length]; omega)]
  ac_rfl

private theorem bv32_zx64_eq_ofNat (v : BitVec 32) :
    v.zeroExtend 64 = BitVec.ofNat 64 v.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide))]

private theorem bv8_zx64_eq_ofNat (b : BitVec 8) :
    b.zeroExtend 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))]

private theorem bv16_zx64_eq_ofNat {n : Nat} (hn : n < 65536) :
    (BitVec.ofNat 16 n).zeroExtend 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega)]

theorem ofNat8_shl5_or {r idx : Nat} (hr : r < 6) (hidx : idx < 32) :
    ((BitVec.ofNat 8 r <<< 5) ||| BitVec.ofNat 8 idx) = BitVec.ofNat 8 ((r <<< 5) ||| idx) := by
  have hgrid : (List.range 6).all (fun r => (List.range 32).all (fun idx =>
      ((BitVec.ofNat 8 r <<< 5) ||| BitVec.ofNat 8 idx) == BitVec.ofNat 8 ((r <<< 5) ||| idx))) = true := by
    decide
  have h1 := List.all_eq_true.mp hgrid r (List.mem_range.mpr hr)
  exact eq_of_beq (List.all_eq_true.mp h1 idx (List.mem_range.mpr hidx))

theorem hdrByte_res1to4 {b8 : BitVec 8} {idx res : Nat}
    (hIdx : (b8.zeroExtend 32 &&& 0x1f#32) = BitVec.ofNat 32 idx)
    (hIdx31 : idx ≤ 31) (hRes4 : res ≤ 4) :
    (((b8.zeroExtend 32 &&& 0x1f#32) + (BitVec.ofNat 32 res <<< 5)) &&& 0xff#32).truncate 8 =
      BitVec.ofNat 8 (((min res 5) <<< 5) ||| idx) := by
  have hMin : min res 5 = res := Nat.min_eq_left (by omega)
  rw [hIdx, hMin]
  have h8 : ∀ (r8 i8 : BitVec 8), r8.ult 5#8 = true → i8.ult 32#8 = true →
      (((i8.zeroExtend 32) + (r8.zeroExtend 32 <<< 5)) &&& 0xff#32).truncate 8 = (r8 <<< 5) ||| i8 := by
    intro r8 i8 h1 h2; revert h1 h2; bv_robdd
  have hr : (BitVec.ofNat 8 res).ult 5#8 = true := by
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; omega
  have hi : (BitVec.ofNat 8 idx).ult 32#8 = true := by
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; omega
  rw [show BitVec.ofNat 32 idx = (BitVec.ofNat 8 idx).zeroExtend 32 by bv_omega,
      show BitVec.ofNat 32 res = (BitVec.ofNat 8 res).zeroExtend 32 by bv_omega,
      h8 _ _ hr hi, ofNat8_shl5_or (by omega) (by omega)]

theorem hdrByte_res5up {b8 : BitVec 8} {idx res : Nat}
    (hIdx : (b8.zeroExtend 32 &&& 0x1f#32) = BitVec.ofNat 32 idx)
    (hIdx31 : idx ≤ 31) (hRes5 : 5 ≤ res) :
    (((b8.zeroExtend 32 &&& 0x1f#32) - 0x60#32) &&& 0xff#32).truncate 8 =
      BitVec.ofNat 8 (((min res 5) <<< 5) ||| idx) := by
  have hMin : min res 5 = 5 := Nat.min_eq_right hRes5
  rw [hIdx, hMin]
  have h8 : ∀ i8 : BitVec 8, i8.ult 32#8 = true →
      (((i8.zeroExtend 32) - 0x60#32) &&& 0xff#32).truncate 8 = (BitVec.ofNat 8 5 <<< 5) ||| i8 := by
    intro i8 hi; revert hi; bv_robdd
  have hi : (BitVec.ofNat 8 idx).ult 32#8 = true := by
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; omega
  rw [show BitVec.ofNat 32 idx = (BitVec.ofNat 8 idx).zeroExtend 32 by bv_omega,
      h8 _ hi, ofNat8_shl5_or (by omega) (by omega)]

theorem neg32_sxtw_of_pos_lt31 {r : Nat} (h1 : 1 ≤ r) (h31 : r < 2 ^ 31) :
    (-BitVec.ofNat 32 r).signExtend 64 = -BitVec.ofNat 64 r := by
  have hlt : (BitVec.ofNat 32 r).ult (1#32 <<< 31) = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change r % 4294967296 < 2147483648; omega
  have hnz : BitVec.ofNat 32 r ≠ 0#32 := by
    intro h0; have ht := congrArg BitVec.toNat h0; simp only [BitVec.toNat_ofNat] at ht; omega
  rw [show BitVec.ofNat 64 r = (BitVec.ofNat 32 r).zeroExtend 64 by bv_omega]
  generalize BitVec.ofNat 32 r = v at hlt hnz ⊢
  revert hlt hnz; bv_robdd

@[simp, arm64_norm, wp_norm] theorem trunc32_zx64_shr2 (x : BitVec 32) :
    (x.zeroExtend 64 >>> 2).truncate 32 = x >>> 2 := by bv_robdd

@[simp, arm64_norm, wp_norm] theorem trunc32_zx64_shr27 (x : BitVec 32) :
    (x.zeroExtend 64 >>> 27).truncate 32 = x >>> 27 := by bv_robdd

@[simp, arm64_norm, wp_norm] theorem trunc32_zx64_shl2 (x : BitVec 32) :
    (x.zeroExtend 64 <<< 2).truncate 32 = x <<< 2 := by bv_robdd

@[simp, arm64_norm, wp_norm] theorem bv32_zero_add (x : BitVec 32) :
    0#32 + x = x := BitVec.zero_add x

@[simp, arm64_norm, wp_norm] theorem trunc32_zx64_8 (b8 : BitVec 8) :
    (b8.zeroExtend 64).truncate 32 = b8.zeroExtend 32 := by bv_robdd

@[simp, arm64_norm, wp_norm] theorem trunc8_zx64_32 (w : BitVec 32) :
    (w.zeroExtend 64).truncate 8 = w.truncate 8 := by bv_robdd

private theorem cinc_ule_sc {u scVal sc1 : Nat} (hu : u + 1 < 65536) (hsc : scVal < 65536) (_h1 : sc1 < 48) :
    (if (BitVec.ofNat 64 (u + 1)).ule
        (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 scVal))) = true then
      BitVec.ofNat 32 (sc1 + 1)
    else
      BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.ofNat 32 (sc1 + 1)) + 1#64)) =
    BitVec.ofNat 32 ((if u + 1 > scVal then sc1 + 1 else sc1) + 1) := by
  have hZx : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 scVal)) = BitVec.ofNat 64 scVal := by
    bv_omega
  rw [hZx]
  by_cases hGt : u + 1 > scVal
  · have hUle : (BitVec.ofNat 64 (u + 1)).ule (BitVec.ofNat 64 scVal) = false := by
      rw [BitVec.ule, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    simp only [hGt, hUle, Bool.false_eq_true, ↓reduceIte]
    bv_omega
  · have hUle : (BitVec.ofNat 64 (u + 1)).ule (BitVec.ofNat 64 scVal) = true := by
      rw [BitVec.ule, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    simp only [hGt, hUle, ↓reduceIte]

/-! ## `realloc_sizeToClass_ok` (`+0x1d0` to `+0x258`) -/

set_option maxHeartbeats 400000 in
theorem realloc_sizeToClass_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    {newSize : BitVec 64} {newSz : Nat} {Rest : SepProp} {oom : State → SepProp}
    (hNewEq : newSize = BitVec.ofNat 64 newSz) (hNewMax : newSz ≤ 131051)
    {s : State} (hpc : s.pc = b + 0x1d0#64) (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = newSize) :
    let P := MallocngRoTablesAt maddrs ∗ Rest
    SepWP (blkPC_b14.rebase b (fun _ => none)) (b + 0x258#64) s P
      (sepPost (fun sf => ReallocReadPres s sf ∧
        sf.readReg32 .x2 = BitVec.ofNat 32 (sizeToClassUnits ((newSz + 3) / 16) + 1) ∧
        sf.readReg64 .x3 = s.readReg64 .x3 ∧
        sf.readReg64 .x4 = s.readReg64 .x4 ∧
        sf.readReg64 .x5 = s.readReg64 .x5 ∧
        sf.readReg64 .x6 = s.readReg64 .x6 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = newSize ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24) P) oom := by
  intro P
  have _ := hb
  subst hNewEq
  let u := (newSz + 3) / 16
  have hAdd3 : BitVec.ofNat 64 newSz + 3#64 = BitVec.ofNat 64 (newSz + 3) := by bv_omega
  have hShr4 : BitVec.ofNat 64 (newSz + 3) >>> 4 = BitVec.ofNat 64 u := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  wp_step; wp_step; wp_step; wp_step; wp_step
  by_cases hu9 : u ≤ 9
  · have hlsTrue : (BitVec.ofNat 64 (newSz + 3)).ule 159#64 = true := by
      simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_ofNat]
      dsimp only [u] at hu9; omega
    wp_if hls
    · refine SepWP.done rfl (by simp [hrun])
        ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp,
            by simp, by simp, by simp [calleeSavedVRegs]⟩,
          ?_, by simp, by simp, by simp, by simp, by simp, by simp, by simp [hx21],
          by simp, by simp, by simp⟩, Entails.refl _⟩
      dsimp only [u] at hu9 ⊢
      simp only [sizeToClassUnits, hu9, ↓reduceIte, wp_norm, arm64_norm]
      bv_omega
    · exact absurd hlsTrue hls
  · have huLo : 10 ≤ u := by omega
    have huHi : u ≤ 8190 := by dsimp only [u]; omega
    have hlsFalse : (BitVec.ofNat 64 (newSz + 3)).ule 159#64 = false := by
      simp only [BitVec.ule, decide_eq_false_iff_not, BitVec.toNat_ofNat]
      dsimp only [u] at huLo; omega
    have hPageDeb := pageOf_add_lo12Of maddrs.debruijnAlloc
    have hPageSc := pageOf_add_lo12Of maddrs.sizeClasses
    let hIdx := sizeToClassHashIdx u
    let db := (debruijn32Table.getD hIdx 0#8).toNat
    let baseSc := (db - 1) * 4
    let sc1 := if u + 1 > sizeClass (baseSc + 1) then baseSc + 2 else baseSc
    let sc2 := if u + 1 > sizeClass sc1 then sc1 + 1 else sc1
    have hLarge := sizeToClassLarge_spec huLo huHi
    unfold sizeToClassLargeOk at hLarge
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hLarge
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hIdx32, hbLo⟩, hbHi⟩, hBaseLt⟩, hSc1Lt⟩, hSc2Lt⟩, _⟩, _⟩, _⟩ := hLarge
    change hIdx < 32 at hIdx32
    change 2 ≤ db at hbLo
    change db ≤ 12 at hbHi
    have hBaseLt : baseSc + 3 < 48 := by dsimp only [baseSc]; omega
    have hScUnits : sizeToClassUnits u = sc2 := by simp [sizeToClassUnits, hu9, hIdx, db, baseSc, sc1, sc2]
    obtain ⟨debRest, hDebSplit⟩ := split_debruijnAlloc_roTablesAt maddrs hIdx32 Rest
    have hU1Add : BitVec.ofNat 64 u + 1#64 = BitVec.ofNat 64 (u + 1) := by dsimp only [u]; bv_omega
    have hU1Tr : (BitVec.ofNat 64 (u + 1)).truncate 32 = BitVec.ofNat 32 (u + 1) := by dsimp only [u]; bv_omega
    wp_if hls
    · rw [hlsFalse] at hls; cases hls
    · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
      wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
      conv => arg 4; dsimp only [P]; rw [hDebSplit]
      have hHashOff :
          let w1 := BitVec.ofNat 32 (u + 1)
          let w0a := (w1 >>> 2) ||| (w1 >>> 1)
          let w0b := w0a ||| (w0a >>> 2)
          let w0c := w0b ||| (w0b >>> 4)
          let w0d := w0c ||| (w0c >>> 8)
          let p2 := (w0d + 1#32) &&& (~~~w0d)
          ((p2 * 0x076be629#32) >>> 27).zeroExtend 64 = BitVec.ofNat 64 hIdx := by
        dsimp only; rw [bv32_zx64_eq_ofNat]; rfl
      dsimp only at hHashOff
      have hIdxUxtw : ((BitVec.ofNat 64 hIdx).truncate 32).zeroExtend 64 = BitVec.ofNat 64 hIdx := by
        generalize hIdx = k at hIdx32 ⊢; bv_omega
      wp_step
      conv => arg 4; rw [← hDebSplit]
      have hBase1Lt : baseSc + 1 < 48 := by omega
      obtain ⟨scRest1, hScSplit1⟩ := split_sizeClass_roTablesAt maddrs hBase1Lt Rest
      have hDbVal : (debruijn32Table.getD hIdx 0#8).zeroExtend 32 = BitVec.ofNat 32 db := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (Nat.lt_trans (debruijn32Table.getD hIdx 0#8).isLt (by decide))]
      have hBaseVal : (BitVec.ofNat 32 db - 1#32) <<< 2 = BitVec.ofNat 32 baseSc := by
        dsimp only [baseSc]; generalize db = d at hbLo hbHi ⊢; bv_omega
      have hBase1Val : BitVec.ofNat 32 baseSc + 1#32 = BitVec.ofNat 32 (baseSc + 1) := by
        generalize baseSc = bs at hBase1Lt ⊢; bv_omega
      wp_step; wp_step; wp_step
      have hSxtw1 : (BitVec.ofNat 32 (baseSc + 1)).signExtend 64 <<< 1 = BitVec.ofNat 64 (2 * (baseSc + 1)) := by
        rw [sxtw32_of_lt31 (by omega)]; generalize baseSc = bs at hBase1Lt ⊢; bv_omega
      conv => arg 4; rw [hScSplit1]
      wp_step; wp_step; wp_step
      conv => arg 4; rw [← hScSplit1]
      have hScB1Bound := (sizeClass_bounds hBase1Lt).2
      have hScB1Zx := bv16_zx64_eq_ofNat (n := sizeClass (baseSc + 1)) (by omega)
      wp_if hls1
      · have hNotGt1 : ¬ (u + 1 > sizeClass (baseSc + 1)) := by
          try rw [hScB1Zx] at hls1
          rw [BitVec.ule, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by dsimp only [u]; omega), Nat.mod_eq_of_lt (by omega)] at hls1
          omega
        have hSc1Eq : sc1 = baseSc := by simp [sc1, hNotGt1]
        have hBase0Lt : baseSc < 48 := by omega
        obtain ⟨scRest2, hScSplit2⟩ := split_sizeClass_roTablesAt maddrs hBase0Lt Rest
        have hSc2Bound := (sizeClass_bounds hBase0Lt).2
        have hSc2Zx := bv16_zx64_eq_ofNat (n := sizeClass baseSc) (by omega)
        have hSxtw2 : (BitVec.ofNat 32 baseSc).signExtend 64 <<< 1 = BitVec.ofNat 64 (2 * baseSc) := by
          rw [sxtw32_of_lt31 (by omega)]; generalize baseSc = bs at hBase0Lt ⊢; bv_omega
        wp_step
        conv => arg 4; rw [hScSplit2]
        wp_step; wp_step; wp_step
        conv => arg 4; rw [← hScSplit2]
        refine SepWP.done rfl (by simp [hrun])
          ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp,
              by simp, by simp, by simp [calleeSavedVRegs]⟩,
            ?_, by simp, by simp, by simp, by simp, by simp, by simp, by simp [hx21],
            by simp, by simp, by simp⟩, Entails.refl _⟩
        change _ = BitVec.ofNat 32 (sizeToClassUnits u + 1)
        rw [hScUnits]
        simp only [wp_norm, arm64_norm]
        try rw [hSc2Zx]
        dsimp only [sc2]; rw [hSc1Eq]
        exact cinc_ule_sc (by dsimp only [u]; omega) (Nat.lt_of_le_of_lt hSc2Bound.1 (by decide)) hBase0Lt
      · have hGt1 : u + 1 > sizeClass (baseSc + 1) := by
          try rw [hScB1Zx] at hls1
          rw [BitVec.ule, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by dsimp only [u]; omega), Nat.mod_eq_of_lt (by omega)] at hls1
          omega
        have hSc1Eq : sc1 = baseSc + 2 := by simp [sc1, hGt1]
        have hBase2Lt : baseSc + 2 < 48 := by omega
        obtain ⟨scRest2, hScSplit2⟩ := split_sizeClass_roTablesAt maddrs hBase2Lt Rest
        have hSc2Bound := (sizeClass_bounds hBase2Lt).2
        have hSc2Zx := bv16_zx64_eq_ofNat (n := sizeClass (baseSc + 2)) (by omega)
        have hBase2Val : BitVec.ofNat 32 baseSc + 2#32 = BitVec.ofNat 32 (baseSc + 2) := by
          generalize baseSc = bs at hBaseLt ⊢; bv_omega
        have hBase3Val : BitVec.ofNat 32 baseSc + 3#32 = BitVec.ofNat 32 (baseSc + 3) := by
          generalize baseSc = bs at hBaseLt ⊢; bv_omega
        have hSxtw2 : (BitVec.ofNat 32 (baseSc + 2)).signExtend 64 <<< 1 = BitVec.ofNat 64 (2 * (baseSc + 2)) := by
          rw [sxtw32_of_lt31 (by omega)]; generalize baseSc = bs at hBaseLt ⊢; bv_omega
        wp_step; wp_step; wp_step
        conv => arg 4; rw [hScSplit2]
        wp_step; wp_step; wp_step
        conv => arg 4; rw [← hScSplit2]
        refine SepWP.done rfl (by simp [hrun])
          ⟨⟨⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, by simp,
              by simp, by simp, by simp [calleeSavedVRegs]⟩,
            ?_, by simp, by simp, by simp, by simp, by simp, by simp, by simp [hx21],
            by simp, by simp, by simp⟩, Entails.refl _⟩
        change _ = BitVec.ofNat 32 (sizeToClassUnits u + 1)
        rw [hScUnits]
        simp only [wp_norm, arm64_norm]
        try rw [hSc2Zx]
        dsimp only [sc2]; rw [hSc1Eq]
        exact cinc_ule_sc (by dsimp only [u]; omega) (Nat.lt_of_le_of_lt hSc2Bound.1 (by decide)) hBase2Lt

end VerifiedLibraries.Mallocng.Proofs
