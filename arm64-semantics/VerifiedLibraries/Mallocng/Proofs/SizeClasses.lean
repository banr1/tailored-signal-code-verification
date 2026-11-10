/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.BV
public import VerifiedLibraries.Mallocng.Spec.Top

/-!
# `.rodata` Lookup Tables, Size Classes, and De Bruijn Bit Scans

Defines `mallocng`'s `.rodata` tables (`__malloc_size_classes`, `debruijn32`, `med_cnt_tab`,
`small_cnt_tab`), size-class stride and capacity bounds (`sizeClass`, `slotStride`,
`nominalSlotCap`), and correctness lemmas for `size_to_class`, `a_ctz_32` (`ctz32DeBruijn_spec`),
and `.rodata` slice splitting (`roTables_split`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

/-! ## `.rodata` Table Literals -/

/-- Stock `musl` v1.2.5 `__malloc_size_classes[0..47]` (`48` entries, in `UNIT = 16`-byte multiples). -/
abbrev sizeClassUnits : List Nat := mallocngSizeClassUnits

/-- Little-endian `u16` byte encoding (`96` B) of `__malloc_size_classes`. -/
abbrev sizeClassBytes : List (BitVec 8) := mallocngSizeClassBytes

/-- 32-byte De Bruijn lookup table (`debruijn32.4681` and `debruijn32.5048`) for `a_ctz_32`. -/
abbrev debruijn32Table : List (BitVec 8) := mallocngDebruijn32Table

/-- 4-byte `med_cnt_tab` (`[28, 24, 20, 32]`) in `alloc_group`. -/
abbrev medCntTabBytes : List (BitVec 8) := mallocngMedCntTabBytes

/-- 27-byte `small_cnt_tab` (`9 × 3` entries for `sc < 9`) in `alloc_group`. -/
abbrev smallCntTabBytes : List (BitVec 8) := mallocngSmallCntTabBytes

theorem sizeClassUnits_length : sizeClassUnits.length = 48 := rfl
theorem sizeClassBytes_length : sizeClassBytes.length = 96 := rfl
theorem debruijn32Table_length : debruijn32Table.length = 32 := rfl
theorem medCntTabBytes_length : medCntTabBytes.length = 4 := rfl
theorem smallCntTabBytes_length : smallCntTabBytes.length = 27 := rfl
set_option maxRecDepth 20000 in
theorem mallocngRoTablesBytes_length : mallocngRoTablesBytes.length = 200 := rfl

/-! ## Size-Class Capacities, Monotonicity, and Accounting Bounds -/

/-- `UNIT` multiple for size class `sc < 48` (`0` out of range). -/
def sizeClass (sc : Nat) : Nat :=
  sizeClassUnits.getD sc 0

/-- Physical slot stride in bytes (`UNIT * size_classes[sc] = 16 * sizeClass sc`). -/
def slotStride (sc : Nat) : Nat :=
  16 * sizeClass sc

/-- Maximum nominal user request capacity (`UNIT * size_classes[sc] - IB = 16 * sizeClass sc - 4`)
    fitting in a single slot of class `sc < 48`. -/
def nominalSlotCap (sc : Nat) : Nat :=
  16 * sizeClass sc - 4

private def checkSizeClassProps : Bool :=
  (List.range 48).all fun sc =>
    let u := sizeClass sc
    (1 ≤ u) && (u ≤ 8191) &&
    (12 ≤ nominalSlotCap sc) && (nominalSlotCap sc ≤ 131052) &&
    (if sc + 1 < 48 then u < sizeClass (sc + 1) else true) &&
    (if sc == 0 then slotStride 0 ≤ 2 * 16
     else slotStride sc ≤ 2 * max (nominalSlotCap (sc - 1) + 1) 16)

private theorem checkSizeClassProps_true : checkSizeClassProps = true := by
  decide +kernel

theorem sizeClass_bounds {sc : Nat} (hsc : sc < 48) :
    1 ≤ sizeClass sc ∧ sizeClass sc ≤ 8191 ∧
    12 ≤ nominalSlotCap sc ∧ nominalSlotCap sc ≤ 131052 := by
  have h := List.all_eq_true.mp checkSizeClassProps_true sc (List.mem_range.mpr hsc)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩

theorem sizeClass_strictMono {sc₁ sc₂ : Nat} (hlt : sc₁ < sc₂) (h₂ : sc₂ < 48) :
    sizeClass sc₁ < sizeClass sc₂ := by
  induction sc₂ with
  | zero => omega
  | succ k ih =>
    have hk : k < 48 := by omega
    have hstep : sizeClass k < sizeClass (k + 1) := by
      have h := List.all_eq_true.mp checkSizeClassProps_true k (List.mem_range.mpr hk)
      simp only [Bool.and_eq_true, decide_eq_true_eq, h₂, ↓reduceIte] at h
      exact h.1.2
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
    · exact Nat.lt_trans (ih hlt' hk) hstep
    · exact hstep

/-- Accounting bound: when `sc` is the minimal size class fitting request `req`
    (`sc = 0` or `nominalSlotCap (sc - 1) < req`), the slot's physical stride `slotStride sc` is at
    most `2 * max req 16`. -/
theorem slotStride_le_two_mul_cost {sc req : Nat} (hsc : sc < 48)
    (hmin : sc = 0 ∨ nominalSlotCap (sc - 1) < req) :
    slotStride sc ≤ 2 * max req 16 := by
  have h := List.all_eq_true.mp checkSizeClassProps_true sc (List.mem_range.mpr hsc)
  simp only [Bool.and_eq_true] at h
  have hbound := h.2
  rcases hmin with rfl | hgt
  · simp only [BEq.beq, decide_true, ↓reduceIte, decide_eq_true_eq] at hbound
    omega
  · by_cases h0 : sc = 0
    · subst h0
      simp only [BEq.beq, decide_true, ↓reduceIte, decide_eq_true_eq] at hbound
      omega
    · have hne : (sc == 0) = false := beq_false_of_ne h0
      rw [hne] at hbound
      simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hbound
      omega

/-! ## `size_to_class` Bit-Search Model and Verification -/

/-- De Bruijn MSB hash index computed by `size_to_class` for `u = (n + 3) >>> 4 ≥ 10`. -/
def sizeToClassHashIdx (u : Nat) : Nat :=
  let w1 : BitVec 32 := BitVec.ofNat 32 (u + 1)
  let w0a := (w1 >>> 2) ||| (w1 >>> 1)
  let w0b := w0a ||| (w0a >>> 2)
  let w0c := w0b ||| (w0b >>> 4)
  let w0d := w0c ||| (w0c >>> 8)
  let w5  := w0d + 1#32
  let p2  := w5 &&& (~~~w0d)
  ((p2 * 0x076be629#32) >>> 27).toNat

/-- ARM64 bit-search calculation for `size_to_class` on `u = (n + 3) >>> 4`: returns `u` for
    `u ≤ 9`, and performs the De Bruijn MSB lookup followed by a 2-step binary search in
    `sizeClassUnits` for `10 ≤ u ≤ 8190` (`157 ≤ n ≤ 131051`). -/
def sizeToClassUnits (u : Nat) : Nat :=
  if u ≤ 9 then u
  else
    let idx := sizeToClassHashIdx u
    let b   := (debruijn32Table.getD idx 0#8).toNat
    let baseSc := (b - 1) * 4
    let sc1 := if u + 1 > sizeClass (baseSc + 1) then baseSc + 2 else baseSc
    if u + 1 > sizeClass sc1 then sc1 + 1 else sc1

/-- Intermediate index safety check for every `u ∈ [10, 8190]` so `MallocImplProof` gets exact
    non-wrapping 32-bit/signed bounds at every instruction of `size_to_class`. -/
def sizeToClassLargeOk (u : Nat) : Bool :=
  let idx := sizeToClassHashIdx u
  let b   := (debruijn32Table.getD idx 0#8).toNat
  let baseSc := (b - 1) * 4
  let sc1 := if u + 1 > sizeClass (baseSc + 1) then baseSc + 2 else baseSc
  let sc2 := if u + 1 > sizeClass sc1 then sc1 + 1 else sc1
  (idx < 32) &&
  (2 ≤ b) && (b ≤ 12) &&
  (baseSc + 2 < 48) &&
  (sc1 < 48) &&
  (sc2 < 48) &&
  (u < sizeClass sc2) &&
  (0 < sc2) &&
  (sizeClass (sc2 - 1) ≤ u)

private def packedSizeClassesNat : Nat :=
  (List.range 48).foldl (fun acc sc => acc ||| ((sizeClass sc) <<< (16 * sc))) 0

private def packedDebruijnNat : Nat :=
  (List.range 32).foldl (fun acc k => acc ||| ((debruijn32Table.getD k 0#8).toNat <<< (8 * k))) 0

private def sizeClassFast (sc : Nat) : Nat :=
  (packedSizeClassesNat >>> (16 * sc)) &&& 0xffff

private def debruijnFast (idx : Nat) : Nat :=
  (packedDebruijnNat >>> (8 * idx)) &&& 0xff

private theorem sizeClassFast_eq_all :
    (List.range 48).all (fun sc => sizeClassFast sc == sizeClass sc) = true := by
  decide +kernel

private theorem debruijnFast_eq_all :
    (List.range 32).all (fun k => debruijnFast k == (debruijn32Table.getD k 0#8).toNat) = true := by
  decide +kernel

private theorem sizeClassFast_eq {sc : Nat} (hsc : sc < 48) :
    sizeClassFast sc = sizeClass sc := by
  simpa only [beq_iff_eq] using List.all_eq_true.mp sizeClassFast_eq_all sc (List.mem_range.mpr hsc)

private theorem debruijnFast_eq {idx : Nat} (hidx : idx < 32) :
    debruijnFast idx = (debruijn32Table.getD idx 0#8).toNat := by
  simpa only [beq_iff_eq] using List.all_eq_true.mp debruijnFast_eq_all idx (List.mem_range.mpr hidx)

private def sizeToClassLargeOkFast (u : Nat) : Bool :=
  let idx := sizeToClassHashIdx u
  let b   := debruijnFast idx
  let baseSc := (b - 1) * 4
  let sc1 := if u + 1 > sizeClassFast (baseSc + 1) then baseSc + 2 else baseSc
  let sc2 := if u + 1 > sizeClassFast sc1 then sc1 + 1 else sc1
  (idx < 32) &&
  (2 ≤ b) && (b ≤ 12) &&
  (baseSc + 2 < 48) &&
  (sc1 < 48) &&
  (sc2 < 48) &&
  (u < sizeClassFast sc2) &&
  (0 < sc2) &&
  (sizeClassFast (sc2 - 1) ≤ u)

private def sizeToClassLargeRow (hi : Nat) : Bool :=
  (List.range 128).all fun lo =>
    let u := 128 * hi + lo
    if 10 ≤ u && u ≤ 8190 then sizeToClassLargeOkFast u else true

private theorem sizeToClassLargeOk_grid :
    (List.range 64).all sizeToClassLargeRow = true := by
  decide +kernel

theorem sizeToClassLarge_spec {u : Nat} (hu_lo : 10 ≤ u) (hu_hi : u ≤ 8190) :
    sizeToClassLargeOk u = true := by
  have hrow := List.all_eq_true.mp sizeToClassLargeOk_grid (u / 128) (List.mem_range.mpr (by omega))
  have hcell := List.all_eq_true.mp hrow (u % 128) (List.mem_range.mpr (by omega))
  have heq : 128 * (u / 128) + u % 128 = u := Nat.div_add_mod u 128
  rw [heq] at hcell
  have hcond : (decide (10 ≤ u) && decide (u ≤ 8190)) = true := by
    simp [hu_lo, hu_hi]
  have hfast : sizeToClassLargeOkFast u = true := by
    simpa [hcond] using hcell
  unfold sizeToClassLargeOkFast at hfast
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfast
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hidx_lt, hb_lo⟩, hb_hi⟩, hbase_lt⟩, hsc1_lt⟩, hsc2_lt⟩, hu_lt⟩, hpos⟩, hprev⟩ := hfast
  unfold sizeToClassLargeOk
  dsimp only
  generalize sizeToClassHashIdx u = idx at hidx_lt hb_lo hb_hi hbase_lt hsc1_lt hsc2_lt hu_lt hpos hprev ⊢
  rw [← debruijnFast_eq hidx_lt]
  generalize debruijnFast idx = b at hb_lo hb_hi hbase_lt hsc1_lt hsc2_lt hu_lt hpos hprev ⊢
  have hb1 : (b - 1) * 4 + 1 < 48 := by omega
  rw [← sizeClassFast_eq hb1]
  generalize (if u + 1 > sizeClassFast ((b - 1) * 4 + 1) then (b - 1) * 4 + 2 else (b - 1) * 4) = sc1 at hsc1_lt hsc2_lt hu_lt hpos hprev ⊢
  rw [← sizeClassFast_eq hsc1_lt]
  generalize (if u + 1 > sizeClassFast sc1 then sc1 + 1 else sc1) = sc2 at hsc2_lt hu_lt hpos hprev ⊢
  have hsc2_prev : sc2 - 1 < 48 := by omega
  rw [← sizeClassFast_eq hsc2_lt, ← sizeClassFast_eq hsc2_prev]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨hidx_lt, hb_lo⟩, hb_hi⟩, hbase_lt⟩, hsc1_lt⟩, hsc2_lt⟩, hu_lt⟩, hpos⟩, hprev⟩

/-- Complete specification of `sizeToClassUnits ((req + 3) / 16)` for every small/medium request
    `req ≤ 131051` (`req < MMAP_THRESHOLD`): returns `sc < 48` with `req ≤ nominalSlotCap sc` and
    minimal-class property `sc = 0 ∨ nominalSlotCap (sc - 1) < req`. -/
theorem sizeToClass_spec {req : Nat} (hreq : req ≤ 131051) :
    let u := (req + 3) / 16
    let sc := sizeToClassUnits u
    sc < 48 ∧ req ≤ nominalSlotCap sc ∧ (sc = 0 ∨ nominalSlotCap (sc - 1) < req) := by
  dsimp only
  by_cases hu : (req + 3) / 16 ≤ 9
  · have hsc_eq : sizeToClassUnits ((req + 3) / 16) = (req + 3) / 16 := by
      simp [sizeToClassUnits, hu]
    rw [hsc_eq]
    have hlt48 : (req + 3) / 16 < 48 := by omega
    have hcap_u : sizeClass ((req + 3) / 16) = (req + 3) / 16 + 1 := by
      rcases (by omega : (req + 3) / 16 = 0 ∨ (req + 3) / 16 = 1 ∨ (req + 3) / 16 = 2 ∨
          (req + 3) / 16 = 3 ∨ (req + 3) / 16 = 4 ∨ (req + 3) / 16 = 5 ∨
          (req + 3) / 16 = 6 ∨ (req + 3) / 16 = 7 ∨ (req + 3) / 16 = 8 ∨
          (req + 3) / 16 = 9) with h | h | h | h | h | h | h | h | h | h <;>
        (rw [h]; rfl)
    refine ⟨hlt48, ?_, ?_⟩
    · unfold nominalSlotCap
      rw [hcap_u]
      omega
    · by_cases h0 : (req + 3) / 16 = 0
      · exact Or.inl h0
      · right
        have hprev : sizeClass ((req + 3) / 16 - 1) = (req + 3) / 16 := by
          rcases (by omega : (req + 3) / 16 = 1 ∨ (req + 3) / 16 = 2 ∨
              (req + 3) / 16 = 3 ∨ (req + 3) / 16 = 4 ∨ (req + 3) / 16 = 5 ∨
              (req + 3) / 16 = 6 ∨ (req + 3) / 16 = 7 ∨ (req + 3) / 16 = 8 ∨
              (req + 3) / 16 = 9) with h | h | h | h | h | h | h | h | h <;>
            (rw [h]; rfl)
        unfold nominalSlotCap
        rw [hprev]
        omega
  · have hu_lo : 10 ≤ (req + 3) / 16 := by omega
    have hu_hi : (req + 3) / 16 ≤ 8190 := by omega
    have hok := sizeToClassLarge_spec hu_lo hu_hi
    have hsc_def : sizeToClassUnits ((req + 3) / 16) =
        (let u := (req + 3) / 16
         let idx := sizeToClassHashIdx u
         let b   := (debruijn32Table.getD idx 0#8).toNat
         let baseSc := (b - 1) * 4
         let sc1 := if u + 1 > sizeClass (baseSc + 1) then baseSc + 2 else baseSc
         if u + 1 > sizeClass sc1 then sc1 + 1 else sc1) := by
      simp [sizeToClassUnits, hu]
    unfold sizeToClassLargeOk at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hok
    have hsc_lt48 : sizeToClassUnits ((req + 3) / 16) < 48 := by
      rw [hsc_def]; exact h1
    have hu_lt_sc : (req + 3) / 16 < sizeClass (sizeToClassUnits ((req + 3) / 16)) := by
      rw [hsc_def]; exact h2
    have hsc_pos : 0 < sizeToClassUnits ((req + 3) / 16) := by
      rw [hsc_def]; exact h3
    have hprev_le : sizeClass (sizeToClassUnits ((req + 3) / 16) - 1) ≤ (req + 3) / 16 := by
      rw [hsc_def]; exact h4
    generalize sizeToClassUnits ((req + 3) / 16) = sc at hsc_lt48 hu_lt_sc hsc_pos hprev_le ⊢
    have hpos_prev : 1 ≤ sizeClass (sc - 1) :=
      (sizeClass_bounds (by omega)).1
    refine ⟨hsc_lt48, ?_, Or.inr ?_⟩
    · unfold nominalSlotCap
      omega
    · unfold nominalSlotCap
      omega

/-! ## De Bruijn `a_ctz_32` Bit-Scan Correctness -/

/-- De Bruijn `a_ctz_32(x)` bit-scan (`debruijn32[(x & -x) * 0x076be629 >> 27]`). -/
def ctz32DeBruijn (x : BitVec 32) : Nat :=
  let isolated := (-x) &&& x
  let hashIdx := ((isolated * 0x076be629#32) >>> 27).toNat
  (debruijn32Table.getD hashIdx 0#8).toNat

/-- Bit `k < 32` is the lowest set bit of `x`: `(-x) &&& x = 1#32 <<< k`, bit `k` of `x` is 1, and
    all lower bits `< k` are 0. -/
def IsLowestBit32 (x : BitVec 32) (k : Nat) : Prop :=
  (-x) &&& x = 1#32 <<< k ∧
  x &&& (1#32 <<< k) = 1#32 <<< k ∧
  x &&& ((1#32 <<< k) - 1#32) = 0#32

/-- Every non-zero `x : BitVec 32` has a lowest set bit `k < 32` isolated by
    `(-x) &&& x = 1#32 <<< k`. -/
theorem isolateLowestBit32_cases (x : BitVec 32) :
    x = 0#32 ∨
    IsLowestBit32 x 0  ∨ IsLowestBit32 x 1  ∨ IsLowestBit32 x 2  ∨ IsLowestBit32 x 3  ∨
    IsLowestBit32 x 4  ∨ IsLowestBit32 x 5  ∨ IsLowestBit32 x 6  ∨ IsLowestBit32 x 7  ∨
    IsLowestBit32 x 8  ∨ IsLowestBit32 x 9  ∨ IsLowestBit32 x 10 ∨ IsLowestBit32 x 11 ∨
    IsLowestBit32 x 12 ∨ IsLowestBit32 x 13 ∨ IsLowestBit32 x 14 ∨ IsLowestBit32 x 15 ∨
    IsLowestBit32 x 16 ∨ IsLowestBit32 x 17 ∨ IsLowestBit32 x 18 ∨ IsLowestBit32 x 19 ∨
    IsLowestBit32 x 20 ∨ IsLowestBit32 x 21 ∨ IsLowestBit32 x 22 ∨ IsLowestBit32 x 23 ∨
    IsLowestBit32 x 24 ∨ IsLowestBit32 x 25 ∨ IsLowestBit32 x 26 ∨ IsLowestBit32 x 27 ∨
    IsLowestBit32 x 28 ∨ IsLowestBit32 x 29 ∨ IsLowestBit32 x 30 ∨ IsLowestBit32 x 31 := by
  dsimp only [IsLowestBit32]
  bv_robdd

private theorem debruijn32_basis_all :
    (List.range 32).all (fun k =>
      let p : BitVec 32 := 1#32 <<< k
      let hashIdx := ((p * 0x076be629#32) >>> 27).toNat
      (hashIdx < 32) && ((debruijn32Table.getD hashIdx 0#8).toNat == k) &&
      ((-p) &&& p == p)) = true := by
  decide +kernel

private theorem debruijn32_of_basis {x : BitVec 32} {k : Nat} (hk : k < 32)
    (h : IsLowestBit32 x k) :
    let idx := ctz32DeBruijn x
    let hashIdx := ((((-x) &&& x) * 0x076be629#32) >>> 27).toNat
    idx = k ∧ idx < 32 ∧ hashIdx < 32 ∧
    (-x) &&& x = 1#32 <<< idx ∧
    (-((-x) &&& x)) &&& ((-x) &&& x) = (-x) &&& x ∧
    x &&& (1#32 <<< idx) = 1#32 <<< idx ∧
    x &&& ((1#32 <<< idx) - 1#32) = 0#32 ∧
    x &&& (~~~(-x)) = x &&& (~~~(1#32 <<< idx)) := by
  have hb := List.all_eq_true.mp debruijn32_basis_all k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
  obtain ⟨hisol, hbit, hlow⟩ := h
  have hidx : ctz32DeBruijn x = k := by
    unfold ctz32DeBruijn
    rw [hisol]
    exact hb.1.2
  have hclear : x &&& (~~~(-x)) = x &&& (~~~(1#32 <<< k)) := by
    have hid : ∀ y : BitVec 32, y &&& (~~~(-y)) = y &&& (~~~((-y) &&& y)) := by
      intro y; bv_robdd
    rw [hid x, hisol]
  dsimp only
  rw [hidx, hisol]
  exact ⟨rfl, hk, hb.1.1, rfl, hb.2, hbit, hlow, hclear⟩

/-- For every `x ≠ 0#32`, `ctz32DeBruijn x` computes the lowest set bit `idx < 32`, with
    `(-x) &&& x = 1#32 <<< idx ≠ 0#32` and `x &&& (~~~(-x)) = x &&& (~~~(1#32 <<< idx))`. -/
theorem ctz32DeBruijn_spec {x : BitVec 32} (hx : x ≠ 0#32) :
    let idx := ctz32DeBruijn x
    let hashIdx := ((((-x) &&& x) * 0x076be629#32) >>> 27).toNat
    (-x) &&& x ≠ 0#32 ∧
    idx < 32 ∧
    hashIdx < 32 ∧
    (-x) &&& x = 1#32 <<< idx ∧
    (-((-x) &&& x)) &&& ((-x) &&& x) = (-x) &&& x ∧
    x &&& (1#32 <<< idx) = 1#32 <<< idx ∧
    x &&& ((1#32 <<< idx) - 1#32) = 0#32 ∧
    x &&& (~~~(-x)) = x &&& (~~~(1#32 <<< idx)) := by
  have hnz : (-x) &&& x ≠ 0#32 := by bv_robdd
  refine ⟨hnz, ?_⟩
  rcases isolateLowestBit32_cases x with rfl |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact absurd rfl hx
  all_goals exact (debruijn32_of_basis (by decide) h).2

/-! ## `.rodata` `SepLoad` and Splitting Bridges -/

private theorem sizeClassBytes_pack16_all :
    (List.range 48).all (fun sc =>
      pack16 (sizeClassBytes.getD (2 * sc) 0#8) (sizeClassBytes.getD (2 * sc + 1) 0#8) ==
        BitVec.ofNat 16 (sizeClass sc)) = true := by
  decide +kernel

/-- Evaluates the `pack16` expression read by `ldrh` at offset `2 * sc` into `sizeClassBytes`. -/
@[simp]
theorem pack16_sizeClassBytes {sc : Nat} (hsc : sc < 48) :
    pack16 (sizeClassBytes.getD (2 * sc) 0#8) (sizeClassBytes.getD (2 * sc + 1) 0#8) =
      BitVec.ofNat 16 (sizeClass sc) := by
  have h := List.all_eq_true.mp sizeClassBytes_pack16_all sc (List.mem_range.mpr hsc)
  simpa only [beq_iff_eq] using h

/-- Decomposes `(roBase ↦ᵣ mallocngRoTablesBytes)` into the five `.rodata` table slices
    (`sizeClassBytes` at `+0x00`, `debruijn32Table` at `+0x60`, `medCntTabBytes` at `+0x80`,
    `smallCntTabBytes` at `+0x88`, and `debruijn32Table` at `+0xa8`) and their alignment padding. -/
theorem roTables_split (roBase : BitVec 64) :
    (roBase ↦ᵣ mallocngRoTablesBytes) =
      ((roBase ↦ᵣ sizeClassBytes) ∗
       ((roBase + 0x60#64) ↦ᵣ debruijn32Table) ∗
       ((roBase + 0x80#64) ↦ᵣ medCntTabBytes) ∗
       ((roBase + 0x84#64) ↦ᵣ List.replicate 4 0#8) ∗
       ((roBase + 0x88#64) ↦ᵣ smallCntTabBytes) ∗
       ((roBase + 0xa3#64) ↦ᵣ List.replicate 5 0#8) ∗
       ((roBase + 0xa8#64) ↦ᵣ debruijn32Table)) := by
  have heq : mallocngRoTablesBytes =
      sizeClassBytes ++ (debruijn32Table ++ (medCntTabBytes ++ (List.replicate 4 0#8 ++
        (smallCntTabBytes ++ (List.replicate 5 0#8 ++ debruijn32Table))))) := by
    simp [mallocngRoTablesBytes, List.append_assoc]
  rw [heq]
  rw [pointsToBytesRO_append, sizeClassBytes_length]
  rw [pointsToBytesRO_append, debruijn32Table_length]
  rw [pointsToBytesRO_append, medCntTabBytes_length]
  rw [pointsToBytesRO_append, List.length_replicate]
  rw [pointsToBytesRO_append, smallCntTabBytes_length]
  rw [pointsToBytesRO_append, List.length_replicate]
  have h1 : roBase + BitVec.ofNat 64 96 = roBase + 0x60#64 := by bv_lin
  have h2 : roBase + 0x60#64 + BitVec.ofNat 64 32 = roBase + 0x80#64 := by bv_lin
  have h3 : roBase + 0x80#64 + BitVec.ofNat 64 4 = roBase + 0x84#64 := by bv_lin
  have h4 : roBase + 0x84#64 + BitVec.ofNat 64 4 = roBase + 0x88#64 := by bv_lin
  have h5 : roBase + 0x88#64 + BitVec.ofNat 64 27 = roBase + 0xa3#64 := by bv_lin
  have h6 : roBase + 0xa3#64 + BitVec.ofNat 64 5 = roBase + 0xa8#64 := by bv_lin
  rw [h1, h2, h3, h4, h5, h6]

end VerifiedLibraries.Mallocng.Proofs
