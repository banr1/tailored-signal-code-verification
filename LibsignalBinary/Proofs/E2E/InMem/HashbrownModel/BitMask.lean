/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownModel.Group

/-!
# Hashbrown `BitMask` and `BitMaskIter` Lemmas

Bitvector lemmas for `hashbrown`'s 64-bit `BitMask` and `BitMaskIter` on AArch64
(`BITMASK_STRIDE = 8`, `BITMASK_ITER_MASK = 0x8080_8080_8080_8080`), modeling
`trailing_zeros() / 8` as `w.reverse.clz >>> 3`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownModel

/-- Trailing zeros of a 64-bit word, modeled via `(w.reverse).clz` (`RBIT` + `CLZ` on `aarch64`). -/
def ctz64 (w : BitVec 64) : BitVec 64 :=
  w.reverse.clz

/-- `BitMask::trailing_zeros`: `self.0.trailing_zeros() / BITMASK_STRIDE` (`(rbit w).clz >>> 3`). -/
def bitmaskTrailingZeros (w : BitVec 64) : Nat :=
  ((ctz64 w) >>> 3).toNat

/-- `BitMask::lowest_set_bit`: `if w = 0 then none else some (bitmaskTrailingZeros w)`. -/
def lowestSetBit (w : BitVec 64) : Option Nat :=
  if w = 0#64 then none else some (bitmaskTrailingZeros w)

/-- `BitMask::remove_lowest_bit`: `w & (w - 1)`. -/
def removeLowestBit (w : BitVec 64) : BitVec 64 :=
  w &&& (w - 1#64)

/-- `BitMask::any_bit_set`: `w != 0`. -/
def anyBitSet (w : BitVec 64) : Bool :=
  w != 0#64

/-- Canonical 8-lane iteration mask built from 8 lane booleans `b0..b7`:
lane `i` has bit `8 * i + 7` set (`0x80 <<< (8 * i)`) iff `bi = true`, and all other bits are `0`. -/
def mkIterMask (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : BitVec 64 :=
  packGroupWord
    (if b0 then 0x80#8 else 0x00#8)
    (if b1 then 0x80#8 else 0x00#8)
    (if b2 then 0x80#8 else 0x00#8)
    (if b3 then 0x80#8 else 0x00#8)
    (if b4 then 0x80#8 else 0x00#8)
    (if b5 then 0x80#8 else 0x00#8)
    (if b6 then 0x80#8 else 0x00#8)
    (if b7 then 0x80#8 else 0x00#8)

/-! ## Equivalence of NEON `match_* &&& bitmaskIterMask` and `mkIterMask` -/

private theorem zext_shift_and_bitmaskIterMask_0 (b : BitVec 8) :
    b.zeroExtend 64 &&& bitmaskIterMask = (if b.msb then 0x80#8 else 0x00#8).zeroExtend 64 := by
  revert b; decide

private theorem zext_shift_and_bitmaskIterMask_8 (b : BitVec 8) :
    (b.zeroExtend 64 <<< 8) &&& bitmaskIterMask = (if b.msb then 0x80#8 else 0x00#8).zeroExtend 64 <<< 8 := by
  revert b; decide

private theorem zext_shift_and_bitmaskIterMask_16 (b : BitVec 8) :
    (b.zeroExtend 64 <<< 16) &&& bitmaskIterMask = (if b.msb then 0x80#8 else 0x00#8).zeroExtend 64 <<< 16 := by
  revert b; decide

private theorem zext_shift_and_bitmaskIterMask_24 (b : BitVec 8) :
    (b.zeroExtend 64 <<< 24) &&& bitmaskIterMask = (if b.msb then 0x80#8 else 0x00#8).zeroExtend 64 <<< 24 := by
  revert b; decide

private theorem zext_shift_and_bitmaskIterMask_32 (b : BitVec 8) :
    (b.zeroExtend 64 <<< 32) &&& bitmaskIterMask = (if b.msb then 0x80#8 else 0x00#8).zeroExtend 64 <<< 32 := by
  revert b; decide

private theorem zext_shift_and_bitmaskIterMask_40 (b : BitVec 8) :
    (b.zeroExtend 64 <<< 40) &&& bitmaskIterMask = (if b.msb then 0x80#8 else 0x00#8).zeroExtend 64 <<< 40 := by
  revert b; decide

private theorem zext_shift_and_bitmaskIterMask_48 (b : BitVec 8) :
    (b.zeroExtend 64 <<< 48) &&& bitmaskIterMask = (if b.msb then 0x80#8 else 0x00#8).zeroExtend 64 <<< 48 := by
  revert b; decide

private theorem zext_shift_and_bitmaskIterMask_56 (b : BitVec 8) :
    (b.zeroExtend 64 <<< 56) &&& bitmaskIterMask = (if b.msb then 0x80#8 else 0x00#8).zeroExtend 64 <<< 56 := by
  revert b; decide

private theorem or_and_distrib_right (x y z : BitVec 64) :
    (x ||| y) &&& z = (x &&& z) ||| (y &&& z) := by
  ext k hk
  simp only [BitVec.getElem_and, BitVec.getElem_or]
  cases x[k] <;> cases y[k] <;> cases z[k] <;> rfl

theorem packGroupWord_and_bitmaskIterMask (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    packGroupWord b0 b1 b2 b3 b4 b5 b6 b7 &&& bitmaskIterMask =
      mkIterMask b0.msb b1.msb b2.msb b3.msb b4.msb b5.msb b6.msb b7.msb := by
  unfold packGroupWord mkIterMask
  simp only [or_and_distrib_right,
    zext_shift_and_bitmaskIterMask_0, zext_shift_and_bitmaskIterMask_8,
    zext_shift_and_bitmaskIterMask_16, zext_shift_and_bitmaskIterMask_24,
    zext_shift_and_bitmaskIterMask_32, zext_shift_and_bitmaskIterMask_40,
    zext_shift_and_bitmaskIterMask_48, zext_shift_and_bitmaskIterMask_56]
  rfl

@[simp]
private theorem msb_if_ff_00 (b : Bool) : (if b then 0xff#8 else 0x00#8).msb = b := by
  cases b <;> rfl

theorem neonMatchTag_and_bitmaskIterMask (w : BitVec 64) (tag : BitVec 8) :
    neonMatchTag w tag &&& bitmaskIterMask =
      mkIterMask
        (groupByte w 0 == tag) (groupByte w 1 == tag)
        (groupByte w 2 == tag) (groupByte w 3 == tag)
        (groupByte w 4 == tag) (groupByte w 5 == tag)
        (groupByte w 6 == tag) (groupByte w 7 == tag) := by
  unfold neonMatchTag
  rw [packGroupWord_and_bitmaskIterMask]
  simp only [msb_if_ff_00]

theorem neonMatchEmptyOrDeleted_and_bitmaskIterMask (w : BitVec 64) :
    neonMatchEmptyOrDeleted w &&& bitmaskIterMask =
      mkIterMask
        (groupByte w 0).msb (groupByte w 1).msb
        (groupByte w 2).msb (groupByte w 3).msb
        (groupByte w 4).msb (groupByte w 5).msb
        (groupByte w 6).msb (groupByte w 7).msb := by
  unfold neonMatchEmptyOrDeleted
  rw [packGroupWord_and_bitmaskIterMask]
  simp only [msb_if_ff_00]

theorem neonMatchFull_and_bitmaskIterMask (w : BitVec 64) :
    neonMatchFull w &&& bitmaskIterMask =
      mkIterMask
        (!(groupByte w 0).msb) (!(groupByte w 1).msb)
        (!(groupByte w 2).msb) (!(groupByte w 3).msb)
        (!(groupByte w 4).msb) (!(groupByte w 5).msb)
        (!(groupByte w 6).msb) (!(groupByte w 7).msb) := by
  unfold neonMatchFull
  rw [packGroupWord_and_bitmaskIterMask]
  simp only [msb_if_ff_00]

/-- Any word masked by `bitmaskIterMask` (`0x8080_8080_8080_8080`) is a `mkIterMask` of its 8 `laneSet` bits. -/
theorem and_bitmaskIterMask_eq_mkIterMask (m : BitVec 64) :
    m &&& bitmaskIterMask =
      mkIterMask
        (laneSet m 0) (laneSet m 1) (laneSet m 2) (laneSet m 3)
        (laneSet m 4) (laneSet m 5) (laneSet m 6) (laneSet m 7) := by
  conv => lhs; rw [← packGroupWord_groupByte m]
  rw [packGroupWord_and_bitmaskIterMask]
  simp only [laneSet_eq_groupByte_msb]

/-- Canonical 8-lane full byte mask (`0xff` in lane `i` iff `bi = true`, `0x00` otherwise),
matching raw NEON comparison outputs (`vceq_u8`, `vcltz_s8`, `vcgez_s8`) prior to `BITMASK_ITER_MASK`. -/
def mkFullMask (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : BitVec 64 :=
  packGroupWord
    (if b0 then 0xff#8 else 0x00#8)
    (if b1 then 0xff#8 else 0x00#8)
    (if b2 then 0xff#8 else 0x00#8)
    (if b3 then 0xff#8 else 0x00#8)
    (if b4 then 0xff#8 else 0x00#8)
    (if b5 then 0xff#8 else 0x00#8)
    (if b6 then 0xff#8 else 0x00#8)
    (if b7 then 0xff#8 else 0x00#8)

theorem neonMatchTag_eq_mkFullMask (w : BitVec 64) (tag : BitVec 8) :
    neonMatchTag w tag =
      mkFullMask
        (groupByte w 0 == tag) (groupByte w 1 == tag)
        (groupByte w 2 == tag) (groupByte w 3 == tag)
        (groupByte w 4 == tag) (groupByte w 5 == tag)
        (groupByte w 6 == tag) (groupByte w 7 == tag) := rfl

theorem neonMatchEmptyOrDeleted_eq_mkFullMask (w : BitVec 64) :
    neonMatchEmptyOrDeleted w =
      mkFullMask
        (groupByte w 0).msb (groupByte w 1).msb
        (groupByte w 2).msb (groupByte w 3).msb
        (groupByte w 4).msb (groupByte w 5).msb
        (groupByte w 6).msb (groupByte w 7).msb := rfl

theorem neonMatchFull_eq_mkFullMask (w : BitVec 64) :
    neonMatchFull w =
      mkFullMask
        (!(groupByte w 0).msb) (!(groupByte w 1).msb)
        (!(groupByte w 2).msb) (!(groupByte w 3).msb)
        (!(groupByte w 4).msb) (!(groupByte w 5).msb)
        (!(groupByte w 6).msb) (!(groupByte w 7).msb) := rfl

/-! ## `laneSet` on `mkIterMask` and `mkFullMask` -/

@[simp]
theorem laneSet_mkIterMask_0 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) 0 = b0 := by
  cases b0 <;> simp [laneSet_eq_groupByte_msb, mkIterMask]

@[simp]
theorem laneSet_mkIterMask_1 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) 1 = b1 := by
  cases b1 <;> simp [laneSet_eq_groupByte_msb, mkIterMask]

@[simp]
theorem laneSet_mkIterMask_2 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) 2 = b2 := by
  cases b2 <;> simp [laneSet_eq_groupByte_msb, mkIterMask]

@[simp]
theorem laneSet_mkIterMask_3 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) 3 = b3 := by
  cases b3 <;> simp [laneSet_eq_groupByte_msb, mkIterMask]

@[simp]
theorem laneSet_mkIterMask_4 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) 4 = b4 := by
  cases b4 <;> simp [laneSet_eq_groupByte_msb, mkIterMask]

@[simp]
theorem laneSet_mkIterMask_5 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) 5 = b5 := by
  cases b5 <;> simp [laneSet_eq_groupByte_msb, mkIterMask]

@[simp]
theorem laneSet_mkIterMask_6 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) 6 = b6 := by
  cases b6 <;> simp [laneSet_eq_groupByte_msb, mkIterMask]

@[simp]
theorem laneSet_mkIterMask_7 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) 7 = b7 := by
  cases b7 <;> simp [laneSet_eq_groupByte_msb, mkIterMask]

@[simp]
theorem laneSet_mkFullMask_0 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) 0 = b0 := by
  cases b0 <;> simp [laneSet_eq_groupByte_msb, mkFullMask]

@[simp]
theorem laneSet_mkFullMask_1 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) 1 = b1 := by
  cases b1 <;> simp [laneSet_eq_groupByte_msb, mkFullMask]

@[simp]
theorem laneSet_mkFullMask_2 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) 2 = b2 := by
  cases b2 <;> simp [laneSet_eq_groupByte_msb, mkFullMask]

@[simp]
theorem laneSet_mkFullMask_3 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) 3 = b3 := by
  cases b3 <;> simp [laneSet_eq_groupByte_msb, mkFullMask]

@[simp]
theorem laneSet_mkFullMask_4 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) 4 = b4 := by
  cases b4 <;> simp [laneSet_eq_groupByte_msb, mkFullMask]

@[simp]
theorem laneSet_mkFullMask_5 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) 5 = b5 := by
  cases b5 <;> simp [laneSet_eq_groupByte_msb, mkFullMask]

@[simp]
theorem laneSet_mkFullMask_6 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) 6 = b6 := by
  cases b6 <;> simp [laneSet_eq_groupByte_msb, mkFullMask]

@[simp]
theorem laneSet_mkFullMask_7 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) 7 = b7 := by
  cases b7 <;> simp [laneSet_eq_groupByte_msb, mkFullMask]

/-! ## `firstTrueLane`: Lowest Set Bit / Trailing Zeros Div 8 = First Matching Lane -/

/-- Index of the first `true` boolean among 8 lanes `b0..b7`, or `none` if all are `false`. -/
def firstTrueLane (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Option Nat :=
  if b0 then some 0
  else if b1 then some 1
  else if b2 then some 2
  else if b3 then some 3
  else if b4 then some 4
  else if b5 then some 5
  else if b6 then some 6
  else if b7 then some 7
  else none

set_option maxRecDepth 4096 in
/-- `lowestSetBit` on `mkIterMask` (`0x80` per matching lane) equals `firstTrueLane`. -/
theorem lowestSetBit_mkIterMask (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    lowestSetBit (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) =
      firstTrueLane b0 b1 b2 b3 b4 b5 b6 b7 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
  cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl

set_option maxRecDepth 4096 in
/-- `lowestSetBit` on `mkFullMask` (`0xff` per matching lane, as produced by `vcltz_s8` / `vceq_u8`
prior to `BITMASK_ITER_MASK`) also equals `firstTrueLane`. -/
theorem lowestSetBit_mkFullMask (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    lowestSetBit (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) =
      firstTrueLane b0 b1 b2 b3 b4 b5 b6 b7 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
  cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl

theorem mkIterMask_eq_zero_iff (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    mkIterMask b0 b1 b2 b3 b4 b5 b6 b7 = 0#64 ↔
      (b0 = false ∧ b1 = false ∧ b2 = false ∧ b3 = false ∧
       b4 = false ∧ b5 = false ∧ b6 = false ∧ b7 = false) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
  cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> decide

theorem mkFullMask_eq_zero_iff (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    mkFullMask b0 b1 b2 b3 b4 b5 b6 b7 = 0#64 ↔
      (b0 = false ∧ b1 = false ∧ b2 = false ∧ b3 = false ∧
       b4 = false ∧ b5 = false ∧ b6 = false ∧ b7 = false) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
  cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> decide

theorem anyBitSet_mkFullMask (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    anyBitSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) =
      (b0 || b1 || b2 || b3 || b4 || b5 || b6 || b7) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
  cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl

theorem anyBitSet_mkIterMask (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    anyBitSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) =
      (b0 || b1 || b2 || b3 || b4 || b5 || b6 || b7) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
  cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl

/-- `anyBitSet (neonMatchEmpty w)` equals `(neonUmaxv8 (neonMatchEmpty w)).getLsbD 0`
(confirming that `umaxv` + `tbnz w8, #0` in the compiled binary implements `match_empty().any_bit_set()`). -/
theorem anyBitSet_neonMatchEmpty_eq_umaxv (w : BitVec 64) :
    anyBitSet (neonMatchEmpty w) = (neonUmaxv8 (neonMatchEmpty w)).getLsbD 0 := by
  rw [neonUmaxv8_neonMatchEmpty_getLsbD_zero]
  unfold neonMatchEmpty
  rw [neonMatchTag_eq_mkFullMask, anyBitSet_mkFullMask]

/-- Characterization of `lowestSetBit (m &&& bitmaskIterMask) = some i`:
`i` is the first matching lane (`i < 8`, `laneSet m i = true`, and `∀ j < i, laneSet m j = false`). -/
theorem lowestSetBit_and_bitmaskIterMask_eq_some_iff (m : BitVec 64) (i : Nat) :
    lowestSetBit (m &&& bitmaskIterMask) = some i ↔
      i < 8 ∧ laneSet m i = true ∧ ∀ j < i, laneSet m j = false := by
  rw [and_bitmaskIterMask_eq_mkIterMask m, lowestSetBit_mkIterMask]
  generalize h0 : laneSet m 0 = b0, h1 : laneSet m 1 = b1,
             h2 : laneSet m 2 = b2, h3 : laneSet m 3 = b3,
             h4 : laneSet m 4 = b4, h5 : laneSet m 5 = b5,
             h6 : laneSet m 6 = b6, h7 : laneSet m 7 = b7
  constructor
  · intro h
    cases b0
    · cases b1
      · cases b2
        · cases b3
          · cases b4
            · cases b5
              · cases b6
                · cases b7
                  · simp [firstTrueLane] at h
                  · simp [firstTrueLane] at h; subst h
                    refine ⟨by decide, h7, fun j hj => ?_⟩
                    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
                      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
                · simp [firstTrueLane] at h; subst h
                  refine ⟨by decide, h6, fun j hj => ?_⟩
                  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
                    rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
              · simp [firstTrueLane] at h; subst h
                refine ⟨by decide, h5, fun j hj => ?_⟩
                rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with
                  rfl | rfl | rfl | rfl | rfl <;> assumption
            · simp [firstTrueLane] at h; subst h
              refine ⟨by decide, h4, fun j hj => ?_⟩
              rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with
                rfl | rfl | rfl | rfl <;> assumption
          · simp [firstTrueLane] at h; subst h
            refine ⟨by decide, h3, fun j hj => ?_⟩
            rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> assumption
        · simp [firstTrueLane] at h; subst h
          refine ⟨by decide, h2, fun j hj => ?_⟩
          rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> assumption
      · simp [firstTrueLane] at h; subst h
        refine ⟨by decide, h1, fun j hj => ?_⟩
        have : j = 0 := by omega
        subst this; exact h0
    · simp [firstTrueLane] at h; subst h
      exact ⟨by decide, h0, fun j hj => by omega⟩
  · rintro ⟨hi, hset, hprev⟩
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h0] at hset; simp [firstTrueLane, hset]
    · have p0 : b0 = false := by rw [← h0]; exact hprev 0 (by omega)
      rw [h1] at hset; simp [firstTrueLane, p0, hset]
    · have p0 : b0 = false := by rw [← h0]; exact hprev 0 (by omega)
      have p1 : b1 = false := by rw [← h1]; exact hprev 1 (by omega)
      rw [h2] at hset; simp [firstTrueLane, p0, p1, hset]
    · have p0 : b0 = false := by rw [← h0]; exact hprev 0 (by omega)
      have p1 : b1 = false := by rw [← h1]; exact hprev 1 (by omega)
      have p2 : b2 = false := by rw [← h2]; exact hprev 2 (by omega)
      rw [h3] at hset; simp [firstTrueLane, p0, p1, p2, hset]
    · have p0 : b0 = false := by rw [← h0]; exact hprev 0 (by omega)
      have p1 : b1 = false := by rw [← h1]; exact hprev 1 (by omega)
      have p2 : b2 = false := by rw [← h2]; exact hprev 2 (by omega)
      have p3 : b3 = false := by rw [← h3]; exact hprev 3 (by omega)
      rw [h4] at hset; simp [firstTrueLane, p0, p1, p2, p3, hset]
    · have p0 : b0 = false := by rw [← h0]; exact hprev 0 (by omega)
      have p1 : b1 = false := by rw [← h1]; exact hprev 1 (by omega)
      have p2 : b2 = false := by rw [← h2]; exact hprev 2 (by omega)
      have p3 : b3 = false := by rw [← h3]; exact hprev 3 (by omega)
      have p4 : b4 = false := by rw [← h4]; exact hprev 4 (by omega)
      rw [h5] at hset; simp [firstTrueLane, p0, p1, p2, p3, p4, hset]
    · have p0 : b0 = false := by rw [← h0]; exact hprev 0 (by omega)
      have p1 : b1 = false := by rw [← h1]; exact hprev 1 (by omega)
      have p2 : b2 = false := by rw [← h2]; exact hprev 2 (by omega)
      have p3 : b3 = false := by rw [← h3]; exact hprev 3 (by omega)
      have p4 : b4 = false := by rw [← h4]; exact hprev 4 (by omega)
      have p5 : b5 = false := by rw [← h5]; exact hprev 5 (by omega)
      rw [h6] at hset; simp [firstTrueLane, p0, p1, p2, p3, p4, p5, hset]
    · have p0 : b0 = false := by rw [← h0]; exact hprev 0 (by omega)
      have p1 : b1 = false := by rw [← h1]; exact hprev 1 (by omega)
      have p2 : b2 = false := by rw [← h2]; exact hprev 2 (by omega)
      have p3 : b3 = false := by rw [← h3]; exact hprev 3 (by omega)
      have p4 : b4 = false := by rw [← h4]; exact hprev 4 (by omega)
      have p5 : b5 = false := by rw [← h5]; exact hprev 5 (by omega)
      have p6 : b6 = false := by rw [← h6]; exact hprev 6 (by omega)
      rw [h7] at hset; simp [firstTrueLane, p0, p1, p2, p3, p4, p5, p6, hset]

theorem lowestSetBit_and_bitmaskIterMask_eq_none_iff (m : BitVec 64) :
    lowestSetBit (m &&& bitmaskIterMask) = none ↔ ∀ i < 8, laneSet m i = false := by
  rw [and_bitmaskIterMask_eq_mkIterMask m, lowestSetBit_mkIterMask]
  generalize h0 : laneSet m 0 = b0, h1 : laneSet m 1 = b1,
             h2 : laneSet m 2 = b2, h3 : laneSet m 3 = b3,
             h4 : laneSet m 4 = b4, h5 : laneSet m 5 = b5,
             h6 : laneSet m 6 = b6, h7 : laneSet m 7 = b7
  constructor
  · intro h i hi
    cases b0
    · cases b1
      · cases b2
        · cases b3
          · cases b4
            · cases b5
              · cases b6
                · cases b7
                  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
                      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
                  · simp [firstTrueLane] at h
                · simp [firstTrueLane] at h
              · simp [firstTrueLane] at h
            · simp [firstTrueLane] at h
          · simp [firstTrueLane] at h
        · simp [firstTrueLane] at h
      · simp [firstTrueLane] at h
    · simp [firstTrueLane] at h
  · intro h
    have p0 : b0 = false := by rw [← h0]; exact h 0 (by omega)
    have p1 : b1 = false := by rw [← h1]; exact h 1 (by omega)
    have p2 : b2 = false := by rw [← h2]; exact h 2 (by omega)
    have p3 : b3 = false := by rw [← h3]; exact h 3 (by omega)
    have p4 : b4 = false := by rw [← h4]; exact h 4 (by omega)
    have p5 : b5 = false := by rw [← h5]; exact h 5 (by omega)
    have p6 : b6 = false := by rw [← h6]; exact h 6 (by omega)
    have p7 : b7 = false := by rw [← h7]; exact h 7 (by omega)
    simp [firstTrueLane, p0, p1, p2, p3, p4, p5, p6, p7]

/-- `lowestSetBit` on `neonMatchEmptyOrDeleted w` (used directly without `bitmaskIterMask` in
`find_insert_index_in_group` and `fix_insert_index`) equals `lowestSetBit (neonMatchEmptyOrDeleted w &&& bitmaskIterMask)`. -/
theorem lowestSetBit_neonMatchEmptyOrDeleted (w : BitVec 64) :
    lowestSetBit (neonMatchEmptyOrDeleted w) =
      lowestSetBit (neonMatchEmptyOrDeleted w &&& bitmaskIterMask) := by
  rw [neonMatchEmptyOrDeleted_and_bitmaskIterMask, neonMatchEmptyOrDeleted_eq_mkFullMask,
      lowestSetBit_mkFullMask, lowestSetBit_mkIterMask]

/-- `lowestSetBit (neonMatchEmptyOrDeleted w) = some i` iff `i < 8` is the first lane whose byte has
`msb = true` (`EMPTY` or `DELETED`). -/
theorem lowestSetBit_neonMatchEmptyOrDeleted_eq_some_iff (w : BitVec 64) (i : Nat) :
    lowestSetBit (neonMatchEmptyOrDeleted w) = some i ↔
      i < 8 ∧ (groupByte w i).msb = true ∧ ∀ j < i, (groupByte w j).msb = false := by
  rw [lowestSetBit_neonMatchEmptyOrDeleted, lowestSetBit_and_bitmaskIterMask_eq_some_iff]
  constructor
  · rintro ⟨hi, hset, hprev⟩
    refine ⟨hi, ?_, ?_⟩
    · rwa [laneSet_neonMatchEmptyOrDeleted w i hi] at hset
    · intro j hj
      have hj8 : j < 8 := by omega
      have := hprev j hj
      rwa [laneSet_neonMatchEmptyOrDeleted w j hj8] at this
  · rintro ⟨hi, hset, hprev⟩
    refine ⟨hi, ?_, ?_⟩
    · rwa [laneSet_neonMatchEmptyOrDeleted w i hi]
    · intro j hj
      have hj8 : j < 8 := by omega
      rw [laneSet_neonMatchEmptyOrDeleted w j hj8]
      exact hprev j hj

/-! ## `BitMask::remove_lowest_bit` (`w &&& (w - 1#64)`) Removes the Lowest Lane -/

/-- Clear the first `true` lane in an 8-lane iteration mask `mkIterMask b0..b7`. -/
def clearFirstTrueLane (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : BitVec 64 :=
  if b0 then mkIterMask false b1 b2 b3 b4 b5 b6 b7
  else if b1 then mkIterMask false false b2 b3 b4 b5 b6 b7
  else if b2 then mkIterMask false false false b3 b4 b5 b6 b7
  else if b3 then mkIterMask false false false false b4 b5 b6 b7
  else if b4 then mkIterMask false false false false false b5 b6 b7
  else if b5 then mkIterMask false false false false false false b6 b7
  else if b6 then mkIterMask false false false false false false false b7
  else 0#64

/-- `removeLowestBit` (`w &&& (w - 1#64)`) on `mkIterMask b0..b7` clears the first `true` lane. -/
theorem removeLowestBit_mkIterMask (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    removeLowestBit (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) =
      clearFirstTrueLane b0 b1 b2 b3 b4 b5 b6 b7 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
  cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl

/-- `removeLowestBit` preserves the `bitmaskIterMask` invariant (`m &&& bitmaskIterMask = m`). -/
theorem removeLowestBit_and_bitmaskIterMask (m : BitVec 64) :
    removeLowestBit (m &&& bitmaskIterMask) &&& bitmaskIterMask =
      removeLowestBit (m &&& bitmaskIterMask) := by
  rw [and_bitmaskIterMask_eq_mkIterMask m]
  generalize laneSet m 0 = b0, laneSet m 1 = b1, laneSet m 2 = b2, laneSet m 3 = b3,
             laneSet m 4 = b4, laneSet m 5 = b5, laneSet m 6 = b6, laneSet m 7 = b7
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
  cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl

private theorem laneSet_clearFirstTrueLane (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) (i j : Nat)
    (hi : firstTrueLane b0 b1 b2 b3 b4 b5 b6 b7 = some i) (hj : j < 8) :
    laneSet (clearFirstTrueLane b0 b1 b2 b3 b4 b5 b6 b7) j =
      (if j = i then false else laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) j) := by
  cases b0
  · cases b1
    · cases b2
      · cases b3
        · cases b4
          · cases b5
            · cases b6
              · cases b7
                · simp [firstTrueLane] at hi
                · simp [firstTrueLane] at hi; subst hi
                  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
                    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
              · simp [firstTrueLane] at hi; subst hi
                rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
                  rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [clearFirstTrueLane]
            · simp [firstTrueLane] at hi; subst hi
              rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [clearFirstTrueLane]
          · simp [firstTrueLane] at hi; subst hi
            rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
              rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [clearFirstTrueLane]
        · simp [firstTrueLane] at hi; subst hi
          rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [clearFirstTrueLane]
      · simp [firstTrueLane] at hi; subst hi
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [clearFirstTrueLane]
    · simp [firstTrueLane] at hi; subst hi
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [clearFirstTrueLane]
  · simp [firstTrueLane] at hi; subst hi
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [clearFirstTrueLane]

/-- If `lowestSetBit (m &&& bitmaskIterMask) = some i`, then `removeLowestBit (m &&& bitmaskIterMask)`
clears lane `i` and leaves every other lane `j < 8` (`j ≠ i`) unchanged. -/
theorem laneSet_removeLowestBit_of_lowestSetBit_eq_some (m : BitVec 64) (i j : Nat)
    (hi : lowestSetBit (m &&& bitmaskIterMask) = some i) (hj : j < 8) :
    laneSet (removeLowestBit (m &&& bitmaskIterMask)) j =
      (if j = i then false else laneSet m j) := by
  rw [and_bitmaskIterMask_eq_mkIterMask m] at hi ⊢
  rw [lowestSetBit_mkIterMask] at hi
  rw [removeLowestBit_mkIterMask]
  rw [laneSet_clearFirstTrueLane _ _ _ _ _ _ _ _ i j hi hj]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-! ## Single-Lane `laneBit` / `laneFullMask` and Zero `BitMask` Concrete Lemmas -/

@[simp]
theorem lowestSetBit_zero : lowestSetBit 0#64 = none := rfl

@[simp]
theorem removeLowestBit_zero : removeLowestBit 0#64 = 0#64 := rfl

@[simp]
theorem anyBitSet_zero : anyBitSet 0#64 = false := rfl

@[simp]
theorem mkIterMask_all_false :
    mkIterMask false false false false false false false false = 0#64 := rfl

@[simp]
theorem mkFullMask_all_false :
    mkFullMask false false false false false false false false = 0#64 := rfl

theorem mkIterMask_single (i : Nat) (hi : i < 8) :
    mkIterMask (i == 0) (i == 1) (i == 2) (i == 3)
               (i == 4) (i == 5) (i == 6) (i == 7) = laneBit i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem mkFullMask_single (i : Nat) (hi : i < 8) :
    mkFullMask (i == 0) (i == 1) (i == 2) (i == 3)
               (i == 4) (i == 5) (i == 6) (i == 7) = laneFullMask i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp]
theorem laneBit_ne_zero (i : Nat) (hi : i < 8) : laneBit i ≠ 0#64 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

@[simp]
theorem anyBitSet_laneBit (i : Nat) (hi : i < 8) : anyBitSet (laneBit i) = true := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp]
theorem laneBit_and_bitmaskIterMask (i : Nat) (hi : i < 8) :
    laneBit i &&& bitmaskIterMask = laneBit i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp]
theorem laneFullMask_and_bitmaskIterMask (i : Nat) (hi : i < 8) :
    laneFullMask i &&& bitmaskIterMask = laneBit i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
@[simp]
theorem bitmaskTrailingZeros_laneBit (i : Nat) (hi : i < 8) :
    bitmaskTrailingZeros (laneBit i) = i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
@[simp]
theorem lowestSetBit_laneBit (i : Nat) (hi : i < 8) :
    lowestSetBit (laneBit i) = some i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp]
theorem removeLowestBit_laneBit (i : Nat) (hi : i < 8) :
    removeLowestBit (laneBit i) = 0#64 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
@[simp]
theorem bitmaskTrailingZeros_laneFullMask (i : Nat) (hi : i < 8) :
    bitmaskTrailingZeros (laneFullMask i) = i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
@[simp]
theorem lowestSetBit_laneFullMask (i : Nat) (hi : i < 8) :
    lowestSetBit (laneFullMask i) = some i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end CryptoVerification.E2E.InMem.HashbrownModel
