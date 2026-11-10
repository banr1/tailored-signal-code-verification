/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

/-!
# Hashbrown 8-Byte Control-Group Lemmas

Bitvector definitions and lane characterizations for `hashbrown`'s 8-byte NEON and scalar SWAR
control-group operations (`Group::WIDTH = 8`).
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownModel

/-- `hashbrown`'s `Group::WIDTH` on `aarch64` (8 control bytes per group). -/
abbrev groupWidth : Nat := 8

abbrev emptyTag : BitVec 8 := 0xff#8

abbrev deletedTag : BitVec 8 := 0x80#8

/-- `BITMASK_STRIDE = 8`: each control byte occupies an 8-bit lane in the 64-bit `BitMask`. -/
abbrev bitmaskStride : Nat := 8

/-- `BITMASK_ITER_MASK = 0x8080_8080_8080_8080`: keeps the MSB (bit 7) of each 8-bit lane. -/
abbrev bitmaskIterMask : BitVec 64 := 0x8080808080808080#64

/-- `Tag::is_full`: a control byte represents a full bucket iff its top bit (MSB) is clear. -/
def isFullTag (b : BitVec 8) : Bool := !b.msb

/-- `Tag::is_special`: a control byte represents `EMPTY` or `DELETED` iff its top bit is set. -/
def isSpecialTag (b : BitVec 8) : Bool := b.msb

/-- `Tag::full(hash)`: top 7 bits of a 64-bit hash, with MSB = 0 (`(hash >> 57) & 0x7f`). -/
def h2Tag (hash : BitVec 64) : BitVec 8 :=
  (hash >>> 57).truncate 8 &&& 0x7f#8

/-- Primary hash `h1(hash)`: the full 64-bit hash word. -/
def h1Word (hash : BitVec 64) : BitVec 64 := hash

/-- Extract byte lane `i` (`0 ≤ i < 8`) from a 64-bit little-endian group word. -/
def groupByte (w : BitVec 64) (i : Nat) : BitVec 8 :=
  w.extractLsb' (8 * i) 8

/-- Pack 8 control bytes `b0..b7` into a 64-bit little-endian group word (byte `0` in bits `0..7`). -/
def packGroupWord (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b0.zeroExtend 64 |||
  (b1.zeroExtend 64 <<< 8) |||
  (b2.zeroExtend 64 <<< 16) |||
  (b3.zeroExtend 64 <<< 24) |||
  (b4.zeroExtend 64 <<< 32) |||
  (b5.zeroExtend 64 <<< 40) |||
  (b6.zeroExtend 64 <<< 48) |||
  (b7.zeroExtend 64 <<< 56)

/-- Replicate an 8-bit tag across all 8 lanes of a 64-bit word (`vdup_n_u8(tag)` / `repeat(tag)`). -/
def repeatByte (b : BitVec 8) : BitVec 64 :=
  packGroupWord b b b b b b b b

/-- Extract the 8-bit mask for lane `i` (`0x80` in lane `i`, `0x00` elsewhere). -/
def laneBit (i : Nat) : BitVec 64 :=
  (0x80#64) <<< (8 * i)

/-- Extract the full 8-bit lane mask (`0xff` in lane `i`, `0x00` elsewhere). -/
def laneFullMask (i : Nat) : BitVec 64 :=
  (0xff#64) <<< (8 * i)

/-- NEON bytewise equality (`vceq_u8(w, vdup_n_u8(tag))` / `cmeq v0.8b, v0.8b, v1.8b`):
lane `i` is `0xff` if `groupByte w i == tag`, else `0x00`. -/
def neonMatchTag (w : BitVec 64) (tag : BitVec 8) : BitVec 64 :=
  packGroupWord
    (if groupByte w 0 == tag then 0xff#8 else 0x00#8)
    (if groupByte w 1 == tag then 0xff#8 else 0x00#8)
    (if groupByte w 2 == tag then 0xff#8 else 0x00#8)
    (if groupByte w 3 == tag then 0xff#8 else 0x00#8)
    (if groupByte w 4 == tag then 0xff#8 else 0x00#8)
    (if groupByte w 5 == tag then 0xff#8 else 0x00#8)
    (if groupByte w 6 == tag then 0xff#8 else 0x00#8)
    (if groupByte w 7 == tag then 0xff#8 else 0x00#8)

/-- NEON `match_empty`: `vceq_u8(w, vdup_n_u8(0xff))` (`cmtst` / `cmeq` against `0xff`). -/
def neonMatchEmpty (w : BitVec 64) : BitVec 64 :=
  neonMatchTag w emptyTag

/-- NEON `match_empty_or_deleted`: `vcltz_s8(w)` (`cmlt v0.8b, v0.8b, #0`):
lane `i` is `0xff` iff `(groupByte w i).msb = true` (signed `< 0`), else `0x00`. -/
def neonMatchEmptyOrDeleted (w : BitVec 64) : BitVec 64 :=
  packGroupWord
    (if (groupByte w 0).msb then 0xff#8 else 0x00#8)
    (if (groupByte w 1).msb then 0xff#8 else 0x00#8)
    (if (groupByte w 2).msb then 0xff#8 else 0x00#8)
    (if (groupByte w 3).msb then 0xff#8 else 0x00#8)
    (if (groupByte w 4).msb then 0xff#8 else 0x00#8)
    (if (groupByte w 5).msb then 0xff#8 else 0x00#8)
    (if (groupByte w 6).msb then 0xff#8 else 0x00#8)
    (if (groupByte w 7).msb then 0xff#8 else 0x00#8)

/-- NEON `match_full`: `vcgez_s8(w)` (`cmge v0.8b, v0.8b, #0`):
lane `i` is `0xff` iff `(groupByte w i).msb = false` (signed `≥ 0`), else `0x00`. -/
def neonMatchFull (w : BitVec 64) : BitVec 64 :=
  packGroupWord
    (if !(groupByte w 0).msb then 0xff#8 else 0x00#8)
    (if !(groupByte w 1).msb then 0xff#8 else 0x00#8)
    (if !(groupByte w 2).msb then 0xff#8 else 0x00#8)
    (if !(groupByte w 3).msb then 0xff#8 else 0x00#8)
    (if !(groupByte w 4).msb then 0xff#8 else 0x00#8)
    (if !(groupByte w 5).msb then 0xff#8 else 0x00#8)
    (if !(groupByte w 6).msb then 0xff#8 else 0x00#8)
    (if !(groupByte w 7).msb then 0xff#8 else 0x00#8)

/-- Scalar SWAR (`generic.rs`) `match_tag`:
`let cmp = w ^ repeat(tag); (cmp.wrapping_sub(0x0101_0101_0101_0101) & !cmp & 0x8080_8080_8080_8080)`. -/
def swarMatchTag (w : BitVec 64) (tag : BitVec 8) : BitVec 64 :=
  let cmp := w ^^^ repeatByte tag
  (cmp - 0x0101010101010101#64) &&& (~~~cmp) &&& 0x8080808080808080#64

/-- Scalar SWAR (`generic.rs`) `match_empty`:
`w & (w << 1) & 0x8080_8080_8080_8080`. -/
def swarMatchEmpty (w : BitVec 64) : BitVec 64 :=
  w &&& (w <<< 1) &&& 0x8080808080808080#64

/-- Scalar SWAR (`generic.rs`) `match_empty_or_deleted`:
`w & 0x8080_8080_8080_8080`. -/
def swarMatchEmptyOrDeleted (w : BitVec 64) : BitVec 64 :=
  w &&& 0x8080808080808080#64

/-- Scalar SWAR (`generic.rs`) `match_full`:
`(w & 0x8080_8080_8080_8080) ^ 0x8080_8080_8080_8080`. -/
def swarMatchFull (w : BitVec 64) : BitVec 64 :=
  (w &&& 0x8080808080808080#64) ^^^ 0x8080808080808080#64

/-! ## Basic `h2Tag` / `isFullTag` / `isSpecialTag` Lemmas -/

@[simp]
theorem emptyTag_msb : emptyTag.msb = true := rfl

@[simp]
theorem deletedTag_msb : deletedTag.msb = true := rfl

@[simp]
theorem isFullTag_emptyTag : isFullTag emptyTag = false := rfl

@[simp]
theorem isFullTag_deletedTag : isFullTag deletedTag = false := rfl

@[simp]
theorem isSpecialTag_emptyTag : isSpecialTag emptyTag = true := rfl

@[simp]
theorem isSpecialTag_deletedTag : isSpecialTag deletedTag = true := rfl

theorem h2Tag_msb (hash : BitVec 64) : (h2Tag hash).msb = false := by
  simp [h2Tag, BitVec.msb_eq_getLsbD_last]

@[simp]
theorem isFullTag_h2Tag (hash : BitVec 64) : isFullTag (h2Tag hash) = true := by
  simp [isFullTag, h2Tag_msb]

@[simp]
theorem isSpecialTag_h2Tag (hash : BitVec 64) : isSpecialTag (h2Tag hash) = false := by
  simp [isSpecialTag, h2Tag_msb]

theorem h2Tag_ne_emptyTag (hash : BitVec 64) : h2Tag hash ≠ emptyTag := by
  intro h
  have := congrArg BitVec.msb h
  rw [h2Tag_msb, emptyTag_msb] at this
  exact Bool.false_ne_true this

theorem h2Tag_ne_deletedTag (hash : BitVec 64) : h2Tag hash ≠ deletedTag := by
  intro h
  have := congrArg BitVec.msb h
  rw [h2Tag_msb, deletedTag_msb] at this
  exact Bool.false_ne_true this

/-! ## Extracting Bytes from `packGroupWord` -/

@[simp]
theorem groupByte_packGroupWord_0 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    groupByte (packGroupWord b0 b1 b2 b3 b4 b5 b6 b7) 0 = b0 := by
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [groupByte, packGroupWord]

@[simp]
theorem groupByte_packGroupWord_1 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    groupByte (packGroupWord b0 b1 b2 b3 b4 b5 b6 b7) 1 = b1 := by
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [groupByte, packGroupWord]

@[simp]
theorem groupByte_packGroupWord_2 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    groupByte (packGroupWord b0 b1 b2 b3 b4 b5 b6 b7) 2 = b2 := by
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [groupByte, packGroupWord]

@[simp]
theorem groupByte_packGroupWord_3 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    groupByte (packGroupWord b0 b1 b2 b3 b4 b5 b6 b7) 3 = b3 := by
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [groupByte, packGroupWord]

@[simp]
theorem groupByte_packGroupWord_4 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    groupByte (packGroupWord b0 b1 b2 b3 b4 b5 b6 b7) 4 = b4 := by
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [groupByte, packGroupWord]

@[simp]
theorem groupByte_packGroupWord_5 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    groupByte (packGroupWord b0 b1 b2 b3 b4 b5 b6 b7) 5 = b5 := by
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [groupByte, packGroupWord]

@[simp]
theorem groupByte_packGroupWord_6 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    groupByte (packGroupWord b0 b1 b2 b3 b4 b5 b6 b7) 6 = b6 := by
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [groupByte, packGroupWord]

@[simp]
theorem groupByte_packGroupWord_7 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    groupByte (packGroupWord b0 b1 b2 b3 b4 b5 b6 b7) 7 = b7 := by
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [groupByte, packGroupWord]

theorem packGroupWord_groupByte (w : BitVec 64) :
    packGroupWord
      (groupByte w 0) (groupByte w 1) (groupByte w 2) (groupByte w 3)
      (groupByte w 4) (groupByte w 5) (groupByte w 6) (groupByte w 7) = w := by
  ext j hj
  rcases (by omega :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
    j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨
    j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨
    j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 ∨
    j = 32 ∨ j = 33 ∨ j = 34 ∨ j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 ∨
    j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨ j = 45 ∨ j = 46 ∨ j = 47 ∨
    j = 48 ∨ j = 49 ∨ j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨ j = 55 ∨
    j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 ∨ j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [packGroupWord, groupByte]

/-! ## NEON Group Match Byte-Lane Characterization (`neon.rs`) -/

/-- Whether lane `i` (`0 ≤ i < 8`) is active in a `BitMask` after applying `BITMASK_ITER_MASK`
(`0x8080_8080_8080_8080`): bit `8 * i + 7` is set. -/
def laneSet (m : BitVec 64) (i : Nat) : Bool :=
  m.getLsbD (8 * i + 7)

/-- Applying `BITMASK_ITER_MASK` (`0x8080_8080_8080_8080`) preserves `laneSet` for every lane `i < 8`. -/
theorem laneSet_and_bitmaskIterMask (m : BitVec 64) (i : Nat) (hi : i < 8) :
    laneSet (m &&& bitmaskIterMask) i = laneSet m i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [laneSet, bitmaskIterMask]

/-- Outside the 8 lane MSB positions (`8 * i + 7`), `m &&& bitmaskIterMask` has all bits `false`. -/
theorem getLsbD_and_bitmaskIterMask_of_mod_ne (m : BitVec 64) (k : Nat) (hk : k % 8 ≠ 7) :
    (m &&& bitmaskIterMask).getLsbD k = false := by
  by_cases hlt : k < 64
  · have hmask : bitmaskIterMask.getLsbD k = false := by
      revert hk
      rcases (by omega :
        k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
        k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨
        k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨
        k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 ∨
        k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨
        k = 40 ∨ k = 41 ∨ k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 ∨
        k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 ∨
        k = 56 ∨ k = 57 ∨ k = 58 ∨ k = 59 ∨ k = 60 ∨ k = 61 ∨ k = 62 ∨ k = 63) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [hmask]
  · exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem groupByte_neonMatchTag (w : BitVec 64) (tag : BitVec 8) (i : Nat) (hi : i < 8) :
    groupByte (neonMatchTag w tag) i = (if groupByte w i == tag then 0xff#8 else 0x00#8) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [neonMatchTag]

theorem groupByte_neonMatchEmpty (w : BitVec 64) (i : Nat) (hi : i < 8) :
    groupByte (neonMatchEmpty w) i = (if groupByte w i == emptyTag then 0xff#8 else 0x00#8) :=
  groupByte_neonMatchTag w emptyTag i hi

theorem groupByte_neonMatchEmptyOrDeleted (w : BitVec 64) (i : Nat) (hi : i < 8) :
    groupByte (neonMatchEmptyOrDeleted w) i = (if (groupByte w i).msb then 0xff#8 else 0x00#8) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [neonMatchEmptyOrDeleted]

theorem groupByte_neonMatchFull (w : BitVec 64) (i : Nat) (hi : i < 8) :
    groupByte (neonMatchFull w) i = (if !(groupByte w i).msb then 0xff#8 else 0x00#8) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [neonMatchFull]

theorem laneSet_eq_groupByte_msb (m : BitVec 64) (i : Nat) :
    laneSet m i = (groupByte m i).msb := by
  simp [laneSet, groupByte, BitVec.msb_eq_getLsbD_last]

/-- `match_byte` (`neonMatchTag`) lane characterization:
for `i < 8`, lane `i` is set in `neonMatchTag w tag` (and in `neonMatchTag w tag &&& bitmaskIterMask`)
if and only if `groupByte w i == tag`. -/
theorem laneSet_neonMatchTag (w : BitVec 64) (tag : BitVec 8) (i : Nat) (hi : i < 8) :
    laneSet (neonMatchTag w tag) i = (groupByte w i == tag) := by
  rw [laneSet_eq_groupByte_msb _ i, groupByte_neonMatchTag w tag i hi]
  by_cases h : (groupByte w i == tag) = true <;> simp [h]

theorem laneSet_neonMatchTag_iff (w : BitVec 64) (tag : BitVec 8) (i : Nat) (hi : i < 8) :
    laneSet (neonMatchTag w tag) i = true ↔ groupByte w i = tag := by
  rw [laneSet_neonMatchTag w tag i hi, beq_iff_eq]

/-- `match_empty` (`neonMatchEmpty`) lane characterization:
for `i < 8`, lane `i` is set in `neonMatchEmpty w` iff `groupByte w i = emptyTag` (`0xff`). -/
theorem laneSet_neonMatchEmpty (w : BitVec 64) (i : Nat) (hi : i < 8) :
    laneSet (neonMatchEmpty w) i = (groupByte w i == emptyTag) :=
  laneSet_neonMatchTag w emptyTag i hi

theorem laneSet_neonMatchEmpty_iff (w : BitVec 64) (i : Nat) (hi : i < 8) :
    laneSet (neonMatchEmpty w) i = true ↔ groupByte w i = emptyTag :=
  laneSet_neonMatchTag_iff w emptyTag i hi

/-- `match_empty_or_deleted` (`neonMatchEmptyOrDeleted`) lane characterization:
for `i < 8`, lane `i` is set in `neonMatchEmptyOrDeleted w` iff `(groupByte w i).msb = true`. -/
theorem laneSet_neonMatchEmptyOrDeleted (w : BitVec 64) (i : Nat) (hi : i < 8) :
    laneSet (neonMatchEmptyOrDeleted w) i = (groupByte w i).msb := by
  rw [laneSet_eq_groupByte_msb _ i, groupByte_neonMatchEmptyOrDeleted w i hi]
  cases (groupByte w i).msb <;> rfl

/-- `match_full` (`neonMatchFull`) lane characterization:
for `i < 8`, lane `i` is set in `neonMatchFull w` iff `(groupByte w i).msb = false` (`isFullTag`). -/
theorem laneSet_neonMatchFull (w : BitVec 64) (i : Nat) (hi : i < 8) :
    laneSet (neonMatchFull w) i = !(groupByte w i).msb := by
  rw [laneSet_eq_groupByte_msb _ i, groupByte_neonMatchFull w i hi]
  cases (groupByte w i).msb <;> rfl

theorem laneSet_neonMatchEmptyOrDeleted_iff (w : BitVec 64) (i : Nat) (hi : i < 8) :
    laneSet (neonMatchEmptyOrDeleted w) i = true ↔ (groupByte w i).msb = true := by
  rw [laneSet_neonMatchEmptyOrDeleted w i hi]

theorem laneSet_neonMatchFull_iff (w : BitVec 64) (i : Nat) (hi : i < 8) :
    laneSet (neonMatchFull w) i = true ↔ (groupByte w i).msb = false := by
  rw [laneSet_neonMatchFull w i hi, Bool.not_eq_true']

/-! ## `umaxv` (`match_empty().any_bit_set()`) and `convert_special_to_empty_and_full_to_deleted` -/

/-- `umaxv b0, v0.8b` on an 8-byte NEON vector: unsigned maximum across the 8 byte lanes. -/
def neonUmaxv8 (w : BitVec 64) : BitVec 8 :=
  let m01 := if (groupByte w 0).toNat ≤ (groupByte w 1).toNat then groupByte w 1 else groupByte w 0
  let m23 := if (groupByte w 2).toNat ≤ (groupByte w 3).toNat then groupByte w 3 else groupByte w 2
  let m45 := if (groupByte w 4).toNat ≤ (groupByte w 5).toNat then groupByte w 5 else groupByte w 4
  let m67 := if (groupByte w 6).toNat ≤ (groupByte w 7).toNat then groupByte w 7 else groupByte w 6
  let m03 := if m01.toNat ≤ m23.toNat then m23 else m01
  let m47 := if m45.toNat ≤ m67.toNat then m67 else m45
  if m03.toNat ≤ m47.toNat then m47 else m03

/-- On `neonMatchTag w tag` (where every byte lane is `0xff#8` or `0x00#8`), `neonUmaxv8` is `0xff#8`
if some lane matches `tag`, else `0x00#8`. -/
theorem neonUmaxv8_neonMatchTag (w : BitVec 64) (tag : BitVec 8) :
    neonUmaxv8 (neonMatchTag w tag) =
      if (groupByte w 0 == tag) || (groupByte w 1 == tag) ||
         (groupByte w 2 == tag) || (groupByte w 3 == tag) ||
         (groupByte w 4 == tag) || (groupByte w 5 == tag) ||
         (groupByte w 6 == tag) || (groupByte w 7 == tag)
      then 0xff#8 else 0x00#8 := by
  simp only [neonUmaxv8, neonMatchTag,
    groupByte_packGroupWord_0, groupByte_packGroupWord_1,
    groupByte_packGroupWord_2, groupByte_packGroupWord_3,
    groupByte_packGroupWord_4, groupByte_packGroupWord_5,
    groupByte_packGroupWord_6, groupByte_packGroupWord_7]
  cases (groupByte w 0 == tag) <;>
  cases (groupByte w 1 == tag) <;>
  cases (groupByte w 2 == tag) <;>
  cases (groupByte w 3 == tag) <;>
  cases (groupByte w 4 == tag) <;>
  cases (groupByte w 5 == tag) <;>
  cases (groupByte w 6 == tag) <;>
  cases (groupByte w 7 == tag) <;> rfl

/-- Bit 0 of `neonUmaxv8 (neonMatchEmpty w)` (tested by `tbnz w8, #0` in compiled `find_inner` /
`find_or_find_insert_index_inner`) is `true` iff at least one byte lane of `w` is `emptyTag` (`0xff`). -/
theorem neonUmaxv8_neonMatchEmpty_getLsbD_zero (w : BitVec 64) :
    (neonUmaxv8 (neonMatchEmpty w)).getLsbD 0 =
      ((groupByte w 0 == emptyTag) || (groupByte w 1 == emptyTag) ||
       (groupByte w 2 == emptyTag) || (groupByte w 3 == emptyTag) ||
       (groupByte w 4 == emptyTag) || (groupByte w 5 == emptyTag) ||
       (groupByte w 6 == emptyTag) || (groupByte w 7 == emptyTag)) := by
  rw [neonMatchEmpty, neonUmaxv8_neonMatchTag]
  cases ((groupByte w 0 == emptyTag) || (groupByte w 1 == emptyTag) ||
         (groupByte w 2 == emptyTag) || (groupByte w 3 == emptyTag) ||
         (groupByte w 4 == emptyTag) || (groupByte w 5 == emptyTag) ||
         (groupByte w 6 == emptyTag) || (groupByte w 7 == emptyTag)) <;> rfl

/-- If at least one lane `i < 8` of `w` is `emptyTag` (`0xff`), then bit 0 of
`neonUmaxv8 (neonMatchEmpty w)` is `true` (`tbnz w8, #0` branches). -/
theorem neonUmaxv8_neonMatchEmpty_getLsbD_zero_of_exists (w : BitVec 64)
    (i : Nat) (hi : i < 8) (hemp : groupByte w i = emptyTag) :
    (neonUmaxv8 (neonMatchEmpty w)).getLsbD 0 = true := by
  rw [neonUmaxv8_neonMatchEmpty_getLsbD_zero]
  have hb : (groupByte w i == emptyTag) = true := beq_iff_eq.mpr hemp
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [hb]

@[simp]
private theorem getElem_if_ff_00_7 (b : Bool) :
    (if b then 0xff#8 else 0x00#8)[7] = b := by
  cases b <;> decide

@[simp]
private theorem getElem_if_false_ff_00_7 (b : Bool) :
    (if b = false then 0xff#8 else 0x00#8)[7] = !b := by
  cases b <;> decide

/-- NEON `convert_special_to_empty_and_full_to_deleted`:
`vorr_u8(vcltz_s8(w), vdup_n_u8(0x80))` maps `EMPTY`/`DELETED` (`msb = true`) to `0xff` (`EMPTY`)
and `FULL` (`msb = false`) to `0x80` (`DELETED`). -/
def neonConvertSpecialToEmptyAndFullToDeleted (w : BitVec 64) : BitVec 64 :=
  neonMatchEmptyOrDeleted w ||| repeatByte deletedTag

theorem groupByte_or (w1 w2 : BitVec 64) (i : Nat) :
    groupByte (w1 ||| w2) i = groupByte w1 i ||| groupByte w2 i := by
  ext j hj
  simp [groupByte]

@[simp]
theorem groupByte_repeatByte (b : BitVec 8) (i : Nat) (hi : i < 8) :
    groupByte (repeatByte b) i = b := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [repeatByte]

theorem groupByte_neonConvertSpecialToEmptyAndFullToDeleted (w : BitVec 64) (i : Nat) (hi : i < 8) :
    groupByte (neonConvertSpecialToEmptyAndFullToDeleted w) i =
      (if (groupByte w i).msb then emptyTag else deletedTag) := by
  rw [neonConvertSpecialToEmptyAndFullToDeleted, groupByte_or,
      groupByte_neonMatchEmptyOrDeleted w i hi, groupByte_repeatByte deletedTag i hi]
  cases (groupByte w i).msb <;> rfl

/-! ## Scalar SWAR (`generic.rs`) Group Match Byte-Lane Characterization -/

theorem swarMatchEmptyOrDeleted_eq_neon (w : BitVec 64) :
    swarMatchEmptyOrDeleted w = neonMatchEmptyOrDeleted w &&& bitmaskIterMask := by
  ext k hk
  rcases (by omega :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
    k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨
    k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨
    k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 ∨
    k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨
    k = 40 ∨ k = 41 ∨ k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 ∨
    k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 ∨
    k = 56 ∨ k = 57 ∨ k = 58 ∨ k = 59 ∨ k = 60 ∨ k = 61 ∨ k = 62 ∨ k = 63) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [swarMatchEmptyOrDeleted, neonMatchEmptyOrDeleted, packGroupWord, groupByte,
          bitmaskIterMask, BitVec.msb_eq_getLsbD_last]

theorem swarMatchFull_eq_neon (w : BitVec 64) :
    swarMatchFull w = neonMatchFull w &&& bitmaskIterMask := by
  ext k hk
  rcases (by omega :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
    k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨
    k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨
    k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 ∨
    k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨
    k = 40 ∨ k = 41 ∨ k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 ∨
    k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 ∨
    k = 56 ∨ k = 57 ∨ k = 58 ∨ k = 59 ∨ k = 60 ∨ k = 61 ∨ k = 62 ∨ k = 63) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [swarMatchFull, neonMatchFull, packGroupWord, groupByte,
          bitmaskIterMask, BitVec.msb_eq_getLsbD_last]

theorem laneSet_swarMatchEmptyOrDeleted (w : BitVec 64) (i : Nat) (hi : i < 8) :
    laneSet (swarMatchEmptyOrDeleted w) i = (groupByte w i).msb := by
  rw [swarMatchEmptyOrDeleted_eq_neon, laneSet_and_bitmaskIterMask _ i hi,
      laneSet_neonMatchEmptyOrDeleted w i hi]

theorem laneSet_swarMatchFull (w : BitVec 64) (i : Nat) (hi : i < 8) :
    laneSet (swarMatchFull w) i = !(groupByte w i).msb := by
  rw [swarMatchFull_eq_neon, laneSet_and_bitmaskIterMask _ i hi,
      laneSet_neonMatchFull w i hi]

/-- `laneSet (swarMatchEmpty w) i`: bit `8 * i + 7` of `w & (w << 1) & 0x8080...` is set iff
both bit `7` (MSB) and bit `6` of `groupByte w i` are set (which for valid tags `EMPTY = 0xff`,
`DELETED = 0x80`, and `FULL < 0x80` holds iff `groupByte w i = emptyTag`). -/
theorem laneSet_swarMatchEmpty (w : BitVec 64) (i : Nat) (hi : i < 8) :
    laneSet (swarMatchEmpty w) i = ((groupByte w i).getLsbD 7 && (groupByte w i).getLsbD 6) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [laneSet, swarMatchEmpty, groupByte]

/-- All-empty group word (`0xffff_ffff_ffff_ffff`). -/
abbrev emptyGroupWord : BitVec 64 := 0xffffffffffffffff#64

@[simp]
theorem repeatByte_emptyTag : repeatByte emptyTag = emptyGroupWord := rfl

@[simp]
theorem groupByte_emptyGroupWord (i : Nat) (hi : i < 8) :
    groupByte emptyGroupWord i = emptyTag := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp]
theorem neonMatchEmpty_emptyGroupWord :
    neonMatchEmpty emptyGroupWord = emptyGroupWord := rfl

@[simp]
theorem neonMatchEmptyOrDeleted_emptyGroupWord :
    neonMatchEmptyOrDeleted emptyGroupWord = emptyGroupWord := rfl

@[simp]
theorem neonMatchFull_emptyGroupWord :
    neonMatchFull emptyGroupWord = 0#64 := rfl

/-- On `emptyGroupWord`, `neonMatchTag emptyGroupWord (h2Tag hash)` is always `0#64`
because `h2Tag hash` has MSB `false` whereas `emptyTag` (`0xff`) has MSB `true`. -/
@[simp]
theorem neonMatchTag_emptyGroupWord_h2Tag (hash : BitVec 64) :
    neonMatchTag emptyGroupWord (h2Tag hash) = 0#64 := by
  have hne : (emptyTag == h2Tag hash) = false :=
    beq_false_of_ne (Ne.symm (h2Tag_ne_emptyTag hash))
  simp [neonMatchTag, groupByte_emptyGroupWord, hne, packGroupWord]

end CryptoVerification.E2E.InMem.HashbrownModel
