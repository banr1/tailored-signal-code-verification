/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownModel.Table

/-!
# Hashbrown `find` and `find_insert_slot` on 4-Bucket Tables

Pure lookup (`find4`) and insertion-slot (`findInsertIndexInGroup`, `fixInsertIndex4`,
`findInsertSlot4At`) lemmas for 4-bucket (`mask = 3#64`) `hashbrown` tables.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownModel

/-! ## `find` (`find_inner`) on 4-Bucket Tables -/

/-- The initial `BitMaskIter` word produced by `g.match_tag(h2_hash).into_iter()` at probe position
`pos` on control byte list `cbs`:
`ldr d9, [ctrl, pos]`, `cmeq v0.8b, v9.8b, v8.8b`, `fmov x8, d0`, `ands x27, x8, #0x8080808080808080`. -/
def findGroupIterMask (cbs : List (BitVec 8)) (pos : Nat) (qtag : BitVec 8) : BitVec 64 :=
  neonMatchTag (loadGroupAt cbs pos) qtag &&& bitmaskIterMask

/-- Bounded loop of `find_inner` on the initial group mask at probe position `pos < 4` (since a
4-bucket table's first group always contains an `EMPTY` padding lane, `find_inner` inspects at most
one group). -/
def findIterMaskLoop (pos : Nat) (m : BitVec 64) (eqAt : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    match lowestSetBit m with
    | none => none
    | some bit =>
      let idx := (pos + bit) % 4
      if eqAt idx then some idx
      else findIterMaskLoop pos (removeLowestBit m) eqAt fuel

/-- Pure model of `RawTableInner::find_inner` on a 4-bucket table (`mask = 3#64`). -/
def find4 (cbs : List (BitVec 8)) (hash : BitVec 64) (eqAt : Nat → Bool) : Option Nat :=
  let pos := (probePos hash 3#64).toNat
  let qtag := h2Tag hash
  findIterMaskLoop pos (findGroupIterMask cbs pos qtag) eqAt 8

@[simp]
theorem findIterMaskLoop_zero_mask (pos : Nat) (eqAt : Nat → Bool) (fuel : Nat) :
    findIterMaskLoop pos 0#64 eqAt (fuel + 1) = none := rfl

@[simp]
theorem findIterMaskLoop_laneBit (pos bit : Nat) (hbit : bit < 8) (eqAt : Nat → Bool) (fuel : Nat) :
    findIterMaskLoop pos (laneBit bit) eqAt (fuel + 2) =
      if eqAt ((pos + bit) % 4) then some ((pos + bit) % 4) else none := by
  simp [findIterMaskLoop, lowestSetBit_laneBit bit hbit, removeLowestBit_laneBit bit hbit]

@[simp]
theorem findGroupIterMask_emptyCtrl4 (pos : Nat) (hpos : pos < 4) (hash : BitVec 64) :
    findGroupIterMask emptyCtrl4 pos (h2Tag hash) = 0#64 :=
  neonMatchTag_loadGroupAt_emptyCtrl4_and_bitmaskIterMask pos hpos (h2Tag hash) (h2Tag_msb hash)

@[simp]
theorem lowestSetBit_findGroupIterMask_emptyCtrl4 (pos : Nat) (hpos : pos < 4) (hash : BitVec 64) :
    lowestSetBit (findGroupIterMask emptyCtrl4 pos (h2Tag hash)) = none := by
  rw [findGroupIterMask_emptyCtrl4 pos hpos hash, lowestSetBit_zero]

@[simp]
theorem find4_emptyCtrl4 (hash : BitVec 64) (eqAt : Nat → Bool) :
    find4 emptyCtrl4 hash eqAt = none := by
  dsimp only [find4]
  have hpos : (probePos hash 3#64).toNat < 4 := probePos_3_toNat_lt hash
  rw [findGroupIterMask_emptyCtrl4 _ hpos hash]
  rfl

/-- On `singleCtrl4 k tag` (`k < 4`, `pos < 4`), `findGroupIterMask` is `laneBit (laneOfBucket4 pos k)`
if `tag == h2Tag hash` and `0#64` otherwise. -/
theorem findGroupIterMask_singleCtrl4 (k pos : Nat) (hk : k < 4) (hpos : pos < 4)
    (tag : BitVec 8) (hash : BitVec 64) :
    findGroupIterMask (singleCtrl4 k tag) pos (h2Tag hash) =
      if tag == h2Tag hash then laneBit (laneOfBucket4 pos k) else 0#64 :=
  neonMatchTag_loadGroupAt_singleCtrl4_and_bitmaskIterMask
    k pos hk hpos tag (h2Tag hash) (h2Tag_msb hash)

/-- On `singleCtrl4 k tag` (`k < 4`, `pos < 4`), when `tag ≠ h2Tag hash`, `lowestSetBit` of
`findGroupIterMask` is immediately `none`. -/
theorem lowestSetBit_findGroupIterMask_singleCtrl4_of_ne
    (k pos : Nat) (hk : k < 4) (hpos : pos < 4)
    (tag : BitVec 8) (hash : BitVec 64) (hne : (tag == h2Tag hash) = false) :
    lowestSetBit (findGroupIterMask (singleCtrl4 k tag) pos (h2Tag hash)) = none := by
  rw [findGroupIterMask_singleCtrl4 k pos hk hpos tag hash, hne]
  rfl

/-- On `singleCtrl4 k tag` (`k < 4`, `pos < 4`), when `tag == h2Tag hash`,
- the first `lowestSetBit` is `some (laneOfBucket4 pos k)`,
- the probed bucket index `(pos + laneOfBucket4 pos k) & 3` is `k`, and
- after `remove_lowest_bit`, the remaining mask is `0#64` (so if the key check at bucket `k` returns
  `false`, the iterator terminates on the next step with `lowestSetBit = none`). -/
theorem findGroupIterMask_singleCtrl4_of_eq
    (k pos : Nat) (hk : k < 4) (hpos : pos < 4)
    (tag : BitVec 8) (hash : BitVec 64) (heq : (tag == h2Tag hash) = true) :
    findGroupIterMask (singleCtrl4 k tag) pos (h2Tag hash) = laneBit (laneOfBucket4 pos k) ∧
    lowestSetBit (findGroupIterMask (singleCtrl4 k tag) pos (h2Tag hash)) =
      some (laneOfBucket4 pos k) ∧
    probeBucketIdx (BitVec.ofNat 64 pos) (laneOfBucket4 pos k) 3#64 = BitVec.ofNat 64 k ∧
    (pos + laneOfBucket4 pos k) % 4 = k ∧
    removeLowestBit (findGroupIterMask (singleCtrl4 k tag) pos (h2Tag hash)) = 0#64 := by
  have hmask : findGroupIterMask (singleCtrl4 k tag) pos (h2Tag hash) = laneBit (laneOfBucket4 pos k) := by
    rw [findGroupIterMask_singleCtrl4 k pos hk hpos tag hash, heq]
    rfl
  have hlt : laneOfBucket4 pos k < 8 := laneOfBucket4_lt_8 pos k hpos hk
  have hprobe := probe4_reaches_every_bucket emptyTag emptyTag emptyTag emptyTag pos k hpos hk
  refine ⟨hmask, ?_, hprobe.2.2, hprobe.2.1, ?_⟩
  · rw [hmask, lowestSetBit_laneBit _ hlt]
  · rw [hmask, removeLowestBit_laneBit _ hlt]

/-- On `singleCtrl4 k tag` (`k < 4`), `find4` returns `some k` if `tag == h2Tag hash` and
`eqAt k = true`, and `none` otherwise. -/
theorem find4_singleCtrl4 (k : Nat) (hk : k < 4) (tag : BitVec 8)
    (hash : BitVec 64) (eqAt : Nat → Bool) :
    find4 (singleCtrl4 k tag) hash eqAt =
      if (tag == h2Tag hash) && eqAt k then some k else none := by
  dsimp only [find4]
  have hpos : (probePos hash 3#64).toNat < 4 := probePos_3_toNat_lt hash
  generalize (probePos hash 3#64).toNat = pos at hpos ⊢
  rw [findGroupIterMask_singleCtrl4 k pos hk hpos tag hash]
  cases hbeq : (tag == h2Tag hash)
  · simp
  · have hlt : laneOfBucket4 pos k < 8 := laneOfBucket4_lt_8 pos k hpos hk
    have hmod : (pos + laneOfBucket4 pos k) % 4 = k :=
      (probe4_reaches_every_bucket emptyTag emptyTag emptyTag emptyTag pos k hpos hk).2.1
    simp [findIterMaskLoop_laneBit pos (laneOfBucket4 pos k) hlt eqAt 6, hmod]

/-! ## `find_insert_slot` on 4-Bucket Tables -/

/-- `RawTableInner::find_insert_index_in_group`:
`group.match_empty_or_deleted().lowest_set_bit()`.
In the compiled `aarch64` binary (`store_session::{closure#0}` at `0x90a4..0x90bc`), this is:
`cmlt v0.8b, v0.8b, #0`, `fmov x9, d0`, `cbz x9`, `rbit x9, x9`, `clz x9, x9`, `lsr #3`. -/
def findInsertIndexInGroup (g : BitVec 64) : Option Nat :=
  lowestSetBit (neonMatchEmptyOrDeleted g)

/-- On any 4-bucket table `mkCtrl4 b0 b1 b2 b3` and `pos < 4`, `neonMatchEmptyOrDeleted` on the
loaded group is nonzero because lane `4 - pos` holds `emptyTag` (`0xff#8`). -/
theorem neonMatchEmptyOrDeleted_loadGroupAt_mkCtrl4_ne_zero
    (b0 b1 b2 b3 : BitVec 8) (pos : Nat) (hpos : pos < 4) :
    neonMatchEmptyOrDeleted (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) ≠ 0#64 := by
  intro hzero
  rw [neonMatchEmptyOrDeleted_eq_mkFullMask, mkFullMask_eq_zero_iff] at hzero
  have hpad := groupByte_loadGroupAt_mkCtrl4_padding_empty b0 b1 b2 b3 pos hpos
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl
  · change groupByte (loadGroupAt (mkCtrl4 b0 b1 b2 b3) 0) 4 = emptyTag at hpad
    have := hzero.2.2.2.2.1; rw [hpad, emptyTag_msb] at this; cases this
  · change groupByte (loadGroupAt (mkCtrl4 b0 b1 b2 b3) 1) 3 = emptyTag at hpad
    have := hzero.2.2.2.1; rw [hpad, emptyTag_msb] at this; cases this
  · change groupByte (loadGroupAt (mkCtrl4 b0 b1 b2 b3) 2) 2 = emptyTag at hpad
    have := hzero.2.2.1; rw [hpad, emptyTag_msb] at this; cases this
  · change groupByte (loadGroupAt (mkCtrl4 b0 b1 b2 b3) 3) 1 = emptyTag at hpad
    have := hzero.2.1; rw [hpad, emptyTag_msb] at this; cases this

set_option maxRecDepth 4096 in
@[simp]
theorem findInsertIndexInGroup_emptyCtrl4 (pos : Nat) (hpos : pos < 4) :
    findInsertIndexInGroup (loadGroupAt emptyCtrl4 pos) = some 0 := by
  unfold findInsertIndexInGroup
  rw [neonMatchEmptyOrDeleted_loadGroupAt_emptyCtrl4 pos hpos]
  rfl

set_option maxRecDepth 4096 in
@[simp]
theorem bitmaskTrailingZeros_neonMatchEmptyOrDeleted_emptyCtrl4 (pos : Nat) (hpos : pos < 4) :
    bitmaskTrailingZeros (neonMatchEmptyOrDeleted (loadGroupAt emptyCtrl4 pos)) = 0 := by
  rw [neonMatchEmptyOrDeleted_loadGroupAt_emptyCtrl4 pos hpos]
  rfl

/-- On `emptyCtrl4`, for any `pos < 4`:
- the candidate insert index `(pos + 0) & 3` is `pos`,
- the control byte at `pos` is `emptyTag` (`msb = true`), so the `tbz w10, #7` branch in
  `fix_insert_index` is NOT taken, and
- `set_ctrl(pos, h2Tag hash)` produces `singleCtrl4 pos (h2Tag hash)`. -/
theorem findInsertSlot_emptyCtrl4 (hash : BitVec 64) :
    let pos := (probePos hash 3#64).toNat
    findInsertIndexInGroup (loadGroupAt emptyCtrl4 pos) = some 0 ∧
    probeBucketIdx (probePos hash 3#64) 0 3#64 = probePos hash 3#64 ∧
    emptyCtrl4.getD pos emptyTag = emptyTag ∧
    (emptyCtrl4.getD pos emptyTag).msb = true ∧
    setCtrlList 3#64 emptyCtrl4 (probePos hash 3#64) (h2Tag hash) =
      singleCtrl4 pos (h2Tag hash) := by
  dsimp only
  have hpos : (probePos hash 3#64).toNat < 4 := probePos_3_toNat_lt hash
  have hp_eq : BitVec.ofNat 64 (probePos hash 3#64).toNat = probePos hash 3#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨findInsertIndexInGroup_emptyCtrl4 _ hpos, ?_, ?_, ?_, ?_⟩
  · rw [← hp_eq]
    generalize (probePos hash 3#64).toNat = pos at hpos ⊢
    rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;> rfl
  · generalize (probePos hash 3#64).toNat = pos at hpos ⊢
    rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;> rfl
  · generalize (probePos hash 3#64).toNat = pos at hpos ⊢
    rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;> rfl
  · generalize (probePos hash 3#64).toNat = pos at hpos hp_eq ⊢
    rw [← hp_eq]
    exact setCtrlList_emptyCtrl4 pos hpos (h2Tag hash)

/-! ### `find_insert_slot` on a 1-Item 4-Bucket Table (`singleCtrl4 k tag`) -/

@[simp]
theorem not_laneFullMask_ne_zero (i : Nat) (hi : i < 8) :
    ~~~(laneFullMask i) ≠ 0#64 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 4096 in
@[simp]
theorem bitmaskTrailingZeros_not_laneFullMask (i : Nat) (hi : i < 8) :
    bitmaskTrailingZeros (~~~(laneFullMask i)) = if i = 0 then 1 else 0 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
@[simp]
theorem lowestSetBit_not_laneFullMask (i : Nat) (hi : i < 8) :
    lowestSetBit (~~~(laneFullMask i)) = some (if i = 0 then 1 else 0) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp]
theorem laneOfBucket4_eq_zero_iff (pos k : Nat) (hpos : pos < 4) (hk : k < 4) :
    laneOfBucket4 pos k = 0 ↔ pos = k := by
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  decide

/-- On `singleCtrl4 k tag` (`k < 4`, `pos < 4`, `tag.msb = false`), `findInsertIndexInGroup`
returns `some 1` if `pos = k` (since lane 0 is bucket `k` which is full, and lane 1 is `emptyTag`)
and `some 0` if `pos ≠ k` (since lane 0 is bucket `pos ≠ k` which is `emptyTag`). -/
theorem findInsertIndexInGroup_singleCtrl4 (k pos : Nat) (hk : k < 4) (hpos : pos < 4)
    (tag : BitVec 8) (htag : tag.msb = false) :
    findInsertIndexInGroup (loadGroupAt (singleCtrl4 k tag) pos) =
      some (if pos = k then 1 else 0) := by
  unfold findInsertIndexInGroup
  rw [neonMatchEmptyOrDeleted_loadGroupAt_singleCtrl4 k pos hk hpos tag htag]
  have hlt : laneOfBucket4 pos k < 8 := laneOfBucket4_lt_8 pos k hpos hk
  rw [lowestSetBit_not_laneFullMask (laneOfBucket4 pos k) hlt]
  simp [laneOfBucket4_eq_zero_iff pos k hpos hk]

/-- The insertion bucket chosen on `singleCtrl4 k tag` at probe position `pos < 4`:
`(k + 1) % 4` if `pos = k` (collision in bucket `k`), and `pos` if `pos ≠ k`. -/
def insertSlot4Single (k pos : Nat) : Nat :=
  if pos = k then (k + 1) % 4 else pos

theorem insertSlot4Single_lt_4 (k pos : Nat) (_hk : k < 4) (hpos : pos < 4) :
    insertSlot4Single k pos < 4 := by
  unfold insertSlot4Single
  split <;> omega

theorem insertSlot4Single_ne (k pos : Nat) (_hk : k < 4) (_hpos : pos < 4) :
    insertSlot4Single k pos ≠ k := by
  unfold insertSlot4Single
  split <;> omega

/-- On `singleCtrl4 k tag` (`k < 4`, `pos < 4`, `tag.msb = false`), `find_insert_slot` selects
`insertSlot4Single k pos` without taking the `fix_insert_index` reload branch, and `set_ctrl` yields
`doubleCtrl4 k tag (insertSlot4Single k pos) newTag`. -/
theorem findInsertSlot_singleCtrl4 (k pos : Nat) (hk : k < 4) (hpos : pos < 4)
    (tag newTag : BitVec 8) (htag : tag.msb = false) (hnew : newTag.msb = false) :
    let bit := if pos = k then 1 else 0
    let slot := insertSlot4Single k pos
    findInsertIndexInGroup (loadGroupAt (singleCtrl4 k tag) pos) = some bit ∧
    probeBucketIdx (BitVec.ofNat 64 pos) bit 3#64 = BitVec.ofNat 64 slot ∧
    (pos + bit) % 4 = slot ∧
    slot < 4 ∧
    slot ≠ k ∧
    (singleCtrl4 k tag).getD slot emptyTag = emptyTag ∧
    ((singleCtrl4 k tag).getD slot emptyTag).msb = true ∧
    setCtrlList 3#64 (singleCtrl4 k tag) (BitVec.ofNat 64 slot) newTag =
      doubleCtrl4 k tag slot newTag ∧
    CtrlMirrorInv 3#64 (setCtrlList 3#64 (singleCtrl4 k tag) (BitVec.ofNat 64 slot) newTag) ∧
    FullBucketsInv 3#64 (setCtrlList 3#64 (singleCtrl4 k tag) (BitVec.ofNat 64 slot) newTag) [k, slot] := by
  dsimp only
  have hfind := findInsertIndexInGroup_singleCtrl4 k pos hk hpos tag htag
  have hslt : insertSlot4Single k pos < 4 := insertSlot4Single_lt_4 k pos hk hpos
  have hsne : insertSlot4Single k pos ≠ k := insertSlot4Single_ne k pos hk hpos
  have hset := setCtrlList_singleCtrl4 k hk tag (insertSlot4Single k pos) hslt newTag
  have hmir : CtrlMirrorInv 3#64 (setCtrlList 3#64 (singleCtrl4 k tag) (BitVec.ofNat 64 (insertSlot4Single k pos)) newTag) := by
    rw [hset]
    exact ctrlMirrorInv_doubleCtrl4 k tag (insertSlot4Single k pos) newTag
  have hfull : FullBucketsInv 3#64 (setCtrlList 3#64 (singleCtrl4 k tag) (BitVec.ofNat 64 (insertSlot4Single k pos)) newTag) [k, insertSlot4Single k pos] := by
    rw [hset]
    exact fullBucketsInv_doubleCtrl4 k (insertSlot4Single k pos) hk hslt hsne.symm tag newTag htag hnew
  have hget : (singleCtrl4 k tag).getD (insertSlot4Single k pos) emptyTag = emptyTag := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;> rfl
  refine ⟨hfind, ?_, ?_, hslt, hsne, hget, ?_, hset, hmir, hfull⟩
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rw [hget]; rfl

/-! ### General `fix_insert_index` on Any Non-Full 4-Bucket Table (`mkCtrl4 b0 b1 b2 b3`) -/

/-- Pure model of `RawTableInner::fix_insert_index` on a 4-bucket table (`mask = 3#64`):
Given the candidate index `idx = (pos + bit) % 4` from `find_insert_index_in_group`, if `cbs[idx]`
is `EMPTY` or `DELETED` (`msb = true`), return `idx`; otherwise (which happens when `pos + bit`
landed in the padding `EMPTY` bytes `4..7` while bucket `idx` in `0..3` was `FULL`), reload the
aligned group at offset `0` and return `bitmaskTrailingZeros (neonMatchEmptyOrDeleted (loadGroupAt cbs 0)) % 4`. -/
def fixInsertIndex4 (cbs : List (BitVec 8)) (idx : Nat) : Nat :=
  if (cbs.getD idx emptyTag).msb then idx
  else bitmaskTrailingZeros (neonMatchEmptyOrDeleted (loadGroupAt cbs 0)) % 4

/-- Complete pure model of `RawTableInner::find_insert_slot` on a 4-bucket table (`mask = 3#64`)
starting at probe position `pos < 4`. -/
def findInsertSlot4At (cbs : List (BitVec 8)) (pos : Nat) : Nat :=
  let bit := bitmaskTrailingZeros (neonMatchEmptyOrDeleted (loadGroupAt cbs pos))
  let idx := (pos + bit) % 4
  fixInsertIndex4 cbs idx

/-- For any 4-bucket table `mkCtrl4 b0 b1 b2 b3` that is not completely full (i.e., at least one of
the 4 buckets has `msb = true`, meaning `EMPTY` or `DELETED`) and any probe position `pos < 4`,
`findInsertSlot4At (mkCtrl4 b0 b1 b2 b3) pos` returns a valid bucket index `< 4` whose control byte
has `msb = true` (`EMPTY` or `DELETED`). -/
theorem findInsertSlot4At_mkCtrl4_valid (b0 b1 b2 b3 : BitVec 8) (pos : Nat) (_hpos : pos < 4)
    (hnotfull : (b0.msb || b1.msb || b2.msb || b3.msb) = true) :
    let slot := findInsertSlot4At (mkCtrl4 b0 b1 b2 b3) pos
    slot < 4 ∧ ((mkCtrl4 b0 b1 b2 b3).getD slot emptyTag).msb = true := by
  dsimp only [findInsertSlot4At, fixInsertIndex4]
  generalize hidx : (pos + bitmaskTrailingZeros (neonMatchEmptyOrDeleted (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos))) % 4 = idx
  have hidx_lt : idx < 4 := by rw [← hidx]; omega
  cases hmsb : ((mkCtrl4 b0 b1 b2 b3).getD idx emptyTag).msb
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have h0 : bitmaskTrailingZeros (neonMatchEmptyOrDeleted (loadGroupAt (mkCtrl4 b0 b1 b2 b3) 0)) =
        match firstTrueLane b0.msb b1.msb b2.msb b3.msb true true true true with
        | some i => i
        | none => 0 := by
      have hlow := lowestSetBit_mkFullMask b0.msb b1.msb b2.msb b3.msb true true true true
      have heq : neonMatchEmptyOrDeleted (loadGroupAt (mkCtrl4 b0 b1 b2 b3) 0) =
          mkFullMask b0.msb b1.msb b2.msb b3.msb true true true true := by
        simp [neonMatchEmptyOrDeleted_eq_mkFullMask]
      rw [heq]
      have hnz : mkFullMask b0.msb b1.msb b2.msb b3.msb true true true true ≠ 0#64 := by
        intro hz
        rw [mkFullMask_eq_zero_iff] at hz
        cases hz.2.2.2.2.1
      simp only [lowestSetBit, hnz, ↓reduceIte] at hlow
      rw [← hlow]
    rw [h0]
    cases hb0 : b0.msb
    · cases hb1 : b1.msb
      · cases hb2 : b2.msb
        · cases hb3 : b3.msb
          · simp [hb0, hb1, hb2, hb3] at hnotfull
          · simp [firstTrueLane, mkCtrl4, hb3]
        · simp [firstTrueLane, mkCtrl4, hb2]
      · simp [firstTrueLane, mkCtrl4, hb1]
    · simp [firstTrueLane, mkCtrl4, hb0]
  · simp only [↓reduceIte]
    exact ⟨hidx_lt, hmsb⟩

/-! ## `CtrlMirrorInv` and `FullBucketsInv` Corollaries (`n ≤ 1`, `mask = 3#64`) -/

/-- Any 12-byte control list satisfying `CtrlMirrorInv 3#64 cbs` whose first 4 buckets are `emptyTag`
equals `emptyCtrl4`. -/
theorem eq_emptyCtrl4_of_ctrlMirrorInv {cbs : List (BitVec 8)}
    (hmir : CtrlMirrorInv 3#64 cbs)
    (hemp : ∀ j < 4, cbs.getD j emptyTag = emptyTag) :
    cbs = emptyCtrl4 := by
  rw [eq_mkCtrl4_of_ctrlMirrorInv cbs hmir,
      hemp 0 (by decide), hemp 1 (by decide), hemp 2 (by decide), hemp 3 (by decide)]
  rfl

/-- Any 12-byte control list satisfying `CtrlMirrorInv 3#64 cbs` with `cbs[k] = tag` (`k < 4`)
and `cbs[j] = emptyTag` for `j < 4, j ≠ k` equals `singleCtrl4 k tag`. -/
theorem eq_singleCtrl4_of_ctrlMirrorInv {cbs : List (BitVec 8)} (k : Nat) (tag : BitVec 8) (hk : k < 4)
    (hmir : CtrlMirrorInv 3#64 cbs)
    (htag : cbs.getD k emptyTag = tag)
    (hemp : ∀ j < 4, j ≠ k → cbs.getD j emptyTag = emptyTag) :
    cbs = singleCtrl4 k tag := by
  rw [eq_mkCtrl4_of_ctrlMirrorInv cbs hmir]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · rw [htag, hemp 1 (by decide) (by decide), hemp 2 (by decide) (by decide), hemp 3 (by decide) (by decide)]; rfl
  · rw [hemp 0 (by decide) (by decide), htag, hemp 2 (by decide) (by decide), hemp 3 (by decide) (by decide)]; rfl
  · rw [hemp 0 (by decide) (by decide), hemp 1 (by decide) (by decide), htag, hemp 3 (by decide) (by decide)]; rfl
  · rw [hemp 0 (by decide) (by decide), hemp 1 (by decide) (by decide), hemp 2 (by decide) (by decide), htag]; rfl

/-- On any 4-bucket control byte list satisfying `CtrlMirrorInv 3#64 cbs` whose first 4 buckets are
`emptyTag` (`0xff`), `find4 cbs hash eqAt = none`. -/
theorem find4_of_ctrlMirrorInv_empty {cbs : List (BitVec 8)}
    (hmir : CtrlMirrorInv 3#64 cbs)
    (hemp : ∀ j < 4, cbs.getD j emptyTag = emptyTag)
    (hash : BitVec 64) (eqAt : Nat → Bool) :
    find4 cbs hash eqAt = none := by
  rw [eq_emptyCtrl4_of_ctrlMirrorInv hmir hemp]
  exact find4_emptyCtrl4 hash eqAt

/-- On any 4-bucket control byte list satisfying `CtrlMirrorInv 3#64 cbs`, `cbs[k] = tag`,
and whose other buckets `< 4` are `emptyTag`, `find4 cbs hash eqAt` returns
`some k` iff `(tag == h2Tag hash) && eqAt k`, and `none` otherwise. -/
theorem find4_of_ctrlMirrorInv_single {cbs : List (BitVec 8)} (k : Nat) (tag : BitVec 8) (hk : k < 4)
    (hmir : CtrlMirrorInv 3#64 cbs)
    (htag : cbs.getD k emptyTag = tag)
    (hemp : ∀ j < 4, j ≠ k → cbs.getD j emptyTag = emptyTag)
    (hash : BitVec 64) (eqAt : Nat → Bool) :
    find4 cbs hash eqAt =
      if (tag == h2Tag hash) && eqAt k then some k else none := by
  rw [eq_singleCtrl4_of_ctrlMirrorInv k tag hk hmir htag hemp]
  exact find4_singleCtrl4 k hk tag hash eqAt

/-- On any 4-bucket control byte list satisfying `CtrlMirrorInv 3#64 cbs` whose first 4 buckets are
`emptyTag`, `findInsertSlot` selects `pos = (probePos hash 3#64).toNat`
and `setCtrlList` produces `singleCtrl4 pos (h2Tag hash)`. -/
theorem findInsertSlot_of_ctrlMirrorInv_empty {cbs : List (BitVec 8)}
    (hmir : CtrlMirrorInv 3#64 cbs)
    (hemp : ∀ j < 4, cbs.getD j emptyTag = emptyTag)
    (hash : BitVec 64) :
    let pos := (probePos hash 3#64).toNat
    findInsertIndexInGroup (loadGroupAt cbs pos) = some 0 ∧
    probeBucketIdx (probePos hash 3#64) 0 3#64 = probePos hash 3#64 ∧
    cbs.getD pos emptyTag = emptyTag ∧
    (cbs.getD pos emptyTag).msb = true ∧
    setCtrlList 3#64 cbs (probePos hash 3#64) (h2Tag hash) =
      singleCtrl4 pos (h2Tag hash) ∧
    CtrlMirrorInv 3#64 (setCtrlList 3#64 cbs (probePos hash 3#64) (h2Tag hash)) ∧
    FullBucketsInv 3#64 (setCtrlList 3#64 cbs (probePos hash 3#64) (h2Tag hash)) [pos] := by
  rw [eq_emptyCtrl4_of_ctrlMirrorInv hmir hemp]
  have hpos : (probePos hash 3#64).toNat < 4 := probePos_3_toNat_lt hash
  rcases findInsertSlot_emptyCtrl4 hash with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · rw [h5]; exact ctrlMirrorInv_singleCtrl4 _ _
  · rw [h5]; exact fullBucketsInv_singleCtrl4 _ hpos _ (h2Tag_msb hash)

/-- On any 4-bucket control byte list satisfying `CtrlMirrorInv 3#64 cbs`, `cbs[k] = tag` (`tag.msb = false`),
and whose other buckets `< 4` are `emptyTag`, `findInsertSlot` selects
`slot = insertSlot4Single k pos ≠ k` and updates `cbs` to `doubleCtrl4`. -/
theorem findInsertSlot_of_ctrlMirrorInv_single {cbs : List (BitVec 8)} (k pos : Nat) (tag newTag : BitVec 8)
    (hk : k < 4) (hpos : pos < 4)
    (hmir : CtrlMirrorInv 3#64 cbs) (htag_msb : tag.msb = false) (hnew_msb : newTag.msb = false)
    (htag : cbs.getD k emptyTag = tag)
    (hemp : ∀ j < 4, j ≠ k → cbs.getD j emptyTag = emptyTag) :
    let bit := if pos = k then 1 else 0
    let slot := insertSlot4Single k pos
    findInsertIndexInGroup (loadGroupAt cbs pos) = some bit ∧
    probeBucketIdx (BitVec.ofNat 64 pos) bit 3#64 = BitVec.ofNat 64 slot ∧
    (pos + bit) % 4 = slot ∧
    slot < 4 ∧
    slot ≠ k ∧
    cbs.getD slot emptyTag = emptyTag ∧
    (cbs.getD slot emptyTag).msb = true ∧
    setCtrlList 3#64 cbs (BitVec.ofNat 64 slot) newTag =
      doubleCtrl4 k tag slot newTag ∧
    CtrlMirrorInv 3#64 (setCtrlList 3#64 cbs (BitVec.ofNat 64 slot) newTag) ∧
    FullBucketsInv 3#64 (setCtrlList 3#64 cbs (BitVec.ofNat 64 slot) newTag) [k, slot] := by
  rw [eq_singleCtrl4_of_ctrlMirrorInv k tag hk hmir htag hemp]
  exact findInsertSlot_singleCtrl4 k pos hk hpos tag newTag htag_msb hnew_msb

end CryptoVerification.E2E.InMem.HashbrownModel
