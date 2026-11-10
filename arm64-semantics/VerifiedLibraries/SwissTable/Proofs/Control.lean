/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.SwissTable.Spec
public import ProofLib.BV.Bits

/-!
# SwissTable Control Bytes, Bucket Masks, and Triangular Probing

Models SwissTable 8-bit control tags (`EMPTY`, `DELETED`, and 7-bit `FULL` hash tags), valid
power-of-two `bucket_mask` values and table capacities, triangular group-probing byte offsets,
and the trailing 8-byte control mirror invariant (`CtrlMirrorInv`). All definitions are
independent of the slot type and hash function.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.SwissTable

open ProofLib

/-! ## Control Tags -/

/-- `Tag::EMPTY` (`0xff = -1i8`). -/
def tagEmpty : BitVec 8 := 0xff#8

/-- `Tag::DELETED` (`0x80 = -128i8`). -/
def tagDeleted : BitVec 8 := 0x80#8

/-- A control tag is `EMPTY` or `DELETED` iff its high bit (bit 7) is `1`. -/
def isSpecialTag (b : BitVec 8) : Bool := (b &&& 0x80#8) == 0x80#8

/-- A control tag is `FULL` (`0x00..0x7f`) iff its high bit (bit 7) is `0`. -/
def isFullTag (b : BitVec 8) : Bool := (b &&& 0x80#8) == 0#8

/-- Full 7-bit SwissTable control tag of a 64-bit hash: `Tag::full(hash) = (hash >> 57) as u8`. -/
def tagOfHash (h : BitVec 64) : BitVec 8 :=
  (h >>> 57).truncate 8

theorem tagOfHash_lt_0x80 (h : BitVec 64) : (tagOfHash h).toNat < 0x80 := by
  have h' : tagOfHash h < 0x80#8 := by unfold tagOfHash; bv_bits
  simpa [BitVec.lt_def] using h'

theorem tagOfHash_and_0x80 (h : BitVec 64) : tagOfHash h &&& 0x80#8 = 0#8 := by
  unfold tagOfHash; bv_bits

@[simp]
theorem tagOfHash_ne_empty (h : BitVec 64) : tagOfHash h ≠ 0xff#8 := by
  have := tagOfHash_lt_0x80 h; intro he; rw [he] at this; contradiction

@[simp]
theorem tagOfHash_ne_deleted (h : BitVec 64) : tagOfHash h ≠ 0x80#8 := by
  have := tagOfHash_lt_0x80 h; intro he; rw [he] at this; contradiction

/-- Every byte in a valid SwissTable control array is `EMPTY`, `DELETED`, or `FULL` (`< 0x80`). -/
def ValidTag (b : BitVec 8) : Prop :=
  b = tagEmpty ∨ b = tagDeleted ∨ b.toNat < 0x80

theorem ValidTag.empty : ValidTag tagEmpty := Or.inl rfl

theorem ValidTag.deleted : ValidTag tagDeleted := Or.inr (Or.inl rfl)

theorem ValidTag.of_tagOfHash (h : BitVec 64) : ValidTag (tagOfHash h) :=
  Or.inr (Or.inr (tagOfHash_lt_0x80 h))

theorem isFullTag_iff_lt_0x80 (b : BitVec 8) : isFullTag b = true ↔ b.toNat < 0x80 := by
  constructor
  · intro h
    have hb : b < 0x80#8 := by
      unfold isFullTag at h
      have h0 : b &&& 0x80#8 = 0#8 := beq_iff_eq.mp h
      bv_bits
    simpa [BitVec.lt_def] using hb
  · intro h
    have hb : b < 0x80#8 := by simpa [BitVec.lt_def] using h
    unfold isFullTag
    rw [beq_iff_eq]
    bv_bits

theorem isSpecialTag_iff_ge_0x80 (b : BitVec 8) : isSpecialTag b = true ↔ 0x80 ≤ b.toNat := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hlt
    have hlt' : b < 0x80#8 := by
      rw [BitVec.lt_def]; change b.toNat < 128; omega
    unfold isSpecialTag at h
    have h1 : b &&& 0x80#8 = 0x80#8 := beq_iff_eq.mp h
    have h2 : b &&& 0x80#8 = 0#8 := by bv_bits
    rw [h1] at h2
    contradiction
  · intro hge
    have hge' : ¬ (b < 0x80#8) := by
      rw [BitVec.lt_def]; change ¬ (b.toNat < 128); omega
    unfold isSpecialTag
    rw [beq_iff_eq]
    bv_bits

@[simp]
theorem isFullTag_tagOfHash (h : BitVec 64) : isFullTag (tagOfHash h) = true :=
  (isFullTag_iff_lt_0x80 _).mpr (tagOfHash_lt_0x80 h)

@[simp]
theorem isFullTag_tagEmpty : isFullTag tagEmpty = false := by decide

@[simp]
theorem isFullTag_tagDeleted : isFullTag tagDeleted = false := by decide

theorem ValidTag.special_cases {b : BitVec 8} (hv : ValidTag b) (hs : isSpecialTag b = true) :
    b = tagEmpty ∨ b = tagDeleted := by
  have hge := (isSpecialTag_iff_ge_0x80 b).mp hs
  rcases hv with rfl | rfl | hlt
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega


/-! ## Power-of-Two `bucket_mask` and Capacity Accounting -/

/-- Valid heap-allocated SwissTable `bucket_mask` on 64-bit AArch64:
    `buckets = 2 ^ exp` with `2 ≤ exp ≤ 58` (`buckets ∈ {4, 8, 16, ..., 2^58}`,
    so `total_size = 17 * buckets + 8 ≤ 0x7ffffffffffffff8 = isize::MAX - 7`). -/
def ValidBucketMask (bm : BitVec 64) : Prop :=
  ∃ exp : Nat, 2 ≤ exp ∧ exp ≤ 58 ∧ bm = BitVec.ofNat 64 (2 ^ exp - 1)

/-- Machine-level `bucket_mask_to_capacity(bucket_mask)` (`raw.rs`):
    `bm` when `bm < 8`, else `((bm + 1) >> 3) * 7`. -/
def bucketMaskToCapacityBV (bm : BitVec 64) : BitVec 64 :=
  if bm < 8#64 then bm else ((bm + 1#64) >>> 3) * 7#64

/-- Usable table capacity (`Nat`) for a given `bucket_mask`. -/
def bucketMaskToCapacity (bm : BitVec 64) : Nat :=
  (bucketMaskToCapacityBV bm).toNat

@[simp]
theorem bucketMaskToCapacityBV_zero : bucketMaskToCapacityBV 0#64 = 0#64 := by decide

@[simp]
theorem bucketMaskToCapacity_zero : bucketMaskToCapacity 0#64 = 0 := by decide

@[simp]
theorem bucketMaskToCapacityBV_three : bucketMaskToCapacityBV 3#64 = 3#64 := by decide

@[simp]
theorem bucketMaskToCapacity_three : bucketMaskToCapacity 3#64 = 3 := by decide

theorem ValidBucketMask.ne_zero {bm : BitVec 64} (h : ValidBucketMask bm) : bm ≠ 0#64 := by
  obtain ⟨exp, hlo, hhi, rfl⟩ := h
  have h258 : 2 ^ 58 < 2 ^ 64 := by decide
  have hpow : 4 ≤ 2 ^ exp ∧ 2 ^ exp ≤ 2 ^ 58 :=
    ⟨show 2 ^ 2 ≤ 2 ^ exp from Nat.pow_le_pow_right (by decide) hlo,
     Nat.pow_le_pow_right (by decide) hhi⟩
  intro hz
  have := congrArg BitVec.toNat hz
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem ValidBucketMask.buckets_eq {bm : BitVec 64} {exp : Nat}
    (hlo : 2 ≤ exp) (hhi : exp ≤ 58) (hbm : bm = BitVec.ofNat 64 (2 ^ exp - 1)) :
    bm.toNat + 1 = 2 ^ exp := by
  subst hbm
  have h258 : 2 ^ 58 < 2 ^ 64 := by decide
  have hpow : 4 ≤ 2 ^ exp ∧ 2 ^ exp ≤ 2 ^ 58 :=
    ⟨show 2 ^ 2 ≤ 2 ^ exp from Nat.pow_le_pow_right (by decide) hlo,
     Nat.pow_le_pow_right (by decide) hhi⟩
  simp only [BitVec.toNat_ofNat]
  omega

theorem ValidBucketMask.capacity_eq {bm : BitVec 64} {exp : Nat}
    (hlo : 2 ≤ exp) (hhi : exp ≤ 58) (hbm : bm = BitVec.ofNat 64 (2 ^ exp - 1)) :
    bucketMaskToCapacity bm = if exp = 2 then 3 else 7 * 2 ^ (exp - 3) := by
  subst hbm
  by_cases he2 : exp = 2
  · subst he2; decide
  · by_cases he3' : exp = 3
    · subst he3'; decide
    · have he4 : 4 ≤ exp := by omega
      have h258 : 2 ^ 58 < 2 ^ 64 := by decide
      have h255 : 7 * 2 ^ 55 < 2 ^ 64 := by decide
      have hpow_lo : 16 ≤ 2 ^ exp := by
        have : 2 ^ 4 ≤ 2 ^ exp := Nat.pow_le_pow_right (by decide : 0 < 2) he4
        have : 2 ^ 4 = 16 := rfl
        omega
      have hpow_hi : 2 ^ exp ≤ 2 ^ 58 := Nat.pow_le_pow_right (by decide) hhi
      have hbm_nat : (BitVec.ofNat 64 (2 ^ exp - 1)).toNat = 2 ^ exp - 1 := by
        simp only [BitVec.toNat_ofNat]; omega
      have hnotlt : ¬ (BitVec.ofNat 64 (2 ^ exp - 1) < 8#64) := by
        rw [BitVec.lt_def, hbm_nat]
        change ¬ (2 ^ exp - 1 < 8)
        omega
      unfold bucketMaskToCapacity bucketMaskToCapacityBV
      simp only [he2, ↓reduceIte, hnotlt]
      have hadd : BitVec.ofNat 64 (2 ^ exp - 1) + 1#64 = BitVec.ofNat 64 (2 ^ exp) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, hbm_nat]
        change ((2 ^ exp - 1) + 1) % 2 ^ 64 = (BitVec.ofNat 64 (2 ^ exp)).toNat
        simp only [BitVec.toNat_ofNat]
        omega
      rw [hadd]
      have hpow8 : 2 ^ exp = 2 ^ (exp - 3) * 8 := by
        have hexp : exp = (exp - 3) + 3 := by omega
        calc 2 ^ exp = 2 ^ ((exp - 3) + 3) := by rw [← hexp]
          _ = 2 ^ (exp - 3) * 2 ^ 3 := Nat.pow_add 2 (exp - 3) 3
          _ = 2 ^ (exp - 3) * 8 := rfl
      have hsh : (BitVec.ofNat 64 (2 ^ exp) >>> 3).toNat = 2 ^ (exp - 3) := by
        rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.shiftRight_eq_div_pow, hpow8]
        exact Nat.mul_div_cancel _ (by decide)
      have hle : 2 ^ (exp - 3) ≤ 2 ^ 55 := Nat.pow_le_pow_right (by decide) (by omega)
      rw [BitVec.toNat_mul, hsh]
      change (2 ^ (exp - 3) * 7) % 2 ^ 64 = 7 * 2 ^ (exp - 3)
      rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]

theorem ValidBucketMask.capacity_bounds {bm : BitVec 64} (h : ValidBucketMask bm) :
    3 ≤ bucketMaskToCapacity bm ∧ bucketMaskToCapacity bm < bm.toNat + 1 := by
  obtain ⟨exp, hlo, hhi, hbm⟩ := h
  rw [ValidBucketMask.buckets_eq hlo hhi hbm, ValidBucketMask.capacity_eq hlo hhi hbm]
  by_cases he2 : exp = 2
  · subst he2; decide
  · simp only [he2, ↓reduceIte]
    have he3 : 3 ≤ exp := by omega
    have hpos : 1 ≤ 2 ^ (exp - 3) := Nat.one_le_pow _ _ (by decide)
    have hpow : 2 ^ exp = 8 * 2 ^ (exp - 3) := by
      have hexp : exp = (exp - 3) + 3 := by omega
      calc 2 ^ exp = 2 ^ ((exp - 3) + 3) := by rw [← hexp]
        _ = 2 ^ (exp - 3) * 2 ^ 3 := Nat.pow_add 2 (exp - 3) 3
        _ = 8 * 2 ^ (exp - 3) := by omega
    omega

/-! ## Triangular Probe Sequence -/

/-- Triangular group step number `k * (k + 1) / 2` after `k` outer-loop strides. -/
def triGroupIdx (k : Nat) : Nat := k * (k + 1) / 2

/-- Triangular byte offset `8 * triGroupIdx k = 4 * k * (k + 1)` added to `pos₀` after `k` steps
    (`stride` increments by `8` each step: `0, 8, 24, 48, ...`). -/
def triByteOff (k : Nat) : Nat := 4 * k * (k + 1)

@[simp]
theorem triByteOff_zero : triByteOff 0 = 0 := rfl

theorem triByteOff_succ (k : Nat) :
    triByteOff (k + 1) = triByteOff k + 8 * (k + 1) := by
  unfold triByteOff
  calc 4 * (k + 1) * (k + 2)
    _ = 4 * (k + 1) * k + 4 * (k + 1) * 2 := Nat.mul_add (4 * (k + 1)) k 2
    _ = 4 * ((k + 1) * k) + 8 * (k + 1) := by rw [Nat.mul_assoc]; omega
    _ = 4 * (k * (k + 1)) + 8 * (k + 1) := by rw [Nat.mul_comm (k + 1) k]
    _ = 4 * k * (k + 1) + 8 * (k + 1) := by rw [← Nat.mul_assoc]

theorem triByteOff_eq_eight_mul_triGroupIdx (k : Nat) :
    triByteOff k = 8 * triGroupIdx k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [triByteOff_succ, ih, ← Nat.mul_add]
    congr 1
    show n * (n + 1) / 2 + (n + 1) = (n + 1) * (n + 2) / 2
    have heq : (n + 1) * (n + 2) = n * (n + 1) + 2 * (n + 1) := by
      calc (n + 1) * (n + 2)
        _ = (n + 1) * n + (n + 1) * 2 := Nat.mul_add (n + 1) n 2
        _ = n * (n + 1) + 2 * (n + 1) := by rw [Nat.mul_comm (n + 1) n, Nat.mul_comm (n + 1) 2]
    rw [heq, Nat.add_mul_div_left _ _ (by decide)]


/-! ## Control-Byte Mirror Invariant and Group Windows -/

/-- Mirror index written by `RawTableInner::set_ctrl(index, tag)`:
    `((index - 8) & bucket_mask) + 8`. -/
def setCtrlMirrorIdx (bm : BitVec 64) (idx : Nat) : Nat :=
  (((BitVec.ofNat 64 idx - 8#64) &&& bm) + 8#64).toNat

/-- Control-byte mirror and tag-validity invariant on `ctrl[0 .. buckets + 8)`:
    for `buckets = 4`, `ctrl[4..8)` are `tagEmpty` (`0xff`) and `ctrl[8..12)` mirror `ctrl[0..4)`;
    for `buckets ≥ 8`, `ctrl[buckets .. buckets + 8)` mirror `ctrl[0..8)`. -/
def CtrlMirrorInv (buckets : Nat) (ctrl : List (BitVec 8)) : Prop :=
  ctrl.length = buckets + 8 ∧
  (∀ b ∈ ctrl, ValidTag b) ∧
  (buckets = 4 →
    (∀ j < 4, ctrl[4 + j]? = some tagEmpty) ∧
    (∀ j < 4, ctrl[8 + j]? = ctrl[j]?)) ∧
  (8 ≤ buckets → ∀ j < 8, ctrl[buckets + j]? = ctrl[j]?)

theorem CtrlMirrorInv_init (buckets : Nat) (hb : buckets = 4 ∨ 8 ≤ buckets) :
    CtrlMirrorInv buckets (List.replicate (buckets + 8) tagEmpty) := by
  refine ⟨List.length_replicate .., ?_, ?_, ?_⟩
  · intro b hmem
    rw [List.mem_replicate] at hmem
    rw [hmem.2]
    exact ValidTag.empty
  · intro h4
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [List.getElem?_eq_getElem (by simp; omega)]
      simp
    · rw [List.getElem?_eq_getElem (by simp; omega), List.getElem?_eq_getElem (by simp; omega)]
      simp
  · intro _ j hj
    rcases hb with rfl | _
    · omega
    · rw [List.getElem?_eq_getElem (by simp; omega), List.getElem?_eq_getElem (by simp; omega)]
      simp

/-- Number of 8-byte probe groups in a table with `bucket_mask = bm`:
    `1` when `buckets = 4`, and `buckets / 8 = 2^(exp - 3)` when `buckets ≥ 8`. -/
def numGroups (bm : BitVec 64) : Nat :=
  max 1 ((bm.toNat + 1) / 8)

/-- 8-byte slice `ctrl[pos .. pos + 8)` loaded by `ldr d, [ctrlPtr, pos]`. -/
def ctrlGroupAt (ctrl : List (BitVec 8)) (pos : Nat) : List (BitVec 8) :=
  (ctrl.drop pos).take 8


end VerifiedLibraries.SwissTable
