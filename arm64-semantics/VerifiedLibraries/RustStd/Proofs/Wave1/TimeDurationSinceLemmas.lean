/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.ExecSeg
public import VerifiedLibraries.RustStd.Proofs.Wave1.TimePlacement
public import VerifiedLibraries.RustStd.Generated.TimePlacedObj
public import ProofLib.GenPlacedFetches
public meta import ProofLib.ProgramReflection
public import ProofLib

/-!
# Helper Lemmas and Placed Fetches for `SystemTime::duration_since`

Proves signed nanosecond borrow-arithmetic and branch equivalences, 128-bit SIMD `eor` tag-flip
and stack/`sret` splitting lemmas, and placed instruction fetches for `Timespec::sub_timespec`
and `SystemTime::duration_since` in `timeMultiLib`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.literalFetch false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches

/-! ## `Timespec` Borrow-Arithmetic and Comparison Lemmas -/

/-- Signed nanosecond timestamp `s.toInt * 10^9 + n.toNat` of a `(tv_sec : i64, tv_nsec : u32)` pair. -/
abbrev timespecNs (s : BitVec 64) (n : BitVec 32) : Int :=
  s.toInt * 10 ^ 9 + n.toNat

/-- Symbolic 64-bit value placed in `x13` by the lexicographic comparison sequence
    `cmp w12, w10; cset w13, hs; cmp x9, x11; cset w14, ge; csel w13, w13, w14, eq`
    (`0x24 .. 0x34` of `Timespec::sub_timespec`). -/
def subTimespecCmpWord (sa sb : BitVec 64) (na nb : BitVec 32) : BitVec 64 :=
  if (sa == sb) = true then if na.ult nb = true then 0#64 else 1#64
  else if sa.slt sb = true then 0#64 else 1#64

/-- Symbolic 32-bit nanosecond difference placed in `w8` on the `t2 ≤ t1` path of
    `Timespec::sub_timespec` (`0x3c .. 0x54`). -/
def subTimespecNsec (na nb : BitVec 32) : BitVec 32 :=
  (if na.ult nb = true then na + 1000000000#32 else na) - nb

/-- Symbolic 64-bit second difference placed in `x9` on the `t2 ≤ t1` path of
    `Timespec::sub_timespec` (`0x50 .. 0x60`: `neg x12, x11; csinv x10, x12, x11, hs; add x9, x10, x9`). -/
def subTimespecSecs (sa sb : BitVec 64) (na nb : BitVec 32) : BitVec 64 :=
  (if nb.ule na = true then -sb else ~~~sb) + sa

private theorem toInt_bounds64 (x : BitVec 64) :
    -(2 ^ 63 : Int) ≤ x.toInt ∧ x.toInt < (2 ^ 63 : Int) := by
  unfold BitVec.toInt
  have := x.isLt
  split <;> omega

private theorem toInt_inj64 {x y : BitVec 64} (h : x.toInt = y.toInt) : x = y := by
  apply BitVec.eq_of_toNat_eq
  unfold BitVec.toInt at h
  have := x.isLt
  have := y.isLt
  split at h <;> split at h <;> omega

private theorem bv64_neg_add_eq_ofNat {a b : BitVec 64} {q : Nat}
    (hq : (q : Int) = a.toInt - b.toInt) (hlt : q < 2 ^ 64) :
    -b + a = BitVec.ofNat 64 q := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  unfold BitVec.toInt at hq
  by_cases hb0 : b.toNat = 0
  · have hq_a : q = a.toNat := by split at hq <;> split at hq <;> omega
    have hb_eq : b = 0#64 := BitVec.eq_of_toNat_eq hb0
    subst hb_eq hq_a
    simp
  · have hneg : (-b).toNat = 2 ^ 64 - b.toNat := by
      rw [BitVec.toNat_neg, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add, hneg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    by_cases hle : b.toNat ≤ a.toNat
    · have hq_eq : q = a.toNat - b.toNat := by split at hq <;> split at hq <;> omega
      rw [show 2 ^ 64 - b.toNat + a.toNat = 2 ^ 64 + (a.toNat - b.toNat) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega), hq_eq]
    · have hq_eq : q = 2 ^ 64 - b.toNat + a.toNat := by split at hq <;> split at hq <;> omega
      rw [Nat.mod_eq_of_lt (by omega), hq_eq]

private theorem bv64_not_add_eq_ofNat {a b : BitVec 64} {q : Nat}
    (hq : (q : Int) = a.toInt - b.toInt - 1) (hlt : q < 2 ^ 64) :
    ~~~b + a = BitVec.ofNat 64 q := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  unfold BitVec.toInt at hq
  rw [BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  by_cases hlt_ba : b.toNat < a.toNat
  · have hq_eq : q = a.toNat - 1 - b.toNat := by split at hq <;> split at hq <;> omega
    rw [show 2 ^ 64 - 1 - b.toNat + a.toNat = 2 ^ 64 + (a.toNat - 1 - b.toNat) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega), hq_eq]
  · have hq_eq : q = 2 ^ 64 - 1 - b.toNat + a.toNat := by split at hq <;> split at hq <;> omega
    rw [Nat.mod_eq_of_lt (by omega), hq_eq]

private theorem bv32_toNat_add_of_lt {x y : BitVec 32} (h : x.toNat + y.toNat < 2 ^ 32) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

private theorem bv32_toNat_sub_of_le {x y : BitVec 32} (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  rw [BitVec.toNat_sub, show 2 ^ 32 - y.toNat + x.toNat = 2 ^ 32 + (x.toNat - y.toNat) by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

theorem subTimespec_tbz_eq_false_of_le {sa sb : BitVec 64} {na nb : BitVec 32}
    (hna : na.toNat < 10 ^ 9) (hnb : nb.toNat < 10 ^ 9)
    (hle : timespecNs sb nb ≤ timespecNs sa na) :
    ((subTimespecCmpWord sa sb na nb).getLsbD 0 == false) = false := by
  unfold subTimespecCmpWord
  by_cases hseq : (sa == sb) = true
  · have hs : sa = sb := eq_of_beq hseq
    subst hs
    have hnle : nb.toNat ≤ na.toNat := by unfold timespecNs at hle; omega
    have hult : na.ult nb = false := decide_eq_false (by omega)
    simp [hult]
  · simp only [Bool.not_eq_true] at hseq
    have hsne : sa.toInt ≠ sb.toInt := fun heq => by
      have := toInt_inj64 heq; subst this; simp at hseq
    have hslt_int : ¬(sa.toInt < sb.toInt) := by
      unfold timespecNs at hle; omega
    have hslt : sa.slt sb = false := decide_eq_false hslt_int
    simp [hseq, hslt]

theorem subTimespec_tbz_eq_true_of_lt {sa sb : BitVec 64} {na nb : BitVec 32}
    (hna : na.toNat < 10 ^ 9) (hnb : nb.toNat < 10 ^ 9)
    (hlt : timespecNs sa na < timespecNs sb nb) :
    ((subTimespecCmpWord sa sb na nb).getLsbD 0 == false) = true := by
  unfold subTimespecCmpWord
  by_cases hseq : (sa == sb) = true
  · have hs : sa = sb := eq_of_beq hseq
    subst hs
    have hnlt : na.toNat < nb.toNat := by unfold timespecNs at hlt; omega
    have hult : na.ult nb = true := decide_eq_true hnlt
    simp [hult]
  · simp only [Bool.not_eq_true] at hseq
    have hsne : sa.toInt ≠ sb.toInt := fun heq => by
      have := toInt_inj64 heq; subst this; simp at hseq
    have hslt_int : sa.toInt < sb.toInt := by
      unfold timespecNs at hlt; omega
    have hslt : sa.slt sb = true := decide_eq_true hslt_int
    simp [hseq, hslt]

theorem subTimespec_tbz_iff {sa sb : BitVec 64} {na nb : BitVec 32}
    (hna : na.toNat < 10 ^ 9) (hnb : nb.toNat < 10 ^ 9) :
    ((subTimespecCmpWord sa sb na nb).getLsbD 0 == false) =
      decide (timespecNs sa na < timespecNs sb nb) := by
  by_cases hlt : timespecNs sa na < timespecNs sb nb
  · rw [decide_eq_true hlt, subTimespec_tbz_eq_true_of_lt hna hnb hlt]
  · rw [decide_eq_false hlt, subTimespec_tbz_eq_false_of_le hna hnb (by omega)]

/-- For `na, nb < 10^9`, `subTimespecNsec na nb < 10^9`, so `b.lo 0x80` (`0x64`) is always taken
    and the carry-overflow / `expect_failed` path is unreachable. -/
theorem subTimespec_nsec_ult_e9 {na nb : BitVec 32}
    (hna : na.toNat < 10 ^ 9) (hnb : nb.toNat < 10 ^ 9) :
    (subTimespecNsec na nb).ult 1000000000#32 = true := by
  unfold subTimespecNsec
  have he9 : (1000000000#32).toNat = 10 ^ 9 := rfl
  by_cases h : na.toNat < nb.toNat
  · have hult : na.ult nb = true := decide_eq_true h
    rw [hult]
    simp only [↓reduceIte]
    have hadd : (na + 1000000000#32).toNat = na.toNat + 10 ^ 9 :=
      bv32_toNat_add_of_lt (by rw [he9]; omega)
    have hsub : (na + 1000000000#32 - nb).toNat = na.toNat + 10 ^ 9 - nb.toNat := by
      rw [bv32_toNat_sub_of_le (by omega), hadd]
    exact decide_eq_true (by rw [hsub, he9]; omega)
  · have hult : na.ult nb = false := decide_eq_false h
    rw [hult]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hsub : (na - nb).toNat = na.toNat - nb.toNat := bv32_toNat_sub_of_le (by omega)
    exact decide_eq_true (by rw [hsub, he9]; omega)

theorem timespec_diff_bounds (sa sb : BitVec 64) {na nb : BitVec 32}
    (hna : na.toNat < 10 ^ 9) (hnb : nb.toNat < 10 ^ 9) :
    (timespecNs sa na - timespecNs sb nb).natAbs < 2 ^ 64 * 10 ^ 9 ∧
      (timespecNs sa na - timespecNs sb nb).natAbs / 10 ^ 9 < 2 ^ 64 := by
  have ha := toInt_bounds64 sa
  have hb := toInt_bounds64 sb
  have hd : (timespecNs sa na - timespecNs sb nb).natAbs < 2 ^ 64 * 10 ^ 9 := by
    unfold timespecNs; omega
  exact ⟨hd, Nat.div_lt_of_lt_mul (by omega)⟩

theorem subTimespec_nsec_eq_mod {sa sb : BitVec 64} {na nb : BitVec 32}
    (hna : na.toNat < 10 ^ 9) (hnb : nb.toNat < 10 ^ 9)
    (hle : timespecNs sb nb ≤ timespecNs sa na) :
    subTimespecNsec na nb =
      BitVec.ofNat 32 ((timespecNs sa na - timespecNs sb nb).natAbs % 10 ^ 9) := by
  unfold subTimespecNsec
  have he9 : (1000000000#32).toNat = 10 ^ 9 := rfl
  apply BitVec.eq_of_toNat_eq
  by_cases h : na.toNat < nb.toNat
  · have hult : na.ult nb = true := decide_eq_true h
    rw [hult]
    simp only [↓reduceIte]
    let q : Nat := (sa.toInt - sb.toInt - 1).toNat
    let r : Nat := na.toNat + 10 ^ 9 - nb.toNat
    have hr_lt : r < 10 ^ 9 := by omega
    have hd_eq : (timespecNs sa na - timespecNs sb nb).natAbs = 10 ^ 9 * q + r := by
      unfold timespecNs at hle ⊢; omega
    have hmod : (timespecNs sa na - timespecNs sb nb).natAbs % 10 ^ 9 = r := by
      rw [hd_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt hr_lt]
    have hadd : (na + 1000000000#32).toNat = na.toNat + 10 ^ 9 :=
      bv32_toNat_add_of_lt (by rw [he9]; omega)
    rw [bv32_toNat_sub_of_le (by omega), hadd, hmod, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  · have hult : na.ult nb = false := decide_eq_false h
    rw [hult]
    simp only [Bool.false_eq_true, ↓reduceIte]
    let q : Nat := (sa.toInt - sb.toInt).toNat
    let r : Nat := na.toNat - nb.toNat
    have hr_lt : r < 10 ^ 9 := by omega
    have hd_eq : (timespecNs sa na - timespecNs sb nb).natAbs = 10 ^ 9 * q + r := by
      unfold timespecNs at hle ⊢; omega
    have hmod : (timespecNs sa na - timespecNs sb nb).natAbs % 10 ^ 9 = r := by
      rw [hd_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt hr_lt]
    rw [bv32_toNat_sub_of_le (by omega), hmod, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]

theorem subTimespec_secs_eq_div {sa sb : BitVec 64} {na nb : BitVec 32}
    (hna : na.toNat < 10 ^ 9) (hnb : nb.toNat < 10 ^ 9)
    (hle : timespecNs sb nb ≤ timespecNs sa na) :
    subTimespecSecs sa sb na nb =
      BitVec.ofNat 64 ((timespecNs sa na - timespecNs sb nb).natAbs / 10 ^ 9) := by
  have ha := toInt_bounds64 sa
  have hb := toInt_bounds64 sb
  unfold subTimespecSecs
  by_cases h : nb.toNat ≤ na.toNat
  · have hule : nb.ule na = true := decide_eq_true h
    rw [hule]
    simp only [↓reduceIte]
    let q : Nat := (sa.toInt - sb.toInt).toNat
    let r : Nat := na.toNat - nb.toNat
    have hr_lt : r < 10 ^ 9 := by omega
    have hd_eq : (timespecNs sa na - timespecNs sb nb).natAbs = 10 ^ 9 * q + r := by
      unfold timespecNs at hle ⊢; omega
    have hdiv : (timespecNs sa na - timespecNs sb nb).natAbs / 10 ^ 9 = q := by
      rw [hd_eq, Nat.mul_add_div (by decide : 0 < 10 ^ 9), Nat.div_eq_of_lt hr_lt, Nat.add_zero]
    rw [hdiv]
    exact bv64_neg_add_eq_ofNat (by unfold timespecNs at hle; omega) (by omega)
  · have hule : nb.ule na = false := decide_eq_false h
    rw [hule]
    simp only [Bool.false_eq_true, ↓reduceIte]
    let q : Nat := (sa.toInt - sb.toInt - 1).toNat
    let r : Nat := na.toNat + 10 ^ 9 - nb.toNat
    have hr_lt : r < 10 ^ 9 := by omega
    have hd_eq : (timespecNs sa na - timespecNs sb nb).natAbs = 10 ^ 9 * q + r := by
      unfold timespecNs at hle ⊢; omega
    have hdiv : (timespecNs sa na - timespecNs sb nb).natAbs / 10 ^ 9 = q := by
      rw [hd_eq, Nat.mul_add_div (by decide : 0 < 10 ^ 9), Nat.div_eq_of_lt hr_lt, Nat.add_zero]
    rw [hdiv]
    exact bv64_not_add_eq_ofNat (by unfold timespecNs at hle; omega) (by omega)

theorem timespec_le_of_lt {t1 t2 : Int} (h : t1 < t2) : t1 ≤ t2 := by omega

theorem timespec_sub_natAbs_comm (t1 t2 : Int) :
    (t2 - t1).natAbs = (t1 - t2).natAbs := by omega

/-! ## 128-Bit SIMD `eor` Tag-Flip and Memory-Splitting Lemmas -/

theorem eor_cst16_truncate64 (secs : BitVec 64) :
    BitVec.truncate 64 ((secs ++ 0#64) ^^^ 1#128) = 1#64 := by
  bv_bits

theorem eor_cst16_extractHi64 (secs : BitVec 64) :
    BitVec.extractLsb' 64 64 ((secs ++ 0#64) ^^^ 1#128) = secs := by
  bv_bits

theorem truncate64_append64 (hi lo : BitVec 64) :
    BitVec.truncate 64 (hi ++ lo) = lo := by
  bv_bits

theorem extractHi64_append64 (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by
  bv_bits

theorem timePlacedData0_pointsToBytesRO_eq (c16 : BitVec 64) :
    (c16 ↦ᵣ timePlacedData0) = ((c16 ↦₆₄ᵣ 1#64) ∗ ((c16 + 8#64) ↦₆₄ᵣ 0#64)) := by
  have hd : timePlacedData0 =
      [1#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++
        [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] := rfl
  rw [hd, pointsToBytesRO_append, pointsToBytesRO8_eq_pointsTo64RO,
    pointsToBytesRO8_eq_pointsTo64RO]
  rfl

theorem memRegion20_eq_sret_slots (out : BitVec 64) :
    memRegion out 20 =
      ∃∗ (w2 : BitVec 32), ∃∗ (w1 : BitVec 64), ∃∗ (w0 : BitVec 64),
        (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₃₂ w2) := by
  rw [show (20 : Nat) = 8 + 8 + 4 from rfl, memRegion_split_three out 8 8 4 (by decide),
    memRegion_eight, memRegion_eight, memRegion_four,
    show out + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = out + 16#64 by bv_arith,
    show BitVec.ofNat 64 8 = 8#64 from rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem cells8_sub64_entails (sp w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    (((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗ ((sp - 48#64) ↦₆₄ w2) ∗
      ((sp - 40#64) ↦₆₄ w3) ∗ ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
      ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) ⊢ stackAt sp 64 := by
  rw [stackAt_eq_cells sp 8]
  refine cells_sub_succ_entails 64 8 <|
    cells_sub_succ_entails 56 7 <|
    cells_sub_succ_entails 48 6 <|
    cells_sub_succ_entails 40 5 <|
    cells_sub_succ_entails 32 4 <|
    cells_sub_succ_entails 24 3 <|
    cells_sub_succ_entails 16 2 ?_
  simpa [cells_zero, sepConj_emp] using
    cells_sub_succ_entails (sp := sp) 8 1 (v := w7) (Entails.refl emp)

theorem frame128_entails (sp w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    (stackAt (sp - 64#64) 64 ∗
      (((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗ ((sp - 48#64) ↦₆₄ w2) ∗
        ((sp - 40#64) ↦₆₄ w3) ∗ ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
        ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7))) ⊢ stackAt sp 128 := by
  rw [stackAt_frame sp 128 8 (by decide), ← stackAt_eq_cells sp 8]
  exact sepConj_mono_right (cells8_sub64_entails sp w0 w1 w2 w3 w4 w5 w6 w7)

theorem frame208_entails (sp w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) :
    (stackAt (sp - 80#64) 128 ∗
      (((sp - 80#64) ↦₆₄ w0) ∗ ((sp - 72#64) ↦₆₄ w1) ∗ ((sp - 64#64) ↦₆₄ w2) ∗
        ((sp - 56#64) ↦₆₄ w3) ∗ ((sp - 48#64) ↦₆₄ w4) ∗ ((sp - 40#64) ↦₆₄ w5) ∗
        ((sp - 32#64) ↦₆₄ w6) ∗ ((sp - 24#64) ↦₆₄ w7) ∗ ((sp - 16#64) ↦₆₄ w8) ∗
        ((sp - 8#64) ↦₆₄ w9))) ⊢ stackFrameAt sp 208 := by
  rw [← stackAt_eq_stackFrameAt sp 208, stackAt_frame sp 208 10 (by decide)]
  refine sepConj_mono_right <|
    cells_sub_succ_entails 80 10 <|
    cells_sub_succ_entails 72 9 <|
    cells_sub_succ_entails 64 8 <|
    cells_sub_succ_entails 56 7 <|
    cells_sub_succ_entails 48 6 <|
    cells_sub_succ_entails 40 5 <|
    cells_sub_succ_entails 32 4 <|
    cells_sub_succ_entails 24 3 <|
    cells_sub_succ_entails 16 2 ?_
  simpa [cells_zero, sepConj_emp] using
    cells_sub_succ_entails (sp := sp) 8 1 (v := w9) (Entails.refl emp)

/-! ## `.ldst128Lo12` Placed-Fetch Helper and `TimePlacement` Fetches -/

/-- Placed rebased fetch rule for 128-bit SIMD `:lo12:` load/store relocations
    (`R_AARCH64_LDST128_ABS_LO12_NC`, `RelocKind.ldst128Lo12`), complementing
    `PlacedLib.fetch_rebase_ldstLo12_of_placeable` (which covers GPR scales `0..3`). -/
theorem fetch_rebase_ldstSimd128Lo12_of_placeable {lib : PlacedLib} {pl : Placement} {off : Nat}
    {X O : String → Option (State → State)} {svc : State → State}
    {X' O' : String → Option (State → State)} {b : BitVec 64}
    {r : RelocEntry} {T : BitVec 64} {isLoad : Bool} {sz : SimdMemSize} {inst : Instr}
    (hP : lib.Placeable pl)
    (hr : lib.text.relocAt? off = some r) (hk : r.kind = .ldst128Lo12)
    (hh : ((lib.program pl X O svc).rebase b X' O').hookAtOff? off = none)
    {w : BitVec 32} (hwd : lib.text.wordAt off = w)
    (htype : decodeSimdLoadStoreType (w.extractLsb' 30 2).toNat (w.extractLsb' 22 2).toNat =
      some (isLoad, sz, 4))
    (hw1 : w &&& 0x3f000000#32 = 0x3d000000#32)
    (hT : lib.text.target pl r = T)
    (hinst : (let addr := AddrMode.Offset (Reg.fromSPBits (w.extractLsb' 5 5)) (lo12Of T)
      if isLoad then some (.ldrSimd sz (w.extractLsb' 0 5) addr)
      else some (.strSimd sz (w.extractLsb' 0 5) addr)) = some inst) :
    ((lib.program pl X O svc).rebase b X' O').fetch (b + BitVec.ofNat 64 off) = some inst := by
  subst hT hwd
  have hroff := CodeBlock.relocAt?_off hr
  obtain ⟨hal4, hlen, hrange⟩ := hP.text.relocs_ok r (CodeBlock.relocAt?_mem hr)
  rw [hroff] at hal4 hlen hrange
  have hnw := hP.text.no_wrap
  have hb : lib.text.b2bNext? r = none := by simp [CodeBlock.b2bNext?, hk]
  have hng : r.kind.isGotOrTlsIe = false := by simp [hk, RelocKind.isGotOrTlsIe]
  rw [CodeBlock.relocInRange_of_not_gotOrTlsIe hng,
    CodeBlock.relocTarget_of_b2bNext_none hb, hk] at hrange
  change Lo12Aligned 4 _ at hrange
  have hnrel : lib.text.relaxableAt off = false :=
    CodeBlock.relaxableAt_false_of_kind hr (by simp [hk])
  have hf := Program.fetch_of_readWordOff (prog := (lib.program pl X O svc).rebase b X' O')
    (off := off) (by omega) hh (CodeBlock.readWordOff_patched (pl := pl) (by simp) hal4 hlen)
  rw [CodeBlock.patchedWord_of_unpaired hr hnrel (by simp [hk]) (by simp [hk]) (by simp [hk]) hng,
    hk, show patchRelocWord .ldst128Lo12 (lib.text.wordAt off) _ _ =
      lo12Word 4 (lib.text.wordAt off) _ from rfl,
    decode_ldstSimdLo12Word htype hw1 hrange, hinst] at hf
  simpa using hf

abbrev timeSubTimespecLocalSym : String :=
  "<std::sys::pal::unix::time::Timespec>::sub_timespec [rust_time]"

theorem timeFnAddr_eq_base [TimePlacement] (j : Nat) (sym : String)
    (hj : j < timeMultiLib.blocks.length)
    (hl : lookup sym timeMultiLib.blocks[j].symbols = some 0) :
    timeMultiLib.fnAddr timeMpl sym = timeMpl.base j :=
  fnAddr_eq_base TimePlacement.placeable j sym hj hl

def timeLib00 : PlacedLib := timeMultiLib.blockLib 0
def timePl00 [TimePlacement] : Placement := timeMultiLib.blockPlacement TimePlacement.mpl 0
theorem timePlaceable00 [TimePlacement] : timeLib00.Placeable timePl00 :=
  timeMultiLib.placeable_blockLib (by decide) TimePlacement.placeable
def timePC00 [TimePlacement] : Program := timeLib00.program timePl00

def timeLib01 : PlacedLib := timeMultiLib.blockLib 1
def timePl01 [TimePlacement] : Placement := timeMultiLib.blockPlacement TimePlacement.mpl 1
theorem timePlaceable01 [TimePlacement] : timeLib01.Placeable timePl01 :=
  timeMultiLib.placeable_blockLib (by decide) TimePlacement.placeable
def timePC01 [TimePlacement] : Program := timeLib01.program timePl01

def timeProg00 : Program := { code := timeLib00.text.code, symbols := timeLib00.text.symbols }
def timeTree00 : WordTree := word_tree_of% timeProg00
theorem time00_code_eq : timeLib00.text.code = timeTree00.toBytes := by rfl_kernel
theorem time00_tree_size : timeTree00.checkSize? = some 60 := by rfl_kernel
def timeSymChars00 : List (List Char × Nat) := sym_chars_of% timeProg00
theorem time00_symbols_eq : timeLib00.text.symbols = toStringSymbols timeSymChars00 := by rfl_kernel
theorem time00_symbols_fresh : allFreshCharSymbols timeSymChars00 = true := by rfl_kernel

gen_placed_fetches timePC00 timeLib00 timeTree00 time00_code_eq time00_tree_size
  via_placement timePl00 timePlaceable00 [0x0 → 0xec]
gen_placed_fnOffs timePC00 timeLib00 timeSymChars00 time00_symbols_eq time00_symbols_fresh

/-- Plain `ADRP x8, rust_time:.rodata.cst16+0x0` step at `0xac` (`172`) in `Timespec::sub_timespec`
    (paired with `ldr q1` at `0xb4`, not an `ADRP+ADD` relaxable pair). -/
theorem timePC00_adrp_0xac [TimePlacement] (b : BitVec 64)
    (X : String → Option (State → State)) (hb : b = timePl00.base)
    {tgt : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 172) (hrun : s.status = .Running)
    (hnext : SepWP (timePC00.rebase b X) tgt
      ((s.writeReg64 (.gpr 8#5) (pageOf (timePl00.ρ "rust_time:.rodata.cst16+0x0"))).setPC
        (b + BitVec.ofNat 64 176)) P post oom) :
    SepWP (timePC00.rebase b X) tgt s P post oom :=
  PlacedLib.sepWP_rebase_adrpPlain (lib := timeLib00) (pl := timePl00) (off := 172) (off4 := 176)
    (r := ⟨172, .adrpHi21, "rust_time:.rodata.cst16+0x0", 0, false⟩) (rd := 8#5) (w := 0x90000008#32)
    timePlaceable00 hb rfl rfl
    (by
      unfold CodeBlock.relaxableAt
      rw [show timeLib00.text.relocAt? 172 = some ⟨172, .adrpHi21, "rust_time:.rodata.cst16+0x0", 0, false⟩ from rfl,
          show timeLib00.text.relocAt? 176 = none from rfl])
    (wordAt_of_getQuad? time00_code_eq time00_tree_size (j := 43) rfl)
    (by decide) rfl (by decide) rfl rfl
    (hookAtOff?_rebase_of_placeable time00_code_eq time00_tree_size timePlaceable00 (by omega))
    hpc hrun hnext

@[simp, arm64_norm] theorem timePC00_rebase_fetch_0xb4 [TimePlacement] (b : BitVec 64)
    (X : String → Option (State → State)) :
    (timePC00.rebase b X).fetch (b + BitVec.ofNat 64 180) =
      some (.ldrSimd .Q128 1#5 (.Offset (.gpr 8#5)
        (lo12Of (timePl00.ρ "rust_time:.rodata.cst16+0x0")))) :=
  fetch_rebase_ldstSimd128Lo12_of_placeable (lib := timeLib00) (pl := timePl00) (off := 180)
    (r := ⟨180, .ldst128Lo12, "rust_time:.rodata.cst16+0x0", 0, false⟩) (w := 0x3dc00101#32)
    timePlaceable00 rfl rfl
    (hookAtOff?_rebase_of_placeable time00_code_eq time00_tree_size timePlaceable00 (by omega))
    (wordAt_of_getQuad? time00_code_eq time00_tree_size (j := 45) rfl)
    rfl (by decide) rfl rfl

def timeProg01 : Program := { code := timeLib01.text.code, symbols := timeLib01.text.symbols }
def timeTree01 : WordTree := word_tree_of% timeProg01
theorem time01_code_eq : timeLib01.text.code = timeTree01.toBytes := by rfl_kernel
theorem time01_tree_size : timeTree01.checkSize? = some 20 := by rfl_kernel
def timeSymChars01 : List (List Char × Nat) := sym_chars_of% timeProg01
theorem time01_symbols_eq : timeLib01.text.symbols = toStringSymbols timeSymChars01 := by rfl_kernel
theorem time01_symbols_fresh : allFreshCharSymbols timeSymChars01 = true := by rfl_kernel

gen_placed_fetches timePC01 timeLib01 timeTree01 time01_code_eq time01_tree_size
  via_placement timePl01 timePlaceable01 [0x0 → 0x4c]
gen_placed_fnOffs timePC01 timeLib01 timeSymChars01 time01_symbols_eq time01_symbols_fresh

theorem timeBlockNoSvc0_00 : checkBlockNoSvc0 timeLib00.text = true := by decide
theorem timeBlockNoSvc0_01 : checkBlockNoSvc0 timeLib01.text = true := by decide

theorem timePl00_rho_cst16 [TimePlacement] :
    timePl00.ρ "rust_time:.rodata.cst16+0x0" = timeMpl.ρ "rust_time:.rodata.cst16+0x0" := rfl

theorem timePl01_rho_subTimespec [TimePlacement] :
    timePl01.ρ timeSubTimespecLocalSym = timePl00.base := by
  have hl : lookupBlockSym timeSubTimespecLocalSym timeMultiLib.blocks = some (0, 0) := by decide
  simp [timePl01, timePl00, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, hl]

end VerifiedLibraries.RustStd
