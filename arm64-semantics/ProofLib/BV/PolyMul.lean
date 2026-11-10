/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SimpAttrs

/-!
# Carry-Less Polynomial Multiplication

Algebraic and bit-level lemmas for `Arm64.polyMul` and `Arm64.evalPmull`: step recurrences,
64-bit SIMD lane extraction, $\mathbb{F}_2[x]$ bilinearity and shift laws, degree bounds, and
packed two-lane 16x16-to-32-bit carry-less multiplication inside a single 64-bit `PMULL`.
-/

@[expose] public section

namespace Arm64

/-! ## `evalPmull` 64-bit lane projections and `polyMul` step recurrence -/

/-- `PMULL Vd.1Q, Vn.1D, Vm.1D` (`q = false`, `is64 = true`) multiplies the low 64-bit lanes. -/
@[simp, arm64_norm, wp_norm]
theorem evalPmull_false_true (vn vm : BitVec 128) :
    evalPmull false true vn vm = polyMul 64 (vn.truncate 64) (vm.truncate 64) :=
  rfl

/-- `PMULL2 Vd.1Q, Vn.2D, Vm.2D` (`q = true`, `is64 = true`) multiplies the high 64-bit lanes. -/
@[simp, arm64_norm, wp_norm]
theorem evalPmull_true_true (vn vm : BitVec 128) :
    evalPmull true true vn vm = polyMul 64 (vn.extractLsb' 64 64) (vm.extractLsb' 64 64) :=
  rfl

@[simp]
theorem polyMul_zero (op1 op2 : BitVec 64) :
    polyMul 0 op1 op2 = 0#128 :=
  rfl

/-- Single-bit step recurrence for `polyMul (n + 1)`. -/
theorem polyMul_succ (n : Nat) (op1 op2 : BitVec 64) :
    polyMul (n + 1) op1 op2 =
      if op1.getLsbD n then polyMul n op1 op2 ^^^ ((op2.zeroExtend 128) <<< n)
      else polyMul n op1 op2 := by
  simp only [polyMul, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ## SIMD 64-bit lane truncation normalizers -/

/-- Low 64-bit lane extraction `(v &&& 0xffffffffffffffff#128).truncate 64` reduces to `v.truncate 64`. -/
theorem truncate_64_and_mask64 (v : BitVec 128) :
    (v &&& 0xffffffffffffffff#128).truncate 64 = v.truncate 64 := by
  have hm : (0xffffffffffffffff#128 : BitVec 128) = (BitVec.allOnes 64).zeroExtend 128 := by decide
  have hall : ∀ (i : Nat) (hi : i < 64), (18446744073709551615#64)[i]'hi = true := by decide
  rw [hm]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, hall]

/-- High 64-bit lane extraction `((v >>> 64) &&& 0xffffffffffffffff#128).truncate 64` (`UMOV Xd, Vn.D[1]`)
    reduces to `v.extractLsb' 64 64`. -/
theorem truncate_64_ushr_64_and_mask64 (v : BitVec 128) :
    ((v >>> 64) &&& 0xffffffffffffffff#128).truncate 64 = v.extractLsb' 64 64 := by
  have hm : (0xffffffffffffffff#128 : BitVec 128) = (BitVec.allOnes 64).zeroExtend 128 := by decide
  have hall : ∀ (i : Nat) (hi : i < 64), (18446744073709551615#64)[i]'hi = true := by decide
  rw [hm]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h128 : i < 128 := by omega
  simp [hi, h128, Nat.add_comm 64 i, hall]

theorem bitvec128_ushiftRight_zero (v : BitVec 128) :
    v >>> 0 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

/-! ## $\mathbb{F}_2[x]$ bilinearity, disjoint-OR, and shift laws -/

@[simp]
theorem polyMul_zero_left (n : Nat) (op2 : BitVec 64) :
    polyMul n 0#64 op2 = 0#128 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [polyMul_succ, ih]
    simp

@[simp]
theorem polyMul_zero_right (n : Nat) (op1 : BitVec 64) :
    polyMul n op1 0#64 = 0#128 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [polyMul_succ, ih]
    have hz : ((0#64).zeroExtend 128) <<< k = 0#128 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp [hi]
    rw [hz]
    split <;> rfl

theorem polyMul_one_left {n : Nat} (hn : 0 < n) (op2 : BitVec 64) :
    polyMul n 1#64 op2 = op2.zeroExtend 128 := by
  induction n with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      rw [polyMul_succ, polyMul_zero]
      have h0 : (1#64).getLsbD 0 = true := by decide
      rw [h0]
      simp only [↓reduceIte]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp [hi]
    | succ m =>
      rw [polyMul_succ, ih (by omega)]
      have hm : (1#64).getLsbD (m + 1) = false := by simp
      rw [hm]
      rfl

private theorem xor_cancel_right {w : Nat} (x y z : BitVec w) :
    (x ^^^ z) ^^^ (y ^^^ z) = x ^^^ y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> rfl

private theorem xor_assoc_symm {w : Nat} (x y z : BitVec w) :
    (x ^^^ y) ^^^ z = x ^^^ (y ^^^ z) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> rfl

private theorem xor_right_comm {w : Nat} (x y z : BitVec w) :
    (x ^^^ z) ^^^ y = (x ^^^ y) ^^^ z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> rfl

private theorem xor_xor_xor_comm {w : Nat} (a b c d : BitVec w) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> cases d.getLsbD i <;> rfl

theorem polyMul_xor_left (n : Nat) (a b c : BitVec 64) :
    polyMul n (a ^^^ b) c = polyMul n a c ^^^ polyMul n b c := by
  induction n with
  | zero => simp [polyMul_zero]
  | succ k ih =>
    rw [polyMul_succ, polyMul_succ, polyMul_succ, ih, BitVec.getLsbD_xor]
    cases a.getLsbD k <;> cases b.getLsbD k <;>
      simp only [Bool.bne_false, Bool.bne_true, Bool.not_false, Bool.not_true,
        ↓reduceIte, Bool.false_eq_true]
    · exact xor_assoc_symm _ _ _
    · exact (xor_right_comm _ _ _).symm
    · exact (xor_cancel_right _ _ _).symm

theorem polyMul_xor_right (n : Nat) (a b c : BitVec 64) :
    polyMul n a (b ^^^ c) = polyMul n a b ^^^ polyMul n a c := by
  induction n with
  | zero => simp [polyMul_zero]
  | succ k ih =>
    rw [polyMul_succ, polyMul_succ, polyMul_succ, ih]
    split
    · have hsh : (((b ^^^ c).zeroExtend 128) <<< k) =
          (((b.zeroExtend 128) <<< k) ^^^ ((c.zeroExtend 128) <<< k)) := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp only [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hi,
          decide_true, Bool.true_and]
        by_cases h1 : i < k
        · simp [h1]
        · have hlt128 : i - k < 128 := by omega
          simp only [h1, hlt128, decide_false, Bool.not_false, decide_true, Bool.true_and]
      rw [hsh]
      exact xor_xor_xor_comm _ _ _ _
    · rfl

private theorem bitvec_or_eq_xor_of_and_eq_zero {w : Nat} {x y : BitVec w} (h : x &&& y = 0#w) :
    x ||| y = x ^^^ y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have hi : (x &&& y).getLsbD i = (0#w).getLsbD i := congrArg (fun z => z.getLsbD i) h
  rw [BitVec.getLsbD_and, BitVec.getLsbD_zero] at hi
  rw [BitVec.getLsbD_or, BitVec.getLsbD_xor]
  cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all

theorem polyMul_or_right_of_and_eq_zero (n : Nat) (a b c : BitVec 64) (hdisj : b &&& c = 0#64) :
    polyMul n a (b ||| c) = polyMul n a b ^^^ polyMul n a c := by
  rw [bitvec_or_eq_xor_of_and_eq_zero hdisj, polyMul_xor_right]

/-- Truncating `esize` from `n` to `m ≤ n` when bits `[m, n)` of `a` are zero. -/
theorem polyMul_eq_of_high_bits_false {m n : Nat} (hmn : m ≤ n) (a b : BitVec 64)
    (ha : ∀ i, m ≤ i → i < n → a.getLsbD i = false) :
    polyMul n a b = polyMul m a b := by
  induction n with
  | zero =>
    have hm0 : m = 0 := by omega
    subst hm0; rfl
  | succ k ih =>
    by_cases hmk : m = k + 1
    · subst hmk; rfl
    · have hle : m ≤ k := by omega
      rw [polyMul_succ, ha k hle (by omega)]
      exact ih hle (fun i h1 h2 => ha i h1 (by omega))

private theorem bitvec128_shiftLeft_xor (x y : BitVec 128) (s : Nat) :
    (x ^^^ y) <<< s = (x <<< s) ^^^ (y <<< s) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_xor, hi, decide_true, Bool.true_and]
  by_cases his : i < s <;> simp [his]

private theorem bitvec128_shiftLeft_comm (z : BitVec 128) (s k : Nat) :
    (z <<< s) <<< k = (z <<< k) <<< s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hlt1 : i - k < 128 := by omega
  have hlt2 : i - s < 128 := by omega
  simp only [BitVec.getLsbD_shiftLeft, hi, hlt1, hlt2, decide_true, Bool.true_and]
  by_cases hks : i < k + s
  · have h1 : i < k ∨ i - k < s := by omega
    have h2 : i < s ∨ i - s < k := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]
  · have h1 : ¬(i < k) := by omega
    have h2 : ¬(i - k < s) := by omega
    have h3 : ¬(i < s) := by omega
    have h4 : ¬(i - s < k) := by omega
    have hsub : i - k - s = i - s - k := by omega
    simp [h1, h2, h3, h4, hsub]

/-- Shifting the right operand by `s` shifts the 128-bit polynomial product by `s`, provided
    shifting `b` left by `s` does not overflow 64 bits. -/
theorem polyMul_shiftLeft_right (n s : Nat) (a b : BitVec 64)
    (hb : ∀ i, 64 - s ≤ i → i < 64 → b.getLsbD i = false) :
    polyMul n a (b <<< s) = (polyMul n a b) <<< s := by
  have hzext : ((b <<< s).zeroExtend 128) = ((b.zeroExtend 128) <<< s) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hsub128 : i - s < 128 := by omega
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, hi, hsub128, decide_true,
      Bool.true_and]
    by_cases his : i < s
    · simp [his]
    · simp only [his, decide_false, Bool.not_false, Bool.true_and]
      by_cases hi64 : i < 64
      · simp [hi64]
      · simp only [hi64, decide_false, Bool.false_and]
        by_cases hsub64 : i - s < 64
        · exact (hb (i - s) (by omega) hsub64).symm
        · exact (BitVec.getLsbD_of_ge b (i - s) (by omega)).symm
  induction n with
  | zero =>
    simp only [polyMul_zero]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]
  | succ k ih =>
    rw [polyMul_succ, polyMul_succ, ih, hzext]
    split
    · rw [bitvec128_shiftLeft_xor, bitvec128_shiftLeft_comm]
    · rfl

/-! ## Degree bounds and packed two-lane 16x16 carry-less multiplication -/

/-- Degree bound: if bits `≥ k` of `b` are zero, then bits `≥ m + k` of `polyMul m a b` are zero. -/
theorem polyMul_getLsbD_false_of_ge (m k : Nat) (a b : BitVec 64)
    (hb : ∀ j, k ≤ j → j < 64 → b.getLsbD j = false) {i : Nat} (hi : m + k ≤ i) :
    (polyMul m a b).getLsbD i = false := by
  induction m with
  | zero => simp [polyMul_zero]
  | succ r ih =>
    rw [polyMul_succ]
    have ihr : (polyMul r a b).getLsbD i = false := ih (by omega)
    split
    · by_cases hi128 : i < 128
      · have hnotlt : ¬(i < r) := by omega
        have hsub128 : i - r < 128 := by omega
        simp only [BitVec.getLsbD_xor, ihr, Bool.false_bne, BitVec.getLsbD_shiftLeft,
          BitVec.getLsbD_setWidth, hi128, hsub128, decide_true, Bool.true_and, hnotlt,
          decide_false, Bool.not_false]
        by_cases hsub64 : i - r < 64
        · exact hb (i - r) (by omega) hsub64
        · exact BitVec.getLsbD_of_ge b (i - r) (by omega)
      · exact BitVec.getLsbD_of_ge _ i (by omega)
    · exact ihr

/-- Any 16x16-bit carry-less product fits in its low 32 bits (`bits ≥ 32` are zero). -/
theorem polyMul_16_eq_zeroExtend_truncate32 (a b : BitVec 16) :
    polyMul 16 (a.zeroExtend 64) (b.zeroExtend 64) =
      ((polyMul 16 (a.zeroExtend 64) (b.zeroExtend 64)).truncate 32).zeroExtend 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases hi32 : i < 32
  · simp [hi32]
  · simp only [hi32, decide_false, Bool.false_and]
    exact polyMul_getLsbD_false_of_ge 16 16 (a.zeroExtend 64) (b.zeroExtend 64)
      (fun j hj _ => by
        rw [BitVec.getLsbD_setWidth]
        simp only [Bool.and_eq_false_imp, decide_eq_true_eq]
        intro _
        exact BitVec.getLsbD_of_ge b j hj)
      (by omega)

/-- Packing two 16-bit operands `b1` (bits `32..47`) and `b2` (bits `0..15`) into a single 64-bit
    lane and multiplying by 16-bit `a` via 64-bit `polyMul 64` produces both independent 32-bit
    carry-less products `(polyMul 16 a b1)[31:0] <<< 32 ||| (polyMul 16 a b2)[31:0]` in the low
    64 bits with zero upper 64 bits. -/
theorem polyMul_64_pack32_u16 (a b1 b2 : BitVec 16) :
    polyMul 64 (a.zeroExtend 64) ((b2.zeroExtend 64) ||| ((b1.zeroExtend 64) <<< 32)) =
      (((polyMul 16 (a.zeroExtend 64) (b1.zeroExtend 64)).truncate 32).zeroExtend 128 <<< 32) |||
        ((polyMul 16 (a.zeroExtend 64) (b2.zeroExtend 64)).truncate 32).zeroExtend 128 := by
  have ha_hi : ∀ i, 16 ≤ i → i < 64 → (a.zeroExtend 64).getLsbD i = false := by
    intro i h16 h64
    rw [BitVec.getLsbD_setWidth]
    simp only [h64, decide_true, Bool.true_and]
    exact BitVec.getLsbD_of_ge a i h16
  have hdisj64 : (b2.zeroExtend 64) &&& ((b1.zeroExtend 64) <<< 32) = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_zero, hi, decide_true, Bool.true_and]
    by_cases h32 : i < 32
    · simp [h32]
    · simp [BitVec.getLsbD_of_ge b2 i (by omega)]
  have hb1_hi : ∀ i, 64 - 32 ≤ i → i < 64 → (b1.zeroExtend 64).getLsbD i = false := by
    intro i h32 h64
    rw [BitVec.getLsbD_setWidth]
    simp only [h64, decide_true, Bool.true_and]
    exact BitVec.getLsbD_of_ge b1 i (by omega)
  rw [polyMul_eq_of_high_bits_false (by decide : 16 ≤ 64) _ _ ha_hi,
      polyMul_or_right_of_and_eq_zero 16 _ _ _ hdisj64,
      polyMul_shiftLeft_right 16 32 _ _ hb1_hi,
      polyMul_16_eq_zeroExtend_truncate32 a b2,
      polyMul_16_eq_zeroExtend_truncate32 a b1]
  generalize (polyMul 16 (a.zeroExtend 64) (b1.zeroExtend 64)).truncate 32 = p1
  generalize (polyMul 16 (a.zeroExtend 64) (b2.zeroExtend 64)).truncate 32 = p2
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hsub128 : i - 32 < 128 := by omega
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, hi, hsub128, decide_true, Bool.true_and]
  by_cases hi32 : i < 32
  · simp [hi32]
  · by_cases hsub32 : i - 32 < 32
    · simp [hi32, hsub32, BitVec.getLsbD_of_ge p2 i (by omega)]
    · simp [hi32, BitVec.getLsbD_of_ge p1 (i - 32) (by omega), BitVec.getLsbD_of_ge p2 i (by omega)]

/-- Low 64-bit word of `polyMul_64_pack32_u16`. -/
theorem polyMul_64_pack32_u16_truncate64 (a b1 b2 : BitVec 16) :
    (polyMul 64 (a.zeroExtend 64) ((b2.zeroExtend 64) ||| ((b1.zeroExtend 64) <<< 32))).truncate 64 =
      (((polyMul 16 (a.zeroExtend 64) (b1.zeroExtend 64)).truncate 32).zeroExtend 64 <<< 32) |||
        ((polyMul 16 (a.zeroExtend 64) (b2.zeroExtend 64)).truncate 32).zeroExtend 64 := by
  rw [polyMul_64_pack32_u16]
  generalize (polyMul 16 (a.zeroExtend 64) (b1.zeroExtend 64)).truncate 32 = p1
  generalize (polyMul 16 (a.zeroExtend 64) (b2.zeroExtend 64)).truncate 32 = p2
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

/-- High 64-bit word (`v.d[1]`) of `polyMul_64_pack32_u16` is identically `0#64`. -/
theorem polyMul_64_pack32_u16_hi64 (a b1 b2 : BitVec 16) :
    (polyMul 64 (a.zeroExtend 64) ((b2.zeroExtend 64) ||| ((b1.zeroExtend 64) <<< 32))).extractLsb' 64 64 =
      0#64 := by
  rw [polyMul_64_pack32_u16]
  generalize (polyMul 16 (a.zeroExtend 64) (b1.zeroExtend 64)).truncate 32 = p1
  generalize (polyMul 16 (a.zeroExtend 64) (b2.zeroExtend 64)).truncate 32 = p2
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h128 : 64 + i < 128 := by omega
  have hnotlt : ¬(64 + i < 32) := by omega
  simp [hi, h128, hnotlt,
    BitVec.getLsbD_of_ge p1 (64 + i - 32) (by omega),
    BitVec.getLsbD_of_ge p2 (64 + i) (by omega)]

/-- Low 32-bit product (`a * b2`) extracted from `polyMul_64_pack32_u16`. -/
theorem polyMul_64_pack32_u16_lo32 (a b1 b2 : BitVec 16) :
    ((polyMul 64 (a.zeroExtend 64)
        ((b2.zeroExtend 64) ||| ((b1.zeroExtend 64) <<< 32))).truncate 64).truncate 32 =
      (polyMul 16 (a.zeroExtend 64) (b2.zeroExtend 64)).truncate 32 := by
  rw [polyMul_64_pack32_u16_truncate64]
  generalize (polyMul 16 (a.zeroExtend 64) (b1.zeroExtend 64)).truncate 32 = p1
  generalize (polyMul 16 (a.zeroExtend 64) (b2.zeroExtend 64)).truncate 32 = p2
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

/-- High 32-bit product (`a * b1`) extracted from bits `[63:32]` of `polyMul_64_pack32_u16`. -/
theorem polyMul_64_pack32_u16_hi32 (a b1 b2 : BitVec 16) :
    (((polyMul 64 (a.zeroExtend 64)
        ((b2.zeroExtend 64) ||| ((b1.zeroExtend 64) <<< 32))).truncate 64) >>> 32).truncate 32 =
      (polyMul 16 (a.zeroExtend 64) (b1.zeroExtend 64)).truncate 32 := by
  rw [polyMul_64_pack32_u16_truncate64]
  generalize (polyMul 16 (a.zeroExtend 64) (b1.zeroExtend 64)).truncate 32 = p1
  generalize (polyMul 16 (a.zeroExtend 64) (b2.zeroExtend 64)).truncate 32 = p2
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hadd64 : 32 + i < 64 := by omega
  have hnotlt : ¬(32 + i < 32) := by omega
  have hsub : 32 + i - 32 = i := by omega
  have hsub64 : i < 64 := by omega
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, hi, hadd64, hnotlt, hsub, hsub64, decide_true, decide_false,
    Bool.true_and, Bool.not_false, BitVec.getLsbD_of_ge p2 (32 + i) (by omega), Bool.or_false]

end Arm64
