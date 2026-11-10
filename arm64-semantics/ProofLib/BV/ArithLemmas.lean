/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Std.Tactic.BVDecide
import Arm64.Trusted.Spec.SepLogic

/-!
# Kernel-Checked Lemmas for `bv_arith`

Core-tactic lemmas instantiated by `ProofLib.BV.ArithTranslate` and `ProofLib.BV.ArithCore`:
`Prop`/`Bool` normalizations (`norm_*`) into `Nat`/`Int` relations over `toNat`/`toInt`, wrap and
no-wrap operator translation equations (`node_*`), one-step interval bound rules (`ub_*`, `lb_*`)
with literal side conditions discharged by `Nat.ble`, and 64-bit pointer-offset and alignment
identities (`BitVec.*`).
-/

@[expose] public section

namespace ProofLib.BV.Arith

/-! ## Prop normalization -/

theorem norm_ult_true {w : Nat} (x y : BitVec w) : (x.ult y = true) ↔ x.toNat < y.toNat := by
  simp [BitVec.ult]
theorem norm_ule_true {w : Nat} (x y : BitVec w) : (x.ule y = true) ↔ x.toNat ≤ y.toNat := by
  simp [BitVec.ule]
theorem norm_ult_false {w : Nat} (x y : BitVec w) : (x.ult y = false) ↔ y.toNat ≤ x.toNat := by
  simp [BitVec.ult]
theorem norm_ule_false {w : Nat} (x y : BitVec w) : (x.ule y = false) ↔ y.toNat < x.toNat := by
  simp [BitVec.ule]
theorem norm_slt_true {w : Nat} (x y : BitVec w) : (x.slt y = true) ↔ x.toInt < y.toInt :=
  BitVec.slt_iff_toInt_lt
theorem norm_sle_true {w : Nat} (x y : BitVec w) : (x.sle y = true) ↔ x.toInt ≤ y.toInt :=
  BitVec.sle_iff_toInt_le
theorem norm_slt_false {w : Nat} (x y : BitVec w) : (x.slt y = false) ↔ y.toInt ≤ x.toInt := by
  rw [← Bool.not_eq_true, norm_slt_true]; omega
theorem norm_sle_false {w : Nat} (x y : BitVec w) : (x.sle y = false) ↔ y.toInt < x.toInt := by
  rw [← Bool.not_eq_true, norm_sle_true]; omega
theorem norm_bv_eq {w : Nat} (x y : BitVec w) : x = y ↔ x.toNat = y.toNat := BitVec.toNat_eq
theorem norm_bv_lt {w : Nat} (x y : BitVec w) : x < y ↔ x.toNat < y.toNat := BitVec.lt_def
theorem norm_bv_le {w : Nat} (x y : BitVec w) : x ≤ y ↔ x.toNat ≤ y.toNat := BitVec.le_def
theorem norm_beq_true {α : Type} [BEq α] [LawfulBEq α] (a b : α) : ((a == b) = true) ↔ a = b :=
  beq_iff_eq
theorem norm_beq_false {α : Type} [BEq α] [LawfulBEq α] (a b : α) : ((a == b) = false) ↔ ¬ a = b := by
  rw [← Bool.not_eq_true, beq_iff_eq]
theorem norm_bne_true {α : Type} [BEq α] [LawfulBEq α] (a b : α) : ((a != b) = true) ↔ ¬ a = b := by
  simp
theorem norm_bne_false {α : Type} [BEq α] [LawfulBEq α] (a b : α) : ((a != b) = false) ↔ a = b := by
  simp
theorem norm_decide_true (p : Prop) [Decidable p] : (decide p = true) ↔ p := decide_eq_true_iff
theorem norm_decide_false (p : Prop) [Decidable p] : (decide p = false) ↔ ¬ p := decide_eq_false_iff_not
theorem norm_not_true (b : Bool) : ((!b) = true) ↔ b = false := by cases b <;> simp
theorem norm_not_false (b : Bool) : ((!b) = false) ↔ b = true := by cases b <;> simp
theorem norm_and_true (a b : Bool) : ((a && b) = true) ↔ a = true ∧ b = true := by simp
theorem norm_and_false (a b : Bool) : ((a && b) = false) ↔ a = false ∨ b = false := by
  cases a <;> cases b <;> simp
theorem norm_or_true (a b : Bool) : ((a || b) = true) ↔ a = true ∨ b = true := by simp
theorem norm_or_false (a b : Bool) : ((a || b) = false) ↔ a = false ∧ b = false := by
  cases a <;> cases b <;> simp
theorem norm_ne_true (b : Bool) : (¬ b = true) ↔ b = false := by simp
theorem norm_ne_false (b : Bool) : (¬ b = false) ↔ b = true := by simp
theorem norm_true_eq (b : Bool) : (true = b) ↔ b = true := by cases b <;> simp
theorem norm_false_eq (b : Bool) : (false = b) ↔ b = false := by cases b <;> simp

/-! ## Node facts

`a`/`b`/`k` are the operands' `toNat` values (passed as atoms, or as literals when the
operand is a literal: the `h*` hypotheses then are `rfl`/`decide`). -/

theorem node_add_nowrap {w : Nat} (x y : BitVec w) {a b : Nat} (ha : x.toNat = a)
    (hb : y.toNat = b) (h : a + b < 2 ^ w) : (x + y).toNat = a + b := by
  subst ha hb; exact BitVec.toNat_add_of_lt h
theorem node_add_wrap {w : Nat} (x y : BitVec w) {a b : Nat} (ha : x.toNat = a)
    (hb : y.toNat = b) : (x + y).toNat = (a + b) % 2 ^ w := by
  subst ha hb; exact BitVec.toNat_add x y
/-- No-wrap subtraction, stated additively so `omega` needs no truncated-subtraction split. -/
theorem node_sub_nowrap {w : Nat} (x y : BitVec w) {a b : Nat} (ha : x.toNat = a)
    (hb : y.toNat = b) (h : b ≤ a) : (x - y).toNat + b = a := by
  subst ha hb; rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)]; omega
/-- Wrapping subtraction over `Int` with a single `emod` (no truncated-subtraction split). -/
theorem node_sub_wrap {w : Nat} (x y : BitVec w) {a b : Nat} (ha : x.toNat = a)
    (hb : y.toNat = b) : ((x - y).toNat : Int) = ((a : Int) - (b : Int)) % ((2 ^ w : Nat) : Int) := by
  subst ha hb
  have hy := y.isLt
  rw [BitVec.toNat_sub, Int.natCast_emod, Int.natCast_add, Int.natCast_sub (by omega)]
  rw [show ((2 ^ w : Nat) : Int) - (y.toNat : Int) + (x.toNat : Int)
        = ((x.toNat : Int) - y.toNat) + ((2 ^ w : Nat) : Int) * 1 by omega]
  rw [Int.add_mul_emod_self_left]
theorem node_mul_nowrap {w : Nat} (x y : BitVec w) {a b : Nat} (ha : x.toNat = a)
    (hb : y.toNat = b) (h : a * b < 2 ^ w) : (x * y).toNat = a * b := by
  subst ha hb; exact BitVec.toNat_mul_of_lt h
theorem node_mul_wrap {w : Nat} (x y : BitVec w) {a b : Nat} (ha : x.toNat = a)
    (hb : y.toNat = b) : (x * y).toNat = (a * b) % 2 ^ w := by
  subst ha hb; exact BitVec.toNat_mul x y
theorem node_shl_nowrap {w : Nat} (x : BitVec w) (n : Nat) {a p : Nat} (ha : x.toNat = a)
    (hp : 2 ^ n = p) (h : a * p < 2 ^ w) : (x <<< n).toNat = a * p := by
  subst ha hp; rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]
theorem node_shl_wrap {w : Nat} (x : BitVec w) (n : Nat) {a p : Nat} (ha : x.toNat = a)
    (hp : 2 ^ n = p) : (x <<< n).toNat = (a * p) % 2 ^ w := by
  subst ha hp; rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
theorem node_shlbv_nowrap {w v : Nat} (x : BitVec w) (y : BitVec v) {a p : Nat}
    (ha : x.toNat = a) (hp : 2 ^ y.toNat = p) (h : a * p < 2 ^ w) :
    (x <<< y).toNat = a * p :=
  node_shl_nowrap x y.toNat ha hp h
theorem node_shlbv_wrap {w v : Nat} (x : BitVec w) (y : BitVec v) {a p : Nat}
    (ha : x.toNat = a) (hp : 2 ^ y.toNat = p) : (x <<< y).toNat = (a * p) % 2 ^ w :=
  node_shl_wrap x y.toNat ha hp
theorem node_shr {w : Nat} (x : BitVec w) (n : Nat) {a p : Nat} (ha : x.toNat = a)
    (hp : 2 ^ n = p) : (x >>> n).toNat = a / p := by
  subst ha hp; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
theorem node_shrbv {w v : Nat} (x : BitVec w) (y : BitVec v) {a p : Nat} (ha : x.toNat = a)
    (hp : 2 ^ y.toNat = p) : (x >>> y).toNat = a / p :=
  node_shr x y.toNat ha hp
theorem node_ofNat_nowrap (w n : Nat) (h : n < 2 ^ w) : (BitVec.ofNat w n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
theorem node_ofNat_wrap (w n : Nat) : (BitVec.ofNat w n).toNat = n % 2 ^ w :=
  BitVec.toNat_ofNat n w
theorem node_setWidth_nowrap {w : Nat} (v : Nat) (x : BitVec w) {a : Nat} (ha : x.toNat = a)
    (h : a < 2 ^ v) : (x.setWidth v).toNat = a := by
  subst ha; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]
theorem node_setWidth_wrap {w : Nat} (v : Nat) (x : BitVec w) {a : Nat} (ha : x.toNat = a) :
    (x.setWidth v).toNat = a % 2 ^ v := by subst ha; exact BitVec.toNat_setWidth v x
theorem node_udiv {w : Nat} (x y : BitVec w) {a b : Nat} (ha : x.toNat = a) (hb : y.toNat = b) :
    (x / y).toNat = a / b := by subst ha hb; exact BitVec.toNat_udiv
theorem node_umod {w : Nat} (x y : BitVec w) {a b : Nat} (ha : x.toNat = a) (hb : y.toNat = b) :
    (x % y).toNat = a % b := by subst ha hb; exact BitVec.toNat_umod
theorem node_neg {w : Nat} (x : BitVec w) {a : Nat} (ha : x.toNat = a) :
    ((-x).toNat : Int) = (-(a : Int)) % ((2 ^ w : Nat) : Int) := by
  have h := node_sub_wrap 0#w x rfl ha
  simpa [BitVec.zero_sub] using h
theorem node_not {w : Nat} (x : BitVec w) {a : Nat} (ha : x.toNat = a) :
    (~~~x).toNat + a + 1 = 2 ^ w := by
  subst ha; have := x.isLt; rw [BitVec.toNat_not]; omega
theorem node_and_le {w : Nat} (x y : BitVec w) {a b : Nat} (ha : x.toNat = a) (hb : y.toNat = b) :
    (x &&& y).toNat ≤ a ∧ (x &&& y).toNat ≤ b := by
  subst ha hb; rw [BitVec.toNat_and]; exact ⟨Nat.and_le_left, Nat.and_le_right⟩
/-- `x &&& m` with literal mask `m = 2^n - 1` as a `%`. -/
theorem node_and_mask {w : Nat} (x y : BitVec w) {a : Nat} (n : Nat) (ha : x.toNat = a)
    (hy : y.toNat + 1 = 2 ^ n) : (x &&& y).toNat = a % 2 ^ n := by
  subst ha
  rw [BitVec.toNat_and, show y.toNat = 2 ^ n - 1 by omega, Nat.and_two_pow_sub_one_eq_mod]
theorem node_and_mask' {w : Nat} (x y : BitVec w) {b : Nat} (n : Nat) (hb : y.toNat = b)
    (hx : x.toNat + 1 = 2 ^ n) : (x &&& y).toNat = b % 2 ^ n := by
  rw [BitVec.and_comm]; exact node_and_mask y x n hb hx
/-- `x &&& m` with a contiguous literal mask `m = (2^k - 1) * 2^lo` (e.g. an ADRP page mask
`~~~4095`): bits `lo .. lo+k-1` of `x`, as `/`, `%` and `*` by literals. -/
theorem node_and_range {w : Nat} (x y : BitVec w) {a p q : Nat} (lo k : Nat) (ha : x.toNat = a)
    (hp : 2 ^ lo = p) (hq : 2 ^ k = q) (hy : y.toNat = (q - 1) * p) :
    (x &&& y).toNat = a / p % q * p := by
  subst ha hp hq
  rw [BitVec.toNat_and, hy]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft,
    Nat.testBit_shiftLeft, ← Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_and,
    Nat.testBit_two_pow_sub_one, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
  by_cases h : lo ≤ i
  · simp only [ge_iff_le, h, decide_true, Bool.true_and]
    rw [Nat.add_sub_cancel' h]
  · simp [h]
theorem node_and_range' {w : Nat} (x y : BitVec w) {b p q : Nat} (lo k : Nat) (hb : y.toNat = b)
    (hp : 2 ^ lo = p) (hq : 2 ^ k = q) (hx : x.toNat = (q - 1) * p) :
    (x &&& y).toNat = b / p % q * p := by
  rw [BitVec.and_comm]; exact node_and_range y x lo k hb hp hq hx
/-- `ite` over `BitVec` as a case split `omega` can consume; `c'` is the normalized condition. -/
theorem node_ite {w : Nat} {c c' : Prop} [Decidable c] (x y : BitVec w) (hc : c = c') :
    (c' ∧ (if c then x else y).toNat = x.toNat) ∨ (¬c' ∧ (if c then x else y).toNat = y.toNat) := by
  subst hc; by_cases h : c <;> simp [h]
/-- `ite` over `BitVec` with a condition outside the `omega` fragment. -/
theorem node_ite' {w : Nat} {c : Prop} [Decidable c] (x y : BitVec w) :
    (if c then x else y).toNat = x.toNat ∨ (if c then x else y).toNat = y.toNat := by
  by_cases h : c <;> simp [h]
theorem node_or_le {w : Nat} (x y : BitVec w) : x.toNat ≤ (x ||| y).toNat ∧ y.toNat ≤ (x ||| y).toNat := by
  rw [BitVec.toNat_or]; exact ⟨Nat.left_le_or, Nat.right_le_or⟩
theorem node_extract {w : Nat} (s m : Nat) (x : BitVec w) {a p : Nat} (ha : x.toNat = a)
    (hp : 2 ^ s = p) : (x.extractLsb' s m).toNat = (a / p) % 2 ^ m := by
  subst ha hp; rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
/-- `toInt` in terms of `toNat`, as a case split `omega` can consume (no `ite`). -/
theorem node_toInt {w : Nat} (x : BitVec w) :
    (2 * x.toNat < 2 ^ w ∧ x.toInt = (x.toNat : Int)) ∨
    (2 ^ w ≤ 2 * x.toNat ∧ x.toInt = (x.toNat : Int) - ((2 ^ w : Nat) : Int)) := by
  rw [BitVec.toInt_eq_toNat_cond]
  split
  · left; exact ⟨by assumption, rfl⟩
  · right; exact ⟨by omega, by simp⟩

/-- `toInt` of a value below `2^(w-1)`: no sign wrap. -/
theorem node_toInt_nowrap {w : Nat} (x : BitVec w) (h : 2 * x.toNat < 2 ^ w) :
    x.toInt = (x.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]; simp [h]

/-! ## Interval steps (literal bounds) -/

theorem ub_of_eq {a k : Nat} (h : a = k) : a ≤ k := Nat.le_of_eq h
theorem ub_trans {a b k : Nat} (h : a ≤ b) (hb : b ≤ k) : a ≤ k := Nat.le_trans h hb
theorem ub_trans_lt {a b k m : Nat} (h : a < b) (hb : b ≤ k) (hk : k = m + 1) : a ≤ m := by omega
theorem ub_add {a b k l m : Nat} (ha : a ≤ k) (hb : b ≤ l) (hm : k + l = m) : a + b ≤ m := by
  omega
theorem ub_mul {a b k l m : Nat} (ha : a ≤ k) (hb : b ≤ l) (hm : k * l = m) : a * b ≤ m := by
  subst hm; exact Nat.mul_le_mul ha hb
theorem ub_div {a b k : Nat} (ha : a ≤ k) : a / b ≤ k := Nat.le_trans (Nat.div_le_self a b) ha
theorem ub_div_lit {a k p m : Nat} (ha : a ≤ k) (hm : k / p = m) : a / p ≤ m := by
  subst hm; exact Nat.div_le_div_right ha
theorem ub_mod {a b k : Nat} (ha : a ≤ k) : a % b ≤ k := Nat.le_trans (Nat.mod_le a b) ha
theorem ub_mod_lit {a p m : Nat} (hp : 0 < p) (hm : p = m + 1) : a % p ≤ m := by
  have := Nat.mod_lt a hp; omega
theorem ub_sub {a b k : Nat} (ha : a ≤ k) : a - b ≤ k := by omega
theorem ub_toNat {w : Nat} (x : BitVec w) (m : Nat) (hm : 2 ^ w = m + 1) : x.toNat ≤ m := by
  have := x.isLt; omega
theorem ub_subnode {t a b k l m : Nat} (h : t + b = a) (ha : a ≤ k) (hb : l ≤ b)
    (hm : k - l = m) : t ≤ m := by omega
theorem lb_of_eq {a k : Nat} (h : a = k) : k ≤ a := Nat.le_of_eq h.symm
theorem lb_trans {a b k : Nat} (h : b ≤ a) (hb : k ≤ b) : k ≤ a := Nat.le_trans hb h
theorem lb_trans_lt {a b k m : Nat} (h : b < a) (hb : k ≤ b) (hk : k + 1 = m) : m ≤ a := by
  omega
theorem lb_add {a b k l m : Nat} (ha : k ≤ a) (hb : l ≤ b) (hm : k + l = m) : m ≤ a + b := by
  omega
theorem lb_mul {a b k l m : Nat} (ha : k ≤ a) (hb : l ≤ b) (hm : k * l = m) : m ≤ a * b := by
  subst hm; exact Nat.mul_le_mul ha hb
theorem lb_zero (a : Nat) : 0 ≤ a := Nat.zero_le a
theorem lt_of_ub {a k m : Nat} (ha : a ≤ k) (hk : k < m) : a < m := Nat.lt_of_le_of_lt ha hk
theorem le_of_bounds {a b k l : Nat} (hb : b ≤ k) (ha : l ≤ a) (hkl : k ≤ l) : b ≤ a := by
  omega
theorem le_of_eq_mul {a b p : Nat} (h : a = b * p) (hp : 1 ≤ p) : b ≤ a := by
  subst h; exact Nat.le_mul_of_pos_right b hp
theorem summand_le_left {a b s : Nat} (h : a + b ≤ s) : a ≤ s := Nat.le_trans (Nat.le_add_right a b) h
theorem summand_le_right {a b s : Nat} (h : a + b ≤ s) : b ≤ s := Nat.le_trans (Nat.le_add_left b a) h
theorem summand_lt_left {a b s : Nat} (h : a + b < s) : a < s :=
  Nat.lt_of_le_of_lt (Nat.le_add_right a b) h
theorem summand_lt_right {a b s : Nat} (h : a + b < s) : b < s :=
  Nat.lt_of_le_of_lt (Nat.le_add_left b a) h
theorem congr_add {a a' b b' : Nat} (ha : a = a') (hb : b = b') : a + b = a' + b' := by
  subst ha hb; rfl
theorem ub_of_eq_trans {a a' k : Nat} (h : a = a') (hk : a' ≤ k) : a ≤ k := h ▸ hk
/-- Push a non-truncating `Nat` subtraction out of `BitVec.ofNat` (`bv_lin` pre-rewrite). -/
theorem ofNat_sub_of_le (w a b : Nat) (h : b ≤ a) :
    BitVec.ofNat w (a - b) = BitVec.ofNat w a - BitVec.ofNat w b := by
  have : a = (a - b) + b := (Nat.sub_add_cancel h).symm
  conv => rhs; rw [this, BitVec.ofNat_add, BitVec.add_sub_cancel]
theorem ub_sum_mono_le {a b c s k : Nat} (hb : b ≤ c) (h : a + c ≤ s) (hs : s ≤ k) :
    a + b ≤ k := by omega
theorem ub_sum_mono_lt {a b c s k m : Nat} (hb : b ≤ c) (h : a + c < s) (hs : s ≤ k)
    (hk : k = m + 1) : a + b ≤ m := by omega
theorem ub_sum_mono_le' {a b c s k : Nat} (hb : b ≤ c) (h : c + a ≤ s) (hs : s ≤ k) :
    b + a ≤ k := by omega
theorem ub_sum_mono_lt' {a b c s k m : Nat} (hb : b ≤ c) (h : c + a < s) (hs : s ≤ k)
    (hk : k = m + 1) : b + a ≤ m := by omega

end ProofLib.BV.Arith

namespace BitVec

/-! ## Pointer-offset arithmetic and alignment masks -/

theorem add_ofNat_beq_add_ofNat_false {start : BitVec 64} {idx len : Nat}
    (hlt : idx < len) (hno : start.toNat + len < 2 ^ 64) :
    (start + BitVec.ofNat 64 idx == start + BitVec.ofNat 64 len) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
  omega

theorem add_ofNat_beq_add_ofNat_false_rev {start : BitVec 64} {idx len : Nat}
    (hlt : idx < len) (hno : start.toNat + len < 2 ^ 64) :
    (start + BitVec.ofNat 64 len == start + BitVec.ofNat 64 idx) = false := by
  rw [BEq.comm]
  exact add_ofNat_beq_add_ofNat_false hlt hno

theorem ofNat64_length_ne_zero {α : Type} {bs : List α}
    (hne : bs ≠ []) (hlt : bs.length < 2 ^ 64) :
    BitVec.ofNat 64 bs.length ≠ 0#64 := by
  cases bs with
  | nil => exact absurd rfl hne
  | cons _ tl =>
    intro h
    have h1 := congrArg BitVec.toNat h
    simp only [List.length_cons, BitVec.toNat_ofNat] at h1 hlt
    omega

theorem ult_self_add_ofNat_false {x : BitVec 64} {n : Nat}
    (hn : x.toNat + n < 2 ^ 64) :
    (x + BitVec.ofNat 64 n).ult x = false := by
  simp only [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), Nat.mod_eq_of_lt hn, decide_eq_false_iff_not]
  omega

theorem ule_self_add_ofNat_false {x : BitVec 64} {n : Nat}
    (hpos : 0 < n) (hn : x.toNat + n < 2 ^ 64) :
    (x + BitVec.ofNat 64 n).ule x = false := by
  simp only [BitVec.ule, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), Nat.mod_eq_of_lt hn, decide_eq_false_iff_not]
  omega

theorem add_ofNat_ult_add_ofNat {base : BitVec 64} {i n : Nat}
    (hi : i < n) (h : base.toNat + n < 2 ^ 64) :
    (base + BitVec.ofNat 64 i).ult (base + BitVec.ofNat 64 n) = true := by
  simp only [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show base.toNat + i < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt h, decide_eq_true_eq]
  omega

theorem add_ofNat_ule_add_ofNat_false {base : BitVec 64} {i n : Nat}
    (hi : i < n) (h : base.toNat + n < 2 ^ 64) :
    (base + BitVec.ofNat 64 n).ule (base + BitVec.ofNat 64 i) = false := by
  simp only [BitVec.ule, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show base.toNat + i < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt h, decide_eq_false_iff_not]
  omega

theorem ult_ofNat64_of_lt {a b : Nat} (hab : a < b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt hb, decide_eq_true_eq]
  exact hab

theorem ult_ofNat64_of_ge {a b : Nat} (hab : b ≤ a) (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), decide_eq_false_iff_not]
  omega

theorem ule_ofNat64_of_le {a b : Nat} (hab : a ≤ b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = true := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt hb, decide_eq_true_eq]
  exact hab

theorem ule_ofNat64_of_gt {a b : Nat} (hab : b < a) (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), decide_eq_false_iff_not]
  omega

theorem add_sub_add_left {w : Nat} (a b c : BitVec w) :
    (a + b) - (a + c) = b - c := by
  rw [BitVec.add_comm a b, ← BitVec.sub_sub, BitVec.add_sub_cancel]

theorem ofNat64_sub_ofNat64_of_le {rem n : Nat} (h : n ≤ rem) :
    BitVec.ofNat 64 rem - BitVec.ofNat 64 n = BitVec.ofNat 64 (rem - n) :=
  (ProofLib.BV.Arith.ofNat_sub_of_le 64 rem n h).symm

theorem add_ofNat_sub_add_ofNat {base : BitVec 64} {x y : Nat} (hle : y ≤ x) :
    (base + BitVec.ofNat 64 x) - (base + BitVec.ofNat 64 y) = BitVec.ofNat 64 (x - y) := by
  rw [add_sub_add_left, ofNat64_sub_ofNat64_of_le hle]

theorem sub_ofNat_add_ofNat_of_le {w : Nat} (sp : BitVec w) {n i : Nat} (h : i ≤ n) :
    sp - BitVec.ofNat w n + BitVec.ofNat w i = sp - BitVec.ofNat w (n - i) := by
  have hn : n = (n - i) + i := (Nat.sub_add_cancel h).symm
  conv => lhs; rw [hn, BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem ofNat_add_sub_cancel (n k : Nat) :
    BitVec.ofNat 64 (n + k) - BitVec.ofNat 64 k = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem sub_ofNat_sub_ofNat {w : Nat} (sp : BitVec w) (a b : Nat) :
    sp - BitVec.ofNat w a - BitVec.ofNat w b = sp - BitVec.ofNat w (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

theorem ofNat64_and_7 {n : Nat} (_hn : n < 2 ^ 64 := by omega) :
    BitVec.ofNat 64 n &&& 7#64 = BitVec.ofNat 64 (n % 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (7 % 2 ^ 64 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem ofNat64_and_mask8 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& 0xfffffffffffffff8#64 = BitVec.ofNat 64 (8 * (n / 8)) := by
  apply BitVec.eq_of_toNat_eq
  rw [ProofLib.BV.Arith.node_and_range (BitVec.ofNat 64 n) 0xfffffffffffffff8#64 3 61 rfl rfl rfl rfl,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat64_and_63 (n : Nat) :
    BitVec.ofNat 64 n &&& 63#64 = BitVec.ofNat 64 (n % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (63 % 2 ^ 64 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem ofNat64_ushiftRight_6 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 6 = BitVec.ofNat 64 (n / 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem and_neg8_eq_sub_and_7 (x : BitVec 64) :
    x &&& (-8#64) = x - (x &&& 7#64) := by
  apply BitVec.eq_of_toNat_eq
  have h1 := ProofLib.BV.Arith.node_and_range x (-8#64) 3 61 rfl rfl rfl rfl
  have h2 := ProofLib.BV.Arith.node_and_mask x 7#64 3 rfl rfl
  have hx := x.isLt
  rw [h1, BitVec.toNat_sub, h2]
  omega

theorem mask_align8_roundtrip (x : BitVec 64) :
    (((x &&& 0xfffffffffffffff8#64) - 1#64) &&& 0xfffffffffffffff8#64) + 8#64 =
      x &&& 0xfffffffffffffff8#64 := by
  apply BitVec.eq_of_toNat_eq
  have h1 := ProofLib.BV.Arith.node_and_range x 0xfffffffffffffff8#64 3 61 rfl rfl rfl rfl
  have h2 := ProofLib.BV.Arith.node_and_range
    ((x &&& 0xfffffffffffffff8#64) - 1#64) 0xfffffffffffffff8#64 3 61 rfl rfl rfl rfl
  have hx := x.isLt
  rw [BitVec.toNat_add, h2, BitVec.toNat_sub, h1]
  simp only [BitVec.toNat_ofNat]
  omega

theorem toNat_addOfNat {w : Nat} {x : BitVec w} {xv i : Nat} (hx : x.toNat = xv)
    (hi : xv + i < 2 ^ w) : (x + BitVec.ofNat w i).toNat = xv + i := by
  subst hx
  have hi' : i < 2 ^ w := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hi
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hi]

/-- Setting bit 0 via `x ||| 1#w` equals `x + 1#w` whenever bit 0 of `x` is `false`. -/
theorem or_one_eq_add_one_of_lsb_false {w : Nat} {x : BitVec w} (hx : x.getLsbD 0 = false) :
    x ||| 1#w = x + 1#w := by
  have hand : x &&& 1#w = 0#w := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp [BitVec.getLsbD_and, hx]
    · simp [BitVec.getLsbD_and, BitVec.getLsbD_one, Nat.ne_of_gt hpos]
  exact (BitVec.add_eq_or_of_and_eq_zero x 1#w hand).symm

end BitVec

namespace ProofLib.BV.Arith

export BitVec (
  toNat_addOfNat
  or_one_eq_add_one_of_lsb_false
  add_ofNat_beq_add_ofNat_false
  add_ofNat_beq_add_ofNat_false_rev
  ofNat64_length_ne_zero
  ult_self_add_ofNat_false
  ule_self_add_ofNat_false
  add_ofNat_ult_add_ofNat
  add_ofNat_ule_add_ofNat_false
  ult_ofNat64_of_lt
  ult_ofNat64_of_ge
  ule_ofNat64_of_le
  ule_ofNat64_of_gt
  add_sub_add_left
  ofNat64_sub_ofNat64_of_le
  add_ofNat_sub_add_ofNat
  sub_ofNat_add_ofNat_of_le
  ofNat_add_sub_cancel
  sub_ofNat_sub_ofNat
  ofNat64_and_7
  ofNat64_and_mask8
  ofNat64_and_63
  ofNat64_ushiftRight_6
  and_neg8_eq_sub_and_7
  mask_align8_roundtrip
)
end ProofLib.BV.Arith
