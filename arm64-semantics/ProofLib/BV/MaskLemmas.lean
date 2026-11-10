/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.BV.ArithLemmas
import Arm64.Trusted.Spec.SepLogic

/-!
# Power-of-Two Bitvector Masks and Alignment

Mask-to-modulo bridges (`x &&& (2 ^ k - 1)`), chunk-remainder bounds (`p - (x &&& m)`), and
complement align-down identities (`x &&& ~~~m`), exported in both `BitVec` and `ProofLib.BV.Arith`.
Lemmas are left out of global simp sets so callers can apply them explicitly without perturbing
normal-form goals.
-/

@[expose] public section

namespace BitVec

/-! ## Symbolic power-of-two masks -/

/-- Masking `x : BitVec w` by `BitVec.ofNat w (2 ^ k - 1)` extracts `x.toNat % 2 ^ k` for every
    width `w` and exponent `k` (with no `k ≤ w` side condition). -/
theorem toNat_and_twoPow_sub_one {w : Nat} (x : BitVec w) (k : Nat) :
    (x &&& BitVec.ofNat w (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.testBit_and, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases hiw : i < w
  · by_cases hik : i < k <;> simp [hiw, hik]
  · have hlt : x.toNat < 2 ^ i :=
      Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    simp [hiw, Nat.testBit_lt_two_pow hlt]

theorem toNat_twoPow_sub_one_and {w : Nat} (x : BitVec w) (k : Nat) :
    (BitVec.ofNat w (2 ^ k - 1) &&& x).toNat = x.toNat % 2 ^ k := by
  rw [BitVec.and_comm]
  exact toNat_and_twoPow_sub_one x k

/-- Masking `x : BitVec w` by `BitVec.ofNat w (2 ^ k - 1)` equals unsigned remainder
    `x % BitVec.ofNat w (2 ^ k)` for every `w` and `k`. -/
theorem and_twoPow_sub_one {w : Nat} (x : BitVec w) (k : Nat) :
    x &&& BitVec.ofNat w (2 ^ k - 1) = x % BitVec.ofNat w (2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and_twoPow_sub_one, BitVec.toNat_umod, BitVec.toNat_ofNat]
  by_cases hkw : k < w
  · have hlt : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by decide) hkw
    rw [Nat.mod_eq_of_lt hlt]
  · have hdvd : 2 ^ w ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
    have hx : x.toNat < 2 ^ k :=
      Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.mod_eq_zero_of_dvd hdvd, Nat.mod_zero, Nat.mod_eq_of_lt hx]

theorem twoPow_sub_one_and {w : Nat} (x : BitVec w) (k : Nat) :
    BitVec.ofNat w (2 ^ k - 1) &&& x = x % BitVec.ofNat w (2 ^ k) := by
  rw [BitVec.and_comm]
  exact and_twoPow_sub_one x k

theorem and_twoPow_sub_one_eq_ofNat_mod {w : Nat} (x : BitVec w) (k : Nat) :
    x &&& BitVec.ofNat w (2 ^ k - 1) = BitVec.ofNat w (x.toNat % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and_twoPow_sub_one, BitVec.toNat_ofNat]
  by_cases hkw : k ≤ w
  · have hlt : x.toNat % 2 ^ k < 2 ^ w :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.pow_le_pow_right (by decide) hkw)
    rw [Nat.mod_eq_of_lt hlt]
  · have hx : x.toNat < 2 ^ k :=
      Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt x.isLt]

theorem ofNat_and_twoPow_sub_one {w : Nat} (n k : Nat) :
    BitVec.ofNat w n &&& BitVec.ofNat w (2 ^ k - 1) = BitVec.ofNat w (n % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and_twoPow_sub_one]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [BitVec.toNat_ofNat, Nat.testBit_mod_two_pow]
  cases decide (i < k) <;> cases decide (i < w) <;> rfl

/-! ## Literal mask bridges -/

/-- Rewrite `(x &&& m).toNat` to `x.toNat % p` for any literal power-of-two mask `m`
    (`m.toNat + 1 = 2 ^ (m.toNat + 1).log2` and `m.toNat + 1 = p`, both discharged by `rfl` on
    concrete numerals with no exponent argument needed). -/
theorem toNat_and_eq_mod {w : Nat} (x m : BitVec w) (p : Nat := m.toNat + 1)
    (hm : m.toNat + 1 = 2 ^ (m.toNat + 1).log2 := by rfl)
    (hp : m.toNat + 1 = p := by rfl) :
    (x &&& m).toNat = x.toNat % p := by
  rw [← hp, hm]
  exact ProofLib.BV.Arith.node_and_mask x m (m.toNat + 1).log2 rfl hm

/-- Rewrite `x &&& m` to `x % p` when `m.toNat + 1` is a power of two equal to `p.toNat`. -/
theorem and_eq_umod_of_add_one {w : Nat} (x m p : BitVec w)
    (hm : m.toNat + 1 = 2 ^ (m.toNat + 1).log2 := by rfl)
    (hp : m.toNat + 1 = p.toNat := by rfl) :
    x &&& m = x % p := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and_eq_mod x m p.toNat hm hp, BitVec.toNat_umod]

/-- Rewrite `x &&& m` to `BitVec.ofNat w (x.toNat % p)` when `m.toNat + 1` is a power of two
    equal to `p`. -/
theorem and_eq_ofNat_mod {w : Nat} (x m : BitVec w) (p : Nat := m.toNat + 1)
    (hm : m.toNat + 1 = 2 ^ (m.toNat + 1).log2 := by rfl)
    (hp : m.toNat + 1 = p := by rfl) :
    x &&& m = BitVec.ofNat w (x.toNat % p) := by
  apply BitVec.eq_of_toNat_eq
  have hm_lt := m.isLt
  have hlt : x.toNat % p < 2 ^ w := by
    have hp_pos : 0 < p := by omega
    have hp_le : p ≤ 2 ^ w := by omega
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hp_pos) hp_le
  rw [toNat_and_eq_mod x m p hm hp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem toNat_and_1 {w : Nat} (x : BitVec w) : (x &&& 1#w).toNat = x.toNat % 2 :=
  toNat_and_twoPow_sub_one x 1

theorem toNat_and_3 {w : Nat} (x : BitVec w) : (x &&& 3#w).toNat = x.toNat % 4 :=
  toNat_and_twoPow_sub_one x 2

theorem toNat_and_7 {w : Nat} (x : BitVec w) : (x &&& 7#w).toNat = x.toNat % 8 :=
  toNat_and_twoPow_sub_one x 3

theorem toNat_and_15 {w : Nat} (x : BitVec w) : (x &&& 15#w).toNat = x.toNat % 16 :=
  toNat_and_twoPow_sub_one x 4

theorem toNat_and_31 {w : Nat} (x : BitVec w) : (x &&& 31#w).toNat = x.toNat % 32 :=
  toNat_and_twoPow_sub_one x 5

theorem toNat_and_63 {w : Nat} (x : BitVec w) : (x &&& 63#w).toNat = x.toNat % 64 :=
  toNat_and_twoPow_sub_one x 6

theorem toNat_and_255 {w : Nat} (x : BitVec w) : (x &&& 255#w).toNat = x.toNat % 256 :=
  toNat_and_twoPow_sub_one x 8

theorem toNat_and_511 {w : Nat} (x : BitVec w) : (x &&& 511#w).toNat = x.toNat % 512 :=
  toNat_and_twoPow_sub_one x 9

theorem toNat_and_4095 {w : Nat} (x : BitVec w) : (x &&& 4095#w).toNat = x.toNat % 4096 :=
  toNat_and_twoPow_sub_one x 12

theorem toNat_and_65535 {w : Nat} (x : BitVec w) : (x &&& 65535#w).toNat = x.toNat % 65536 :=
  toNat_and_twoPow_sub_one x 16

/-! ## Mask bounds and chunk remainders -/

theorem toNat_and_le_left {w : Nat} (x y : BitVec w) : (x &&& y).toNat ≤ x.toNat := by
  rw [BitVec.toNat_and]
  exact Nat.and_le_left

theorem toNat_and_le_right {w : Nat} (x y : BitVec w) : (x &&& y).toNat ≤ y.toNat := by
  rw [BitVec.toNat_and]
  exact Nat.and_le_right

theorem toNat_and_lt_of_add_one {w : Nat} (x m : BitVec w) {p : Nat}
    (hm : m.toNat + 1 ≤ p := by decide) :
    (x &&& m).toNat < p := by
  have hle := toNat_and_le_right x m
  omega

theorem toNat_sub_and_of_le {w : Nat} (x m p : BitVec w)
    (hmp : m.toNat ≤ p.toNat := by decide) :
    (p - (x &&& m)).toNat = p.toNat - (x &&& m).toNat := by
  have hle : (x &&& m).toNat ≤ p.toNat := Nat.le_trans (toNat_and_le_right x m) hmp
  exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)

/-- Chunk-remainder `.toNat` identity: `(p - (x &&& m)).toNat = n - x.toNat % n`
    when `m.toNat + 1` is a power of two equal to `p.toNat` and `n` (for example
    `(512#64 - (x &&& 511#64)).toNat = 512 - x.toNat % 512` or
    `(64#64 - (x &&& 63#64)).toNat = 64 - x.toNat % 64`). -/
theorem toNat_twoPow_sub_and {w : Nat} (x m p : BitVec w) (n : Nat := p.toNat)
    (hm : m.toNat + 1 = 2 ^ (m.toNat + 1).log2 := by rfl)
    (hp : m.toNat + 1 = p.toNat := by rfl)
    (hn : p.toNat = n := by rfl) :
    (p - (x &&& m)).toNat = n - x.toNat % n := by
  have hmp : m.toNat ≤ p.toNat := by omega
  have hmn : m.toNat + 1 = n := hp.trans hn
  rw [toNat_sub_and_of_le x m p hmp, hn, toNat_and_eq_mod x m n hm hmn]

theorem sub_and_pos_le_of_lt {w : Nat} (x m p : BitVec w)
    (hmp : m.toNat < p.toNat := by decide) :
    0 < (p - (x &&& m)).toNat ∧ (p - (x &&& m)).toNat ≤ p.toNat := by
  have hsub := toNat_sub_and_of_le x m p (Nat.le_of_lt hmp)
  have hle := toNat_and_le_right x m
  omega

theorem toNat_and_add_one_of_lt {w : Nat} (x m : BitVec w)
    (hm : m.toNat + 1 < 2 ^ w := by decide) :
    ((x &&& m) + 1#w).toNat = (x &&& m).toNat + 1 := by
  have hle := toNat_and_le_right x m
  have hw : 1 < 2 ^ w := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt (by omega)]

/-- `p.ult ((x &&& m) + 1#w) = false` whenever `m.toNat + 1 ≤ p.toNat` (e.g.,
    `(512#64).ult ((idx &&& 511#64) + 1#64) = false`). -/
theorem ult_and_add_one_eq_false {w : Nat} (x m p : BitVec w)
    (hm : m.toNat + 1 ≤ p.toNat := by decide) :
    p.ult ((x &&& m) + 1#w) = false := by
  have hp := p.isLt
  have h1 := toNat_and_add_one_of_lt x m (by omega)
  have hle := toNat_and_le_right x m
  rw [BitVec.ult, h1]
  exact decide_eq_false (by omega)

/-! ## Alignment predicates and complement align-down -/

theorem and_twoPow_sub_one_eq_zero_iff {w : Nat} (x : BitVec w) (k : Nat) :
    x &&& BitVec.ofNat w (2 ^ k - 1) = 0#w ↔ x.toNat % 2 ^ k = 0 := by
  rw [BitVec.toNat_eq, toNat_and_twoPow_sub_one, BitVec.toNat_ofNat, Nat.zero_mod]

/-- `x &&& m = 0#w` iff `x.toNat % p = 0` for any power-of-two mask `m`
    (`m.toNat + 1 = 2 ^ (m.toNat + 1).log2` and `m.toNat + 1 = p`). -/
theorem and_eq_zero_iff_mod_eq_zero {w : Nat} (x m : BitVec w) (p : Nat := m.toNat + 1)
    (hm : m.toNat + 1 = 2 ^ (m.toNat + 1).log2 := by rfl)
    (hp : m.toNat + 1 = p := by rfl) :
    x &&& m = 0#w ↔ x.toNat % p = 0 := by
  rw [BitVec.toNat_eq, toNat_and_eq_mod x m p hm hp, BitVec.toNat_ofNat, Nat.zero_mod]

theorem beq_and_zero_eq_true_iff_mod_eq_zero {w : Nat} (x m : BitVec w) (p : Nat := m.toNat + 1)
    (hm : m.toNat + 1 = 2 ^ (m.toNat + 1).log2 := by rfl)
    (hp : m.toNat + 1 = p := by rfl) :
    ((x &&& m == 0#w) = true) ↔ x.toNat % p = 0 := by
  rw [beq_iff_eq]
  exact and_eq_zero_iff_mod_eq_zero x m p hm hp

/-- Clearing the bits of `m` from `x` subtracts `x &&& m` (`x &&& ~~~m = x - (x &&& m)`), for
    every width `w` and arbitrary mask `m`. -/
theorem and_not_eq_sub_and {w : Nat} (x m : BitVec w) :
    x &&& ~~~m = x - (x &&& m) := by
  have hdisj : (x &&& ~~~m) &&& (x &&& m) = 0#w := by
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases x[i] <;> cases m[i] <;> rfl
  have hor : (x &&& ~~~m) ||| (x &&& m) = x := by
    ext i hi
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases x[i] <;> cases m[i] <;> rfl
  have hadd : (x &&& ~~~m) + (x &&& m) = x := by
    rw [BitVec.add_eq_or_of_and_eq_zero _ _ hdisj, hor]
  calc
    x &&& ~~~m = (x &&& ~~~m) + (x &&& m) - (x &&& m) := (BitVec.add_sub_cancel _ _).symm
    _ = x - (x &&& m) := by rw [hadd]

/-- Folded complement-literal form of `and_not_eq_sub_and` (e.g., `x &&& (-512#64) = x - (x &&& 511#64)`
    or `x &&& 0xfffffffffffff000#64 = x - (x &&& 4095#64)`). -/
theorem and_compl_eq_sub_and {w : Nat} (x c m : BitVec w)
    (hc : c = ~~~m := by rfl) :
    x &&& c = x - (x &&& m) := by
  subst hc
  exact and_not_eq_sub_and x m

theorem toNat_and_not {w : Nat} (x m : BitVec w) :
    (x &&& ~~~m).toNat = x.toNat - (x &&& m).toNat := by
  rw [and_not_eq_sub_and]
  exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr (toNat_and_le_left x m))

/-- Align-down `.toNat` identity: `(x &&& c).toNat = x.toNat / p * p` when `c = ~~~m`,
    `m.toNat + 1` is a power of two, and `m.toNat + 1 = p`. -/
theorem toNat_and_compl_eq_div_mul {w : Nat} (x c m : BitVec w) (p : Nat := m.toNat + 1)
    (hc : c = ~~~m := by rfl)
    (hm : m.toNat + 1 = 2 ^ (m.toNat + 1).log2 := by rfl)
    (hp : m.toNat + 1 = p := by rfl) :
    (x &&& c).toNat = x.toNat / p * p := by
  subst hc
  rw [toNat_and_not, toNat_and_eq_mod x m p hm hp]
  have hdm := Nat.div_add_mod x.toNat p
  have hm' : p * (x.toNat / p) = x.toNat / p * p := Nat.mul_comm _ _
  omega

end BitVec

namespace ProofLib.BV.Arith

export BitVec (
  toNat_and_twoPow_sub_one
  toNat_twoPow_sub_one_and
  and_twoPow_sub_one
  twoPow_sub_one_and
  and_twoPow_sub_one_eq_ofNat_mod
  ofNat_and_twoPow_sub_one
  toNat_and_eq_mod
  and_eq_umod_of_add_one
  and_eq_ofNat_mod
  toNat_and_1
  toNat_and_3
  toNat_and_7
  toNat_and_15
  toNat_and_31
  toNat_and_63
  toNat_and_255
  toNat_and_511
  toNat_and_4095
  toNat_and_65535
  toNat_and_le_left
  toNat_and_le_right
  toNat_and_lt_of_add_one
  toNat_sub_and_of_le
  toNat_twoPow_sub_and
  sub_and_pos_le_of_lt
  toNat_and_add_one_of_lt
  ult_and_add_one_eq_false
  and_twoPow_sub_one_eq_zero_iff
  and_eq_zero_iff_mod_eq_zero
  beq_and_zero_eq_true_iff_mod_eq_zero
  and_not_eq_sub_and
  and_compl_eq_sub_and
  toNat_and_not
  toNat_and_compl_eq_div_mul
)

end ProofLib.BV.Arith
