/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Lemmas
public import ProofLib.BV.WidthNormAttr
public import ProofLib.BV.AddrNormAttr
import Arm64.Trusted.Spec.SepLogic

/-!
# Width Round-Trip, Shift-Amount, and `UMULH` Normalization Lemmas

Provides generic `BitVec` normalization lemmas for width round trips (`setWidth`, `truncate`,
`zeroExtend`) around shifts, bitwise operations, and comparisons, register-shift amount masking
(`LSLV`/`LSRV`), signed 32-to-64-bit index scaling, `UMULH` high-word products, sign/zero
extensions, and the `bv_to_nat` / `bv_nat` tactics.

Because `BitVec.truncate` and `BitVec.zeroExtend` are reducible abbreviations of
`BitVec.setWidth`, every `setWidth` lemma applies to `truncate` and `zeroExtend` forms as well.
Most lemmas are registered in the opt-in `[width_norm]` simp set (`simp only [wp_norm, width_norm]`)
so default `simp`, `arm64_norm`, and `wp_norm` normal forms remain unchanged.
-/

@[expose] public section

namespace BitVec

attribute [width_norm] BitVec.setWidth_eq BitVec.setWidth_setWidth_of_le

attribute [wp_branch]
  Bool.false_eq_true Bool.true_eq_false
  Bool.not_eq_true Bool.not_eq_false
  decide_eq_true_eq decide_eq_false_iff_not
  beq_iff_eq bne_iff_ne
  Bool.and_true Bool.true_and Bool.and_false Bool.false_and
  Bool.or_true Bool.true_or Bool.or_false Bool.false_or

/-! ## Shift Round Trips -/

/-- Truncating `x >>> n` to `v` bits loses nothing when `w ≤ v + n`; zero-extending back to `w`
    recovers `x >>> n`. -/
@[width_norm]
theorem setWidth_setWidth_ushiftRight_of_le {w : Nat} (v n : Nat) (x : BitVec w)
    (h : w ≤ v + n) : setWidth w (setWidth v (x >>> n)) = x >>> n := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [toNat_setWidth, toNat_ushiftRight]
  have hlt : x.toNat >>> n < 2 ^ v := by
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    calc x.toNat < 2 ^ w := hx
      _ ≤ 2 ^ (n + v) := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 2 ^ n * 2 ^ v := Nat.pow_add _ _ _
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hx)]

@[width_norm]
theorem setWidth_setWidth_ushiftRight_bv_of_le {w m : Nat} (v : Nat) (x : BitVec w) (y : BitVec m)
    (h : w ≤ v + y.toNat) : setWidth w (setWidth v (x >>> y)) = x >>> y := by
  rw [BitVec.ushiftRight_eq']
  exact setWidth_setWidth_ushiftRight_of_le v _ x h

@[width_norm]
theorem setWidth_ushiftRight_setWidth_of_le {w v : Nat} (n : Nat) (x : BitVec w) (h : w ≤ v) :
    setWidth w (setWidth v x >>> n) = x >>> n := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hxv : x.toNat < 2 ^ v := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) h)
  simp only [toNat_setWidth, toNat_ushiftRight, Nat.mod_eq_of_lt hxv]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hx)]

@[width_norm]
theorem setWidth_shiftLeft_setWidth_of_le {w v : Nat} (n : Nat) (x : BitVec w) (h : w ≤ v) :
    setWidth w (setWidth v x <<< n) = x <<< n := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hxv : x.toNat < 2 ^ v := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) h)
  simp only [toNat_setWidth, toNat_shiftLeft, Nat.mod_eq_of_lt hxv]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)

@[width_norm]
theorem setWidth_ushiftRight_setWidth_bv_of_le {w v m : Nat} (y : BitVec m) (x : BitVec w)
    (h : w ≤ v) : setWidth w (setWidth v x >>> y) = x >>> y := by
  rw [BitVec.ushiftRight_eq', BitVec.ushiftRight_eq']
  exact setWidth_ushiftRight_setWidth_of_le _ x h

@[width_norm]
theorem setWidth_shiftLeft_setWidth_bv_of_le {w v m : Nat} (y : BitVec m) (x : BitVec w)
    (h : w ≤ v) : setWidth w (setWidth v x <<< y) = x <<< y := by
  rw [BitVec.shiftLeft_eq', BitVec.shiftLeft_eq']
  exact setWidth_shiftLeft_setWidth_of_le _ x h

/-! ## Bitwise Round Trips -/

@[width_norm]
theorem setWidth_and_setWidth_of_le {w v : Nat} (x : BitVec w) (y : BitVec v) (h : w ≤ v) :
    setWidth w (setWidth v x &&& y) = x &&& setWidth w y := by
  rw [BitVec.setWidth_and, BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq]

@[width_norm]
theorem setWidth_setWidth_and_of_le {w v : Nat} (x : BitVec w) (y : BitVec v) (h : w ≤ v) :
    setWidth w (y &&& setWidth v x) = setWidth w y &&& x := by
  rw [BitVec.setWidth_and, BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq]

@[width_norm]
theorem setWidth_or_setWidth_of_le {w v : Nat} (x : BitVec w) (y : BitVec v) (h : w ≤ v) :
    setWidth w (setWidth v x ||| y) = x ||| setWidth w y := by
  rw [BitVec.setWidth_or, BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq]

@[width_norm]
theorem setWidth_setWidth_or_of_le {w v : Nat} (x : BitVec w) (y : BitVec v) (h : w ≤ v) :
    setWidth w (y ||| setWidth v x) = setWidth w y ||| x := by
  rw [BitVec.setWidth_or, BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq]

@[width_norm]
theorem setWidth_xor_setWidth_of_le {w v : Nat} (x : BitVec w) (y : BitVec v) (h : w ≤ v) :
    setWidth w (setWidth v x ^^^ y) = x ^^^ setWidth w y := by
  rw [BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq]

@[width_norm]
theorem setWidth_setWidth_xor_of_le {w v : Nat} (x : BitVec w) (y : BitVec v) (h : w ≤ v) :
    setWidth w (y ^^^ setWidth v x) = setWidth w y ^^^ x := by
  rw [BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq]

/-! ## Comparisons Through a Zero-Extension -/

@[width_norm, wp_branch]
theorem setWidth_beq_ofNat {w v : Nat} (x : BitVec w) (k : Nat)
    (h : w ≤ v := by omega) (hk : k < 2 ^ w := by omega) :
    (setWidth v x == BitVec.ofNat v k) = (x == BitVec.ofNat w k) := by
  have hkv : k < 2 ^ v := Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by omega) h)
  have hxv : x.toNat < 2 ^ v := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) h)
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj, ← BitVec.toNat_inj]
  simp [toNat_setWidth, Nat.mod_eq_of_lt hxv, Nat.mod_eq_of_lt hkv, Nat.mod_eq_of_lt hk]

@[width_norm, wp_branch]
theorem setWidth_eq_ofNat {w v : Nat} (x : BitVec w) (k : Nat)
    (h : w ≤ v := by omega) (hk : k < 2 ^ w := by omega) :
    (setWidth v x = BitVec.ofNat v k) = (x = BitVec.ofNat w k) := by
  have hkv : k < 2 ^ v := Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by omega) h)
  have hxv : x.toNat < 2 ^ v := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) h)
  rw [← BitVec.toNat_inj, ← BitVec.toNat_inj]
  simp [toNat_setWidth, Nat.mod_eq_of_lt hxv, Nat.mod_eq_of_lt hkv, Nat.mod_eq_of_lt hk]

@[width_norm, wp_branch]
theorem setWidth_ult_ofNat {w v : Nat} (x : BitVec w) (k : Nat)
    (h : w ≤ v := by omega) (hk : k < 2 ^ w := by omega) :
    (setWidth v x).ult (BitVec.ofNat v k) = x.ult (BitVec.ofNat w k) := by
  have hkv : k < 2 ^ v := Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by omega) h)
  have hxv : x.toNat < 2 ^ v := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) h)
  simp [BitVec.ult, toNat_setWidth, Nat.mod_eq_of_lt hxv, Nat.mod_eq_of_lt hkv, Nat.mod_eq_of_lt hk]

@[width_norm, wp_branch]
theorem ofNat_beq_setWidth {w v : Nat} (x : BitVec w) (k : Nat)
    (h : w ≤ v := by omega) (hk : k < 2 ^ w := by omega) :
    (BitVec.ofNat v k == setWidth v x) = (BitVec.ofNat w k == x) := by
  rw [BEq.comm, setWidth_beq_ofNat x k h hk, BEq.comm]

@[width_norm, wp_branch]
theorem ofNat_eq_setWidth {w v : Nat} (x : BitVec w) (k : Nat)
    (h : w ≤ v := by omega) (hk : k < 2 ^ w := by omega) :
    (BitVec.ofNat v k = setWidth v x) = (BitVec.ofNat w k = x) := by
  rw [@eq_comm _ (BitVec.ofNat v k), setWidth_eq_ofNat x k h hk]
  exact propext eq_comm

@[width_norm, wp_branch]
theorem ofNat_ult_setWidth {w v : Nat} (x : BitVec w) (k : Nat)
    (h : w ≤ v := by omega) (hk : k < 2 ^ w := by omega) :
    (BitVec.ofNat v k).ult (setWidth v x) = (BitVec.ofNat w k).ult x := by
  have hkv : k < 2 ^ v := Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by omega) h)
  have hxv : x.toNat < 2 ^ v := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) h)
  simp [BitVec.ult, toNat_setWidth, Nat.mod_eq_of_lt hxv, Nat.mod_eq_of_lt hkv, Nat.mod_eq_of_lt hk]

@[width_norm, wp_branch]
theorem setWidth_eq_zero_iff {w v : Nat} (x : BitVec w) (h : w ≤ v := by omega) :
    (setWidth v x = 0#v) ↔ (x = 0#w) := by
  have hx0 : 0 < 2 ^ w := Nat.two_pow_pos w
  simpa using Eq.to_iff (setWidth_eq_ofNat x 0 h hx0)

@[width_norm, wp_branch]
theorem setWidth_ult_setWidth {w v : Nat} (x y : BitVec w) (h : w ≤ v := by omega) :
    (setWidth v x).ult (setWidth v y) = x.ult y := by
  have hxv : x.toNat < 2 ^ v := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) h)
  have hyv : y.toNat < 2 ^ v := Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by omega) h)
  simp [BitVec.ult, toNat_setWidth, Nat.mod_eq_of_lt hxv, Nat.mod_eq_of_lt hyv]

@[width_norm, wp_branch]
theorem setWidth_ule_setWidth {w v : Nat} (x y : BitVec w) (h : w ≤ v := by omega) :
    (setWidth v x).ule (setWidth v y) = x.ule y := by
  have hxv : x.toNat < 2 ^ v := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) h)
  have hyv : y.toNat < 2 ^ v := Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by omega) h)
  simp [BitVec.ule, toNat_setWidth, Nat.mod_eq_of_lt hxv, Nat.mod_eq_of_lt hyv]

@[width_norm, wp_branch]
theorem setWidth_inj_iff {w v : Nat} (x y : BitVec w) (h : w ≤ v := by omega) :
    (setWidth v x = setWidth v y) ↔ (x = y) := by
  have hxv : x.toNat < 2 ^ v := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) h)
  have hyv : y.toNat < 2 ^ v := Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by omega) h)
  rw [← BitVec.toNat_inj, ← BitVec.toNat_inj]
  simp [toNat_setWidth, Nat.mod_eq_of_lt hxv, Nat.mod_eq_of_lt hyv]

/-- `SXTW` (`SBFM` with `immr = 0, imms = 31` at `.W64`) normalizes to `(v.setWidth 32).signExtend 64`. -/
@[width_norm]
theorem sbfm_sxtw_eq_signExtend (dst v : BitVec 64) :
    Arm64.evalBitfield .W64 .SBFM dst v 0 31 = (v.setWidth 32).signExtend 64 := by
  simp only [Arm64.evalBitfield]
  ext i hi
  have hlo : (4294967295#64)[i] = decide (i < 32) := by
    rw [BitVec.getElem_eq_testBit_toNat, show (4294967295#64).toNat = 2 ^ 32 - 1 from rfl,
        Nat.testBit_two_pow_sub_one]
  have hhi : (18446744069414584320#64)[i] = !decide (i < 32) := by
    rw [show 18446744069414584320#64 = ~~~4294967295#64 from rfl, BitVec.getElem_not, hlo]
  by_cases h32 : i < 32
  · simp [hlo, hhi, h32, BitVec.getElem_signExtend]
    rfl
  · have hmsb : (v.setWidth 32).msb = v[31] := by
      rw [BitVec.msb_eq_getLsbD_last]; simp
    by_cases hs : v[31] = true <;>
      simp [hlo, hhi, h32, hmsb, hs, BitVec.getElem_signExtend]

/-! ## Register-Shift Amount Masks (`LSLV` / `LSRV`)

`Arm64.shift64 x .LSL y.toNat` reduces to `x <<< (y.toNat % 64)`, so these lemmas orient masked
shifts (`y &&& 63#64`) toward `% 64`. They are omitted from `@[simp]` because core `simp` rewrites
`x <<< (y &&& 63#64)` to `x <<< (y.toNat &&& 63)`. -/

@[width_norm]
theorem shiftLeft_and_63 (x y : BitVec 64) : x <<< (y &&& 63#64) = x <<< (y.toNat % 64) := by
  rw [BitVec.shiftLeft_eq', BitVec.toNat_and, toNat_ofNat]
  exact congrArg _ (Nat.and_two_pow_sub_one_eq_mod _ 6)

@[width_norm]
theorem ushiftRight_and_63 (x y : BitVec 64) : x >>> (y &&& 63#64) = x >>> (y.toNat % 64) := by
  rw [BitVec.ushiftRight_eq', BitVec.toNat_and, toNat_ofNat]
  exact congrArg _ (Nat.and_two_pow_sub_one_eq_mod _ 6)

@[width_norm]
theorem shiftLeft_and_31 (x y : BitVec 32) : x <<< (y &&& 31#32) = x <<< (y.toNat % 32) := by
  rw [BitVec.shiftLeft_eq', BitVec.toNat_and, toNat_ofNat]
  exact congrArg _ (Nat.and_two_pow_sub_one_eq_mod _ 5)

@[width_norm]
theorem ushiftRight_and_31 (x y : BitVec 32) : x >>> (y &&& 31#32) = x >>> (y.toNat % 32) := by
  rw [BitVec.ushiftRight_eq', BitVec.toNat_and, toNat_ofNat]
  exact congrArg _ (Nat.and_two_pow_sub_one_eq_mod _ 5)

/-! ## `UMULH` -/

/-- `UMULH` (`Arm64.execDataProc3 .W64 .UMULH`) as a `Nat` product: high 64 bits of `a * b`.
    Untagged: rewriting into `toNat` arithmetic is a proof-strategy choice, not a normal form. -/
theorem setWidth_umulh (a b : BitVec 64) :
    setWidth 64 ((setWidth 128 a * setWidth 128 b) >>> 64) =
      BitVec.ofNat 64 ((a.toNat * b.toNat) >>> 64) := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  have hprod : a.toNat * b.toNat < 2 ^ 128 := by
    calc a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 128 := by decide
  simp only [toNat_setWidth, toNat_ushiftRight, toNat_mul, toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : a.toNat < 2 ^ 128),
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 128), Nat.mod_eq_of_lt hprod]

/-! ## Signed 32-to-64-Bit Index Scaling (`LSL #32` Followed by `ASR #(32 - s)`)

When a non-negative 32-bit signed index `k < 2 ^ 31` is sign-extended and scaled by `2 ^ s`
(`s ≤ 32`) via a 64-bit left shift by 32 (`BitVec.ofNat 64 (k * 2 ^ 32)`) followed by an
arithmetic right shift by `32 - s` (`.sshiftRight (32 - s)`), the sign bit is `false` and the
composite shift normalizes to `BitVec.ofNat 64 (k * 2 ^ s)`. Concrete specializations for
`s = 1, 2, 3, 0` and folded `4294967296` (`2 ^ 32`) multipliers match after numeral reduction. -/

/-- Arithmetic right shift coincides with unsigned logical right shift whenever the sign bit is
    clear (`v.toNat < 2 ^ (w - 1)` for positive width `w`). -/
@[width_norm]
theorem sshiftRight_of_lt_sign {w : Nat} (v : BitVec w) (k : Nat) (hw : 0 < w)
    (h : v.toNat < 2 ^ (w - 1)) : v.sshiftRight k = v >>> k := by
  have hmsb : v.msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    have hp : 2 ^ w = 2 * 2 ^ (w - 1) := by
      have hw1 : w = 1 + (w - 1) := by omega
      conv => lhs; rw [hw1, Nat.pow_add, Nat.pow_one]
    omega
  exact BitVec.sshiftRight_eq_of_msb_false hmsb

@[simp, width_norm]
theorem sshiftRight_ofNat_mul_two_pow_32_sub (k s : Nat) (hs : s ≤ 32) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight (32 - s) = BitVec.ofNat 64 (k * 2 ^ s) := by
  have hlt64 : k * 2 ^ 32 < 2 ^ 64 := by omega
  have hlt63 : (BitVec.ofNat 64 (k * 2 ^ 32)).toNat < 2 ^ (64 - 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]; omega
  have hlt_s : k * 2 ^ s < 2 ^ 64 := by
    have hle : 2 ^ s ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hs
    have : k * 2 ^ s ≤ k * 2 ^ 32 := Nat.mul_le_mul_left k hle
    omega
  rw [sshiftRight_of_lt_sign _ _ (by omega) hlt63]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64,
    Nat.shiftRight_eq_div_pow]
  have hpow : k * 2 ^ 32 = (k * 2 ^ s) * 2 ^ (32 - s) := by
    have h32 : 32 = s + (32 - s) := by omega
    conv => lhs; rw [h32, Nat.pow_add, ← Nat.mul_assoc]
  rw [hpow, Nat.mul_div_cancel _ (Nat.two_pow_pos (32 - s)),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_s]

@[simp, width_norm]
theorem sshiftRight_ofNat_mul_4294967296_sub (k s : Nat) (hs : s ≤ 32) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 4294967296)).sshiftRight (32 - s) = BitVec.ofNat 64 (k * 2 ^ s) :=
  sshiftRight_ofNat_mul_two_pow_32_sub k s hs hk

@[simp, width_norm]
theorem sshiftRight_ofNat_two_pow_32_mul_sub (k s : Nat) (hs : s ≤ 32) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (2 ^ 32 * k)).sshiftRight (32 - s) = BitVec.ofNat 64 (k * 2 ^ s) :=
  Nat.mul_comm (2 ^ 32) k ▸ sshiftRight_ofNat_mul_two_pow_32_sub k s hs hk

@[simp, width_norm]
theorem sshiftRight_ofNat_4294967296_mul_sub (k s : Nat) (hs : s ≤ 32) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (4294967296 * k)).sshiftRight (32 - s) = BitVec.ofNat 64 (k * 2 ^ s) :=
  Nat.mul_comm (2 ^ 32) k ▸ sshiftRight_ofNat_mul_two_pow_32_sub k s hs hk

@[simp, width_norm]
theorem sshiftRight_31_ofNat_mul_two_pow_32 (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight 31 = BitVec.ofNat 64 (k * 2) :=
  sshiftRight_ofNat_mul_two_pow_32_sub k 1 (by omega) hk

@[simp, width_norm]
theorem sshiftRight_31_ofNat_mul_4294967296 (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 4294967296)).sshiftRight 31 = BitVec.ofNat 64 (k * 2) :=
  sshiftRight_ofNat_mul_two_pow_32_sub k 1 (by omega) hk

@[simp, width_norm]
theorem sshiftRight_31_ofNat_two_pow_32_mul (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (2 ^ 32 * k)).sshiftRight 31 = BitVec.ofNat 64 (k * 2) :=
  Nat.mul_comm (2 ^ 32) k ▸ sshiftRight_ofNat_mul_two_pow_32_sub k 1 (by omega) hk

@[simp, width_norm]
theorem sshiftRight_31_ofNat_4294967296_mul (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (4294967296 * k)).sshiftRight 31 = BitVec.ofNat 64 (k * 2) :=
  Nat.mul_comm (2 ^ 32) k ▸ sshiftRight_ofNat_mul_two_pow_32_sub k 1 (by omega) hk

@[simp, width_norm]
theorem sshiftRight_30_ofNat_mul_two_pow_32 (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight 30 = BitVec.ofNat 64 (k * 4) :=
  sshiftRight_ofNat_mul_two_pow_32_sub k 2 (by omega) hk

@[simp, width_norm]
theorem sshiftRight_30_ofNat_mul_4294967296 (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 4294967296)).sshiftRight 30 = BitVec.ofNat 64 (k * 4) :=
  sshiftRight_ofNat_mul_two_pow_32_sub k 2 (by omega) hk

@[simp, width_norm]
theorem sshiftRight_30_ofNat_two_pow_32_mul (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (2 ^ 32 * k)).sshiftRight 30 = BitVec.ofNat 64 (k * 4) :=
  Nat.mul_comm (2 ^ 32) k ▸ sshiftRight_ofNat_mul_two_pow_32_sub k 2 (by omega) hk

@[simp, width_norm]
theorem sshiftRight_30_ofNat_4294967296_mul (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (4294967296 * k)).sshiftRight 30 = BitVec.ofNat 64 (k * 4) :=
  Nat.mul_comm (2 ^ 32) k ▸ sshiftRight_ofNat_mul_two_pow_32_sub k 2 (by omega) hk

@[simp, width_norm]
theorem sshiftRight_29_ofNat_mul_two_pow_32 (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight 29 = BitVec.ofNat 64 (k * 8) :=
  sshiftRight_ofNat_mul_two_pow_32_sub k 3 (by omega) hk

@[simp, width_norm]
theorem sshiftRight_29_ofNat_mul_4294967296 (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 4294967296)).sshiftRight 29 = BitVec.ofNat 64 (k * 8) :=
  sshiftRight_ofNat_mul_two_pow_32_sub k 3 (by omega) hk

@[simp, width_norm]
theorem sshiftRight_29_ofNat_two_pow_32_mul (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (2 ^ 32 * k)).sshiftRight 29 = BitVec.ofNat 64 (k * 8) :=
  Nat.mul_comm (2 ^ 32) k ▸ sshiftRight_ofNat_mul_two_pow_32_sub k 3 (by omega) hk

@[simp, width_norm]
theorem sshiftRight_29_ofNat_4294967296_mul (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (4294967296 * k)).sshiftRight 29 = BitVec.ofNat 64 (k * 8) :=
  Nat.mul_comm (2 ^ 32) k ▸ sshiftRight_ofNat_mul_two_pow_32_sub k 3 (by omega) hk

@[simp, width_norm]
theorem sshiftRight_32_ofNat_mul_two_pow_32 (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 2 ^ 32)).sshiftRight 32 = BitVec.ofNat 64 k := by
  simpa using sshiftRight_ofNat_mul_two_pow_32_sub k 0 (by omega) hk

@[simp, width_norm]
theorem sshiftRight_32_ofNat_mul_4294967296 (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (k * 4294967296)).sshiftRight 32 = BitVec.ofNat 64 k := by
  simpa using sshiftRight_ofNat_mul_two_pow_32_sub k 0 (by omega) hk

@[simp, width_norm]
theorem sshiftRight_32_ofNat_two_pow_32_mul (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (2 ^ 32 * k)).sshiftRight 32 = BitVec.ofNat 64 k := by
  rw [Nat.mul_comm (2 ^ 32) k]; simpa using sshiftRight_ofNat_mul_two_pow_32_sub k 0 (by omega) hk

@[simp, width_norm]
theorem sshiftRight_32_ofNat_4294967296_mul (k : Nat) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 64 (4294967296 * k)).sshiftRight 32 = BitVec.ofNat 64 k := by
  rw [show 4294967296 * k = k * 2 ^ 32 by omega]; simpa using sshiftRight_ofNat_mul_two_pow_32_sub k 0 (by omega) hk

/-! ## Unsigned Bounds and Right-Shift / Bitfield `Nat` Normalization -/

/-- Alias for `BitVec.isLt` supporting dot notation `x.toNat_lt`. -/
theorem toNat_lt {w : Nat} (x : BitVec w) : x.toNat < 2 ^ w :=
  x.isLt

theorem toNat_div_pow_lt {w : Nat} (x : BitVec w) (k : Nat) :
    x.toNat / 2 ^ k < 2 ^ (w - k) := by
  have hx := x.isLt
  have hpow : 2 ^ w ≤ 2 ^ k * 2 ^ (w - k) := by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  exact Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le hx hpow)

@[width_norm]
theorem toNat_ushiftRight_mod {n : Nat} (x : BitVec n) (k m : Nat) :
    (x >>> k).toNat % m = (x.toNat / 2 ^ k) % m := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[width_norm]
theorem toNat_shiftRight_mod_pow2 {n : Nat} (x : BitVec n) (k m : Nat) :
    (x.toNat >>> k) % m = (x.toNat / 2 ^ k) % m := by
  rw [Nat.shiftRight_eq_div_pow]

@[width_norm]
theorem toNat_shiftRight_mod {n : Nat} (x : BitVec n) (k m : Nat) :
    (x.toNat >>> k) % m = (x.toNat / 2 ^ k) % m :=
  toNat_shiftRight_mod_pow2 x k m

@[width_norm]
theorem toNat_ushiftRight_mod_pow {n : Nat} (x : BitVec n) (k w : Nat) :
    (x >>> k).toNat % 2 ^ w = (x.toNat / 2 ^ k) % 2 ^ w :=
  toNat_ushiftRight_mod x k (2 ^ w)

@[width_norm]
theorem toNat_extractLsb'_div_pow {n : Nat} (x : BitVec n) (k w : Nat) :
    (x.extractLsb' k w).toNat = (x.toNat / 2 ^ k) % 2 ^ w := by
  simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

@[simp, width_norm]
theorem toNat_shiftRight_mod_64 (x : BitVec 64) (k m : Nat) :
    (x.toNat >>> k) % m = (x.toNat / 2 ^ k) % m :=
  toNat_shiftRight_mod_pow2 x k m

@[simp, width_norm]
theorem toNat_shiftRight_mod_32 (x : BitVec 32) (k m : Nat) :
    (x.toNat >>> k) % m = (x.toNat / 2 ^ k) % m :=
  toNat_shiftRight_mod_pow2 x k m

@[simp, width_norm]
theorem toNat_shiftRight_mod_16 (x : BitVec 16) (k m : Nat) :
    (x.toNat >>> k) % m = (x.toNat / 2 ^ k) % m :=
  toNat_shiftRight_mod_pow2 x k m

@[simp, width_norm]
theorem toNat_shiftRight_mod_8 (x : BitVec 8) (k m : Nat) :
    (x.toNat >>> k) % m = (x.toNat / 2 ^ k) % m :=
  toNat_shiftRight_mod_pow2 x k m

/-- Extract bits `[k, k + w)` from a low `(k + w)`-bit slice. -/
@[width_norm]
theorem toNat_mod_pow_add_div_pow {n : Nat} (x : BitVec n) (k w : Nat) :
    (x.toNat % 2 ^ (k + w)) / 2 ^ k = (x.toNat / 2 ^ k) % 2 ^ w := by
  rw [Nat.pow_add, Nat.mod_mul_right_div_self]

@[addr_norm]
theorem add_ofNat_add_ofNat {w : Nat} (base : BitVec w) (a b : Nat) :
    base + BitVec.ofNat w a + BitVec.ofNat w b = base + BitVec.ofNat w (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

@[addr_norm]
theorem add_ofNat_sub_ofNat_of_le {w : Nat} (base : BitVec w) (a b : Nat) (h : b ≤ a) :
    base + BitVec.ofNat w a - BitVec.ofNat w b = base + BitVec.ofNat w (a - b) := by
  have h1 := add_ofNat_add_ofNat base (a - b) b
  rw [show a - b + b = a by omega] at h1
  rw [← h1, BitVec.add_sub_cancel]

attribute [addr_norm] BitVec.sub_ofNat_add_ofNat_of_le BitVec.sub_ofNat_sub_ofNat

@[addr_norm]
theorem add_setWidth_add_ofNat (base : BitVec 64) (idx : BitVec 32) (off : Nat)
    (h : idx.toNat + off < 2 ^ 64) :
    base + idx.setWidth 64 + BitVec.ofNat 64 off = base + BitVec.ofNat 64 (idx.toNat + off) := by
  let _ := h
  have hidx : idx.setWidth 64 = BitVec.ofNat 64 idx.toNat := by
    apply BitVec.eq_of_toNat_eq
    have hi := idx.isLt
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : idx.toNat < 2 ^ 64)]
  rw [hidx, add_ofNat_add_ofNat]

@[addr_norm]
theorem add_ofNat_add_setWidth (base : BitVec 64) (off : Nat) (idx : BitVec 32)
    (h : off + idx.toNat < 2 ^ 64) :
    base + BitVec.ofNat 64 off + idx.setWidth 64 = base + BitVec.ofNat 64 (off + idx.toNat) := by
  let _ := h
  have hidx : idx.setWidth 64 = BitVec.ofNat 64 idx.toNat := by
    apply BitVec.eq_of_toNat_eq
    have hi := idx.isLt
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : idx.toNat < 2 ^ 64)]
  rw [hidx, add_ofNat_add_ofNat]

@[addr_norm]
theorem ofNat_toNat_add {w : Nat} (a : BitVec w) (b : Nat) :
    BitVec.ofNat w (a.toNat + b) = a + BitVec.ofNat w b := by
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## Sign-Extension, Truncation Sign-Bit, and Signed-Byte Helpers -/

/-- Sign-extension agrees with zero-extension whenever the source sign bit `v.getLsbD idx`
    (`idx = w - 1`, `0 < w`) is `false`. -/
theorem signExtend_eq_zeroExtend_of_getLsbD_false {w w' idx : Nat} (v : BitVec w)
    (h : v.getLsbD idx = false) (hw : 0 < w := by decide) (hidx : idx = w - 1 := by rfl) :
    BitVec.signExtend w' v = BitVec.zeroExtend w' v := by
  let _ := hw
  subst hidx
  have hmsb : v.msb = false := by rwa [BitVec.msb_eq_getLsbD_last]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_signExtend, hmsb]

abbrev sext_eq_zext := @signExtend_eq_zeroExtend_of_getLsbD_false

/-- Sign bit of a `k`-bit truncation `(v.truncate k).msb` (`0 < k`) is bit `idx` (`idx = k - 1`). -/
theorem msb_truncate {w k idx : Nat} (v : BitVec w)
    (hk : 0 < k := by decide) (hidx : idx = k - 1 := by rfl) :
    (v.truncate k).msb = v.getLsbD idx := by
  subst hidx
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_setWidth]
  simp [Nat.sub_lt hk (by decide : 0 < 1)]

/-- Sign bit of a 32-bit truncation `(v.truncate 32).msb` of a 64-bit word is bit 31. -/
theorem msb_trunc32 (v : BitVec 64) : (v.truncate 32).msb = v.getLsbD 31 :=
  msb_truncate v

/-- Sign-extending a non-negative byte (`v.toNat < 128`) to 64 bits yields `BitVec.ofNat 64 v.toNat`. -/
theorem signExtend64_byte_of_lt (v : BitVec 8) (hv : v.toNat < 128) :
    BitVec.signExtend 64 v = BitVec.ofNat 64 v.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  omega

/-- Sign-extending a negative signed byte (`128 ≤ v.toNat`) to 64 bits yields
    `BitVec.ofNat 64 v.toNat - 256#64`. -/
theorem signExtend64_byte_of_ge (v : BitVec 8) (hv : 128 ≤ v.toNat) :
    BitVec.signExtend 64 v = BitVec.ofNat 64 v.toNat - 256#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_signExtend, BitVec.msb_eq_decide, BitVec.toNat_sub, hv]
  omega

/-- Bit 63 (sign bit) of a byte sign-extended to 64 bits is `decide (128 ≤ v.toNat)`. -/
theorem getLsbD_63_signExtend64_byte (v : BitVec 8) :
    (BitVec.signExtend 64 v).getLsbD 63 = decide (128 ≤ v.toNat) := by
  rw [BitVec.getLsbD_signExtend, BitVec.msb_eq_decide]
  simp

end BitVec

namespace ProofLib

/-- `mulHi64 x y` as `BitVec.ofNat 64 ((x.toNat * y.toNat) >>> 64)` (see `BitVec.setWidth_umulh`). -/
theorem mulHi64_eq_ofNat (x y : BitVec 64) :
    mulHi64 x y = BitVec.ofNat 64 ((x.toNat * y.toNat) >>> 64) :=
  BitVec.setWidth_umulh x y

abbrev sext_eq_zext := @BitVec.signExtend_eq_zeroExtend_of_getLsbD_false
abbrev msb_truncate := @BitVec.msb_truncate
abbrev msb_trunc32 := @BitVec.msb_trunc32
abbrev signExtend64_byte_of_lt := @BitVec.signExtend64_byte_of_lt
abbrev signExtend64_byte_of_ge := @BitVec.signExtend64_byte_of_ge
abbrev getLsbD_63_signExtend64_byte := @BitVec.getLsbD_63_signExtend64_byte

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

end ProofLib

public section BvToNatTactic
/-- Lift `BitVec` equalities, unsigned comparisons (`ult`/`ule`/`<`/`≤`), and arithmetic operations
    across hypotheses and goal into `Nat` `.toNat` obligations. -/
macro "bv_to_nat" : tactic => `(tactic|
  (try simp (disch := omega) only [addr_norm] at *;
   simp only [
     ← BitVec.toNat_inj,
     BitVec.ult, BitVec.ule, BitVec.lt_def, BitVec.le_def,
     decide_eq_true_eq, decide_eq_false_iff_not,
     BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul,
     BitVec.toNat_ofNat, BitVec.toNat_setWidth,
     BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
     Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
     width_norm
   ] at *))

/-- Normalize `[addr_norm]` pointer/width offsets, lift `BitVec` operations and width bounds into
    `Nat` via `bv_to_nat`, and close linear/modular arithmetic goals with `omega`. -/
macro "bv_nat" : tactic => `(tactic| (bv_to_nat; omega))

end BvToNatTactic
