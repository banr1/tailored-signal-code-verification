/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.BV.Bits
import Arm64.Trusted.Spec.SepLogic

/-!
# Regression Tests for `bv_bits`

Positive and negative regression tests for the `bv_bits` tactic across bitmasks, shifts, unsigned
and signed comparisons, byte extraction, concatenation chains, and kernel axiom checks.
-/

@[expose] public section

set_option linter.unusedVariables false

namespace ProofLib.BV.BitsTests

/-! ## Masks -/

theorem ls_ofNat_and_63 (n : Nat) : BitVec.ofNat 64 n &&& 63#64 = BitVec.ofNat 64 (n % 64) := by
  bv_bits

theorem ls_and_clear_low (x : BitVec 64) (h : x < 0x8000000000000000#64) :
    x &&& 0x7FFFFFFFFFFFFFC0#64 = x - (x &&& 63#64) := by
  bv_bits

theorem ls_ofNat_div (x : BitVec 64) : BitVec.ofNat 8 (x.toNat / 2 ^ 8) = x.extractLsb' 8 8 := by
  bv_bits

theorem ls_xor_63 (n : Nat) (h : n < 64) : BitVec.ofNat 64 n ^^^ 63#64 = BitVec.ofNat 64 (63 - n) := by
  bv_bits

theorem ls_adrp (b : BitVec 64) : b.toNat % 4096 = 0 ↔ b &&& 4095#64 = 0#64 := by
  bv_bits

theorem ls_sp_align (sp : BitVec 64) (h : sp &&& 15#64 = 0#64) : (sp - 512#64) &&& 15#64 = 0#64 := by
  bv_bits

theorem z_and_mod (x : BitVec 64) : (x &&& 4095#64).toNat = x.toNat % 2 ^ 12 := by
  bv_bits

theorem z_and_not (x : BitVec 64) : (x &&& ~~~7#64).toNat = x.toNat / 8 * 8 := by
  bv_bits

theorem z_mod64_div_mod8 (n : BitVec 64) : (n &&& 63#64) >>> 3 = (n >>> 3) &&& 7#64 := by
  bv_bits

/-! ## Comparisons and Branching -/

theorem A001 {u v : BitVec 64} : ¬(63#64).ult (v ||| u) = true → u < 64#64 ∧ v < 64#64 := by
  bv_bits

theorem A002 {u v : BitVec 64} : ¬(64#64).ule (v ||| u) = true → u < 64#64 ∧ v < 64#64 := by
  bv_bits

theorem D048 (x : BitVec 64) : (34#64).ule x = true ↔ ¬x.ule 33#64 = true := by
  bv_bits

theorem D045 (x_1 x_2 : BitVec 64) :
    (if x_2.ult x_1 = true then x_1 - x_2 else -(x_1 - x_2)) =
      if x_1.ult x_2 = true then x_2 - x_1 else x_1 - x_2 := by
  bv_bits

theorem D046 (x_1 x_2 x_3 : BitVec 64) :
    (if (if x_2.ult x_1 = true then x_1 else x_2).ult x_3 = true then
        if x_2.ult x_1 = true then x_1 else x_2
      else x_3) =
      if (if x_2.ule x_1 = true then x_1 else x_2).ule x_3 = true then
        if x_2.ule x_1 = true then x_1 else x_2
      else x_3 := by
  bv_bits

/-! ## Shifts, Masks, and Byte Extraction -/

theorem F061 {n : Nat} : n < 2 ^ 64 → BitVec.ofNat 64 (n / 8 * 8) = BitVec.ofNat 64 n >>> 3 <<< 3 →
    BitVec.ofNat 64 n &&& -8#64 = BitVec.ofNat 64 n >>> 3 <<< 3 := by
  bv_bits

theorem F062 {n : Nat} : n < 2 ^ 64 →
    BitVec.ofNat 64 n &&& 7#64 = BitVec.ofNat 64 n - BitVec.ofNat 64 n >>> 3 <<< 3 := by
  bv_bits

theorem H098 (lo hi : BitVec 64) : hi = BitVec.extractLsb' 64 64 (hi ++ lo) := by
  bv_bits

theorem H091 (ea : BitVec 64) (val32 : BitVec 32) (f_read8 : BitVec 64 → BitVec 8) :
    BitVec.extractLsb' 40 8
        (f_read8 (ea + 7#64) ++ f_read8 (ea + 6#64) ++ f_read8 (ea + 5#64) ++ f_read8 (ea + 4#64) ++
              f_read8 (ea + 3#64) ++ f_read8 (ea + 2#64) ++ f_read8 (ea + 1#64) ++ f_read8 (ea + 0#64) &&&
            18446744069414584320#64 |||
          BitVec.zeroExtend 64 val32) =
      f_read8 (ea + 5#64) := by
  bv_bits

theorem H101 (a : BitVec 64) (n : BitVec 8)
    (h : BitVec.zeroExtend 64 (BitVec.truncate 32 a) = BitVec.zeroExtend 64 n) :
    a &&& 255#64 = BitVec.zeroExtend 64 n := by
  bv_bits

theorem H096 (a_dst a_src : BitVec 64) (f_read8 : BitVec 64 → BitVec 8) :
    (if a_dst + 6#64 = a_dst + 7#64 then
        BitVec.extractLsb' 56 8
          (f_read8 (a_src + 7#64) ++ f_read8 (a_src + 6#64) ++ f_read8 (a_src + 5#64) ++
            f_read8 (a_src + 4#64) ++ f_read8 (a_src + 3#64) ++ f_read8 (a_src + 2#64) ++
            f_read8 (a_src + 1#64) ++ f_read8 (a_src + 0#64))
      else if True then
        BitVec.extractLsb' 48 8
          (f_read8 (a_src + 7#64) ++ f_read8 (a_src + 6#64) ++ f_read8 (a_src + 5#64) ++
            f_read8 (a_src + 4#64) ++ f_read8 (a_src + 3#64) ++ f_read8 (a_src + 2#64) ++
            f_read8 (a_src + 1#64) ++ f_read8 (a_src + 0#64))
      else f_read8 (a_dst + 6#64)) =
      f_read8 (a_src + 6#64) := by
  bv_bits

theorem I119 (u v a_proj2 : BitVec 64) (P : Prop) :
    P → (a_proj2 &&& 15#64 == 0#64) = true → ¬(u == v) = true → u ≠ v →
      (63#64).ult (v ||| u) = true → 64#64 ≤ u ∨ 64#64 ≤ v := by
  bv_bits

theorem H086 (x y : BitVec 32) :
    ((if true = true then 1#33 else 0#33) + (BitVec.zeroExtend 33 (~~~y) +
      BitVec.zeroExtend 33 x)).msb = y.ule x := by
  bv_bits

theorem K144_like (dst src : BitVec 64) (len align : Nat)
    (r1 r2 r3 : BitVec 64) (h1 : r1 = dst + BitVec.ofNat 64 (len - align))
    (h2 : r2 = src + BitVec.ofNat 64 len) (h3 : r3 = -BitVec.ofNat 64 align)
    (h4 : (dst + BitVec.ofNat 64 (len - align)).ule (dst + BitVec.ofNat 64 ((len - align) % 8)) = false)
    (ha : align < 8) (hw : 1 ≤ (len - align) / 8)
    (hr : (len - align) % 8 + (len - align) / 8 * 8 = len - align) :
    (len - align) % 8 + ((len - align) / 8 - 1) * 8 = len - align - 8 := by
  bv_bits

theorem Z066 (x y : BitVec 32) :
    (BitVec.truncate 32 ((if True then BitVec.ofNat 33 1 else BitVec.ofNat 33 0) +
      (BitVec.zeroExtend 33 (~~~y) + BitVec.zeroExtend 33 x))).msb =
    (x - y).slt (BitVec.ofNat 32 0) := by
  bv_bits

theorem Z067 (err : BitVec 32) :
    (if (err - 3#32).ule (err - 3#32 + 9#32) = true then 9#64
      else BitVec.truncate 64 (2#32 - err)) =
    BitVec.truncate 64 (if (err.slt (-6#32) || (2#32).slt err) = true then 9#32
      else 2#32 - err) := by
  bv_bits

theorem or_shift_disjoint (b0 b1 : BitVec 8) :
    (b1.zeroExtend 16 <<< 8 ||| b0.zeroExtend 16) = b1 ++ b0 := by
  bv_bits

theorem shift_or_bounded (x y : BitVec 64) (h : y < 64#64) :
    x <<< 9 ||| y <<< 3 = x * 512#64 + y * 8#64 := by
  bv_bits

theorem low_byte_of_word (a : BitVec 8) (b : BitVec 32) :
    (((b.zeroExtend 64 <<< 32) + (a.zeroExtend 64)).extractLsb' 0 8) = a := by
  bv_bits

theorem stack_offsets (sp : BitVec 64) (h : sp &&& 15#64 = 0#64) :
    sp - 48#64 - 40#64 = sp - 80#64 - 8#64 := by
  bv_bits

/-! ## Negative Tests -/

#guard_msgs (drop error) in
example (x : BitVec 64) : x &&& 15#64 = x := by bv_bits

#guard_msgs (drop error) in
example (x y : BitVec 8) : x ||| y = x + y := by bv_bits

/-! ## Kernel Axiom Checks -/

/-- info: 'ProofLib.BV.BitsTests.H091' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms H091

/-- info: 'ProofLib.BV.BitsTests.D046' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms D046

/-- info: 'ProofLib.BV.BitsTests.ls_and_clear_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ls_and_clear_low

end ProofLib.BV.BitsTests
