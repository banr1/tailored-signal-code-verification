/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.BV.Arith
public import ProofLib.BV.MaskLemmas
import ProofLib.SimpAttrs
import Arm64.Trusted.Spec.SepLogic

/-!
# Regression Tests for `ProofLib.BV.Arith`

Regression tests for `bv_arith`, `bv_solve`, `decide_prop?`, and power-of-two mask lemmas.
-/

@[expose] public section

namespace ProofLib.BV.ArithTests

/-! ## `bv_arith` -/

-- Stack-offset folding goal; the `bv_lin` shortcut closes it without looking at hyps
theorem off1 (sp : BitVec 64) (P Q : Prop) (_ : P) (_ : Q) (_ : sp.toNat % 16 = 0) :
    sp - 512#64 - 4240#64 = sp - 4752#64 := by bv_arith

-- bound-driven, mod-free node facts
theorem bnd1 (x y : BitVec 64) (hx : x < 0x1000#64) (hy : y < 0x1000#64) :
    (x + y).toNat = x.toNat + y.toNat := by bv_arith

-- irrelevant hypotheses (no shared atoms) are never translated
theorem rel1 (a b c : BitVec 64) (_ : b * c = c * b + 1) (h : a < 10#64) : a + 1 ≤ 10#64 := by
  bv_arith

-- `ult`/`ule` as `Bool` equations
theorem ult1 (L : Nat) (_ : L < 2 ^ 32) (h : (BitVec.ofNat 64 L).ult 32#64 = true) : L < 32 := by
  bv_arith
theorem ule1 (x y : BitVec 32) (h : x.toNat ≤ y.toNat) : x.ule y = true := by bv_arith
theorem ule2 (x : BitVec 32) (y : BitVec 64) (h : x.toNat > y.toNat) :
    ¬ (BitVec.ule (BitVec.zeroExtend 64 x) y = true) := by bv_arith

-- `zeroExtend`/`truncate` abbreviations
theorem zx1 (n : Nat) (h : n < 2 ^ 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by
  bv_arith

-- low masks and contiguous range masks (ADRP page masks)
theorem mask1 (n : Nat) : BitVec.ofNat 64 n &&& 63#64 = BitVec.ofNat 64 (n % 64) := by bv_arith
theorem mask2 (n : Nat) (h : n < 2 ^ 63) :
    BitVec.ofNat 64 n &&& 9223372036854775744#64 = BitVec.ofNat 64 (64 * (n / 64)) := by
  bv_arith
theorem adrp1 (b : BitVec 64) (h : b.toNat % 4096 = 0) :
    (b + 91720#64 + 152#64 &&& 18446744073709547520#64) + 188416#64 + 3617#64 =
      b + 282145#64 := by bv_arith
theorem adrp2 (b x : BitVec 64) (h : b &&& 4095#64 = 0#64) :
    (b + x &&& 18446744073709547520#64) = b + (x &&& 18446744073709547520#64) := by bv_arith

-- the goal is literally a hypothesis
theorem asm1 (P : Prop) (a : BitVec 64) (_ : a = 1#64) (h : P) : P := by bv_arith

-- closed false goal: contradiction among hypotheses
theorem gnd1 (a : BitVec 64) (h1 : a < 4#64) (h2 : 8#64 ≤ a) : 1#64 = 0#64 := by bv_arith

-- register-file equations share `len`/`src`/`dst` with the goal but define otherwise-unused
-- atoms (`r k`); they are pruned as dangling definitions instead of handed to `omega`
theorem dangle1 (r : Nat → BitVec 64) (dst src : BitVec 64) (len align : Nat)
    (_hd : dst.toNat + len < 2 ^ 64) (_h16 : 16 ≤ len) (_ha : align < 8)
    (_h1 : r 1 = src) (_h2 : r 2 = BitVec.ofNat 64 len) (_h9 : r 9 = src + BitVec.ofNat 64 len)
    (_h10 : r 10 = dst + BitVec.ofNat 64 (len - align)) (_h11 : r 11 = BitVec.ofNat 64 align)
    (_h12 : r 12 = -BitVec.ofNat 64 align) (_h13 : r 13 = src + BitVec.ofNat 64 (len - align))
    (_h14 : r 14 = -BitVec.ofNat 64 ((len - align) / 8 * 8)) :
    (dst + BitVec.ofNat 64 (len - align)) - BitVec.ofNat 64 ((len - align) / 8 * 8) =
      dst + BitVec.ofNat 64 ((len - align) % 8) := by
  bv_arith

-- let-bound locals are opaque atoms to `omega`; `bv_arith` adds `x = v` facts for them
theorem let1 (dst : BitVec 64) (len align : Nat) (_hd : dst.toNat + len < 2 ^ 64)
    (_ha : align ≤ len) :
    let words := (len - align) / 8
    let words_bytes := words * 8
    let rem := (len - align) % 8
    (dst + BitVec.ofNat 64 (len - align)) - BitVec.ofNat 64 words_bytes =
      dst + BitVec.ofNat 64 rem := by
  intro words words_bytes rem
  bv_arith

-- same with the `let` tactic, whose locals' types are still metavariables
theorem let2 (dst : BitVec 64) (len align : Nat) (_hd : dst.toNat + len < 2 ^ 64)
    (_h16 : 16 ≤ len) (_ha : align < 8) : True := by
  let words := (len - align) / 8
  let words_bytes := words * 8
  let rem := (len - align) % 8
  have _h : (dst + BitVec.ofNat 64 (len - align)) - BitVec.ofNat 64 words_bytes =
      dst + BitVec.ofNat 64 rem := by bv_arith
  have _h' : BitVec.ofNat 64 (len - align) + dst - 8#64 =
      dst + BitVec.ofNat 64 (rem + (words - 1) * 8) := by bv_arith
  trivial

-- sum-bound interval analysis: from `dst.toNat + len < 2^64` the `+`/`ofNat` node facts for
-- `dst + ofNat len` and `dst + ofNat (len - align)` are mod-free (summand facts, `canonSum`
-- congruence and sum monotonicity), so `omega` gets no `%` facts
theorem sumbound1 (dst : BitVec 64) (len align : Nat) (_hd : dst.toNat + len < 2 ^ 64)
    (_h16 : 16 ≤ len) (_ha : align < 8) :
    (dst + BitVec.ofNat 64 (len - align)).toNat = dst.toNat + len - align ∧
      (dst + BitVec.ofNat 64 len).toNat = dst.toNat + len := by
  bv_arith

-- `ofNat w (a - b)` is pushed out (`ofNat_sub_of_le`, side condition by `arithCore`), then
-- the linear normal form closes the goal: no wrapping facts for the unbounded `src`
theorem linsub1 (src : BitVec 64) (rem : Nat) (_h : 4 ≤ rem) (_h' : rem < 16) :
    (src + BitVec.ofNat 64 rem) - 4#64 = src + BitVec.ofNat 64 (rem - 4) := by bv_arith

-- nested: rewriting `ofNat (i - (rem - 4))` exposes `ofNat (rem - 4)` (second round)
theorem linsub2 (src : BitVec 64) (rem i : Nat) (_h : 4 ≤ rem) (_h' : rem - 4 ≤ i) :
    src + BitVec.ofNat 64 (rem - 4) + BitVec.ofNat 64 (i - (rem - 4)) = src + BitVec.ofNat 64 i := by
  bv_arith

-- `toInt` of a value bounded below `2^(w-1)`: the no-wrap equation, not the sign case split
theorem toint_nowrap (x : BitVec 64) (n : Nat) (_h : n < 2 ^ 63) (_hx : x.toNat < 100) :
    (BitVec.ofNat 64 n).slt 0#64 = false ∧ x.toInt < 100 := by bv_arith

-- relational no-wrap: `y.toNat ≤ (y <<< 4).toNat` from the shift node (`le_of_eq_mul`), so the
-- subtraction needs no wrapping fact
theorem sub_shl (y : BitVec 64) (_h : y.toNat < 2 ^ 32) : (y <<< 4 - y).toNat = y.toNat * 15 := by
  bv_arith

/-! ## `bv_solve` -/

theorem s_ground : (3#8 : BitVec 8) + 5#8 = 8#8 := by bv_solve
theorem s_lin (a : BitVec 64) : a + 8 + 16 - 8 = a + 16 := by bv_solve
theorem s_arith (x : BitVec 64) (h : x.toNat < 100) : x + 1#64 ≠ 0#64 := by bv_solve
theorem s_bits (x : BitVec 64) : x &&& ~~~x = 0#64 := by bv_solve
-- bit-level structure only in a hypothesis: routed to the kernel-only `bv_fallback` | `simp_all`
theorem s_bits_hyp (x y : BitVec 8) (h : x ^^^ y = 0#8) : x = y := by bv_solve

-- symbolic product in the goal: classified `unsupported`, fails immediately
/-- error: bv_solve [unsupported]: bv_solve: goal classified as unsupported; no solver is run for this class -/
#guard_msgs in
example (a b : BitVec 64) : (a + b) * (a - b) = a * a - b * b := by bv_solve

/-! ## `decideProp?` -/

/-- info: proved: a + 1#64 ≠ 0#64 -/
#guard_msgs in
example (a : BitVec 64) (_ : a < 16#64) : True := by
  decide_prop? a + 1#64 ≠ 0#64
  trivial

/-- info: refuted: a = 20#64 -/
#guard_msgs in
example (a : BitVec 64) (_ : a < 16#64) : True := by
  decide_prop? a = 20#64
  trivial

/-- info: undetermined: a = 3#64 -/
#guard_msgs in
example (a : BitVec 64) (_ : a < 16#64) : True := by
  decide_prop? a = 3#64
  trivial

/-! ## Pointer-offset and alignment lemmas -/

example (start : BitVec 64) (idx len : Nat) (hlt : idx < len) (hno : start.toNat + len < 2 ^ 64) :
    (start + BitVec.ofNat 64 idx == start + BitVec.ofNat 64 len) = false ∧
    (start + BitVec.ofNat 64 len == start + BitVec.ofNat 64 idx) = false :=
  ⟨BitVec.add_ofNat_beq_add_ofNat_false hlt hno,
   BitVec.add_ofNat_beq_add_ofNat_false_rev hlt hno⟩

example (bs : List UInt8) (hne : bs ≠ []) (hlt : bs.length < 2 ^ 64) :
    BitVec.ofNat 64 bs.length ≠ 0#64 :=
  BitVec.ofNat64_length_ne_zero hne hlt

example (x : BitVec 64) (i n : Nat) (hi : i < n) (hn : x.toNat + n < 2 ^ 64) :
    (x + BitVec.ofNat 64 n).ult x = false ∧
    (x + BitVec.ofNat 64 n).ule x = false ∧
    (x + BitVec.ofNat 64 i).ult (x + BitVec.ofNat 64 n) = true ∧
    (x + BitVec.ofNat 64 n).ule (x + BitVec.ofNat 64 i) = false :=
  ⟨BitVec.ult_self_add_ofNat_false hn,
   BitVec.ule_self_add_ofNat_false (by omega) hn,
   BitVec.add_ofNat_ult_add_ofNat hi hn,
   BitVec.add_ofNat_ule_add_ofNat_false hi hn⟩

example (a b : Nat) (hab : a < b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = true ∧
    (BitVec.ofNat 64 b).ult (BitVec.ofNat 64 a) = false ∧
    (BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = true ∧
    (BitVec.ofNat 64 b).ule (BitVec.ofNat 64 a) = false :=
  ⟨BitVec.ult_ofNat64_of_lt hab hb,
   BitVec.ult_ofNat64_of_ge (by omega) hb,
   BitVec.ule_ofNat64_of_le (by omega) hb,
   BitVec.ule_ofNat64_of_gt hab hb⟩

example (sp : BitVec 64) (x y : Nat) (hle : y ≤ x) :
    (sp + BitVec.ofNat 64 x) - (sp + BitVec.ofNat 64 y) = BitVec.ofNat 64 (x - y) ∧
    sp - BitVec.ofNat 64 x + BitVec.ofNat 64 y = sp - BitVec.ofNat 64 (x - y) ∧
    BitVec.ofNat 64 (x + y) - BitVec.ofNat 64 y = BitVec.ofNat 64 x ∧
    sp - BitVec.ofNat 64 x - BitVec.ofNat 64 y = sp - BitVec.ofNat 64 (x + y) :=
  ⟨BitVec.add_ofNat_sub_add_ofNat hle,
   BitVec.sub_ofNat_add_ofNat_of_le sp hle,
   BitVec.ofNat_add_sub_cancel x y,
   BitVec.sub_ofNat_sub_ofNat sp x y⟩

example (x : BitVec 64) (n : Nat) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& 7#64 = BitVec.ofNat 64 (n % 8) ∧
    BitVec.ofNat 64 n &&& 0xfffffffffffffff8#64 = BitVec.ofNat 64 (8 * (n / 8)) ∧
    BitVec.ofNat 64 n &&& 63#64 = BitVec.ofNat 64 (n % 64) ∧
    BitVec.ofNat 64 n >>> 6 = BitVec.ofNat 64 (n / 64) ∧
    x &&& (-8#64) = x - (x &&& 7#64) ∧
    (((x &&& 0xfffffffffffffff8#64) - 1#64) &&& 0xfffffffffffffff8#64) + 8#64 =
      x &&& 0xfffffffffffffff8#64 :=
  ⟨BitVec.ofNat64_and_7 hn,
   BitVec.ofNat64_and_mask8 hn,
   BitVec.ofNat64_and_63 n,
   BitVec.ofNat64_ushiftRight_6 hn,
   BitVec.and_neg8_eq_sub_and_7 x,
   BitVec.mask_align8_roundtrip x⟩

/-! ## Width-polymorphic power-of-two mask lemmas -/

example {w : Nat} (x : BitVec w) (n k : Nat) :
    (x &&& BitVec.ofNat w (2 ^ k - 1)).toNat = x.toNat % 2 ^ k ∧
    (BitVec.ofNat w (2 ^ k - 1) &&& x).toNat = x.toNat % 2 ^ k ∧
    x &&& BitVec.ofNat w (2 ^ k - 1) = x % BitVec.ofNat w (2 ^ k) ∧
    BitVec.ofNat w (2 ^ k - 1) &&& x = x % BitVec.ofNat w (2 ^ k) ∧
    x &&& BitVec.ofNat w (2 ^ k - 1) = BitVec.ofNat w (x.toNat % 2 ^ k) ∧
    BitVec.ofNat w n &&& BitVec.ofNat w (2 ^ k - 1) = BitVec.ofNat w (n % 2 ^ k) :=
  ⟨BitVec.toNat_and_twoPow_sub_one x k,
   BitVec.toNat_twoPow_sub_one_and x k,
   BitVec.and_twoPow_sub_one x k,
   BitVec.twoPow_sub_one_and x k,
   BitVec.and_twoPow_sub_one_eq_ofNat_mod x k,
   BitVec.ofNat_and_twoPow_sub_one n k⟩

example {w : Nat} (x : BitVec w) :
    (x &&& 1#w).toNat = x.toNat % 2 ∧
    (x &&& 3#w).toNat = x.toNat % 4 ∧
    (x &&& 7#w).toNat = x.toNat % 8 ∧
    (x &&& 15#w).toNat = x.toNat % 16 ∧
    (x &&& 31#w).toNat = x.toNat % 32 ∧
    (x &&& 63#w).toNat = x.toNat % 64 ∧
    (x &&& 255#w).toNat = x.toNat % 256 ∧
    (x &&& 511#w).toNat = x.toNat % 512 ∧
    (x &&& 4095#w).toNat = x.toNat % 4096 ∧
    (x &&& 65535#w).toNat = x.toNat % 65536 :=
  ⟨BitVec.toNat_and_1 x,
   BitVec.toNat_and_3 x,
   BitVec.toNat_and_7 x,
   BitVec.toNat_and_15 x,
   BitVec.toNat_and_31 x,
   BitVec.toNat_and_63 x,
   BitVec.toNat_and_255 x,
   BitVec.toNat_and_511 x,
   BitVec.toNat_and_4095 x,
   BitVec.toNat_and_65535 x⟩

example (x : BitVec 64) :
    (x &&& 511#64).toNat = x.toNat % 512 ∧
    x &&& 511#64 = x % 512#64 ∧
    x &&& 511#64 = BitVec.ofNat 64 (x.toNat % 512) ∧
    (x &&& 511#64).toNat ≤ x.toNat ∧
    (x &&& 511#64).toNat ≤ (511#64).toNat ∧
    (x &&& 511#64).toNat < 512 ∧
    (512#64 - (x &&& 511#64)).toNat = (512#64).toNat - (x &&& 511#64).toNat ∧
    (512#64 - (x &&& 511#64)).toNat = 512 - x.toNat % 512 ∧
    (0 < (512#64 - (x &&& 511#64)).toNat ∧ (512#64 - (x &&& 511#64)).toNat ≤ (512#64).toNat) ∧
    ((x &&& 511#64) + 1#64).toNat = (x &&& 511#64).toNat + 1 ∧
    (512#64).ult ((x &&& 511#64) + 1#64) = false :=
  ⟨BitVec.toNat_and_eq_mod x 511#64 512,
   BitVec.and_eq_umod_of_add_one x 511#64 512#64,
   BitVec.and_eq_ofNat_mod x 511#64 512,
   BitVec.toNat_and_le_left x 511#64,
   BitVec.toNat_and_le_right x 511#64,
   BitVec.toNat_and_lt_of_add_one x 511#64 (p := 512),
   BitVec.toNat_sub_and_of_le x 511#64 512#64,
   BitVec.toNat_twoPow_sub_and x 511#64 512#64 512,
   BitVec.sub_and_pos_le_of_lt x 511#64 512#64,
   BitVec.toNat_and_add_one_of_lt x 511#64,
   BitVec.ult_and_add_one_eq_false x 511#64 512#64⟩

example (x : BitVec 64) (k : Nat) :
    (x &&& BitVec.ofNat 64 (2 ^ k - 1) = 0#64 ↔ x.toNat % 2 ^ k = 0) ∧
    (x &&& 511#64 = 0#64 ↔ x.toNat % 512 = 0) ∧
    (((x &&& 511#64 == 0#64) = true) ↔ x.toNat % 512 = 0) ∧
    x &&& ~~~511#64 = x - (x &&& 511#64) ∧
    x &&& (-512#64) = x - (x &&& 511#64) ∧
    (x &&& ~~~511#64).toNat = x.toNat - (x &&& 511#64).toNat ∧
    (x &&& (-512#64)).toNat = x.toNat / 512 * 512 ∧
    (x &&& 0xfffffffffffff000#64).toNat = x.toNat / 4096 * 4096 :=
  ⟨BitVec.and_twoPow_sub_one_eq_zero_iff x k,
   BitVec.and_eq_zero_iff_mod_eq_zero x 511#64 512,
   BitVec.beq_and_zero_eq_true_iff_mod_eq_zero x 511#64 512,
   BitVec.and_not_eq_sub_and x 511#64,
   BitVec.and_compl_eq_sub_and x (-512#64) 511#64,
   BitVec.toNat_and_not x 511#64,
   BitVec.toNat_and_compl_eq_div_mul x (-512#64) 511#64 512,
   ProofLib.BV.Arith.toNat_and_compl_eq_div_mul x 0xfffffffffffff000#64 4095#64 4096⟩

-- MaskLemmas are deliberately excluded from @[simp], @[wp_norm], and @[arm64_norm].
/-- error: `simp` made no progress -/
#guard_msgs in
example (x : BitVec 64) : (x &&& 511#64).toNat = x.toNat % 512 := by
  simp only [wp_norm, arm64_norm]

-- Non-power-of-two masks (e.g. `6#64`, where `6 + 1 = 7 ≠ 2 ^ k`) are rejected.
#guard_msgs (drop error) in
example (x : BitVec 64) : (x &&& 6#64).toNat = x.toNat % 7 :=
  BitVec.toNat_and_eq_mod x 6#64 7

end ProofLib.BV.ArithTests
