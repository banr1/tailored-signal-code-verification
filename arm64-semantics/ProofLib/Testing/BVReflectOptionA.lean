/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.BV.ReflectROBDD
public import ProofLib.BV.Linear
public import Arm64.Trusted.ISA.Eval

/-!
# Benchmark and Regression Suite for `bv_slice` and `bv_robdd`

Tests and benchmarks `bv_slice` and `bv_robdd` across bitfield/slice/varint identities, mixed
bitwise-arithmetic and `AddWithCarry64`/`ConditionHolds` equivalences, multi-hypothesis and
power-of-two multiplication goals, `#guard_msgs` error diagnostics, and `#print axioms` checks.
-/

@[expose] public section

namespace Testing.BVReflectOptionA

open Arm64

/-! ## Benchmark Measurement Command -/

public meta section
open Lean Elab Command Meta

/-- Elaborate a command, recording wall-clock milliseconds and kernel/elaborator heartbeats. -/
elab "#bench_bv " label:str cmd:command : command => do
  let hb0 ← IO.getNumHeartbeats
  let t0 ← IO.monoNanosNow
  elabCommand cmd
  let t1 ← IO.monoNanosNow
  let hb1 ← IO.getNumHeartbeats
  let ms := (t1 - t0).toFloat / 1000000.0
  let dHb := (hb1 - hb0) / 1000
  logInfo m!"[BENCH] {label.getString}: {ms} ms, {dHb}k heartbeats"

end

/-! ## Bitfield, Slice, Shift, Mask, and Varint Identities -/

theorem s1_01_extract_append_lo (hi lo : BitVec 32) :
    BitVec.extractLsb' 0 32 (hi ++ lo) = lo := by
  bv_slice

theorem s1_01_extract_append_lo_robdd (hi lo : BitVec 32) :
    BitVec.extractLsb' 0 32 (hi ++ lo) = lo := by
  bv_robdd

theorem s1_02_extract_append_hi (hi lo : BitVec 32) :
    BitVec.extractLsb' 32 32 (hi ++ lo) = hi := by
  bv_slice

theorem s1_03_byte_pack_unpack_32 (x : BitVec 32) :
    BitVec.extractLsb' 24 8 x ++
    BitVec.extractLsb' 16 8 x ++
    BitVec.extractLsb' 8 8 x ++
    BitVec.extractLsb' 0 8 x = x := by
  bv_slice

theorem s1_04_byte_shift_or_eq_append (b3 b2 b1 b0 : BitVec 8) :
    (BitVec.zeroExtend 32 b0) |||
    ((BitVec.zeroExtend 32 b1) <<< 8) |||
    ((BitVec.zeroExtend 32 b2) <<< 16) |||
    ((BitVec.zeroExtend 32 b3) <<< 24) =
    b3 ++ b2 ++ b1 ++ b0 := by
  bv_slice

theorem s1_05_zeroExtend_extract_roundtrip (x : BitVec 32) :
    BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64 x) = x := by
  bv_slice

theorem s1_06_signExtend_msb (x : BitVec 32) :
    (BitVec.signExtend 64 x).getLsbD 63 = x.msb := by
  bv_slice

theorem s1_07_signExtend_extract_lo (x : BitVec 32) :
    BitVec.extractLsb' 0 32 (BitVec.signExtend 64 x) = x := by
  bv_slice

theorem s1_08_varint_2byte_lo (b0 b1 : BitVec 64) :
    (((b0 &&& 0x7f#64) ||| ((b1 &&& 0x7f#64) <<< 7)) &&& 0x7f#64) = (b0 &&& 0x7f#64) := by
  bv_slice

theorem s1_09_varint_2byte_hi (b0 b1 : BitVec 64) :
    ((((b0 &&& 0x7f#64) ||| ((b1 &&& 0x7f#64) <<< 7)) >>> 7) &&& 0x7f#64) = (b1 &&& 0x7f#64) := by
  bv_slice

theorem s1_10_varint_3byte_extract (b0 b1 b2 : BitVec 64) :
    (((((b0 &&& 0x7f#64) ||| ((b1 &&& 0x7f#64) <<< 7)) ||| ((b2 &&& 0x7f#64) <<< 14)) >>> 14) &&& 0x7f#64) =
      (b2 &&& 0x7f#64) := by
  bv_slice

theorem s1_11_varint_5byte_horner_eq_flat (b0 b1 b2 b3 b4 : BitVec 64) :
    (b0 &&& 0x7f#64) |||
      (((b1 &&& 0x7f#64) |||
        (((b2 &&& 0x7f#64) |||
          (((b3 &&& 0x7f#64) |||
            ((b4 &&& 0x7f#64) <<< 7)) <<< 7)) <<< 7)) <<< 7) =
    (b0 &&& 0x7f#64) |||
      ((b1 &&& 0x7f#64) <<< 7) |||
      ((b2 &&& 0x7f#64) <<< 14) |||
      ((b3 &&& 0x7f#64) <<< 21) |||
      ((b4 &&& 0x7f#64) <<< 28) := by
  bv_slice

theorem s1_12_sshiftRight_sign_mask (x : BitVec 64) :
    BitVec.sshiftRight x 63 = (if x.msb then 0xffffffffffffffff#64 else 0#64) := by
  bv_slice

theorem s1_13_replicate_and_xor_cancel (x y : BitVec 16) :
    BitVec.extractLsb' 16 16 (BitVec.replicate 4 ((x ^^^ y) ^^^ y)) = x ∧
    ~~~(x &&& y) = (~~~x ||| ~~~y) := by
  bv_slice

/-! ## Mixed Arithmetic, Bitwise Operations, and `AddWithCarry64` -/

theorem s2_14_align8_mask_eq_sub (x : BitVec 64) :
    x &&& (-8#64) = x - (x &&& 7#64) := by
  bv_robdd

theorem s2_15_xor_eq_or_sub_and (x y : BitVec 64) :
    x ^^^ y = (x ||| y) - (x &&& y) := by
  bv_robdd

theorem s2_16_add_eq_or_add_and (x y : BitVec 64) :
    x + y = (x ||| y) + (x &&& y) := by
  bv_robdd

theorem s2_17_add_eq_xor_add_carry (x y : BitVec 64) :
    x + y = (x ^^^ y) + ((x &&& y) <<< 1) := by
  bv_robdd

theorem s2_18_add_sub_cancel (x y : BitVec 64) :
    (x + y) - y = x := by
  bv_robdd

theorem s2_19_clear_lowest_bit_ule (r : BitVec 64) :
    (r - 1#64) &&& r ≤ r := by
  bv_robdd

theorem s2_20_neg_eq_not_add_one (x : BitVec 64) :
    -x = ~~~x + 1#64 := by
  bv_robdd

theorem s2_21_sub_eq_add_not_add_one (x y : BitVec 64) :
    x - y = x + ~~~y + 1#64 := by
  bv_robdd

theorem s2_22_not_ule_or_imp_lt (u v : BitVec 64) :
    ¬(64#64).ule (v ||| u) → u < 64#64 ∧ v < 64#64 := by
  bv_robdd

theorem s2_23_addWithCarry64_sub_fst (x y : BitVec 64) :
    (AddWithCarry64 x (~~~y) true).1 = x - y := by
  bv_robdd

theorem s2_24_addWithCarry64_add_fst (x y : BitVec 64) :
    (AddWithCarry64 x y false).1 = x + y := by
  bv_robdd

theorem s2_25_addWithCarry64_n_false (x y : BitVec 64) :
    (AddWithCarry64 x y false).2.n = (x + y).getLsbD 63 := by
  bv_robdd

theorem s2_26_conditionHolds_eq_subs64 (x y : BitVec 64) :
    ConditionHolds .EQ (AddWithCarry64 x (~~~y) true).2 = (x == y) := by
  bv_robdd

theorem s2_27_conditionHolds_cs_subs64 (x y : BitVec 64) :
    ConditionHolds .CS (AddWithCarry64 x (~~~y) true).2 = BitVec.ule y x := by
  bv_robdd

theorem s2_28_conditionHolds_cc_subs64 (x y : BitVec 64) :
    ConditionHolds .CC (AddWithCarry64 x (~~~y) true).2 = BitVec.ult x y := by
  bv_robdd

theorem s2_29_conditionHolds_hi_subs64 (x y : BitVec 64) :
    ConditionHolds .HI (AddWithCarry64 x (~~~y) true).2 = BitVec.ult y x := by
  bv_robdd

theorem s2_30_conditionHolds_ls_subs64 (x y : BitVec 64) :
    ConditionHolds .LS (AddWithCarry64 x (~~~y) true).2 = BitVec.ule x y := by
  bv_robdd

theorem s2_31_conditionHolds_ge_subs64 (x y : BitVec 64) :
    ConditionHolds .GE (AddWithCarry64 x (~~~y) true).2 = BitVec.sle y x := by
  bv_robdd

theorem s2_32_conditionHolds_lt_subs64 (x y : BitVec 64) :
    ConditionHolds .LT (AddWithCarry64 x (~~~y) true).2 = BitVec.slt x y := by
  bv_robdd

theorem s2_33_conditionHolds_gt_subs64 (x y : BitVec 64) :
    ConditionHolds .GT (AddWithCarry64 x (~~~y) true).2 = BitVec.slt y x := by
  bv_robdd

theorem s2_34_conditionHolds_le_subs64 (x y : BitVec 64) :
    ConditionHolds .LE (AddWithCarry64 x (~~~y) true).2 = BitVec.sle x y := by
  bv_robdd

/-! ## Propositional and Branch-Classification Hypotheses -/

theorem s3_35_aligned_ptr_offset_roundtrip (x off : BitVec 64)
    (h1 : x &&& 7#64 = 0#64) (h2 : off < 8#64) :
    (x + off) &&& (-8#64) = x ∧ (x + off) &&& 7#64 = off := by
  bv_robdd

theorem s3_36_page_bound_and_alignment (x y : BitVec 64)
    (h1 : x &&& 7#64 = 0#64) (h2 : x < 4096#64) (h3 : y &&& 7#64 = 0#64) :
    (x + y) &&& 7#64 = 0#64 ∧ x ≤ 4088#64 := by
  bv_robdd

theorem s3_37_tagged_pointer_roundtrip (ptr tag : BitVec 64)
    (h1 : ptr &&& 7#64 = 0#64) (h2 : tag < 8#64) (h3 : tag ≠ 0#64) :
    (ptr ||| tag) ≠ ptr ∧
    ((ptr ||| tag) &&& 7#64) = tag ∧
    ((ptr ||| tag) &&& (-8#64)) = ptr := by
  bv_robdd

theorem s3_38_four_hyp_range_parity (x y : BitVec 64)
    (h1 : x < 256#64) (h2 : y < 256#64)
    (h3 : x &&& 1#64 = 0#64) (h4 : y &&& 1#64 = 1#64) :
    (x ||| y) < 256#64 ∧ (x ^^^ y) ≠ 0#64 ∧ ((x + y) &&& 1#64) = 1#64 := by
  bv_robdd

theorem s3_39_slt_imp_ult_of_nonneg (x y : BitVec 64)
    (hx : x.msb = false) (hy : y.msb = false) (hlt : BitVec.slt x y = true) :
    x < y := by
  bv_robdd

theorem s3_40_uninterpreted_mul_abstraction (x y z : BitVec 64) :
    ((x * y) + z) - z = x * y ∧
    ((x * y) &&& (-8#64)) + ((x * y) &&& 7#64) = x * y := by
  bv_robdd

/-! ## Multiplication by Power-of-Two Literals -/

theorem s3b_41_mul4_add1_low_bit (w : BitVec 32) :
    ((w <<< 4 - w) * 4#32 + 1#32).extractLsb' 0 1 = 1#1 := by
  bv_robdd

theorem s3b_42_mul4_or1_low_bits (w : BitVec 32) :
    ((w <<< 4 ^^^ w) * 4#32 ||| 1#32).extractLsb' 0 2 = 1#2 := by
  bv_slice

theorem s3b_43_mul8_left_and7 (x : BitVec 64) : (8#64 * x) &&& 7#64 = 0#64 := by
  bv_slice

theorem s3b_44_mul16_ofNat_and15 (x : BitVec 64) : (x * (16 : BitVec 64)) &&& 15 = 0 := by
  bv_slice

theorem s3b_45_mul2_eq_shl (x : BitVec 16) : x * 2#16 = x <<< 1 := by
  bv_slice

theorem s3b_46_mul32_hyp (x : BitVec 8) (h : x * 32#8 = 0#8) (h2 : 64#8 * x ≠ 0#8) :
    x &&& 1#8 = 0#8 ∧ x.getLsbD 1 = true := by
  bv_slice

theorem s3b_47_mul2_left_eq_add (x : BitVec 8) : 2#8 * x = x + x := by
  bv_robdd

/-! ## Negative `#guard_msgs` Diagnostics and Axiom Checks -/

/--
error: bv_slice: operator '+' requires ripple-carry reasoning and is outside the Tier 1 pure bit-slice grammar; use 'bv_robdd' instead
-/
#guard_msgs in
example (x y : BitVec 64) : x + y = y + x := by
  bv_slice

/--
error: bv_robdd failed: goal is not a tautology (ROBDD reduced to node 3 ≠ 1)
counterexample witness: x = 0x0#8
hint: if these atoms are constrained by local hypotheses, rewrite or substitute them before calling `bv_robdd` / `bv_slice`, or use `bv_solve`
-/
#guard_msgs in
example (x : BitVec 8) : (x &&& 1#8) = 1#8 := by
  bv_robdd

/--
error: bv_slice failed: goal is not a bit-slice tautology
counterexample witness: x = 0x0#8
hint: if these atoms are constrained by local hypotheses, rewrite or substitute them before calling `bv_robdd` / `bv_slice`, or use `bv_solve`
-/
#guard_msgs in
example (x : BitVec 8) : (x &&& 1#8) = 1#8 := by
  bv_slice

-- Non-power-of-two multipliers are still abstracted as opaque atoms.
/--
error: bv_robdd failed: goal is not a tautology (ROBDD reduced to node 204 ≠ 1)
Note: unsupported subterms were abstracted as atomic variables: '* (BitVec multiplication)' in (x * 3#8)
counterexample witness: x * 3#8 = 0x1#8, x = 0x0#8
hint: if these atoms are constrained by local hypotheses, rewrite or substitute them before calling `bv_robdd` / `bv_slice`, or use `bv_solve`
-/
#guard_msgs in
example (x : BitVec 8) : x * 3#8 = x + x + x := by
  bv_robdd

-- After the pre-pass, the only remaining obstacle in `bv_slice` is the ripple-carry `+`.
/--
error: bv_slice: operator '+' requires ripple-carry reasoning and is outside the Tier 1 pure bit-slice grammar; use 'bv_robdd' instead
-/
#guard_msgs in
example (w : BitVec 32) : ((w <<< 4 - w) * 4#32 + 1#32).extractLsb' 0 1 = 1#1 := by
  bv_slice

/-- info: 'Testing.BVReflectOptionA.s3b_41_mul4_add1_low_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s3b_41_mul4_add1_low_bit

/-- info: 'Testing.BVReflectOptionA.s3b_44_mul16_ofNat_and15' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s3b_44_mul16_ofNat_and15

/-- info: 'Testing.BVReflectOptionA.s1_11_varint_5byte_horner_eq_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s1_11_varint_5byte_horner_eq_flat

/-- info: 'Testing.BVReflectOptionA.s2_14_align8_mask_eq_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2_14_align8_mask_eq_sub

/-- info: 'Testing.BVReflectOptionA.s2_19_clear_lowest_bit_ule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2_19_clear_lowest_bit_ule

/-- info: 'Testing.BVReflectOptionA.s2_22_not_ule_or_imp_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2_22_not_ule_or_imp_lt

/-- info: 'Testing.BVReflectOptionA.s2_27_conditionHolds_cs_subs64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2_27_conditionHolds_cs_subs64

/-- info: 'Testing.BVReflectOptionA.s2_33_conditionHolds_gt_subs64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2_33_conditionHolds_gt_subs64

/-- info: 'Testing.BVReflectOptionA.s3_35_aligned_ptr_offset_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s3_35_aligned_ptr_offset_roundtrip

/-- info: 'Testing.BVReflectOptionA.s3_38_four_hyp_range_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s3_38_four_hyp_range_parity

/--
info: 'Testing.BVReflectOptionA.s3_40_uninterpreted_mul_abstraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms s3_40_uninterpreted_mul_abstraction

/-! ## `bv_lin` Local Equality Rewriting and `bv_auto` Fallback -/

theorem s5_bv_lin_local_offset_eq (x y : BitVec 64) (h : x = y + 8#64) :
    x + 16#64 = y + 24#64 := by
  bv_lin

theorem s5_bv_lin_mask_atom_eq (a b : BitVec 64) (hb : b &&& 0xfff#64 = 0#64) :
    (b &&& 0xfff#64) + a + 8#64 = a + 8#64 := by
  bv_lin

theorem s5_bv_lin_explicit_hyps (x y : BitVec 64) (h : x = y + 8#64) :
    x + 16#64 = y + 24#64 := by
  set_option proofLib.bvLinAutoHyps false in
  bv_lin [h]

theorem s5_bv_auto_page_mask (x y : BitVec 64) (h : x = y + 8#64) (hy : y.toNat + 8 < 2 ^ 64) :
    y ≤ x := by
  bv_auto

end Testing.BVReflectOptionA
