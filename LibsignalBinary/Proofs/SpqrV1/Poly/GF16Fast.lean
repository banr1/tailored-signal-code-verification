/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly

/-!
# Fast Verified `GF(2^16)` Multiplication and Lagrange Basis Evaluation

**Checked by Lean.**

Kernel-friendly `Nat`-primitive evaluators for `GF16.mul`, `GF16.constMul`, `GF16.constDiv`,
`PolyConst.lagrangeInterpolatePt`, and `lagrangePolysForCompletePoints`
(`COMPLETE_POINTS_POLYS_{30,34,36}`).

Equivalence `∀ a b : BitVec 16, unaccelerated.mul a b = mulFastBV a b` is established via
$\mathbb{F}_2$-bilinearity in both arguments together with a closed `decide +kernel` check on the
$16 \times 16 = 256$ basis pairs `(1#16 <<< i, 1#16 <<< j)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Poly.GF16Fast

open CryptoVerification.LibsignalSpqrV1

/-! ## 1. Fast `Nat`-Primitive `GF(2^16)` Evaluator -/

/-- Unconditional 1-bit carryless multiply loop on `Nat` (for bilinearity proofs). -/
def clmulNoShort : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, a, b, acc =>
    let acc' :=
      match b.testBit 0 with
      | true => acc ^^^ a
      | false => acc
    clmulNoShort fuel (a <<< 1) (b >>> 1) acc'

/-- Short-circuiting carryless multiply loop on `Nat` (terminates as soon as `Nat.beq b 0` is `true`,
    building zero `Decidable` proof terms in the kernel). -/
def clmulLoopNat : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, a, b, acc =>
    match Nat.beq b 0 with
    | true => acc
    | false =>
      let acc' :=
        match b.testBit 0 with
        | true => acc ^^^ a
        | false => acc
      clmulLoopNat fuel (a <<< 1) (b >>> 1) acc'

/-- One degree-folding step modulo $x^{16} + x^{12} + x^3 + x + 1$ (`65536 + 4107 = 69643`),
    using only `Nat` C++ kernel primitives (`&&&`, `>>>`, `<<<`, `^^^`). -/
def reduceStepNat (v : Nat) : Nat :=
  let lo := v &&& 65535
  let hi := v >>> 16
  lo ^^^ (hi <<< 12) ^^^ (hi <<< 3) ^^^ (hi <<< 1) ^^^ hi

/-- Four-fold degree reduction from $\deg \le 31$ down to $\deg \le 15$. -/
def reduceFastNat (v : Nat) : Nat :=
  reduceStepNat (reduceStepNat (reduceStepNat (reduceStepNat v)))

/-- Fast `Nat` evaluator for $\mathrm{GF}(2^{16})$ multiplication on `u16` representatives. -/
def mulFastNat (a b : Nat) : Nat :=
  reduceFastNat (clmulLoopNat 16 a b 0)

/-- Fast `BitVec 16` evaluator for `unaccelerated.mul`. -/
def mulFastBV (a b : BitVec 16) : BitVec 16 :=
  BitVec.ofNat 16 (mulFastNat a.toNat b.toNat)

/-- Fast `GF16` multiplication equivalent to `GF16.mul` and `GF16.constMul`. -/
def mulFast (a b : GF16) : GF16 :=
  ⟨mulFastBV a.value b.value⟩

/-! ## 2. Bitwise XOR Linearity of `mulFastBV` -/

private theorem nat_xor_self (x : Nat) : x ^^^ x = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.zero_testBit]
  cases x.testBit i <;> rfl

private theorem nat_xor_zero (x : Nat) : x ^^^ 0 = x := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.zero_testBit]
  cases x.testBit i <;> rfl

private theorem nat_xor_assoc (x y z : Nat) : (x ^^^ y) ^^^ z = x ^^^ (y ^^^ z) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor, Bool.xor_assoc]

private theorem nat_xor_right_comm (x y z : Nat) : (x ^^^ y) ^^^ z = (x ^^^ z) ^^^ y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor]
  cases x.testBit i <;> cases y.testBit i <;> cases z.testBit i <;> rfl

private theorem nat_xor4_interchange (a b c d : Nat) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> cases d.testBit i <;> rfl

private theorem nat_xor_cancel_both (x y a : Nat) : (x ^^^ a) ^^^ (y ^^^ a) = x ^^^ y := by
  rw [nat_xor4_interchange, nat_xor_self, nat_xor_zero]

private theorem nat_and_xor (x y m : Nat) : (x ^^^ y) &&& m = (x &&& m) ^^^ (y &&& m) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_xor]
  cases x.testBit i <;> cases y.testBit i <;> cases m.testBit i <;> rfl

private theorem nat_shiftRight_xor (x y k : Nat) : (x ^^^ y) >>> k = (x >>> k) ^^^ (y >>> k) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_shiftRight, Nat.testBit_xor]

private theorem nat_shiftLeft_xor (x y k : Nat) : (x ^^^ y) <<< k = (x <<< k) ^^^ (y <<< k) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_shiftLeft, Nat.testBit_xor]
  cases decide (i ≥ k) <;> cases x.testBit (i - k) <;> cases y.testBit (i - k) <;> rfl

private theorem clmulNoShort_zero_right :
    ∀ (fuel a acc : Nat), clmulNoShort fuel a 0 acc = acc
  | 0, _, _ => rfl
  | fuel + 1, a, acc => clmulNoShort_zero_right fuel (a <<< 1) acc

private theorem clmulLoopNat_eq_noShort :
    ∀ (fuel a b acc : Nat), clmulLoopNat fuel a b acc = clmulNoShort fuel a b acc
  | 0, _, _, _ => rfl
  | fuel + 1, a, b, acc => by
    dsimp only [clmulLoopNat, clmulNoShort]
    cases hbeq : Nat.beq b 0
    · exact clmulLoopNat_eq_noShort fuel (a <<< 1) (b >>> 1) _
    · have hb : b = 0 := Nat.eq_of_beq_eq_true hbeq
      subst hb
      exact (clmulNoShort_zero_right fuel (a <<< 1) acc).symm

private theorem clmulNoShort_zero_left :
    ∀ (fuel b : Nat), clmulNoShort fuel 0 b 0 = 0
  | 0, _ => rfl
  | fuel + 1, b => by
    dsimp only [clmulNoShort]
    cases b.testBit 0 <;> exact clmulNoShort_zero_left fuel (b >>> 1)

private theorem clmulNoShort_xor_left :
    ∀ (fuel a1 a2 b acc1 acc2 : Nat),
      clmulNoShort fuel (a1 ^^^ a2) b (acc1 ^^^ acc2) =
        clmulNoShort fuel a1 b acc1 ^^^ clmulNoShort fuel a2 b acc2
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, a1, a2, b, acc1, acc2 => by
    dsimp only [clmulNoShort]
    rw [nat_shiftLeft_xor]
    cases b.testBit 0
    · exact clmulNoShort_xor_left fuel (a1 <<< 1) (a2 <<< 1) (b >>> 1) acc1 acc2
    · rw [nat_xor4_interchange]
      exact clmulNoShort_xor_left fuel (a1 <<< 1) (a2 <<< 1) (b >>> 1) (acc1 ^^^ a1) (acc2 ^^^ a2)

private theorem clmulNoShort_xor_right :
    ∀ (fuel a b1 b2 acc1 acc2 : Nat),
      clmulNoShort fuel a (b1 ^^^ b2) (acc1 ^^^ acc2) =
        clmulNoShort fuel a b1 acc1 ^^^ clmulNoShort fuel a b2 acc2
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, a, b1, b2, acc1, acc2 => by
    dsimp only [clmulNoShort]
    rw [Nat.testBit_xor, nat_shiftRight_xor]
    cases b1.testBit 0 <;> cases b2.testBit 0
    · exact clmulNoShort_xor_right fuel (a <<< 1) (b1 >>> 1) (b2 >>> 1) acc1 acc2
    · rw [nat_xor_assoc]
      exact clmulNoShort_xor_right fuel (a <<< 1) (b1 >>> 1) (b2 >>> 1) acc1 (acc2 ^^^ a)
    · rw [nat_xor_right_comm]
      exact clmulNoShort_xor_right fuel (a <<< 1) (b1 >>> 1) (b2 >>> 1) (acc1 ^^^ a) acc2
    · dsimp
      rw [← nat_xor_cancel_both acc1 acc2 a]
      exact clmulNoShort_xor_right fuel (a <<< 1) (b1 >>> 1) (b2 >>> 1) (acc1 ^^^ a) (acc2 ^^^ a)

private theorem bool_xor_interchange (u v c d : Bool) :
    ((u ^^ v) ^^ (c ^^ d)) = ((u ^^ c) ^^ (v ^^ d)) := by
  cases u <;> cases v <;> cases c <;> cases d <;> rfl

private theorem reduceStepNat_xor (x y : Nat) :
    reduceStepNat (x ^^^ y) = reduceStepNat x ^^^ reduceStepNat y := by
  dsimp only [reduceStepNat]
  simp only [nat_and_xor, nat_shiftRight_xor, nat_shiftLeft_xor]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor]
  rw [bool_xor_interchange ((x &&& 65535).testBit i) ((y &&& 65535).testBit i),
      bool_xor_interchange _ _ (((x >>> 16) <<< 3).testBit i) (((y >>> 16) <<< 3).testBit i),
      bool_xor_interchange _ _ (((x >>> 16) <<< 1).testBit i) (((y >>> 16) <<< 1).testBit i),
      bool_xor_interchange _ _ ((x >>> 16).testBit i) ((y >>> 16).testBit i)]

private theorem reduceFastNat_xor (x y : Nat) :
    reduceFastNat (x ^^^ y) = reduceFastNat x ^^^ reduceFastNat y := by
  unfold reduceFastNat
  simp only [reduceStepNat_xor]

private theorem mulFastNat_zero_left (b : Nat) : mulFastNat 0 b = 0 := by
  unfold mulFastNat
  rw [clmulLoopNat_eq_noShort, clmulNoShort_zero_left]
  rfl

private theorem mulFastNat_zero_right (a : Nat) : mulFastNat a 0 = 0 := by
  unfold mulFastNat
  rw [clmulLoopNat_eq_noShort, clmulNoShort_zero_right]
  rfl

private theorem mulFastNat_xor_left (a1 a2 b : Nat) :
    mulFastNat (a1 ^^^ a2) b = mulFastNat a1 b ^^^ mulFastNat a2 b := by
  unfold mulFastNat
  rw [clmulLoopNat_eq_noShort, clmulLoopNat_eq_noShort, clmulLoopNat_eq_noShort]
  have h := clmulNoShort_xor_left 16 a1 a2 b 0 0
  change clmulNoShort 16 (a1 ^^^ a2) b 0 = _ at h
  rw [h, reduceFastNat_xor]

private theorem mulFastNat_xor_right (a b1 b2 : Nat) :
    mulFastNat a (b1 ^^^ b2) = mulFastNat a b1 ^^^ mulFastNat a b2 := by
  unfold mulFastNat
  rw [clmulLoopNat_eq_noShort, clmulLoopNat_eq_noShort, clmulLoopNat_eq_noShort]
  have h := clmulNoShort_xor_right 16 a b1 b2 0 0
  change clmulNoShort 16 a (b1 ^^^ b2) 0 = _ at h
  rw [h, reduceFastNat_xor]

private theorem bv16_ofNat_xor (x y : Nat) :
    BitVec.ofNat 16 (x ^^^ y) = BitVec.ofNat 16 x ^^^ BitVec.ofNat 16 y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
    Nat.testBit_xor]

private theorem mulFastBV_zero_left (b : BitVec 16) : mulFastBV 0#16 b = 0#16 := by
  unfold mulFastBV
  have hz : (0#16 : BitVec 16).toNat = 0 := rfl
  rw [hz, mulFastNat_zero_left]

private theorem mulFastBV_zero_right (a : BitVec 16) : mulFastBV a 0#16 = 0#16 := by
  unfold mulFastBV
  have hz : (0#16 : BitVec 16).toNat = 0 := rfl
  rw [hz, mulFastNat_zero_right]

private theorem mulFastBV_xor_left (a1 a2 b : BitVec 16) :
    mulFastBV (a1 ^^^ a2) b = mulFastBV a1 b ^^^ mulFastBV a2 b := by
  unfold mulFastBV
  rw [BitVec.toNat_xor, mulFastNat_xor_left, bv16_ofNat_xor]

private theorem mulFastBV_xor_right (a b1 b2 : BitVec 16) :
    mulFastBV a (b1 ^^^ b2) = mulFastBV a b1 ^^^ mulFastBV a b2 := by
  unfold mulFastBV
  rw [BitVec.toNat_xor, mulFastNat_xor_right, bv16_ofNat_xor]

/-! ## 3. Bitwise XOR Linearity of `unaccelerated.mul` -/

private theorem bv_xor4_interchange {w : Nat} (a b c d : BitVec w) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> cases d.getLsbD i <;> rfl

private theorem bv_xor_assoc_local {w : Nat} (a b c : BitVec w) :
    (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor, Bool.xor_assoc]

private theorem bv_xor_right_comm_local {w : Nat} (a b c : BitVec w) :
    (a ^^^ b) ^^^ c = (a ^^^ c) ^^^ b := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

private theorem bv_xor_cancel_both {w : Nat} (a b m : BitVec w) :
    (a ^^^ m) ^^^ (b ^^^ m) = a ^^^ b := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases m.getLsbD i <;> rfl

private theorem bv_shiftLeft_xor {w : Nat} (a b : BitVec w) (k : Nat) :
    (a ^^^ b) <<< k = (a <<< k) ^^^ (b <<< k) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_xor]
  cases decide (i < w) <;> cases decide (i < k) <;>
    cases a.getLsbD (i - k) <;> cases b.getLsbD (i - k) <;> rfl

private theorem bv_ushiftRight_xor {w : Nat} (a b : BitVec w) (k : Nat) :
    (a ^^^ b) >>> k = (a >>> k) ^^^ (b >>> k) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]

private theorem bv_setWidth_xor {w v : Nat} (a b : BitVec w) :
    (a ^^^ b).setWidth v = a.setWidth v ^^^ b.setWidth v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, BitVec.getLsbD_xor]

private theorem bv_zeroExtend_xor {w v : Nat} (a b : BitVec w) :
    (a ^^^ b).zeroExtend v = a.zeroExtend v ^^^ b.zeroExtend v :=
  bv_setWidth_xor a b

private theorem bv_truncate_xor {w v : Nat} (a b : BitVec w) :
    (a ^^^ b).truncate v = a.truncate v ^^^ b.truncate v :=
  bv_setWidth_xor a b

private theorem one_shiftLeft_getLsbD {w : Nat} {k j : Nat} (hk : k < w) (hj : j < w) :
    (1#w <<< k).getLsbD j = decide (j = k) := by
  have hw0 : 0 < w := Nat.zero_lt_of_lt hk
  simp only [BitVec.getLsbD_shiftLeft, hj, decide_true, Bool.true_and]
  by_cases hlt : j < k
  · have hne : j ≠ k := Nat.ne_of_lt hlt
    simp only [hlt, decide_true, Bool.not_true, Bool.false_and, hne, decide_false]
  · have hge : k ≤ j := Nat.le_of_not_lt hlt
    simp only [hlt, decide_false, Bool.not_false, Bool.true_and]
    by_cases heq : j = k
    · subst heq
      simp only [Nat.sub_self, BitVec.getLsbD_one, hw0, decide_true, Bool.and_self]
    · have hpos : 0 < j - k := Nat.sub_pos_of_lt (Nat.lt_of_le_of_ne hge (Ne.symm heq))
      have hne0 : j - k ≠ 0 := Nat.ne_of_gt hpos
      simp only [BitVec.getLsbD_one, hne0, decide_false, Bool.and_false, heq]

private theorem mask16_test_eq_getLsbD (b : BitVec 16) {k : Nat} (hk : k < 16) :
    (0#16 != (b &&& (1#16 <<< k))) = b.getLsbD k := by
  cases hbit : b.getLsbD k
  · suffices h0 : b &&& (1#16 <<< k) = 0#16 by rw [h0]; rfl
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [BitVec.getLsbD_and, one_shiftLeft_getLsbD hk hj, BitVec.getLsbD_zero]
    by_cases hjk : j = k
    · subst hjk; simp only [hbit, Bool.false_and]
    · simp only [hjk, decide_false, Bool.and_false]
  · suffices hne : 0#16 ≠ b &&& (1#16 <<< k) by exact bne_iff_ne.mpr hne
    intro heq
    have h := congrArg (fun v : BitVec 16 => v.getLsbD k) heq
    simp only [BitVec.getLsbD_zero, BitVec.getLsbD_and, one_shiftLeft_getLsbD hk hk,
      decide_true, hbit, Bool.and_self] at h
    exact Bool.false_ne_true h

private theorem mask8_test_eq_getLsbD (a : BitVec 8) {k : Nat} (hk : k < 8) :
    (((1#8 <<< k) &&& a) != 0#8) = a.getLsbD k := by
  cases hbit : a.getLsbD k
  · suffices h0 : (1#8 <<< k) &&& a = 0#8 by rw [h0]; rfl
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [BitVec.getLsbD_and, one_shiftLeft_getLsbD hk hj, BitVec.getLsbD_zero]
    by_cases hjk : j = k
    · subst hjk; simp only [hbit, Bool.and_false]
    · simp only [hjk, decide_false, Bool.false_and]
  · suffices hne : (1#8 <<< k) &&& a ≠ 0#8 by exact bne_iff_ne.mpr hne
    intro heq
    have h := congrArg (fun v : BitVec 8 => v.getLsbD k) heq
    simp only [BitVec.getLsbD_zero, BitVec.getLsbD_and, one_shiftLeft_getLsbD hk hk,
      decide_true, hbit, Bool.and_self] at h
    exact Bool.noConfusion h

private theorem reduceFromByteLoop_xor :
    ∀ (steps : Nat), steps ≤ 8 → ∀ (a1 a2 : BitVec 8) (out1 out2 : BitVec 32),
      reduce.reduceFromByteLoop steps (a1 ^^^ a2) (out1 ^^^ out2) =
        reduce.reduceFromByteLoop steps a1 out1 ^^^ reduce.reduceFromByteLoop steps a2 out2
  | 0, _, _, _, _, _ => rfl
  | i + 1, hi, a1, a2, out1, out2 => by
    have hilt : i < 8 := Nat.lt_of_succ_le hi
    have hle : i ≤ 8 := Nat.le_of_lt hilt
    dsimp only [reduce.reduceFromByteLoop]
    rw [mask8_test_eq_getLsbD (a1 ^^^ a2) hilt, mask8_test_eq_getLsbD a1 hilt,
        mask8_test_eq_getLsbD a2 hilt, BitVec.getLsbD_xor]
    cases a1.getLsbD i <;> cases a2.getLsbD i
    · dsimp
      exact reduceFromByteLoop_xor i hle a1 a2 out1 out2
    · dsimp
      rw [bv_xor_assoc_local a1 a2, bv_xor_assoc_local out1 out2]
      exact reduceFromByteLoop_xor i hle a1 (a2 ^^^ _) out1 (out2 ^^^ _)
    · dsimp
      rw [bv_xor_right_comm_local a1 a2, bv_xor_right_comm_local out1 out2]
      exact reduceFromByteLoop_xor i hle (a1 ^^^ _) a2 (out1 ^^^ _) out2
    · dsimp
      rw [← bv_xor_cancel_both a1 a2 (((POLY <<< i) >>> 16).truncate 8),
          ← bv_xor_cancel_both out1 out2 (POLY <<< i)]
      exact reduceFromByteLoop_xor i hle (a1 ^^^ _) (a2 ^^^ _) (out1 ^^^ _) (out2 ^^^ _)

private theorem reduceByteEntry_xor (a1 a2 : BitVec 8) :
    reduce.reduceByteEntry (a1 ^^^ a2) =
      reduce.reduceByteEntry a1 ^^^ reduce.reduceByteEntry a2 := by
  unfold reduce.reduceByteEntry reduce.reduceFromByte
  have h := reduceFromByteLoop_xor 8 (Nat.le_refl 8) a1 a2 0#32 0#32
  change reduce.reduceFromByteLoop 8 (a1 ^^^ a2) 0#32 = _ at h
  rw [h, bv_truncate_xor]

private theorem polyReduce_xor (v1 v2 : BitVec 32) :
    reduce.polyReduce (v1 ^^^ v2) = reduce.polyReduce v1 ^^^ reduce.polyReduce v2 := by
  dsimp only [reduce.polyReduce]
  have hr1 :
      reduce.reduceByteEntry (((v1 ^^^ v2) >>> 24).truncate 8) =
        reduce.reduceByteEntry ((v1 >>> 24).truncate 8) ^^^
          reduce.reduceByteEntry ((v2 >>> 24).truncate 8) := by
    rw [bv_ushiftRight_xor, bv_truncate_xor, reduceByteEntry_xor]
  have ha' :
      (v1 ^^^ v2) ^^^ ((reduce.reduceByteEntry (((v1 ^^^ v2) >>> 24).truncate 8)).zeroExtend 32 <<< 8) =
        (v1 ^^^ ((reduce.reduceByteEntry ((v1 >>> 24).truncate 8)).zeroExtend 32 <<< 8)) ^^^
          (v2 ^^^ ((reduce.reduceByteEntry ((v2 >>> 24).truncate 8)).zeroExtend 32 <<< 8)) := by
    rw [hr1, bv_zeroExtend_xor, bv_shiftLeft_xor, bv_xor4_interchange]
  rw [ha']
  generalize v1 ^^^ ((reduce.reduceByteEntry ((v1 >>> 24).truncate 8)).zeroExtend 32 <<< 8) = u1
  generalize v2 ^^^ ((reduce.reduceByteEntry ((v2 >>> 24).truncate 8)).zeroExtend 32 <<< 8) = u2
  have ha'' :
      (u1 ^^^ u2) ^^^ (reduce.reduceByteEntry (((u1 ^^^ u2) >>> 16).truncate 8)).zeroExtend 32 =
        (u1 ^^^ (reduce.reduceByteEntry ((u1 >>> 16).truncate 8)).zeroExtend 32) ^^^
          (u2 ^^^ (reduce.reduceByteEntry ((u2 >>> 16).truncate 8)).zeroExtend 32) := by
    rw [bv_ushiftRight_xor, bv_truncate_xor, reduceByteEntry_xor, bv_zeroExtend_xor,
        bv_xor4_interchange]
  rw [ha'', bv_truncate_xor]

private theorem polyReduce_zero : reduce.polyReduce 0#32 = 0#16 := by
  decide +kernel

private theorem polyMulLoop_xor_left :
    ∀ (fuel shift : Nat) (me1 me2 : BitVec 32) (b : BitVec 16) (acc1 acc2 : BitVec 32),
      unaccelerated.polyMulLoop (me1 ^^^ me2) b fuel shift (acc1 ^^^ acc2) =
        unaccelerated.polyMulLoop me1 b fuel shift acc1 ^^^
          unaccelerated.polyMulLoop me2 b fuel shift acc2
  | 0, _, _, _, _, _, _ => rfl
  | fuel + 1, shift, me1, me2, b, acc1, acc2 => by
    dsimp only [unaccelerated.polyMulLoop]
    split
    · rw [bv_shiftLeft_xor, bv_xor4_interchange]
      exact polyMulLoop_xor_left fuel (shift + 1) me1 me2 b
        (acc1 ^^^ (me1 <<< shift)) (acc2 ^^^ (me2 <<< shift))
    · exact polyMulLoop_xor_left fuel (shift + 1) me1 me2 b acc1 acc2

private theorem polyMulLoop_xor_right :
    ∀ (fuel shift : Nat), shift + fuel ≤ 16 →
      ∀ (me : BitVec 32) (b1 b2 : BitVec 16) (acc1 acc2 : BitVec 32),
        unaccelerated.polyMulLoop me (b1 ^^^ b2) fuel shift (acc1 ^^^ acc2) =
          unaccelerated.polyMulLoop me b1 fuel shift acc1 ^^^
            unaccelerated.polyMulLoop me b2 fuel shift acc2
  | 0, _, _, _, _, _, _, _ => rfl
  | fuel + 1, shift, hle, me, b1, b2, acc1, acc2 => by
    have hlt : shift < 16 := by omega
    have hle' : (shift + 1) + fuel ≤ 16 := by omega
    dsimp only [unaccelerated.polyMulLoop]
    rw [mask16_test_eq_getLsbD (b1 ^^^ b2) hlt, mask16_test_eq_getLsbD b1 hlt,
        mask16_test_eq_getLsbD b2 hlt, BitVec.getLsbD_xor]
    cases b1.getLsbD shift <;> cases b2.getLsbD shift
    · dsimp
      exact polyMulLoop_xor_right fuel (shift + 1) hle' me b1 b2 acc1 acc2
    · dsimp
      rw [bv_xor_assoc_local]
      exact polyMulLoop_xor_right fuel (shift + 1) hle' me b1 b2 acc1 (acc2 ^^^ (me <<< shift))
    · dsimp
      rw [bv_xor_right_comm_local]
      exact polyMulLoop_xor_right fuel (shift + 1) hle' me b1 b2 (acc1 ^^^ (me <<< shift)) acc2
    · dsimp
      rw [← bv_xor_cancel_both acc1 acc2 (me <<< shift)]
      exact polyMulLoop_xor_right fuel (shift + 1) hle' me b1 b2
        (acc1 ^^^ (me <<< shift)) (acc2 ^^^ (me <<< shift))

private theorem unaccelerated_mul_zero_left (b : BitVec 16) :
    unaccelerated.mul 0#16 b = 0#16 := by
  have hloop : ∀ fuel shift, unaccelerated.polyMulLoop 0#32 b fuel shift 0#32 = 0#32 := by
    intro fuel
    induction fuel with
    | zero => intro _; rfl
    | succ fuel ih =>
      intro shift
      dsimp only [unaccelerated.polyMulLoop]
      have hs : (0#32 : BitVec 32) <<< shift = 0#32 := BitVec.zero_shiftLeft shift
      have hx : (0#32 : BitVec 32) ^^^ 0#32 = 0#32 := rfl
      rw [hs, hx]
      split <;> exact ih (shift + 1)
  unfold unaccelerated.mul unaccelerated.polyMul
  have hz : (0#16 : BitVec 16).zeroExtend 32 = 0#32 := rfl
  rw [hz, hloop 16 0, polyReduce_zero]

private theorem unaccelerated_mul_zero_right (a : BitVec 16) :
    unaccelerated.mul a 0#16 = 0#16 := by
  have hloop : ∀ fuel shift me, unaccelerated.polyMulLoop me 0#16 fuel shift 0#32 = 0#32 := by
    intro fuel
    induction fuel with
    | zero => intro _ _; rfl
    | succ fuel ih =>
      intro shift me
      dsimp only [unaccelerated.polyMulLoop]
      have hand : (0#16 : BitVec 16) &&& (1#16 <<< shift) = 0#16 := BitVec.zero_and
      have hbne : (0#16 != (0#16 : BitVec 16)) = false := rfl
      rw [hand, hbne]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih (shift + 1) me
  unfold unaccelerated.mul unaccelerated.polyMul
  rw [hloop 16 0 _, polyReduce_zero]

private theorem unaccelerated_mul_xor_left (a1 a2 b : BitVec 16) :
    unaccelerated.mul (a1 ^^^ a2) b =
      unaccelerated.mul a1 b ^^^ unaccelerated.mul a2 b := by
  unfold unaccelerated.mul unaccelerated.polyMul
  have h := polyMulLoop_xor_left 16 0 (a1.zeroExtend 32) (a2.zeroExtend 32) b 0#32 0#32
  change unaccelerated.polyMulLoop _ b 16 0 0#32 = _ at h
  rw [bv_zeroExtend_xor, h, polyReduce_xor]

private theorem unaccelerated_mul_xor_right (a b1 b2 : BitVec 16) :
    unaccelerated.mul a (b1 ^^^ b2) =
      unaccelerated.mul a b1 ^^^ unaccelerated.mul a b2 := by
  unfold unaccelerated.mul unaccelerated.polyMul
  have h := polyMulLoop_xor_right 16 0 (by omega) (a.zeroExtend 32) b1 b2 0#32 0#32
  change unaccelerated.polyMulLoop _ (b1 ^^^ b2) 16 0 0#32 = _ at h
  rw [h, polyReduce_xor]

/-! ## 4. 16-Bit Basis Expansion and Closed 256-Pair Basis Check -/

private def bitTerm16 (x : BitVec 16) (i : Nat) : BitVec 16 :=
  if x.getLsbD i then 1#16 <<< i else 0#16

private theorem bitTerm16_getLsbD (x : BitVec 16) {i k : Nat} (hi : i < 16) (hk : k < 16) :
    (bitTerm16 x i).getLsbD k = (decide (k = i) && x.getLsbD i) := by
  unfold bitTerm16
  cases x.getLsbD i
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_zero, Bool.and_false]
  · simp only [↓reduceIte, one_shiftLeft_getLsbD hi hk, Bool.and_true]

private theorem bv16_eq_basis_sum (x : BitVec 16) :
    x = bitTerm16 x 0 ^^^ bitTerm16 x 1 ^^^ bitTerm16 x 2 ^^^ bitTerm16 x 3 ^^^
        bitTerm16 x 4 ^^^ bitTerm16 x 5 ^^^ bitTerm16 x 6 ^^^ bitTerm16 x 7 ^^^
        bitTerm16 x 8 ^^^ bitTerm16 x 9 ^^^ bitTerm16 x 10 ^^^ bitTerm16 x 11 ^^^
        bitTerm16 x 12 ^^^ bitTerm16 x 13 ^^^ bitTerm16 x 14 ^^^ bitTerm16 x 15 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_xor,
    bitTerm16_getLsbD x (i := 0) (by omega) hk,
    bitTerm16_getLsbD x (i := 1) (by omega) hk,
    bitTerm16_getLsbD x (i := 2) (by omega) hk,
    bitTerm16_getLsbD x (i := 3) (by omega) hk,
    bitTerm16_getLsbD x (i := 4) (by omega) hk,
    bitTerm16_getLsbD x (i := 5) (by omega) hk,
    bitTerm16_getLsbD x (i := 6) (by omega) hk,
    bitTerm16_getLsbD x (i := 7) (by omega) hk,
    bitTerm16_getLsbD x (i := 8) (by omega) hk,
    bitTerm16_getLsbD x (i := 9) (by omega) hk,
    bitTerm16_getLsbD x (i := 10) (by omega) hk,
    bitTerm16_getLsbD x (i := 11) (by omega) hk,
    bitTerm16_getLsbD x (i := 12) (by omega) hk,
    bitTerm16_getLsbD x (i := 13) (by omega) hk,
    bitTerm16_getLsbD x (i := 14) (by omega) hk,
    bitTerm16_getLsbD x (i := 15) (by omega) hk]
  have hk_cases :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
      k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                       rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

private theorem eq_of_xor_linear_basis (f g : BitVec 16 → BitVec 16)
    (hf0 : f 0#16 = 0#16) (hg0 : g 0#16 = 0#16)
    (hfx : ∀ u v, f (u ^^^ v) = f u ^^^ f v)
    (hgx : ∀ u v, g (u ^^^ v) = g u ^^^ g v)
    (hbasis : ∀ i < 16, f (1#16 <<< i) = g (1#16 <<< i))
    (x : BitVec 16) : f x = g x := by
  have hterm : ∀ i < 16, f (bitTerm16 x i) = g (bitTerm16 x i) := by
    intro i hi
    unfold bitTerm16
    split
    · exact hbasis i hi
    · rw [hf0, hg0]
  rw [bv16_eq_basis_sum x]
  simp only [hfx, hgx,
    hterm 0 (by omega), hterm 1 (by omega), hterm 2 (by omega), hterm 3 (by omega),
    hterm 4 (by omega), hterm 5 (by omega), hterm 6 (by omega), hterm 7 (by omega),
    hterm 8 (by omega), hterm 9 (by omega), hterm 10 (by omega), hterm 11 (by omega),
    hterm 12 (by omega), hterm 13 (by omega), hterm 14 (by omega), hterm 15 (by omega)]

private theorem basis_256_check :
    ((List.range 16).all fun i =>
      (List.range 16).all fun j =>
        unaccelerated.mul (1#16 <<< i) (1#16 <<< j) == mulFastBV (1#16 <<< i) (1#16 <<< j)) =
      true := by
  decide +kernel

private theorem basis_mul_eq {i j : Nat} (hi : i < 16) (hj : j < 16) :
    unaccelerated.mul (1#16 <<< i) (1#16 <<< j) = mulFastBV (1#16 <<< i) (1#16 <<< j) := by
  have h1 := List.all_eq_true.mp basis_256_check i (List.mem_range.mpr hi)
  have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
  exact beq_iff_eq.mp h2

/-- Verified equivalence of `unaccelerated.mul` and `mulFastBV` for all 16-bit inputs. -/
theorem unaccelerated_mul_eq_mulFastBV (a b : BitVec 16) :
    unaccelerated.mul a b = mulFastBV a b := by
  refine eq_of_xor_linear_basis
    (fun y => unaccelerated.mul a y)
    (fun y => mulFastBV a y)
    (unaccelerated_mul_zero_right a)
    (mulFastBV_zero_right a)
    (unaccelerated_mul_xor_right a)
    (mulFastBV_xor_right a)
    (fun j hj => ?_)
    b
  exact eq_of_xor_linear_basis
    (fun x => unaccelerated.mul x (1#16 <<< j))
    (fun x => mulFastBV x (1#16 <<< j))
    (unaccelerated_mul_zero_left (1#16 <<< j))
    (mulFastBV_zero_left (1#16 <<< j))
    (fun u v => unaccelerated_mul_xor_left u v (1#16 <<< j))
    (fun u v => mulFastBV_xor_left u v (1#16 <<< j))
    (fun i hi => basis_mul_eq hi hj)
    a

theorem gf16_mul_eq_mulFast (a b : GF16) : GF16.mul a b = mulFast a b := by
  unfold GF16.mul mulFast
  rw [unaccelerated_mul_eq_mulFastBV]

theorem gf16_constMul_eq_mulFast (a b : GF16) : GF16.constMul a b = mulFast a b := by
  unfold GF16.constMul mulFast
  rw [unaccelerated_mul_eq_mulFastBV]

/-! ## 5. Fast `GF16.constDiv`, `PolyConst.lagrangeInterpolatePt`, and Complete-Points Basis -/

def constDivLoopFast : Nat → GF16 → GF16 → GF16
  | 0, _, out => out
  | n + 1, square, out =>
    let square' := mulFast square square
    let out' := mulFast out square'
    constDivLoopFast n square' out'

def constDivFast (self other : GF16) : GF16 :=
  constDivLoopFast 15 other self

theorem constDivLoop_eq_fast :
    ∀ (k : Nat) (sq out : GF16), GF16.constDivLoop k sq out = constDivLoopFast k sq out
  | 0, _, _ => rfl
  | k + 1, sq, out => by
    unfold GF16.constDivLoop constDivLoopFast
    simp only [gf16_constMul_eq_mulFast]
    exact constDivLoop_eq_fast k _ _

theorem gf16_constDiv_eq_fast (self other : GF16) :
    GF16.constDiv self other = constDivFast self other :=
  constDivLoop_eq_fast 15 other self

def polyConstMultFast {n : Nat} (self : PolyConst n) (m : GF16) : PolyConst n :=
  { coefficients := self.coefficients.map (fun c => mulFast c m) }

theorem polyConst_mult_eq_fast {n : Nat} (self : PolyConst n) (m : GF16) :
    self.mult m = polyConstMultFast self m := by
  unfold PolyConst.mult polyConstMultFast
  simp only [gf16_constMul_eq_mulFast]

def polyConstMultXdiffFast {n : Nat} (self : PolyConst n) (difference : GF16) :
    Except PolyPanic (PolyConst n) := do
  if n == 0 then
    .error .subOverflow
  else
    let some top := self.coefficients[n - 1]? | .error .boundsCheck
    if top != GF16.ZERO then
      .error .explicitPanic
    else
      let xp : List GF16 := GF16.ZERO :: self.coefficients.take (n - 1)
      let dp : List GF16 := self.coefficients.map (fun c => mulFast c difference)
      let out : List GF16 := (xp.zip dp).map (fun (a, b) => GF16.constSub a b)
      return { coefficients := out }

theorem polyConst_multXdiff_eq_fast {n : Nat} (self : PolyConst n) (difference : GF16) :
    self.multXdiff difference = polyConstMultXdiffFast self difference := by
  unfold PolyConst.multXdiff polyConstMultXdiffFast
  have hfn : (fun c => GF16.constMul c difference) = (fun c => mulFast c difference) :=
    funext (fun c => gf16_constMul_eq_mulFast c difference)
  rw [hfn]
  rfl

def lagrangeInterpolatePtLoopFast (n : Nat) (pts : List Pt) (pix : GF16) :
    Nat → Nat → PolyConst n → GF16 → Except PolyPanic (PolyConst n × GF16)
  | _, 0, p, denominator => .ok (p, denominator)
  | j, rem + 1, p, denominator => do
    let some pj := pts[j]? | .error .boundsCheck
    if pix == pj.x then
      lagrangeInterpolatePtLoopFast n pts pix (j + 1) rem p denominator
    else
      let p' ← polyConstMultXdiffFast p pj.x
      let denominator' := mulFast denominator (GF16.constSub pix pj.x)
      lagrangeInterpolatePtLoopFast n pts pix (j + 1) rem p' denominator'

theorem lagrangeInterpolatePtLoop_eq_fast (n : Nat) (pts : List Pt) (pix : GF16) :
    ∀ (j rem : Nat) (p : PolyConst n) (denom : GF16),
      PolyConst.lagrangeInterpolatePtLoop n pts pix j rem p denom =
        lagrangeInterpolatePtLoopFast n pts pix j rem p denom
  | _, 0, _, _ => rfl
  | j, rem + 1, p, denom => by
    unfold PolyConst.lagrangeInterpolatePtLoop lagrangeInterpolatePtLoopFast
    cases pts[j]? with
    | none => rfl
    | some pj =>
      dsimp only
      split
      · exact lagrangeInterpolatePtLoop_eq_fast n pts pix (j + 1) rem p denom
      · rw [polyConst_multXdiff_eq_fast, gf16_constMul_eq_mulFast]
        cases polyConstMultXdiffFast p pj.x with
        | error _ => rfl
        | ok p' =>
          exact lagrangeInterpolatePtLoop_eq_fast n pts pix (j + 1) rem p' _

def lagrangeInterpolatePtFast (n : Nat) (pts : List Pt) (i : Nat) :
    Except PolyPanic (PolyConst n) := do
  let some pi := pts[i]? | .error .boundsCheck
  if n == 0 then
    .error .boundsCheck
  else
    let p0 : PolyConst n := { coefficients := GF16.ONE :: List.replicate (n - 1) GF16.ZERO }
    let (p, denominator) ← lagrangeInterpolatePtLoopFast n pts pi.x 0 n p0 GF16.ONE
    return polyConstMultFast p (constDivFast pi.y denominator)

theorem lagrangeInterpolatePt_eq_fast (n : Nat) (pts : List Pt) (i : Nat) :
    PolyConst.lagrangeInterpolatePt n pts i = lagrangeInterpolatePtFast n pts i := by
  unfold PolyConst.lagrangeInterpolatePt lagrangeInterpolatePtFast
  cases pts[i]? with
  | none => rfl
  | some pi =>
    dsimp only
    split
    · rfl
    · rw [lagrangeInterpolatePtLoop_eq_fast]
      cases lagrangeInterpolatePtLoopFast n pts pi.x 0 n
          { coefficients := GF16.ONE :: List.replicate (n - 1) GF16.ZERO } GF16.ONE with
      | error _ => rfl
      | ok res =>
        dsimp only [bind, Except.bind, pure, Except.pure]
        rw [polyConst_mult_eq_fast, gf16_constDiv_eq_fast]

def lagrangePolysForCompletePointsFast (n : Nat) : Except PolyPanic (List (PolyConst n)) := do
  let ones : List Pt :=
    (List.range n).map (fun i => { x := GF16.new (BitVec.ofNat 16 i), y := GF16.ONE })
  (List.range n).mapM (fun i => lagrangeInterpolatePtFast n ones i)

theorem lagrangePolysForCompletePoints_eq_fast (n : Nat) :
    lagrangePolysForCompletePoints n = lagrangePolysForCompletePointsFast n := by
  unfold lagrangePolysForCompletePoints lagrangePolysForCompletePointsFast
  simp only [lagrangeInterpolatePt_eq_fast]

end CryptoVerification.SpqrV1.Poly.GF16Fast
