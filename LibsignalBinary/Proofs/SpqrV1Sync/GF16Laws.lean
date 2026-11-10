/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16

/-!
# Algebraic Field Laws for `GF16`

Proves the ring, characteristic-2, and division laws for `LibsignalSpqrV1.GF16` (`GF(2 ^ 16)` modulo
the degree-16 irreducible polynomial `POLY`):
* Multiplicative ring laws follow by embedding `BitVec 16` into 64-bit carryless polynomial
  arithmetic (`clmul64`) and reducing uniquely modulo `POLY`.
* `mul_inv_cancel'` and `div_eq_mul_inv'` follow from `divImplLoop` and the fact that `⟨2#16⟩` has
  multiplicative order `65535 = 3 * 5 * 17 * 257`, generating `GF16 \ {0}`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.GF16Field

open CryptoVerification.LibsignalSpqrV1

private theorem gf16_ext {a b : GF16} (h : a.value = b.value) : a = b := by
  cases a; cases b; cases h; rfl

theorem add_assoc' (a b c : GF16) :
    GF16.add (GF16.add a b) c = GF16.add a (GF16.add b c) :=
  gf16_ext (BitVec.xor_assoc a.value b.value c.value)

theorem add_comm' (a b : GF16) : GF16.add a b = GF16.add b a :=
  gf16_ext (BitVec.xor_comm a.value b.value)

theorem zero_add' (a : GF16) : GF16.add GF16.ZERO a = a := by
  apply gf16_ext
  change 0#16 ^^^ a.value = a.value
  rw [BitVec.xor_comm, BitVec.xor_zero]

theorem add_zero' (a : GF16) : GF16.add a GF16.ZERO = a :=
  gf16_ext BitVec.xor_zero

/-- Characteristic 2: every element is its own additive inverse. -/
theorem add_self' (a : GF16) : GF16.add a a = GF16.ZERO :=
  gf16_ext BitVec.xor_self

theorem zero_ne_one' : GF16.ZERO ≠ GF16.ONE := by
  decide

/-! ### Private `BitVec 64` carryless multiplication and reduction modulo `POLY` -/

private def clmul64Aux (a b : BitVec 64) : Nat → BitVec 64
  | 0 => 0#64
  | i + 1 =>
    clmul64Aux a b i ^^^ (if b.getLsbD i then a <<< i else 0#64)

private def clmul64 (a b : BitVec 64) : BitVec 64 :=
  clmul64Aux a b 64

private theorem zero_shiftLeft_64 (j : Nat) : (0#64 : BitVec 64) <<< j = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k _
  simp

private theorem clmul64Aux_zero_left (b : BitVec 64) : ∀ n, clmul64Aux 0#64 b n = 0#64
  | 0 => rfl
  | n + 1 => by
    simp only [clmul64Aux, clmul64Aux_zero_left b n, zero_shiftLeft_64]
    cases b.getLsbD n <;> rfl

private theorem clmul64_zero_left (b : BitVec 64) : clmul64 0#64 b = 0#64 :=
  clmul64Aux_zero_left b 64

private theorem clmul64Aux_zero_right (a : BitVec 64) : ∀ n, clmul64Aux a 0#64 n = 0#64
  | 0 => rfl
  | n + 1 => by
    simp [clmul64Aux, clmul64Aux_zero_right a n]

private theorem clmul64_zero_right (a : BitVec 64) : clmul64 a 0#64 = 0#64 :=
  clmul64Aux_zero_right a 64

private theorem xor_four_swap {w : Nat} (p q r s : BitVec w) :
    (p ^^^ q) ^^^ (r ^^^ s) = (p ^^^ r) ^^^ (q ^^^ s) := by
  rw [BitVec.xor_assoc p q (r ^^^ s), ← BitVec.xor_assoc q r s, BitVec.xor_comm q r,
      BitVec.xor_assoc r q s, ← BitVec.xor_assoc p r (q ^^^ s)]

private theorem clmul64Aux_xor_left (x y b : BitVec 64) :
    ∀ n, clmul64Aux (x ^^^ y) b n = clmul64Aux x b n ^^^ clmul64Aux y b n
  | 0 => by simp [clmul64Aux]
  | n + 1 => by
    simp only [clmul64Aux, clmul64Aux_xor_left x y b n]
    cases b.getLsbD n
    · simp
    · simp only [↓reduceIte, BitVec.shiftLeft_xor_distrib, xor_four_swap]

private theorem clmul64_xor_left (x y b : BitVec 64) :
    clmul64 (x ^^^ y) b = clmul64 x b ^^^ clmul64 y b :=
  clmul64Aux_xor_left x y b 64

private theorem clmul64Aux_shiftLeft_left (x b : BitVec 64) (j : Nat) :
    ∀ n, clmul64Aux (x <<< j) b n = (clmul64Aux x b n) <<< j
  | 0 => by simp [clmul64Aux]
  | n + 1 => by
    simp only [clmul64Aux, clmul64Aux_shiftLeft_left x b j n, BitVec.shiftLeft_xor_distrib]
    cases b.getLsbD n
    · simp
    · simp only [↓reduceIte, ← BitVec.shiftLeft_add, Nat.add_comm]

private theorem clmul64_shiftLeft_left (x b : BitVec 64) (j : Nat) :
    clmul64 (x <<< j) b = (clmul64 x b) <<< j :=
  clmul64Aux_shiftLeft_left x b j 64

private theorem clmul64Aux_one_getLsbD (b : BitVec 64) :
    ∀ n k, k < 64 → (clmul64Aux 1#64 b n).getLsbD k = (decide (k < n) && b.getLsbD k)
  | 0, k, _ => by simp [clmul64Aux]
  | n + 1, k, hk => by
    simp only [clmul64Aux, BitVec.getLsbD_xor, clmul64Aux_one_getLsbD b n k hk]
    by_cases h1 : k < n
    · have h2 : k < n + 1 := by omega
      cases b.getLsbD n <;> simp [BitVec.getLsbD_shiftLeft, h1, h2]
    · by_cases hEq : k = n
      · subst hEq
        cases hbk : b.getLsbD k <;>
          simp [hk]
      · have hgt : ¬(k < n + 1) := by omega
        have hsub : k - n ≠ 0 := by omega
        cases b.getLsbD n <;>
          simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, h1, hgt, hsub]

private theorem clmul64_one_left (b : BitVec 64) : clmul64 1#64 b = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [clmul64, clmul64Aux_one_getLsbD b 64 k hk]
  simp [hk]

private theorem clmul64Aux_comm_step (a b : BitVec 64) :
    ∀ n, clmul64 (clmul64Aux 1#64 a n) b = clmul64Aux b a n
  | 0 => by simp [clmul64Aux, clmul64_zero_left]
  | n + 1 => by
    simp only [clmul64Aux, clmul64_xor_left, clmul64Aux_comm_step a b n]
    cases a.getLsbD n
    · simp [clmul64_zero_left]
    · simp [clmul64_shiftLeft_left, clmul64_one_left]

private theorem clmul64_comm (a b : BitVec 64) : clmul64 a b = clmul64 b a := by
  have h := clmul64Aux_comm_step a b 64
  rw [← clmul64, clmul64_one_left] at h
  exact h

private theorem clmul64_xor_right (a x y : BitVec 64) :
    clmul64 a (x ^^^ y) = clmul64 a x ^^^ clmul64 a y := by
  rw [clmul64_comm a (x ^^^ y), clmul64_xor_left, clmul64_comm x a, clmul64_comm y a]

private theorem clmul64_shiftLeft_right (a y : BitVec 64) (j : Nat) :
    clmul64 a (y <<< j) = (clmul64 a y) <<< j := by
  rw [clmul64_comm a (y <<< j), clmul64_shiftLeft_left, clmul64_comm y a]

private theorem clmul64Aux_assoc (a b c : BitVec 64) :
    ∀ n, clmul64Aux (clmul64 a b) c n = clmul64 a (clmul64Aux b c n)
  | 0 => by simp [clmul64Aux, clmul64_zero_right]
  | n + 1 => by
    simp only [clmul64Aux, clmul64_xor_right, clmul64Aux_assoc a b c n]
    cases c.getLsbD n
    · simp [clmul64_zero_right]
    · simp [clmul64_shiftLeft_right]

private theorem clmul64_assoc (a b c : BitVec 64) :
    clmul64 (clmul64 a b) c = clmul64 a (clmul64 b c) :=
  clmul64Aux_assoc a b c 64

private def degLt (d : Nat) (x : BitVec 64) : Prop :=
  ∀ k, d ≤ k → x.getLsbD k = false

private theorem degLt_zero (d : Nat) : degLt d 0#64 := by
  intro k _
  simp

private theorem degLt_of_le {d1 d2 : Nat} {x : BitVec 64} (hx : degLt d1 x) (hle : d1 ≤ d2) :
    degLt d2 x :=
  fun k hk => hx k (by omega)

private theorem degLt_of_ushiftRight_eq_zero {d : Nat} {x : BitVec 64} (h : x >>> d = 0#64) :
    degLt d x := by
  intro k hk
  have hkd : d + (k - d) = k := by omega
  rw [← hkd, ← BitVec.getLsbD_ushiftRight, h]
  simp

private theorem degLt_zeroExtend {w : Nat} (v : BitVec w) : degLt w (v.zeroExtend 64) := by
  intro k hk
  simp [BitVec.zeroExtend, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge v k hk]

private theorem degLt_xor {d : Nat} {x y : BitVec 64} (hx : degLt d x) (hy : degLt d y) :
    degLt d (x ^^^ y) := by
  intro k hk
  simp [BitVec.getLsbD_xor, hx k hk, hy k hk]

private theorem degLt_shiftLeft {d : Nat} {x : BitVec 64} (hx : degLt d x) (j : Nat) :
    degLt (d + j) (x <<< j) := by
  intro k hk
  simp only [BitVec.getLsbD_shiftLeft]
  by_cases hlt : k < j
  · simp [hlt]
  · rw [hx (k - j) (by omega)]
    simp

private theorem clmul64Aux_eq_of_degLt (a : BitVec 64) {b : BitVec 64} {d : Nat} (hb : degLt d b) :
    ∀ n, d ≤ n → clmul64Aux a b n = clmul64Aux a b d
  | 0, h0 => by
    have hd : d = 0 := by omega
    subst hd; rfl
  | n + 1, hn => by
    by_cases hEq : d = n + 1
    · subst hEq; rfl
    · have hdn : d ≤ n := by omega
      simp [clmul64Aux, hb n hdn, clmul64Aux_eq_of_degLt a hb n hdn]

private theorem clmul64Aux_getLsbD_of_degLt {da : Nat} {a : BitVec 64} (ha : degLt da a)
    (b : BitVec 64) :
    ∀ n k, da + n ≤ k + 1 → (clmul64Aux a b n).getLsbD k = false
  | 0, k, _ => by simp [clmul64Aux]
  | n + 1, k, hk => by
    simp only [clmul64Aux, BitVec.getLsbD_xor]
    rw [clmul64Aux_getLsbD_of_degLt ha b n k (by omega)]
    cases b.getLsbD n
    · simp
    · have hsh := degLt_shiftLeft ha n k (by omega)
      simp [hsh]

private theorem degLt_clmul64 {da db : Nat} {a b : BitVec 64}
    (ha : degLt da a) (hb : degLt db b) (hdb : db ≤ 64) :
    degLt (da + db) (clmul64 a b) := by
  intro k hk
  rw [clmul64, clmul64Aux_eq_of_degLt a hb 64 hdb]
  exact clmul64Aux_getLsbD_of_degLt ha b db k (by omega)

private def POLY64 : BitVec 64 := POLY.zeroExtend 64

private theorem poly64_degLt17 : degLt 17 POLY64 :=
  degLt_of_ushiftRight_eq_zero (by decide)

private theorem poly64_bit16 : POLY64.getLsbD 16 = true := by
  decide

private theorem clmul64_poly_zero_of_degLt :
    ∀ d, d ≤ 48 → ∀ q : BitVec 64, degLt d q → degLt 16 (clmul64 q POLY64) → q = 0#64
  | 0, _, q, hq, _ => by
    apply BitVec.eq_of_getLsbD_eq
    intro k _
    simp [hq k (by omega)]
  | d + 1, hd, q, hq, hprod => by
    have hbit0 : q.getLsbD d = false := by
      cases hqd : q.getLsbD d with
      | false => rfl
      | true =>
        have heq : clmul64 q POLY64 = clmul64Aux POLY64 q d ^^^ (POLY64 <<< d) := by
          rw [clmul64_comm, clmul64, clmul64Aux_eq_of_degLt POLY64 hq 64 (by omega)]
          simp [clmul64Aux, hqd]
        have h1 : (clmul64 q POLY64).getLsbD (d + 16) = false := hprod (d + 16) (by omega)
        rw [heq, BitVec.getLsbD_xor,
            clmul64Aux_getLsbD_of_degLt poly64_degLt17 q d (d + 16) (by omega)] at h1
        have hsh : (POLY64 <<< d).getLsbD (d + 16) = true := by
          rw [BitVec.getLsbD_shiftLeft]
          have hlt64 : d + 16 < 64 := by omega
          have hnlt : ¬(d + 16 < d) := by omega
          have hsub : d + 16 - d = 16 := by omega
          simp [hlt64, hnlt, hsub, poly64_bit16]
        rw [hsh] at h1
        cases h1
    have hqd' : degLt d q := by
      intro k hk
      by_cases hEq : k = d
      · subst hEq; exact hbit0
      · exact hq k (by omega)
    exact clmul64_poly_zero_of_degLt d (by omega) q hqd' hprod

private def equivModPoly (x y : BitVec 64) : Prop :=
  ∃ q : BitVec 64, degLt 48 q ∧ x ^^^ y = clmul64 q POLY64

private theorem equivModPoly_refl (x : BitVec 64) : equivModPoly x x :=
  ⟨0#64, degLt_zero 48, by simp [clmul64_zero_left]⟩

private theorem equivModPoly_symm {x y : BitVec 64} (h : equivModPoly x y) : equivModPoly y x := by
  rcases h with ⟨q, hq, heq⟩
  exact ⟨q, hq, by rw [BitVec.xor_comm, heq]⟩

private theorem equivModPoly_trans {x y z : BitVec 64}
    (h1 : equivModPoly x y) (h2 : equivModPoly y z) : equivModPoly x z := by
  rcases h1 with ⟨q1, hq1, heq1⟩
  rcases h2 with ⟨q2, hq2, heq2⟩
  refine ⟨q1 ^^^ q2, degLt_xor hq1 hq2, ?_⟩
  have hxz : x ^^^ z = (x ^^^ y) ^^^ (y ^^^ z) := by
    rw [BitVec.xor_assoc, ← BitVec.xor_assoc y y z, BitVec.xor_self]
    rw [BitVec.xor_comm 0#64 z, BitVec.xor_zero]
  rw [hxz, heq1, heq2, clmul64_xor_left]

private theorem equivModPoly_xor {x1 y1 x2 y2 : BitVec 64}
    (h1 : equivModPoly x1 y1) (h2 : equivModPoly x2 y2) :
    equivModPoly (x1 ^^^ x2) (y1 ^^^ y2) := by
  rcases h1 with ⟨q1, hq1, heq1⟩
  rcases h2 with ⟨q2, hq2, heq2⟩
  refine ⟨q1 ^^^ q2, degLt_xor hq1 hq2, ?_⟩
  rw [xor_four_swap, heq1, heq2, clmul64_xor_left]

private theorem eq_of_equivModPoly_16 {r1 r2 : BitVec 16}
    (h : equivModPoly (r1.zeroExtend 64) (r2.zeroExtend 64)) : r1 = r2 := by
  rcases h with ⟨q, hq, heq⟩
  have hdeg : degLt 16 (clmul64 q POLY64) := by
    rw [← heq]
    exact degLt_xor (degLt_zeroExtend r1) (degLt_zeroExtend r2)
  have hq0 : q = 0#64 := clmul64_poly_zero_of_degLt 48 (by omega) q hq hdeg
  rw [hq0, clmul64_zero_left] at heq
  have heq64 : r1.zeroExtend 64 = r2.zeroExtend 64 := BitVec.xor_eq_zero_iff.mp heq
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hk64 : k < 64 := by omega
  have hbit := congrArg (fun v => v.getLsbD k) heq64
  simpa [BitVec.zeroExtend, BitVec.getLsbD_setWidth, hk64] using hbit

/-! ### Bridge from `unaccelerated.polyMul` and `reduce.polyReduce` to `clmul64` -/

private theorem bit16_mask_test (b : BitVec 16) {s : Nat} (hs : s < 16) :
    (0#16 != (b &&& (1#16 <<< s))) = b.getLsbD s := by
  cases hbs : b.getLsbD s with
  | false =>
    suffices h0 : b &&& (1#16 <<< s) = 0#16 by simp [h0]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
    by_cases hks : k = s
    · subst hks; simp [hbs]
    · have hsub : k - s ≠ 0 ∨ k < s := by omega
      rcases hsub with hsub | hlt
      · simp [hsub]
      · simp [hlt]
  | true =>
    suffices hne : b &&& (1#16 <<< s) ≠ 0#16 by
      cases hbeq : (0#16 == b &&& (1#16 <<< s))
      · simp [bne, hbeq]
      · exfalso
        exact hne (eq_of_beq hbeq).symm
    intro heq
    have hbit := congrArg (fun v => v.getLsbD s) heq
    simp [hs] at hbit hbs
    rw [hbs] at hbit
    cases hbit

private theorem shift16_in_32_zeroExtend64 (a : BitVec 16) {s : Nat} (hs : s < 16) :
    ((a.zeroExtend 32) <<< s).zeroExtend 64 = (a.zeroExtend 64) <<< s := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.zeroExtend, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, hk, decide_true,
    Bool.true_and]
  by_cases hks : k < s
  · simp [hks]
  · by_cases hk32 : k < 32
    · have hsub32 : k - s < 32 := by omega
      have hsub64 : k - s < 64 := by omega
      simp [hks, hk32, hsub32, hsub64]
    · have hge16 : 16 ≤ k - s := by omega
      simp [hks, hk32, BitVec.getLsbD_of_ge a (k - s) hge16]

private theorem polyMulLoop_eq_clmul64Aux (a b : BitVec 16) :
    ∀ fuel s (acc : BitVec 32), fuel + s = 16 →
      acc.zeroExtend 64 = clmul64Aux (a.zeroExtend 64) (b.zeroExtend 64) s →
      (unaccelerated.polyMulLoop (a.zeroExtend 32) b fuel s acc).zeroExtend 64 =
        clmul64Aux (a.zeroExtend 64) (b.zeroExtend 64) 16
  | 0, s, acc, hs, hacc => by
    have hs16 : s = 16 := by omega
    subst hs16
    simpa [unaccelerated.polyMulLoop] using hacc
  | fuel + 1, s, acc, hs, hacc => by
    have hs_lt : s < 16 := by omega
    have hs_lt64 : s < 64 := by omega
    simp only [unaccelerated.polyMulLoop]
    apply polyMulLoop_eq_clmul64Aux a b fuel (s + 1) _ (by omega)
    rw [bit16_mask_test b hs_lt]
    have hb64 : (b.zeroExtend 64).getLsbD s = b.getLsbD s := by
      simp [BitVec.zeroExtend, hs_lt64]
    simp only [clmul64Aux, hb64, ← hacc]
    cases b.getLsbD s
    · simp
    · simp [BitVec.zeroExtend, BitVec.setWidth_xor, ← shift16_in_32_zeroExtend64 a hs_lt]

private theorem polyMul_zeroExtend64 (a b : BitVec 16) :
    (unaccelerated.polyMul a b).zeroExtend 64 = clmul64 (a.zeroExtend 64) (b.zeroExtend 64) := by
  rw [unaccelerated.polyMul, polyMulLoop_eq_clmul64Aux a b 16 0 0#32 (by omega) rfl]
  rw [clmul64, clmul64Aux_eq_of_degLt (a.zeroExtend 64) (degLt_zeroExtend b) 64 (by omega)]

private def qByteLoop : Nat → BitVec 8 → BitVec 8 → BitVec 8
  | 0, _, q => q
  | i + 1, a, q =>
    let mask : BitVec 8 := 1#8 <<< i
    if (mask &&& a) != 0#8 then
      let shiftedPoly : BitVec 32 := POLY <<< i
      let a' := a ^^^ ((shiftedPoly >>> 16).truncate 8)
      qByteLoop i a' (q ^^^ (1#8 <<< i))
    else
      qByteLoop i a q

private def qByte (a : BitVec 8) : BitVec 8 :=
  qByteLoop 8 a 0#8

private theorem qByte_spec_all :
    (List.range 256).all (fun n =>
      let a := BitVec.ofNat 8 n
      let q := (qByte a).zeroExtend 64
      let e := (reduce.reduceByteEntry a).zeroExtend 64
      ((a.zeroExtend 64) <<< 16) ^^^ e == clmul64 q POLY64) = true := by
  decide +kernel

private theorem qByte_spec (a : BitVec 8) :
    ((a.zeroExtend 64) <<< 16) ^^^ (reduce.reduceByteEntry a).zeroExtend 64 =
      clmul64 ((qByte a).zeroExtend 64) POLY64 := by
  have hmem : a.toNat ∈ List.range 256 := List.mem_range.mpr a.isLt
  have hall := List.all_eq_true.mp qByte_spec_all a.toNat hmem
  simpa [BitVec.ofNat_toNat, BitVec.setWidth_eq] using eq_of_beq hall

private theorem polyReduce_splicing (v : BitVec 32) (e1 e2 : BitVec 16) :
    let i1 : BitVec 8 := (v >>> 24).truncate 8
    let v1 : BitVec 32 := v ^^^ (e1.zeroExtend 32 <<< 8)
    let i2 : BitVec 8 := (v1 >>> 16).truncate 8
    let v2 : BitVec 32 := v1 ^^^ e2.zeroExtend 32
    v.zeroExtend 64 ^^^ (v2.truncate 16).zeroExtend 64 =
      (((i1.zeroExtend 64) <<< 24) ^^^ (e1.zeroExtend 64 <<< 8)) ^^^
      (((i2.zeroExtend 64) <<< 16) ^^^ e2.zeroExtend 64) := by
  intro i1 v1 i2 v2
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [i1, v1, i2, v2, BitVec.zeroExtend, BitVec.truncate, BitVec.getLsbD_xor,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, hk,
    decide_true, Bool.true_and]
  by_cases hk16 : k < 16
  · have hk24 : k < 24 := by omega
    have hk32 : k < 32 := by omega
    have hk8 : k - 8 < 32 := by omega
    have hk8' : k - 8 < 64 := by omega
    simp only [hk16, hk24, hk32, hk8, hk8', decide_true, Bool.true_and, Bool.not_true,
      Bool.false_and, Bool.false_xor]
    cases v.getLsbD k <;> cases (!decide (k < 8) && e1.getLsbD (k - 8)) <;>
      cases e2.getLsbD k <;> rfl
  · by_cases hk24 : k < 24
    · have hk8_lt : ¬(k < 8) := by omega
      have hk32 : k < 32 := by omega
      have hk16_8 : k - 16 < 8 := by omega
      have hk16_64 : k - 16 < 64 := by omega
      have hk8_32 : k - 8 < 32 := by omega
      have hk8_64 : k - 8 < 64 := by omega
      have hadd16 : 16 + (k - 16) = k := by omega
      have hsub8 : 16 + (k - 16) - 8 = k - 8 := by omega
      have hnlt8 : ¬(16 + (k - 16) < 8) := by omega
      have he2 : e2.getLsbD k = false := BitVec.getLsbD_of_ge e2 k (by omega)
      simp only [hk16, hk24, hk8_lt, hk32, hk16_8, hk16_64, hk8_32, hk8_64, hadd16, he2,
        decide_false, decide_true, Bool.false_and, Bool.true_and, Bool.not_true, Bool.not_false,
        Bool.xor_false, Bool.false_xor]
      cases v.getLsbD k <;> cases e1.getLsbD (k - 8) <;> rfl
    · by_cases hk32 : k < 32
      · have hk24_8 : k - 24 < 8 := by omega
        have hk24_64 : k - 24 < 64 := by omega
        have hadd24 : 24 + (k - 24) = k := by omega
        have he1 : e1.getLsbD (k - 8) = false := BitVec.getLsbD_of_ge e1 (k - 8) (by omega)
        have he2 : e2.getLsbD k = false := BitVec.getLsbD_of_ge e2 k (by omega)
        have hi2 : ¬(k - 16 < 8) := by omega
        simp only [hk16, hk24, hk32, hk24_8, hk24_64, hadd24, he1, he2, hi2,
          decide_false, decide_true, Bool.false_and, Bool.true_and, Bool.and_false,
          Bool.xor_false]
        cases v.getLsbD k <;> rfl
      · have hv : v.getLsbD k = false := BitVec.getLsbD_of_ge v k (by omega)
        have he1 : e1.getLsbD (k - 8) = false := BitVec.getLsbD_of_ge e1 (k - 8) (by omega)
        have he2 : e2.getLsbD k = false := BitVec.getLsbD_of_ge e2 k (by omega)
        have hi1 : ¬(k - 24 < 8) := by omega
        have hi2 : ¬(k - 16 < 8) := by omega
        simp [hk16, hk32, hv, he1, he2, hi1, hi2]

private theorem polyReduce_spec (v : BitVec 32) :
    ∃ q : BitVec 64, degLt 16 q ∧
      v.zeroExtend 64 ^^^ (reduce.polyReduce v).zeroExtend 64 = clmul64 q POLY64 := by
  let i1 : BitVec 8 := (v >>> 24).truncate 8
  let e1 : BitVec 16 := reduce.reduceByteEntry i1
  let v1 : BitVec 32 := v ^^^ (e1.zeroExtend 32 <<< 8)
  let i2 : BitVec 8 := (v1 >>> 16).truncate 8
  let e2 : BitVec 16 := reduce.reduceByteEntry i2
  refine ⟨((qByte i1).zeroExtend 64 <<< 8) ^^^ (qByte i2).zeroExtend 64, ?_, ?_⟩
  · exact degLt_xor
      (degLt_shiftLeft (degLt_zeroExtend (qByte i1)) 8)
      (degLt_of_le (degLt_zeroExtend (qByte i2)) (by omega))
  · change v.zeroExtend 64 ^^^ ((v1 ^^^ e2.zeroExtend 32).truncate 16).zeroExtend 64 = _
    rw [polyReduce_splicing v e1 e2]
    have hq1 := congrArg (fun x : BitVec 64 => x <<< 8) (qByte_spec i1)
    simp only [BitVec.shiftLeft_xor_distrib, ← BitVec.shiftLeft_add, ← clmul64_shiftLeft_left] at hq1
    have hq2 := qByte_spec i2
    rw [hq1, hq2, ← clmul64_xor_left]

private theorem gf16_mul_equiv (a b : GF16) :
    ∃ q : BitVec 64, degLt 16 q ∧
      clmul64 (a.value.zeroExtend 64) (b.value.zeroExtend 64) ^^^
        (GF16.mul a b).value.zeroExtend 64 = clmul64 q POLY64 := by
  rcases polyReduce_spec (unaccelerated.polyMul a.value b.value) with ⟨q, hq, heq⟩
  rw [polyMul_zeroExtend64] at heq
  exact ⟨q, hq, heq⟩

private theorem gf16_mul_equivModPoly (a b : GF16) :
    equivModPoly ((GF16.mul a b).value.zeroExtend 64)
      (clmul64 (a.value.zeroExtend 64) (b.value.zeroExtend 64)) := by
  rcases gf16_mul_equiv a b with ⟨q, hq, heq⟩
  exact ⟨q, degLt_of_le hq (by omega), by rw [BitVec.xor_comm, heq]⟩

private theorem equivModPoly_clmul_right {x y z : BitVec 64}
    (hxy : ∃ q : BitVec 64, degLt 16 q ∧ x ^^^ y = clmul64 q POLY64)
    (hz : degLt 16 z) :
    equivModPoly (clmul64 x z) (clmul64 y z) := by
  rcases hxy with ⟨q, hq, heq⟩
  refine ⟨clmul64 q z, degLt_of_le (degLt_clmul64 hq hz (by omega)) (by omega), ?_⟩
  rw [← clmul64_xor_left, heq, clmul64_assoc, clmul64_comm POLY64 z, ← clmul64_assoc]

theorem mul_comm' (a b : GF16) : GF16.mul a b = GF16.mul b a := by
  apply gf16_ext
  apply eq_of_equivModPoly_16
  refine equivModPoly_trans (gf16_mul_equivModPoly a b) ?_
  rw [clmul64_comm]
  exact equivModPoly_symm (gf16_mul_equivModPoly b a)

theorem mul_assoc' (a b c : GF16) :
    GF16.mul (GF16.mul a b) c = GF16.mul a (GF16.mul b c) := by
  apply gf16_ext
  apply eq_of_equivModPoly_16
  let A := a.value.zeroExtend 64
  let B := b.value.zeroExtend 64
  let C := c.value.zeroExtend 64
  have h1 : equivModPoly ((GF16.mul (GF16.mul a b) c).value.zeroExtend 64)
      (clmul64 (clmul64 A B) C) := by
    refine equivModPoly_trans (gf16_mul_equivModPoly (GF16.mul a b) c) ?_
    rcases gf16_mul_equiv a b with ⟨q, hq, heq⟩
    exact equivModPoly_symm (equivModPoly_clmul_right ⟨q, hq, heq⟩ (degLt_zeroExtend c.value))
  have h2 : equivModPoly ((GF16.mul a (GF16.mul b c)).value.zeroExtend 64)
      (clmul64 A (clmul64 B C)) := by
    rw [mul_comm' a (GF16.mul b c)]
    refine equivModPoly_trans (gf16_mul_equivModPoly (GF16.mul b c) a) ?_
    rcases gf16_mul_equiv b c with ⟨q, hq, heq⟩
    have hstep := equivModPoly_symm (equivModPoly_clmul_right ⟨q, hq, heq⟩ (degLt_zeroExtend a.value))
    simpa [clmul64_comm A (clmul64 B C)] using hstep
  rw [clmul64_assoc] at h1
  exact equivModPoly_trans h1 (equivModPoly_symm h2)

theorem one_mul' (a : GF16) : GF16.mul GF16.ONE a = a := by
  apply gf16_ext
  apply eq_of_equivModPoly_16
  have hone : (GF16.ONE.value.zeroExtend 64) = 1#64 := rfl
  have h := gf16_mul_equivModPoly GF16.ONE a
  rw [hone, clmul64_one_left] at h
  exact h

theorem mul_one' (a : GF16) : GF16.mul a GF16.ONE = a := by
  rw [mul_comm', one_mul']

theorem zero_mul' (a : GF16) : GF16.mul GF16.ZERO a = GF16.ZERO := by
  apply gf16_ext
  apply eq_of_equivModPoly_16
  have hzero : (GF16.ZERO.value.zeroExtend 64) = 0#64 := rfl
  have h := gf16_mul_equivModPoly GF16.ZERO a
  rw [hzero, clmul64_zero_left] at h
  exact h

theorem mul_zero' (a : GF16) : GF16.mul a GF16.ZERO = GF16.ZERO := by
  rw [mul_comm', zero_mul']

theorem left_distrib' (a b c : GF16) :
    GF16.mul a (GF16.add b c) = GF16.add (GF16.mul a b) (GF16.mul a c) := by
  apply gf16_ext
  apply eq_of_equivModPoly_16
  have hlhs := gf16_mul_equivModPoly a (GF16.add b c)
  have hbc : (GF16.add b c).value.zeroExtend 64 =
      b.value.zeroExtend 64 ^^^ c.value.zeroExtend 64 := BitVec.setWidth_xor
  rw [hbc, clmul64_xor_right] at hlhs
  have hrhs := equivModPoly_xor (gf16_mul_equivModPoly a b) (gf16_mul_equivModPoly a c)
  change equivModPoly _ ((GF16.mul a b).value.zeroExtend 64 ^^^ (GF16.mul a c).value.zeroExtend 64)
  rw [← BitVec.setWidth_xor] at hrhs
  exact equivModPoly_trans hlhs (equivModPoly_symm hrhs)

theorem right_distrib' (a b c : GF16) :
    GF16.mul (GF16.add a b) c = GF16.add (GF16.mul a c) (GF16.mul b c) := by
  rw [mul_comm' (GF16.add a b) c, left_distrib', mul_comm' c a, mul_comm' c b]

/-! ### Multiplicative inverse via generator order `65535` and finite pigeonhole -/

private def gfPow (x : GF16) : Nat → GF16
  | 0 => GF16.ONE
  | n + 1 => GF16.mul x (gfPow x n)

private theorem gfPow_one_base : ∀ n, gfPow GF16.ONE n = GF16.ONE
  | 0 => rfl
  | n + 1 => by simp [gfPow, one_mul', gfPow_one_base n]

private theorem gfPow_add (x : GF16) :
    ∀ m n, gfPow x (m + n) = GF16.mul (gfPow x m) (gfPow x n)
  | 0, n => by simp [gfPow, one_mul']
  | m + 1, n => by
    rw [Nat.succ_add, gfPow, gfPow, gfPow_add x m n, mul_assoc']

private theorem gfPow_two (x : GF16) : gfPow x 2 = GF16.mul x x := by
  simp [gfPow, mul_one']

private theorem gfPow_mul (x : GF16) :
    ∀ m n, gfPow x (m * n) = gfPow (gfPow x m) n
  | _, 0 => rfl
  | m, n + 1 => by
    rw [Nat.mul_succ, Nat.add_comm, gfPow_add, gfPow, gfPow_mul x m n]

private def gfFastPowAux : Nat → GF16 → Nat → GF16
  | 0, _, _ => GF16.ONE
  | fuel + 1, x, n =>
    if n = 0 then
      GF16.ONE
    else
      let half := gfFastPowAux fuel (GF16.mul x x) (n / 2)
      if n % 2 = 1 then GF16.mul x half else half

private theorem gfFastPowAux_eq_gfPow :
    ∀ fuel (x : GF16) n, n < 2 ^ fuel → gfFastPowAux fuel x n = gfPow x n
  | 0, x, n, hn => by
    have hn0 : n = 0 := by omega
    subst hn0; rfl
  | fuel + 1, x, n, hn => by
    simp only [gfFastPowAux]
    by_cases hn0 : n = 0
    · subst hn0; rfl
    · simp only [hn0, ↓reduceIte]
      have hhalf : n / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hn
        omega
      rw [gfFastPowAux_eq_gfPow fuel (GF16.mul x x) (n / 2) hhalf, ← gfPow_two, ← gfPow_mul]
      by_cases hodd : n % 2 = 1
      · simp only [hodd, ↓reduceIte]
        have hdecomp : 2 * (n / 2) + 1 = n := by omega
        conv => rhs; rw [← hdecomp]
        rfl
      · simp only [hodd, ↓reduceIte]
        have hdecomp : 2 * (n / 2) = n := by omega
        rw [hdecomp]

private theorem divImplLoop_eq_pow :
    ∀ n (sq out : BitVec 16),
      (⟨GF16.divImplLoop n sq out⟩ : GF16) = GF16.mul ⟨out⟩ (gfPow ⟨sq⟩ (2 ^ n - 1))
  | 0, sq, out => by
    simp [GF16.divImplLoop, gfPow, mul_one']
  | n + 1, sq, out => by
    simp only [GF16.divImplLoop, mul2U16]
    rw [divImplLoop_eq_pow n (unaccelerated.mul sq sq) (unaccelerated.mul sq out)]
    have hout : (⟨unaccelerated.mul sq out⟩ : GF16) = GF16.mul ⟨out⟩ ⟨sq⟩ := mul_comm' ⟨sq⟩ ⟨out⟩
    have hsq : (⟨unaccelerated.mul sq sq⟩ : GF16) = gfPow ⟨sq⟩ 2 := (gfPow_two ⟨sq⟩).symm
    rw [hout, hsq, ← gfPow_mul, mul_assoc']
    have hpow_ge : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hexp : 2 * (2 ^ n - 1) + 1 = 2 ^ (n + 1) - 1 := by
      rw [Nat.pow_succ]
      omega
    have hstep : GF16.mul ⟨sq⟩ (gfPow ⟨sq⟩ (2 * (2 ^ n - 1))) = gfPow ⟨sq⟩ (2 ^ (n + 1) - 1) := by
      rw [← hexp]
      rfl
    rw [hstep]

private theorem mul_div_one_eq_pow (b : GF16) :
    GF16.mul b (GF16.div GF16.ONE b) = gfPow b 65535 := by
  have hdiv : GF16.div GF16.ONE b = gfPow b 65534 := by
    have h := divImplLoop_eq_pow 15 (GF16.mul b b).value 1#16
    change GF16.div GF16.ONE b = GF16.mul GF16.ONE (gfPow (GF16.mul b b) (2 ^ 15 - 1)) at h
    rw [one_mul', ← gfPow_two, ← gfPow_mul] at h
    exact h
  rw [hdiv]
  rfl

private def genG : GF16 := ⟨2#16⟩

private theorem genG_fast_checks :
    (gfFastPowAux 16 genG 65535 == GF16.ONE) &&
    (gfFastPowAux 16 genG 21845 != GF16.ONE) &&
    (gfFastPowAux 16 genG 13107 != GF16.ONE) &&
    (gfFastPowAux 16 genG 3855 != GF16.ONE) &&
    (gfFastPowAux 16 genG 255 != GF16.ONE) = true := by
  decide +kernel

private theorem genG_pow_65535 : gfPow genG 65535 = GF16.ONE := by
  rw [← gfFastPowAux_eq_gfPow 16 genG 65535 (by decide)]
  have h := genG_fast_checks
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1

private theorem genG_pow_cofactors :
    gfPow genG 21845 ≠ GF16.ONE ∧
    gfPow genG 13107 ≠ GF16.ONE ∧
    gfPow genG 3855 ≠ GF16.ONE ∧
    gfPow genG 255 ≠ GF16.ONE := by
  rw [← gfFastPowAux_eq_gfPow 16 genG 21845 (by decide),
      ← gfFastPowAux_eq_gfPow 16 genG 13107 (by decide),
      ← gfFastPowAux_eq_gfPow 16 genG 3855 (by decide),
      ← gfFastPowAux_eq_gfPow 16 genG 255 (by decide)]
  have h := genG_fast_checks
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem gfPow_gcd :
    ∀ a b, gfPow genG a = GF16.ONE → gfPow genG b = GF16.ONE →
      gfPow genG (Nat.gcd a b) = GF16.ONE := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b ha hb
    by_cases ha0 : a = 0
    · subst ha0
      simpa using hb
    · rw [Nat.gcd_rec]
      apply ih (b % a) (Nat.mod_lt b (by omega)) a ?_ ha
      have hdiv : b = a * (b / a) + b % a := (Nat.div_add_mod b a).symm
      rw [hdiv, gfPow_add, gfPow_mul, ha, gfPow_one_base, one_mul'] at hb
      exact hb

private theorem div_65535_below_256 :
    (List.range 256).all (fun k =>
      !(65535 % k == 0) ||
      ((255 % k == 0) && (k < 2 || k % 3 == 0 || k % 5 == 0 || k % 17 == 0))) = true := by
  decide +kernel

private theorem proper_div_65535 {c : Nat} (hc0 : 0 < c) (hclt : c < 65535) (hdvd : c ∣ 65535) :
    c ∣ 21845 ∨ c ∣ 13107 ∨ c ∣ 3855 ∨ c ∣ 255 := by
  have hall := List.all_eq_true.mp div_65535_below_256
  by_cases hc256 : c < 256
  · have hc_mod : 65535 % c = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have h := hall c (List.mem_range.mpr hc256)
    rw [hc_mod] at h
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      beq_iff_eq] at h
    exact Or.inr (Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero h.1)))
  · rcases hdvd with ⟨q, hq⟩
    have hq_lt256 : q < 256 := by
      by_cases hge : 256 ≤ q
      · have hmul : 256 * 256 ≤ c * q := Nat.mul_le_mul (by omega) hge
        omega
      · omega
    have hq_ge2 : ¬(q < 2) := by
      intro hlt2
      have hq01 : q = 0 ∨ q = 1 := by omega
      rcases hq01 with rfl | rfl <;> omega
    have hq_mod : 65535 % q = 0 := Nat.mod_eq_zero_of_dvd ⟨c, by rw [Nat.mul_comm]; exact hq⟩
    have h := hall q (List.mem_range.mpr hq_lt256)
    rw [hq_mod] at h
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rcases h.2 with ((hq2 | h3) | h5) | h17
    · exact absurd hq2 hq_ge2
    · refine Or.inl ⟨q / 3, ?_⟩
      have hq3 : 3 * (q / 3) = q := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h3)
      have hprod : 3 * (c * (q / 3)) = 65535 := by
        calc 3 * (c * (q / 3)) = c * (3 * (q / 3)) := by rw [Nat.mul_left_comm]
        _ = c * q := by rw [hq3]
        _ = 65535 := hq.symm
      omega
    · refine Or.inr (Or.inl ⟨q / 5, ?_⟩)
      have hq5 : 5 * (q / 5) = q := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h5)
      have hprod : 5 * (c * (q / 5)) = 65535 := by
        calc 5 * (c * (q / 5)) = c * (5 * (q / 5)) := by rw [Nat.mul_left_comm]
        _ = c * q := by rw [hq5]
        _ = 65535 := hq.symm
      omega
    · refine Or.inr (Or.inr (Or.inl ⟨q / 17, ?_⟩))
      have hq17 : 17 * (q / 17) = q := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h17)
      have hprod : 17 * (c * (q / 17)) = 65535 := by
        calc 17 * (c * (q / 17)) = c * (17 * (q / 17)) := by rw [Nat.mul_left_comm]
        _ = c * q := by rw [hq17]
        _ = 65535 := hq.symm
      omega

private theorem genG_pow_ne_one {d : Nat} (hd0 : 0 < d) (hdlt : d < 65535) :
    gfPow genG d ≠ GF16.ONE := by
  intro hd1
  let c := Nat.gcd d 65535
  have hc1 : gfPow genG c = GF16.ONE := gfPow_gcd d 65535 hd1 genG_pow_65535
  have hcd : c ∣ d := Nat.gcd_dvd_left d 65535
  have hc6 : c ∣ 65535 := Nat.gcd_dvd_right d 65535
  have hcle : c ≤ d := Nat.le_of_dvd hd0 hcd
  have hc0 : 0 < c := by
    by_cases hz : c = 0
    · rw [hz] at hcd
      have hd_zero : d = 0 := Nat.eq_zero_of_zero_dvd hcd
      omega
    · omega
  have hpow_dvd : ∀ m, c ∣ m → gfPow genG m = GF16.ONE := by
    intro m ⟨k, hk⟩
    rw [hk, gfPow_mul, hc1, gfPow_one_base]
  rcases genG_pow_cofactors with ⟨h21845, h13107, h3855, h255⟩
  rcases proper_div_65535 hc0 (by omega) hc6 with hm | hm | hm | hm
  · exact h21845 (hpow_dvd 21845 hm)
  · exact h13107 (hpow_dvd 13107 hm)
  · exact h3855 (hpow_dvd 3855 hm)
  · exact h255 (hpow_dvd 255 hm)

private theorem genG_pow_ne_zero {i : Nat} (hi : i < 65535) : gfPow genG i ≠ GF16.ZERO := by
  intro hz
  have h65535 : gfPow genG (i + (65535 - i)) = GF16.ONE := by
    have hsum : i + (65535 - i) = 65535 := by omega
    rw [hsum]
    exact genG_pow_65535
  rw [gfPow_add, hz, zero_mul'] at h65535
  exact zero_ne_one' h65535

private theorem genG_pow_step_cancel {i d : Nat} (hi : i < 65535)
    (heq : gfPow genG i = gfPow genG (i + d)) : gfPow genG d = GF16.ONE := by
  have hmul := congrArg (fun x => GF16.mul (gfPow genG (65535 - i)) x) heq
  simp only [gfPow_add] at hmul
  rw [← mul_assoc'] at hmul
  have hinv : GF16.mul (gfPow genG (65535 - i)) (gfPow genG i) = GF16.ONE := by
    rw [← gfPow_add, show 65535 - i + i = 65535 by omega]
    exact genG_pow_65535
  rw [hinv, one_mul'] at hmul
  exact hmul.symm

private theorem genG_pow_inj {i j : Nat} (hi : i < 65535) (hj : j < 65535)
    (heq : gfPow genG i = gfPow genG j) : i = j := by
  by_cases hlt : i < j
  · exfalso
    have hj_eq : j = i + (j - i) := by omega
    rw [hj_eq] at heq
    exact genG_pow_ne_one (by omega) (by omega) (genG_pow_step_cancel hi heq)
  · by_cases hgt : j < i
    · exfalso
      have hi_eq : i = j + (i - j) := by omega
      rw [hi_eq] at heq
      exact genG_pow_ne_one (by omega) (by omega) (genG_pow_step_cancel hj heq.symm)
    · omega

private theorem nat_inj_surj :
    ∀ n (f : Nat → Nat),
      (∀ k, k < n → f k < n) →
      (∀ i j, i < n → j < n → f i = f j → i = j) →
      ∀ y, y < n → ∃ k, k < n ∧ f k = y
  | 0, _, _, _, y, hy => by omega
  | n + 1, f, hbdd, hinj, y, hy => by
    let g : Nat → Nat := fun i => if f i = n then f n else f i
    have hgbdd : ∀ k, k < n → g k < n := by
      intro k hk
      have hfk := hbdd k (by omega)
      have hfn := hbdd n (by omega)
      by_cases hEq : f k = n
      · have hfn_ne : f n ≠ n := by
          intro hfn_eq
          have := hinj k n (by omega) (by omega) (hEq.trans hfn_eq.symm)
          omega
        simp only [g, hEq, ↓reduceIte]
        omega
      · simp only [g, hEq, ↓reduceIte]
        omega
    have hginj : ∀ i j, i < n → j < n → g i = g j → i = j := by
      intro i j hi hj hgij
      by_cases hfi : f i = n <;> by_cases hfj : f j = n
      · exact hinj i j (by omega) (by omega) (hfi.trans hfj.symm)
      · simp only [g, hfi, hfj, ↓reduceIte] at hgij
        have := hinj n j (by omega) (by omega) hgij
        omega
      · simp only [g, hfi, hfj, ↓reduceIte] at hgij
        have := hinj i n (by omega) (by omega) hgij
        omega
      · simp only [g, hfi, hfj, ↓reduceIte] at hgij
        exact hinj i j (by omega) (by omega) hgij
    have ih := nat_inj_surj n g hgbdd hginj
    by_cases hyfn : y = f n
    · exact ⟨n, by omega, hyfn.symm⟩
    · by_cases hyn : y = n
      · rw [hyn]
        have hfn_lt : f n < n := by
          have := hbdd n (by omega)
          omega
        rcases ih (f n) hfn_lt with ⟨k, hk, hgk⟩
        refine ⟨k, by omega, ?_⟩
        by_cases hfk : f k = n
        · exact hfk
        · simp only [g, hfk, ↓reduceIte] at hgk
          have := hinj k n (by omega) (by omega) hgk
          omega
      · rcases ih y (by omega) with ⟨k, hk, hgk⟩
        refine ⟨k, by omega, ?_⟩
        by_cases hfk : f k = n
        · simp only [g, hfk, ↓reduceIte] at hgk
          exact absurd hgk.symm hyfn
        · simp only [g, hfk, ↓reduceIte] at hgk
          exact hgk

/-- Multiplicative inverse: `b * (1 / b) = 1` for `b ≠ 0`. -/
theorem mul_inv_cancel' (b : GF16) (hb : b ≠ GF16.ZERO) :
    GF16.mul b (GF16.div GF16.ONE b) = GF16.ONE := by
  let f : Nat → Nat := fun k => if k = 65535 then 0 else (gfPow genG k).value.toNat
  have hfbdd : ∀ k, k < 65536 → f k < 65536 := by
    intro k hk
    by_cases hkEq : k = 65535
    · simp [f, hkEq]
    · simp only [f, hkEq, ↓reduceIte]
      exact (gfPow genG k).value.isLt
  have hfinj : ∀ i j, i < 65536 → j < 65536 → f i = f j → i = j := by
    intro i j hi hj hfij
    have hnz : ∀ m, m < 65535 → (gfPow genG m).value.toNat ≠ 0 := by
      intro m hm hz
      apply genG_pow_ne_zero hm
      apply gf16_ext
      exact BitVec.eq_of_toNat_eq hz
    by_cases hiEq : i = 65535 <;> by_cases hjEq : j = 65535
    · omega
    · simp only [f, hiEq, hjEq, ↓reduceIte] at hfij
      exact absurd hfij.symm (hnz j (by omega))
    · simp only [f, hiEq, hjEq, ↓reduceIte] at hfij
      exact absurd hfij (hnz i (by omega))
    · simp only [f, hiEq, hjEq, ↓reduceIte] at hfij
      exact genG_pow_inj (by omega) (by omega) (gf16_ext (BitVec.eq_of_toNat_eq hfij))
  rcases nat_inj_surj 65536 f hfbdd hfinj b.value.toNat b.value.isLt with ⟨k, hk, hfk⟩
  have hbnz : b.value.toNat ≠ 0 := by
    intro hz
    apply hb
    exact gf16_ext (BitVec.eq_of_toNat_eq hz)
  have hk_ne : k ≠ 65535 := by
    intro hkEq
    simp only [f, hkEq, ↓reduceIte] at hfk
    exact hbnz hfk.symm
  simp only [f, hk_ne, ↓reduceIte] at hfk
  have hb_eq : b = gfPow genG k := (gf16_ext (BitVec.eq_of_toNat_eq hfk)).symm
  rw [mul_div_one_eq_pow, hb_eq, ← gfPow_mul, Nat.mul_comm, gfPow_mul, genG_pow_65535,
      gfPow_one_base]

private theorem divImplLoop_mul_out :
    ∀ n (sq a : BitVec 16),
      (⟨GF16.divImplLoop n sq a⟩ : GF16) = GF16.mul ⟨a⟩ ⟨GF16.divImplLoop n sq 1#16⟩
  | 0, sq, a => by
    simp only [GF16.divImplLoop]
    exact (mul_one' ⟨a⟩).symm
  | n + 1, sq, a => by
    simp only [GF16.divImplLoop, mul2U16]
    rw [divImplLoop_mul_out n (unaccelerated.mul sq sq) (unaccelerated.mul sq a)]
    rw [divImplLoop_mul_out n (unaccelerated.mul sq sq) (unaccelerated.mul sq 1#16)]
    have hsq1 : (⟨unaccelerated.mul sq 1#16⟩ : GF16) = ⟨sq⟩ := mul_one' ⟨sq⟩
    have hsqa : (⟨unaccelerated.mul sq a⟩ : GF16) = GF16.mul ⟨a⟩ ⟨sq⟩ := mul_comm' ⟨sq⟩ ⟨a⟩
    rw [hsq1, hsqa, mul_assoc']

/-- Division is multiplication by `1 / b` (for every `b`, including `0`). -/
theorem div_eq_mul_inv' (a b : GF16) :
    GF16.div a b = GF16.mul a (GF16.div GF16.ONE b) := by
  simpa [GF16.div, GF16.divImpl, GF16.ONE] using
    divImplLoop_mul_out 15 (GF16.mul b b).value a.value

/-- `GF16.div GF16.ONE GF16.ZERO = GF16.ZERO` (`divImpl` has no zero guard). -/
theorem inv_zero' : GF16.div GF16.ONE GF16.ZERO = GF16.ZERO := by
  decide +kernel

theorem constSub_eq_add (a b : GF16) : GF16.constSub a b = GF16.add a b := rfl

theorem constMul_eq_mul (a b : GF16) : GF16.constMul a b = GF16.mul a b := rfl

namespace ConstDiv

theorem constDivLoop_eq_divImplLoop (n : Nat) (sq out : GF16) :
    GF16.constDivLoop n sq out = ⟨GF16.divImplLoop n (GF16.mul sq sq).value out.value⟩ := by
  induction n generalizing sq out with
  | zero => rfl
  | succ n ih =>
    simp only [GF16.constDivLoop, GF16.divImplLoop, mul2U16]
    rw [ih]
    exact congrArg
      (fun x : GF16 => (⟨GF16.divImplLoop n (GF16.mul (GF16.mul sq sq) (GF16.mul sq sq)).value x.value⟩ : GF16))
      (mul_comm' out (GF16.mul sq sq))

end ConstDiv

theorem constDiv_eq_div (a b : GF16) : GF16.constDiv a b = GF16.div a b := by
  exact ConstDiv.constDivLoop_eq_divImplLoop 15 b a

theorem parallelMult_eq_map (a : GF16) (xs : List GF16) :
    parallelMult a xs = xs.map (fun x => GF16.mul x a) := by
  match xs with
  | [] => rfl
  | [x] => rfl
  | x1 :: x2 :: rest =>
    simp only [parallelMult, mul2U16, List.map_cons]
    rw [mul_comm' x1 a, mul_comm' x2 a, parallelMult_eq_map a rest]
    rfl

end CryptoVerification.SpqrV1Sync.GF16Field
