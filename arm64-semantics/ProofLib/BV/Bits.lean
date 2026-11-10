/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.BV.BitsAttr
import Arm64.Trusted.Spec.SepLogic

/-!
# Bit-Structure Decision Procedure for `BitVec`

Defines the `bv_bits` tactic and `@[bv_bits_nat]` rewrite rules and simprocs for closing `BitVec`,
`Nat`, and `Bool` goals combining arithmetic with literal masks, bit-slice extraction, `++`,
`setWidth`, disjoint `|||`, comparisons, and `if`-`then`-`else` expressions via `simp` and `omega`.

## Proof strategy

1. Introduce binders and generalize every closed non-`Prop` `if c then t else e` subterm into a
   fresh variable `v` with `(c ∧ v = t) ∨ (¬c ∧ v = e)`.
2. Rewrite to `Nat` using `simp only [bitvec_to_nat, bv_bits_nat]` and custom simprocs:
   * `x &&& c` (literal `c`) peels runs of set bits `[a, a + n)` into `x / 2^a % 2^n * 2^a`
     (`NatLemmas.and_peel`, `SimprocLemmas.and_peel`).
   * `a ||| b` with provably disjoint bit ranges rewrites to `a + b` (`SimprocLemmas.or_eq_add`).
   * `x ||| c` and `x ^^^ c` for literal `c` reduce to `&&&` (`SimprocLemmas.or_eq`,
     `SimprocLemmas.xor_eq`).
3. Add linear bound facts for any remaining `&&&`, `|||`, and `^^^` atoms, then close the goal
   with `omega`.
-/

namespace ProofLib.BV.Bits

@[expose] public section

/-! ## `Nat` bit lemmas -/

namespace NatLemmas


/-- A run of ones `[a, a+n)` selects `n` bits of `x` starting at bit `a`. -/
theorem and_run (x a n : Nat) : x &&& ((2 ^ n - 1) <<< a) = (x >>> a % 2 ^ n) <<< a := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases h : a ≤ i
  · have : a + (i - a) = i := by omega
    simp [h, this, Bool.and_comm]
  · simp [h]

theorem or_eq_add_of_dvd_lt {a b k : Nat} (ha : a % 2 ^ k = 0) (hb : b < 2 ^ k) :
    a ||| b = a + b := by
  have : a = (a / 2 ^ k) <<< k := by
    rw [Nat.shiftLeft_eq, Nat.mul_comm]; have := Nat.div_add_mod a (2 ^ k); rw [ha] at this
    omega
  rw [this, ← Nat.shiftLeft_add_eq_or_of_lt hb]

theorem or_eq_add_of_lt_dvd {a b k : Nat} (ha : a < 2 ^ k) (hb : b % 2 ^ k = 0) :
    a ||| b = a + b := by
  rw [Nat.or_comm, or_eq_add_of_dvd_lt hb ha, Nat.add_comm]

theorem or_add_and (x y : Nat) : (x ||| y) + (x &&& y) = x + y := by
  induction x using Nat.strongRecOn generalizing y with
  | ind x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    have h1 := ih (x / 2) (Nat.div_lt_self hx (by decide)) (y / 2)
    rw [← Nat.or_div_two, ← Nat.and_div_two] at h1
    have e1 := Nat.div_add_mod (x ||| y) 2
    have e2 := Nat.div_add_mod (x &&& y) 2
    have e3 := Nat.div_add_mod x 2
    have e4 := Nat.div_add_mod y 2
    have ho := @Nat.or_mod_two_eq_one x y
    have ha := @Nat.and_mod_two_eq_one x y
    have : x % 2 < 2 := Nat.mod_lt _ (by decide)
    have : y % 2 < 2 := Nat.mod_lt _ (by decide)
    have : (x ||| y) % 2 < 2 := Nat.mod_lt _ (by decide)
    have : (x &&& y) % 2 < 2 := Nat.mod_lt _ (by decide)
    omega

theorem xor_add_and (x y : Nat) : (x ^^^ y) + 2 * (x &&& y) = x + y := by
  induction x using Nat.strongRecOn generalizing y with
  | ind x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    have h1 := ih (x / 2) (Nat.div_lt_self hx (by decide)) (y / 2)
    rw [← Nat.xor_div_two, ← Nat.and_div_two] at h1
    have e1 := Nat.div_add_mod (x ^^^ y) 2
    have e2 := Nat.div_add_mod (x &&& y) 2
    have e3 := Nat.div_add_mod x 2
    have e4 := Nat.div_add_mod y 2
    have hx := @Nat.xor_mod_two_eq_one x y
    have ha := @Nat.and_mod_two_eq_one x y
    have : x % 2 < 2 := Nat.mod_lt _ (by decide)
    have : y % 2 < 2 := Nat.mod_lt _ (by decide)
    have : (x ^^^ y) % 2 < 2 := Nat.mod_lt _ (by decide)
    have : (x &&& y) % 2 < 2 := Nat.mod_lt _ (by decide)
    omega

theorem or_eq_sub_and (x y : Nat) : x ||| y = x + y - (x &&& y) := by
  have := or_add_and x y; omega

theorem xor_eq_sub_and (x y : Nat) : x ^^^ y = x + y - 2 * (x &&& y) := by
  have := xor_add_and x y; omega

theorem or_le_add (x y : Nat) : x ||| y ≤ x + y := by
  have := or_add_and x y; omega

theorem xor_le_add (x y : Nat) : x ^^^ y ≤ x + y := by
  have := xor_add_and x y; omega

/-- Peel the top run of ones off a literal mask `c = r + (2^n - 1) * 2^a` (with `r < 2^a`). -/
theorem and_peel (x c r a n : Nat) (h : c = r + (2 ^ n - 1) * 2 ^ a ∧ r < 2 ^ a) :
    x &&& c = x / 2 ^ a % 2 ^ n * 2 ^ a + (x &&& r) := by
  obtain ⟨rfl, hr⟩ := h
  have hsplit : r + (2 ^ n - 1) * 2 ^ a = ((2 ^ n - 1) <<< a) ||| r := by
    rw [Nat.shiftLeft_eq, Nat.or_comm, or_eq_add_of_lt_dvd hr (by simp [Nat.mul_mod_left])]
  rw [hsplit, Nat.and_or_distrib_left, and_run, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  apply or_eq_add_of_dvd_lt (by simp [Nat.mul_mod_left]) (Nat.and_lt_two_pow x hr)



/-! Pushing `% m` through sums whose other summands are multiples of `m` (literal side
conditions `n % m = 0` are discharged by `Nat.reduceMod` during `simp`). -/

theorem mod_mod_dvd (a n m : Nat) (h : n % m = 0) : a % n % m = a % m :=
  Nat.mod_mod_of_dvd a (Nat.dvd_of_mod_eq_zero h)

theorem add_mod_mod_dvd (a b n m : Nat) (h : n % m = 0) : (a + b % n) % m = (a + b) % m := by
  rw [Nat.add_mod, mod_mod_dvd b n m h, ← Nat.add_mod]

theorem mod_add_mod_dvd (a b n m : Nat) (h : n % m = 0) : (a % n + b) % m = (a + b) % m := by
  rw [Nat.add_mod, mod_mod_dvd a n m h, ← Nat.add_mod]

theorem mul_mod_dvd (a k m : Nat) (h : k % m = 0) : a * k % m = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left_of_dvd (Nat.dvd_of_mod_eq_zero h) a)

theorem mul_add_mod_dvd (a k b m : Nat) (h : k % m = 0) : (a * k + b) % m = b % m := by
  rw [Nat.add_mod, mul_mod_dvd a k m h, Nat.zero_add, Nat.mod_mod]

theorem add_mul_mod_dvd (a k b m : Nat) (h : k % m = 0) : (b + a * k) % m = b % m := by
  rw [Nat.add_comm, mul_add_mod_dvd a k b m h]

theorem mod_mod_le (a n m : Nat) (h : 0 < n ∧ n ≤ m) : a % n % m = a % n :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt a h.1) h.2)

theorem mod_mul_mod_le (a n k m : Nat) (h : 0 < n ∧ 0 < k ∧ n * k ≤ m) :
    a % n * k % m = a % n * k :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt a h.1) h.2.1) h.2.2)

theorem add_mul_div_dvd (a b k m : Nat) (h : k % m = 0 ∧ 0 < m) :
    (a + b * k) / m = a / m + b * (k / m) := by
  have hk : k = m * (k / m) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.1)).symm
  conv => lhs; rw [hk, ← Nat.mul_assoc, Nat.mul_comm b m, Nat.mul_assoc,
                   Nat.add_mul_div_left a _ h.2]

theorem mul_add_div_dvd (a k b m : Nat) (h : k % m = 0 ∧ 0 < m) :
    (a * k + b) / m = a * (k / m) + b / m := by
  rw [Nat.add_comm, add_mul_div_dvd b a k m h, Nat.add_comm]

end NatLemmas

/-! ## `BitVec`-to-`Nat` bridge lemmas -/

namespace BVLemmas
universe u

theorem toNat_mod_le {w : Nat} (x : BitVec w) (m : Nat) (h : 2 ^ w ≤ m) :
    x.toNat % m = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt h)

theorem toNat_div_le {w : Nat} (x : BitVec w) (m : Nat) (h : 2 ^ w ≤ m) :
    x.toNat / m = 0 :=
  Nat.div_eq_of_lt (Nat.lt_of_lt_of_le x.isLt h)

theorem toNat_mul_mod_le {w : Nat} (x : BitVec w) (k m : Nat) (h : 2 ^ w * k ≤ m) :
    x.toNat * k % m = x.toNat * k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right x.isLt hk) h)

theorem toNat_append_mul {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, Nat.shiftLeft_eq]
  exact NatLemmas.or_eq_add_of_dvd_lt (by simp [Nat.mul_mod_left]) y.isLt

theorem toNat_extractLsb' {n : Nat} (s m : Nat) (x : BitVec n) :
    (x.extractLsb' s m).toNat = x.toNat / 2 ^ s % 2 ^ m := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem getLsbD_eq_decide {n : Nat} (x : BitVec n) (i : Nat) :
    x.getLsbD i = decide (i < n ∧ x.toNat / 2 ^ i % 2 = 1) := by
  rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : i < n
  · simp [h]
  · have : x.toNat < 2 ^ i :=
      Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    simp [h, Nat.div_eq_of_lt this]

theorem ite_prop (c : Prop) [Decidable c] (p q : Prop) :
    (if c then p else q) = ((c ∧ p) ∨ (¬c ∧ q)) := by
  by_cases h : c <;> simp [h]

theorem ite_cases {α : Sort u} (c : Prop) [Decidable c] (t e : α) :
    (c ∧ (if c then t else e) = t) ∨ (¬c ∧ (if c then t else e) = e) := by
  by_cases h : c <;> simp [h]

/-- Signed `<` as a `Nat` fact: equal sign bits reduce to unsigned `<`, distinct sign bits to its negation. -/
theorem slt_eq_decide' {w : Nat} (x y : BitVec w) :
    x.slt y = decide ((2 ^ (w - 1) ≤ x.toNat ↔ 2 ^ (w - 1) ≤ y.toNat) ↔ x.toNat < y.toNat) := by
  rw [BitVec.slt_eq_ult, BitVec.msb_eq_decide, BitVec.msb_eq_decide, BitVec.ult_eq_decide]
  by_cases h1 : 2 ^ (w - 1) ≤ x.toNat <;> by_cases h2 : 2 ^ (w - 1) ≤ y.toNat <;>
    by_cases h3 : x.toNat < y.toNat <;> simp [h1, h2, h3]

/-- Signed `<=` as a `Nat` fact. -/
theorem sle_eq_decide' {w : Nat} (x y : BitVec w) :
    x.sle y = decide ((2 ^ (w - 1) ≤ x.toNat ↔ 2 ^ (w - 1) ≤ y.toNat) ↔ x.toNat ≤ y.toNat) := by
  rw [BitVec.sle_eq_not_slt, slt_eq_decide']
  by_cases h1 : 2 ^ (w - 1) ≤ x.toNat <;> by_cases h2 : 2 ^ (w - 1) ≤ y.toNat <;>
    by_cases h3 : x.toNat ≤ y.toNat <;> simp [h1, h2, h3] <;> omega

/-! `==` and `!=` at concrete types, avoiding `LawfulBEq` synthesis in `beq_iff_eq`. -/
theorem beq_bv {w : Nat} (x y : BitVec w) : (x == y) = decide (x = y) := rfl
theorem bne_bv {w : Nat} (x y : BitVec w) : (x != y) = !decide (x = y) := rfl
theorem beq_nat (x y : Nat) : (x == y) = decide (x = y) := by by_cases h : x = y <;> simp [h]
theorem bne_nat (x y : Nat) : (x != y) = !decide (x = y) := by by_cases h : x = y <;> simp [h]
theorem beq_bool (x y : Bool) : (x == y) = decide (x = y) := by cases x <;> cases y <;> rfl
theorem bne_bool (x y : Bool) : (x != y) = !decide (x = y) := by cases x <;> cases y <;> rfl

end BVLemmas


/-! ## Lemmas used by the simprocs (side conditions discharged by `decide` or `omega`) -/

namespace SimprocLemmas

theorem and_mask (x c m n : Nat) (h : m = 2 ^ n ∧ c + 1 = m) : x &&& c = x % m := by
  obtain ⟨rfl, hc⟩ := h; rw [show c = 2 ^ n - 1 by omega]; exact Nat.and_two_pow_sub_one_eq_mod x n

theorem mask_and (x c m n : Nat) (h : m = 2 ^ n ∧ c + 1 = m) : c &&& x = x % m := by
  rw [Nat.and_comm]; exact and_mask x c m n h

theorem and_peel (x c r A N a n : Nat)
    (h : A = 2 ^ a ∧ N = 2 ^ n ∧ c = r + (N - 1) * A ∧ r < A) :
    x &&& c = x / A % N * A + (x &&& r) := by
  obtain ⟨rfl, rfl, h1, h2⟩ := h; exact NatLemmas.and_peel x c r a n ⟨h1, h2⟩

theorem peel_and (x c r A N a n : Nat)
    (h : A = 2 ^ a ∧ N = 2 ^ n ∧ c = r + (N - 1) * A ∧ r < A) :
    c &&& x = x / A % N * A + (x &&& r) := by
  rw [Nat.and_comm]; exact and_peel x c r A N a n h

theorem and_zero_of_disj (a b k : Nat) (h : (a < 2 ^ k ∧ b % 2 ^ k = 0) ∨ (b < 2 ^ k ∧ a % 2 ^ k = 0)) :
    a &&& b = 0 := by
  have hab := NatLemmas.or_add_and a b
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := NatLemmas.or_eq_add_of_lt_dvd h1 h2; omega
  · have := NatLemmas.or_eq_add_of_dvd_lt h2 h1; omega

theorem or_eq (a b : Nat) : a ||| b = a + b - (a &&& b) := NatLemmas.or_eq_sub_and a b
theorem xor_eq (a b : Nat) : a ^^^ b = a + b - 2 * (a &&& b) := NatLemmas.xor_eq_sub_and a b

theorem or_eq_add (a b : Nat) (h : a &&& b = 0) : a ||| b = a + b := by
  have := NatLemmas.or_add_and a b; omega
theorem xor_eq_add (a b : Nat) (h : a &&& b = 0) : a ^^^ b = a + b := by
  have := NatLemmas.xor_add_and a b; omega

theorem and_bounds (a b : Nat) : a &&& b ≤ a ∧ a &&& b ≤ b := ⟨Nat.and_le_left, Nat.and_le_right⟩
theorem or_bounds (a b : Nat) : a ≤ a ||| b ∧ b ≤ a ||| b ∧ a ||| b ≤ a + b :=
  ⟨Nat.left_le_or, Nat.right_le_or, NatLemmas.or_le_add a b⟩
theorem xor_bounds (a b : Nat) : a ^^^ b ≤ a + b := NatLemmas.xor_le_add a b
theorem or_lt_pow (a b k : Nat) : 2 ^ k ≤ a ∨ 2 ^ k ≤ b ∨ a ||| b < 2 ^ k := by
  by_cases ha : a < 2 ^ k
  · by_cases hb : b < 2 ^ k
    · exact .inr (.inr (Nat.or_lt_two_pow ha hb))
    · exact .inr (.inl (by omega))
  · exact .inl (by omega)
theorem xor_lt_pow (a b k : Nat) : 2 ^ k ≤ a ∨ 2 ^ k ≤ b ∨ a ^^^ b < 2 ^ k := by
  by_cases ha : a < 2 ^ k
  · by_cases hb : b < 2 ^ k
    · exact .inr (.inr (Nat.xor_lt_two_pow ha hb))
    · exact .inr (.inl (by omega))
  · exact .inl (by omega)

end SimprocLemmas

end

/-! ## Simprocs and tactic -/

public meta section

namespace Meta
open Lean Meta Elab Tactic

/-- `Nat` literal, including `2 ^ k` with literal `k ≤ 4096`. -/
partial def natVal? (e : Expr) : Option Nat :=
  match e.nat? with
  | some n => some n
  | none => match e.rawNatLit? with
    | some n => some n
    | none =>
      if e.isAppOfArity ``HPow.hPow 6 then
        match natVal? (e.getArg! 4), natVal? (e.getArg! 5) with
        | some b, some k => if k ≤ 4096 && (b ≤ 2 || k ≤ 64) && b < 2 ^ 4096 then some (b ^ k) else none
        | _, _ => none
      else none

def isNatTy (e : Expr) : Bool := e.isConstOf ``Nat

/-- `(op, a, b)` for a homogeneous `Nat` binary operator application. -/
def natBin? (op : Name) (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity op 6 && isNatTy (e.getArg! 0) && isNatTy (e.getArg! 1) then
    some (e.getArg! 4, e.getArg! 5)
  else none

def isPow2 (c : Nat) : Option Nat :=
  if c > 0 && c &&& (c - 1) == 0 then some (Nat.log2 c) else none

def lowZeros (c : Nat) : Nat := Id.run do
  if c == 0 then return 4096
  let mut k := 0
  let mut v := c
  while v % 2 == 0 do
    v := v / 2; k := k + 1
  return k

/-- Bit range estimate: value is a multiple of `2^tz` and (if `bl = some b`) below `2^b`. -/
structure Rng where
  tz : Nat := 0
  bl : Option Nat := none
  deriving Inhabited

def omin : Option Nat → Option Nat → Option Nat
  | some a, some b => some (min a b) | some a, none => some a | none, b => b
def omax : Option Nat → Option Nat → Option Nat
  | some a, some b => some (max a b) | _, _ => none

partial def rng (e : Expr) : Rng :=
  match natVal? e with
  | some c => { tz := lowZeros c, bl := some (if c == 0 then 0 else Nat.log2 c + 1) }
  | none =>
  if e.isAppOfArity ``BitVec.toNat 2 then
    { bl := natVal? (e.getArg! 0) }
  else if let some (x, m) := natBin? ``HMod.hMod e then
    let rx := rng x
    match natVal? m with
    | some m => match isPow2 m with
      | some k => { tz := min rx.tz k, bl := omin rx.bl (some k) }
      | none => if m == 0 then rx else { bl := omin rx.bl (some (Nat.log2 m + 1)) }
    | none => { bl := rx.bl }
  else if let some (x, y) := natBin? ``HMul.hMul e then
    let rx := rng x; let ry := rng y
    let tz := min 4096 (rx.tz + ry.tz)
    let pow? (z : Expr) := (natVal? z).bind isPow2
    let bl := match pow? x, pow? y with
      | some k, _ => ry.bl.map (· + k)
      | _, some k => rx.bl.map (· + k)
      | _, _ => match rx.bl, ry.bl with | some a, some b => some (a + b) | _, _ => none
    { tz, bl }
  else if let some (x, y) := natBin? ``HDiv.hDiv e then
    let rx := rng x
    match (natVal? y).bind isPow2 with
    | some k => { tz := rx.tz - k, bl := rx.bl.map (· - k) }
    | none => { bl := rx.bl }
  else if let some (x, y) := natBin? ``HAdd.hAdd e then
    let rx := rng x; let ry := rng y
    { tz := min rx.tz ry.tz, bl := (omax rx.bl ry.bl).map (· + 1) }
  else if let some (x, y) := natBin? ``HSub.hSub e then
    let rx := rng x; let ry := rng y
    { tz := min rx.tz ry.tz, bl := rx.bl }
  else if let some (x, y) := natBin? ``HAnd.hAnd e then
    let rx := rng x; let ry := rng y
    { tz := max rx.tz ry.tz, bl := omin rx.bl ry.bl }
  else if let some (x, y) := (natBin? ``HOr.hOr e).orElse fun _ => natBin? ``HXor.hXor e then
    let rx := rng x; let ry := rng y
    { tz := min rx.tz ry.tz, bl := omax rx.bl ry.bl }
  else {}

/-- Candidate exponents `k` for `a ||| b < 2^k` facts: from literals `2^k`, `2^k - 1` in `es`. -/
partial def litExps (es : Array Expr) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut seen : Std.HashSet Expr := {}
  let mut todo := es.toList
  let mut fuel := 100000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | e :: rest =>
      todo := rest
      if seen.contains e then continue
      seen := seen.insert e
      if let some c := e.nat? then
        for k in [isPow2 c, isPow2 (c + 1)] do
          if let some k := k then
            if k > 0 && k ≤ 128 && !out.contains k then out := out.push k
      else match e with
        | .app f a => todo := f :: a :: todo
        | .mdata _ b => todo := b :: todo
        | _ => pure ()
  return out

/-- Bound facts for the bitwise atoms of `es` (for `omega`). With `withPow`, also the
disjunctive facts `2^k ≤ a ∨ 2^k ≤ b ∨ a ||| b < 2^k` (costly case splits for `omega`). -/
partial def bitFacts (es : Array Expr) (withPow := true) : MetaM (Array Expr) := do
  let seen ← IO.mkRef ({} : Std.HashSet Expr)
  let out ← IO.mkRef (#[] : Array Expr)
  let exps := litExps es
  let rec go (e : Expr) : MetaM Unit := do
    -- memoize every visited subterm: hypotheses share large subterms (DAG, not tree)
    if (← seen.get).contains e then return
    seen.modify (·.insert e)
    match e with
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
    if e.hasLooseBVars then return
    let push (x : Expr) : MetaM Unit := out.modify (·.push x)
    if let some (a, b) := natBin? ``HAnd.hAnd e then
      push (mkApp2 (mkConst ``SimprocLemmas.and_bounds) a b)
    else
      let orx? := match natBin? ``HOr.hOr e with
        | some ab => some (true, ab)
        | none => (natBin? ``HXor.hXor e).map (false, ·)
      if let some (isOr, a, b) := orx? then
        push (mkApp2 (mkConst (if isOr then ``SimprocLemmas.or_bounds else ``SimprocLemmas.xor_bounds)) a b)
        let ks := if !withPow then #[] else match omax (rng a).bl (rng b).bl with
          | some k => if exps.contains k then exps else exps.push k
          | none => exps
        for k in ks do
          push (mkApp3 (mkConst (if isOr then ``SimprocLemmas.or_lt_pow else ``SimprocLemmas.xor_lt_pow))
            a b (mkNatLit k))
  for e in es do go e
  out.get

/-- Prove `p` with `omega`, given `facts`; restores state on failure. -/
def omegaProve? (p : Expr) (facts : Array Expr) : MetaM (Option Expr) := do
  let s ← saveState
  try
    let g ← mkFreshExprMVar p
    let some g' ← g.mvarId!.falseOrByContra | return none
    g'.withContext do
      let lctx ← getLCtx
      let hyp := (lctx.lastDecl.get!).toExpr
      Lean.Elab.Tactic.Omega.omega (hyp :: facts.toList) g'
    return some (← instantiateMVars g)
  catch _ =>
    s.restore; return none

/-- Local `Prop` hypotheses mentioning a free variable of `es` (at most `max`). -/
def relevantHyps (es : Array Expr) (max := 8) : MetaM (Array Expr) := do
  let fvs := es.foldl (fun s e => collectFVars s e) {}
  if fvs.fvarIds.isEmpty then return #[]
  let mut out := #[]
  for d in ← getLCtx do
    if out.size ≥ max then break
    if d.isImplementationDetail || d.isLet then continue
    let ty ← instantiateMVars d.type
    if !(ty.hasAnyFVar fvs.fvarSet.contains) then continue
    if !(← Meta.isProp ty) then continue
    out := out.push d.toExpr
  return out

/-- Try to prove `a &&& b = 0` from the bit range estimates and `omega`. If the purely syntactic
estimate gives no split point, try `k = tz` of either operand using relevant hypotheses. -/
def proveAndZero? (a b : Expr) : MetaM (Option Expr) := do
  let ra := rng a; let rb := rng b
  let k? : Option Nat :=
    match ra.bl, rb.bl with
    | some x, _ => if x ≤ rb.tz then some x else
        match rb.bl with | some y => if y ≤ ra.tz then some y else none | none => none
    | none, some y => if y ≤ ra.tz then some y else none
    | none, none => none
  let attempt (k : Nat) (extra : Array Expr) : MetaM (Option Expr) := do
    if k > 4096 then return none
    let lemType ← inferType (mkApp3 (mkConst ``SimprocLemmas.and_zero_of_disj) a b (mkNatLit k))
    let .forallE _ hTy _ _ := lemType | return none
    let facts ← bitFacts #[a, b]
    let some h ← omegaProve? hTy (facts ++ extra) | return none
    return some (mkApp4 (mkConst ``SimprocLemmas.and_zero_of_disj) a b (mkNatLit k) h)
  if let some k := k? then return ← attempt k #[]
  -- fallback: bounds from hypotheses
  let ks := #[ra.tz, rb.tz].filter (· > 0)
  if ks.isEmpty then return none
  let hyps ← relevantHyps #[a, b]
  if hyps.isEmpty then return none
  for k in ks do
    if let some pf ← attempt k hyps then return some pf
  return none

def decideProof (p : Expr) : MetaM Expr := do
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  return mkApp3 (mkConst ``of_decide_eq_true) p inst (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))

def mkStep (pf : Expr) : MetaM Simp.Step := do
  let ty ← inferType pf
  let some (_, _, rhs) := ty.eq? | return .continue
  return .visit { expr := rhs, proof? := some pf }

/-- Apply a lemma `lem x c m_1 ... m_k (h : P)` whose side condition `P` is closed and decidable. -/
def applyDecided (lem : Name) (args : Array Expr) : MetaM Simp.Step := do
  let s ← saveState
  try
    let partial_ := mkAppN (mkConst lem) args
    let .forallE _ hTy _ _ ← inferType partial_ | return .continue
    let h ← decideProof hTy
    mkStep (mkApp partial_ h)
  catch _ =>
    s.restore; return .continue

def andLit (lemMask lemPeel : Name) (x cE : Expr) (c : Nat) : MetaM Simp.Step := do
  if c == 0 then return .continue
  let lit := mkNatLit
  let hi := Nat.log2 c
  -- walk down from the top bit while bits are set
  let mut a := hi
  while a > 0 && (c >>> (a - 1)) % 2 == 1 do a := a - 1
  let n := hi + 1 - a
  let r := c % 2 ^ a
  if a == 0 then
    applyDecided lemMask #[x, cE, lit (2 ^ n), lit n]
  else
    applyDecided lemPeel #[x, cE, lit r, lit (2 ^ a), lit (2 ^ n), lit a, lit n]

def andStep (e : Expr) : MetaM Simp.Step := do
  let some (x, y) := natBin? ``HAnd.hAnd e | return .continue
  match natVal? x, natVal? y with
  | some _, some _ => return .continue
  | _, _ => pure ()
  if let some pf ← proveAndZero? x y then return ← mkStep pf
  match natVal? y, natVal? x with
  | some c, _ => andLit ``SimprocLemmas.and_mask ``SimprocLemmas.and_peel x y c
  | none, some c => andLit ``SimprocLemmas.mask_and ``SimprocLemmas.peel_and y x c
  | none, none => return .continue

def orXorStep (isOr : Bool) (e : Expr) : MetaM Simp.Step := do
  let some (x, y) := natBin? (if isOr then ``HOr.hOr else ``HXor.hXor) e | return .continue
  match natVal? x, natVal? y with
  | some _, some _ => return .continue
  | _, _ => pure ()
  if let some h ← proveAndZero? x y then
    return ← mkStep (mkApp3 (mkConst (if isOr then ``SimprocLemmas.or_eq_add
      else ``SimprocLemmas.xor_eq_add)) x y h)
  -- with a literal operand the `&&&` peels exactly; otherwise keep the atom (bounded in `bitFacts`)
  if (natVal? x).isNone && (natVal? y).isNone then return .continue
  mkStep (mkApp2 (mkConst (if isOr then ``SimprocLemmas.or_eq else ``SimprocLemmas.xor_eq)) x y)

end Meta

open Lean Meta in
/-- Rewrite `x &&& c` (literal mask) into `/`, `%`, `*`, and `a &&& b` with disjoint bits to `0`. -/
simproc_decl natAndBits ((_ : Nat) &&& (_ : Nat)) := fun e => Meta.andStep e
open Lean Meta in
/-- Rewrite `a ||| b` to `a + b` (disjoint) or `a + b - (a &&& b)`. -/
simproc_decl natOrBits ((_ : Nat) ||| (_ : Nat)) := fun e => Meta.orXorStep true e
open Lean Meta in
/-- Rewrite `a ^^^ b` to `a + b` (disjoint) or `a + b - 2 * (a &&& b)`. -/
simproc_decl natXorBits ((_ : Nat) ^^^ (_ : Nat)) := fun e => Meta.orXorStep false e
open Lean Meta in
/-- Reassociate `x + a + b` to `x + (a + b)` for literals `a`, `b` (then folded by `Nat.reduceAdd`).
Without this, `simp` may close `x + A + B = x + C + D` by `Meta`'s offset-aware defeq, which the
kernel then checks by unfolding `Nat.add` on large literals and hits deep recursion. -/
simproc_decl natAddLitAssoc (((_ : Nat) + _) + _) := fun e => do
  let some (xa, b) := Meta.natBin? ``HAdd.hAdd e | return .continue
  let some _ := b.nat? | return .continue
  let some (x, a) := Meta.natBin? ``HAdd.hAdd xa | return .continue
  let some _ := a.nat? | return .continue
  Meta.mkStep (mkApp3 (mkConst ``Nat.add_assoc) x a b)

open Lean Meta in
/-- Eliminate redundant `% m` when the dividend is already bounded by `m`
(`x.toNat % m = x.toNat` for `2^w ≤ m`, `a % n % m = a % n` for `n ≤ m`,
`a % n * k % m = a % n * k` for `n * k ≤ m`). -/
simproc_decl natModSmall ((_ : Nat) % (_ : Nat)) := fun e => do
  let some (lhs, mE) := Meta.natBin? ``HMod.hMod e | return .continue
  let some m := Meta.natVal? mE | return .continue
  if lhs.isAppOfArity ``BitVec.toNat 2 then
    if let some w := Meta.natVal? (lhs.getArg! 0) then
      if w ≤ 256 && 2 ^ w ≤ m then
        return ← Meta.applyDecided ``BVLemmas.toNat_mod_le #[lhs.getArg! 0, lhs.getArg! 1, mE]
  if let some (a, nE) := Meta.natBin? ``HMod.hMod lhs then
    if let some n := Meta.natVal? nE then
      if 0 < n && n ≤ m then
        return ← Meta.applyDecided ``NatLemmas.mod_mod_le #[a, nE, mE]
  if let some (an, kE) := Meta.natBin? ``HMul.hMul lhs then
    if let some k := Meta.natVal? kE then
      if an.isAppOfArity ``BitVec.toNat 2 then
        if let some w := Meta.natVal? (an.getArg! 0) then
          if w ≤ 256 && 2 ^ w * k ≤ m then
            return ← Meta.applyDecided ``BVLemmas.toNat_mul_mod_le #[an.getArg! 0, an.getArg! 1, kE, mE]
      if let some (a, nE) := Meta.natBin? ``HMod.hMod an then
        if let some n := Meta.natVal? nE then
          if 0 < n && 0 < k && n * k ≤ m then
            return ← Meta.applyDecided ``NatLemmas.mod_mul_mod_le #[a, nE, kE, mE]
  return .continue

open Lean Meta in
/-- Simplify `x.toNat / m = 0` for `2^w ≤ m` and `(a + b * k) / m = a / m + b * (k / m)`
for `m ∣ k`. -/
simproc_decl natDivSmall ((_ : Nat) / (_ : Nat)) := fun e => do
  let some (lhs, mE) := Meta.natBin? ``HDiv.hDiv e | return .continue
  let some m := Meta.natVal? mE | return .continue
  if m == 0 then return .continue
  if lhs.isAppOfArity ``BitVec.toNat 2 then
    if let some w := Meta.natVal? (lhs.getArg! 0) then
      if w ≤ 256 && 2 ^ w ≤ m then
        return ← Meta.applyDecided ``BVLemmas.toNat_div_le #[lhs.getArg! 0, lhs.getArg! 1, mE]
  if let some (s1, s2) := Meta.natBin? ``HAdd.hAdd lhs then
    if let some (b, kE) := Meta.natBin? ``HMul.hMul s2 then
      if let some k := Meta.natVal? kE then
        if k % m == 0 then
          return ← Meta.applyDecided ``NatLemmas.add_mul_div_dvd #[s1, b, kE, mE]
    if let some (a, kE) := Meta.natBin? ``HMul.hMul s1 then
      if let some k := Meta.natVal? kE then
        if k % m == 0 then
          return ← Meta.applyDecided ``NatLemmas.mul_add_div_dvd #[a, kE, s2, mE]
  return .continue

open Lean Meta in
/-- `(x ++ y).toNat = x.toNat * 2^n + y.toNat` (a simproc so that literal widths `w` match `m + n`). -/
simproc_decl toNatAppend (BitVec.toNat (_ ++ _)) := fun e => do
  let_expr BitVec.toNat _ xy := e | return .continue
  let_expr HAppend.hAppend _ _ _ _ x y := xy | return .continue
  let pf ← mkAppM ``BVLemmas.toNat_append_mul #[x, y]
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  return .visit { expr := rhs, proof? := some pf }

/-! ## Lemma sets -/

attribute [bv_bits_nat] BitVec.toNat_and BitVec.toNat_or BitVec.toNat_xor BitVec.toNat_not
  BitVec.toNat_setWidth BitVec.truncate_eq_setWidth BitVec.zeroExtend_eq_setWidth
  BitVec.toNat_signExtend BitVec.msb_eq_decide BitVec.toNat_ushiftRight BitVec.toNat_shiftLeft
  BitVec.shiftLeft_eq' BitVec.ushiftRight_eq'
  BitVec.ult_eq_decide BitVec.ule_eq_decide BitVec.lt_def BitVec.le_def BitVec.toNat_eq
  BVLemmas.toNat_extractLsb' BVLemmas.getLsbD_eq_decide BVLemmas.slt_eq_decide' BVLemmas.sle_eq_decide'
  Nat.shiftLeft_eq Nat.shiftRight_eq_div_pow

namespace Meta
open Lean Meta Elab Tactic

/-- First closed non-`Prop` `ite` in `e`. -/
partial def findIte? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``ite 5 && !e.hasLooseBVars && !(e.getArg! 0).isProp then
    -- prefer an inner one (its condition/branches are then ite-free after generalization)
    (e.getAppArgs.findSome? findIte?).getD e
  else match e with
    | .app f a => (findIte? f).orElse fun _ => findIte? a
    | .lam _ t b _ | .forallE _ t b _ => (findIte? t).orElse fun _ => findIte? b
    | .mdata _ b => findIte? b
    | _ => none

/-- Cheap syntactic test: is `ty` an arithmetic/Bool proposition `bv_bits` can use? -/
partial def isBitsProp (ty : Expr) : Bool :=
  let ty := ty.consumeMData
  match ty.getAppFnArgs with
  | (``Not, #[p]) => isBitsProp p
  | (``And, #[p, q]) | (``Or, #[p, q]) | (``Iff, #[p, q]) =>
    isBitsProp p || isBitsProp q
  | (``Eq, #[α, _, _]) | (``Ne, #[α, _, _]) => isBitsType α
  | (``LT.lt, #[α, _, _, _]) | (``LE.le, #[α, _, _, _])
  | (``GT.gt, #[α, _, _, _]) | (``GE.ge, #[α, _, _, _]) => isBitsType α
  | (``False, _) | (``True, _) => true
  | _ =>
    if ty.isArrow then
      ty.bindingBody!.consumeMData.isConstOf ``False && isBitsProp ty.bindingDomain!
    else
      false
where
  isBitsType (α : Expr) : Bool :=
    let α := α.consumeMData
    α.isConstOf ``Nat || α.isConstOf ``Int || α.isConstOf ``Bool || α.isProp ||
    α.isAppOfArity ``BitVec 1 || α.isAppOfArity ``Fin 1 || α.isAppOfArity ``UInt8 0 ||
    α.isAppOfArity ``UInt16 0 || α.isAppOfArity ``UInt32 0 || α.isAppOfArity ``UInt64 0

/-- Clear local `Prop` hypotheses that cannot contribute to `bv_bits` (e.g. `SepWP`, `⊨`, or
`∀` induction hypotheses) so `simp ... at *` and `generalizeIte` do not traverse them. -/
def pruneNonBitsHyps (g : MVarId) : MetaM MVarId := do
  let mut g := g
  let ds ← g.withContext do
    let mut ds := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail || d.isLet then continue
      let ty ← instantiateMVars d.type
      if !(← isProp ty) then continue
      if isBitsProp ty then continue
      if !ty.isForall then
        if isBitsProp (← withReducible (whnf ty)) then continue
      ds := ds.push d.fvarId
    return ds
  for fv in ds.reverse do
    g ← g.tryClear fv
  return g

/-- Replace one closed `ite` `t = if c then a else b` by a fresh variable `v` with the fact
`(c ∧ v = a) ∨ (¬c ∧ v = b)`. Returns `none` if there is no such `ite`. -/
def generalizeIte (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let mut t? := findIte? (← instantiateMVars (← g.getType))
  if t?.isNone then
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if let some t := findIte? (← instantiateMVars d.type) then t? := some t; break
  let some t := t? | return none
  let α := t.getArg! 0
  let u ← getLevel α
  let fact := mkAppN (mkConst ``BVLemmas.ite_cases [u]) #[α, t.getArg! 1, t.getArg! 2, t.getArg! 3, t.getArg! 4]
  let factTy ← inferType fact
  -- `assert` adds `h_ite` as an antecedent of the target (`factTy -> goal`), not to the local
  -- context, so `generalize` below abstracts `t` in it as well.
  let g ← g.assert `h_ite factTy fact
  g.withContext do
    let mut deps := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if Option.isSome ((← instantiateMVars d.type).find? (· == t)) then deps := deps.push d.fvarId
    let (reverted, g) ← g.revert deps (preserveOrder := true)
    let (_, g) ← g.generalize #[{ expr := t, xName? := `v_ite }]
    let (_, g) ← g.introNP reverted.size
    return some g

/-- Generalize all closed non-`Prop` `ite`s (bounded). -/
def generalizeItes (g : MVarId) : MetaM MVarId := do
  let mut g := g
  for _ in [0:64] do
    match ← generalizeIte g with
    | some g' => g := g'
    | none => break
  return g

/-- Free variables of `e`, unfolding `let`-bound locals. -/
partial def fvarsDeep (e : Expr) (acc : Std.HashSet FVarId := {}) : MetaM (Std.HashSet FVarId) := do
  let mut acc := acc
  for fv in (collectFVars {} e).fvarIds do
    if acc.contains fv then continue
    acc := acc.insert fv
    if let some v ← fv.getValue? then acc ← fvarsDeep (← instantiateMVars v) acc
  return acc

/-- Try `omega` on `g` with `hyps`; restores state and returns `false` on failure. -/
def tryOmega (g : MVarId) (hyps : Array Expr) : MetaM Bool := do
  let s ← saveState
  try Lean.Elab.Tactic.Omega.omega hyps.toList g; return true
  catch _ => s.restore; return false

/-- `omega` with all hypotheses plus bound facts for the bitwise atoms. Staged for speed:
(1) only hypotheses whose free variables all occur in the (negated) goal, with the cheap
conjunctive facts; (2) all hypotheses, cheap facts; (3) all hypotheses plus the disjunctive
`a ||| b < 2^k` facts. -/
def bitsOmega (g : MVarId) : MetaM Unit := do
  let before := (← g.getDecl).lctx
  let some g ← g.falseOrByContra | return
  g.withContext do
    let mut hyps := #[]
    let mut tys := #[]
    let mut goalFVs : Std.HashSet FVarId := {}
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      hyps := hyps.push d.toExpr
      let ty ← instantiateMVars d.type
      tys := tys.push ty
      if !before.contains d.fvarId then goalFVs ← fvarsDeep ty goalFVs
    let cheap ← bitFacts tys (withPow := false)
    -- stage 1: goal-relevant hypotheses only
    if !goalFVs.isEmpty then
      let mut rhyps := #[]
      let mut rtys := #[]
      for h in hyps, ty in tys do
        let fvs ← fvarsDeep ty
        if (← Meta.isProp ty) && fvs.toList.all goalFVs.contains then
          rhyps := rhyps.push h; rtys := rtys.push ty
      if rhyps.size < hyps.size then
        if ← tryOmega g (rhyps ++ (← bitFacts rtys (withPow := false))) then return
    let full ← bitFacts tys
    if full.size == cheap.size then
      Lean.Elab.Tactic.Omega.omega (hyps ++ cheap).toList g
    else
      if ← tryOmega g (hyps ++ cheap) then return
      Lean.Elab.Tactic.Omega.omega (hyps ++ full).toList g

end Meta

open Lean Elab Tactic in
/-- Clear local `Prop` hypotheses that are not arithmetic/Bool propositions before `bv_bits`. -/
elab "bv_bits_prune_hyps" : tactic => liftMetaTactic fun g => do
  return [← Meta.pruneNonBitsHyps g]

open Lean Elab Tactic in
/-- Generalize every closed non-`Prop` `if-then-else` into a fresh variable plus a disjunction. -/
elab "bv_bits_generalize_ite" : tactic => liftMetaTactic fun g => do
  return [← Meta.generalizeItes g]

open Lean Elab Tactic in
/-- Like `bv_bits_generalize_ite`, but fails if there is no `if-then-else` to generalize. -/
elab "bv_bits_generalize_ite!" : tactic => liftMetaTactic fun g => do
  let some g ← Meta.generalizeIte g | throwError "bv_bits: no if-then-else"
  return [← Meta.generalizeItes g]

open Lean Elab Tactic in
/-- `omega` plus bound facts for the remaining `&&&`/`|||`/`^^^` atoms. -/
elab "bv_bits_omega" : tactic => liftMetaFinishingTactic Meta.bitsOmega

open Lean Parser Tactic in
/-- Apply the `BitVec`/`Bool`-to-`Nat` simp set of `bv_bits` at a given location. -/
syntax (name := bvBitsNatAt) "bv_bits_nat_at" (location)? : tactic

macro_rules
  | `(tactic| bv_bits_nat_at $[$loc]?) => `(tactic|
  simp -implicitDefEqProofs -failIfUnchanged only [bv_bits_nat, bitvec_to_nat,
    natAndBits, natOrBits, natXorBits,
    Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceAnd, Nat.reduceOr, Nat.reduceXor,
    toNatAppend, natModSmall, natDivSmall,
    Nat.and_zero, Nat.zero_and, Nat.or_zero, Nat.zero_or, Nat.add_zero, Nat.zero_add, Nat.sub_zero, Nat.pow_zero,
    Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.one_mul, Nat.mod_mod,
    NatLemmas.mod_mod_dvd, NatLemmas.add_mod_mod_dvd, NatLemmas.mod_add_mod_dvd, natAddLitAssoc,
    NatLemmas.mul_mod_dvd, NatLemmas.mul_add_mod_dvd, NatLemmas.add_mul_mod_dvd,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.not_eq_false', Bool.not_eq_true,
    Bool.and_eq_false_iff, Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not,
    decide_not, Bool.not_not,
    BVLemmas.beq_bv, BVLemmas.bne_bv, BVLemmas.beq_nat, BVLemmas.bne_nat,
    BVLemmas.beq_bool, BVLemmas.bne_bool,
    decide_eq_decide, beq_iff_eq, bne_iff_ne, beq_eq_false_iff_ne, bne_eq_false_iff_eq, ne_eq,
    ↓reduceIte, ite_true, ite_false, BVLemmas.ite_prop] $[$loc]?)

/-- Translate `BitVec`/`Bool` facts to `Nat` with literal masks and disjoint `|||` eliminated. -/
macro "bv_bits_nat" : tactic => `(tactic| bv_bits_nat_at at *)

/-- Close a `BitVec`/`Nat`/`Bool` goal involving masks, byte extraction, `++`,
`setWidth`/`extractLsb'`, `|||` of disjoint pieces, comparisons, and `if` expressions via
`simp` and `omega`. -/
macro "bv_bits" : tactic => `(tactic| (
  intros
  bv_bits_prune_hyps
  try simp -failIfUnchanged only [↓reduceIte, ite_true, ite_false, BVLemmas.ite_prop,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at *
  all_goals bv_bits_generalize_ite
  all_goals bv_bits_nat
  all_goals try (bv_bits_generalize_ite!; bv_bits_nat)
  -- goal-only rerun: simprocs now see the translated hypotheses (bounds for disjointness)
  all_goals bv_bits_nat_at
  all_goals bv_bits_omega))

end

end ProofLib.BV.Bits
