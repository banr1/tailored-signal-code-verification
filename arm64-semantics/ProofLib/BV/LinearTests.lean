/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.BV.Linear
import Arm64.Trusted.Spec.SepLogic

/-!
# Regression Tests for `ProofLib.BV.Linear`

Regression tests for `bv_lin`, `bv_lin_norm`, and the `ProofLib.BV.Lin` meta API.
-/

@[expose] public section

namespace ProofLib.BV.LinTests

open ProofLib.BV.Lin

/-! ## Offset normalization -/

theorem a1 (a : BitVec 64) : a + 8 + 16 - 8 = a + 16 := by bv_lin
theorem a2 (b x y : BitVec 64) : (b + x - y) - b = x - y := by bv_lin
theorem a3 (sp : BitVec 64) : sp - 16 + 8 + 8 = sp := by bv_lin
theorem a4 (a i j : BitVec 64) : (a + i) + (j + 8) = (a + 8) + i + j := by bv_lin
theorem a5 (a : BitVec 64) : a + 0x10 - 0x20 + 0x8 + 0x18 - 0x10 + 0x4 = a + 0x4 := by bv_lin
theorem a6 (a : BitVec 64) (i : Nat) (_ : i < 100) :
    a + BitVec.ofNat 64 i + 1 = a + BitVec.ofNat 64 (i + 1) := by bv_lin
theorem a7 (a : BitVec 64) (i : Nat) :
    a + BitVec.ofNat 64 i + 1 = a + BitVec.ofNat 64 (i + 1) := by bv_lin

/-! ## Disequalities -/

theorem b1 (a : BitVec 64) : a + 8 ≠ a + 16 := by bv_lin
theorem b4 (sp : BitVec 64) : sp - 8 ≠ sp - 16 := by bv_lin
theorem b7 (a : BitVec 64) : a + 3 ≠ a + 8 + 5 := by bv_lin
example (a : BitVec 64) : ¬ (a + 3 = a + 8 + 5) := by bv_lin

/-! ## Scaling and shifts -/

theorem i1 (a : BitVec 64) : a <<< 3 = a * 8 := by bv_lin
theorem i4 (a i : BitVec 64) : a + (i <<< 3) ≠ a + (i <<< 3) + 8 := by bv_lin
theorem i7 (a : BitVec 64) : a * 3 + a = a * 4 := by bv_lin
theorem i8 (a b : BitVec 64) : (a + b) * 8 = a * 8 + b * 8 := by bv_lin

/-! ## Literal forms -/

example (a : BitVec 64) : a + 5#64 = a + (5 : BitVec 64) := by bv_lin
example (a : BitVec 64) : a + BitVec.ofNat 64 5 = a + 5 := by bv_lin
example (a : BitVec 64) : a + BitVec.ofFin ⟨5, by decide⟩ = a + 5 := by bv_lin
example (a : BitVec 64) : a + -5#64 = a - 5 := by bv_lin
example (a : BitVec 64) : a + (0#64 - 5) = a - 5 := by bv_lin
example (a : BitVec 64) : a - 1 = a + 0xFFFFFFFFFFFFFFFF := by bv_lin
example (a : BitVec 64) : a + BitVec.ofNat 64 (2^12 + 1) = a + 4097 := by bv_lin
example (a : BitVec 64) : a + 8 * 2 = 2 * (a + 8) - a := by bv_lin
example (a : BitVec 64) : -(-a) = a := by bv_lin
example (a b : BitVec 64) : a - b = -(b - a) := by bv_lin

/-! ## Width 32 and generic widths -/

example (a : BitVec 32) : a + 8 + 16 - 8 = a + 16 := by bv_lin
example (a : BitVec 32) : a + 0xFFFFFFFF = a - 1 := by bv_lin
example (a : BitVec 32) : a + 4 ≠ a := by bv_lin
example (w : Nat) (a b : BitVec w) : a + b - a = b := by bv_lin
example (w : Nat) (a b c : BitVec w) : (a + b) + c - b = c + a := by bv_lin
example (w : Nat) (a : BitVec w) : a + 3 + 5 = a + 8 := by bv_lin
example (w : Nat) (a : BitVec w) : a <<< 2 = a * 4 := by bv_lin
example (w : Nat) (a : BitVec w) (i : Nat) :
    a + BitVec.ofNat w (2 * i + 3) = a + BitVec.ofNat w i + BitVec.ofNat w i + 3 := by bv_lin
-- `a + 3 ≠ a` is false for `w ≤ 1`; symbolic widths only prove equalities.
set_option linter.unusedVariables false in
example (w : Nat) (a : BitVec w) : True := by
  fail_if_success have : a + 3 ≠ a := by bv_lin
  trivial

/-! ## Opaque atoms -/

example (f : BitVec 64 → BitVec 64) (x : BitVec 64) : f x + 8 - 8 = f x := by bv_lin
example (f : BitVec 64 → BitVec 64) (x : BitVec 64) : f (x + 0) + 8 ≠ f (x + 0) := by bv_lin
example (x y : BitVec 64) : (x &&& y) + 4 - (x &&& y) = 4 := by bv_lin
example (x y : BitVec 64) : x * y + x * y = 2 * (x * y) := by bv_lin
example (m : Nat → BitVec 64) (n : Nat) : m (n + 1) - m (n + 1) = 0 := by bv_lin

/-! ## Long sp-offset chains -/

theorem chain10 (sp : BitVec 64) :
    sp - 0x10 - 0x20 + 0x8 - 0x8 + 0x30 - 0x40 + 0x18 + 0x8 - 0x10 + 0x38 = sp + 0x8 := by
  bv_lin

theorem chain30 (sp x y : BitVec 64) :
    sp + x - 8 + y - 8 + 16 - x + 8 - y + 8 + x - 16 + 32 - x + y - 32 + 1 + 2 + 3 + 4 - 10
      + x - x + y - y + 7 - 7 + 0x100 - 0x100 - y + y - y = sp := by
  bv_lin

/-! ## Negative tests -/

section Negative
set_option linter.unusedVariables false

example (a : BitVec 64) : True := by
  fail_if_success have : a + 8 = a + 16 := by bv_lin
  trivial
example (a b : BitVec 64) : True := by
  fail_if_success have : a + 8 ≠ b + 16 := by bv_lin
  trivial
example (a b : BitVec 64) : True := by
  fail_if_success have : (a + b) * (a - b) = a * a - b * b := by bv_lin
  trivial
example (a : BitVec 64) : True := by
  fail_if_success have : a + 8 ≠ a + 8 := by bv_lin
  trivial
example (x : Nat) : x + 1 = 1 + x := by
  fail_if_success bv_lin
  omega

end Negative

/-- error: bv_lin: linear normal form does not decide the goal; a - b normalizes to
  -a + b + 8
hint: bv_lin is a pure ring normalizer and ignores local hypotheses as well as bitwise/cast/comparison operations (which are treated as opaque atoms in the residue above); rewrite local equalities first (`rw [h]; bv_lin`) or use `bv_omega` / `bv_solve` / `bv_bits` -/
#guard_msgs in
example (a b : BitVec 64) : b + 16 = a + 8 := by bv_lin

/-! ## Local equality rewriting (`proofLib.bvLinAutoHyps`, `bv_lin*`, `bv_lin [...]`, `bv_auto`) -/

example (x y : BitVec 64) (h : x = y + 8#64) : x + 16#64 = y + 24#64 := by
  bv_lin

example (a b : BitVec 64) (hb : b &&& 0xfff#64 = 0#64) : (b &&& 0xfff#64) + a = a := by
  bv_lin

example (x y z : BitVec 64) (h1 : x = y + 8#64) (h2 : y = z + 4#64) : x + 4#64 = z + 16#64 := by
  bv_lin*

example (x y : BitVec 64) (h : x = y + 8#64) : x + 16#64 = y + 24#64 := by
  set_option proofLib.bvLinAutoHyps false in
  bv_lin [h]

example (x y : BitVec 64) (h : x = y + 8#64) (hy : y.toNat + 8 < 2 ^ 64) : y ≤ x := by
  bv_auto

/-! ## `bv_lin_norm` simp set -/

example (a : BitVec 64) (P : BitVec 64 → Prop) (h : P (a + 16)) : P (a + 8 + 16 - 8) := by
  simp only [bv_lin_norm]; exact h

example (sp : BitVec 64) (P : BitVec 64 → Prop) (h : P (sp - 16)) : P (sp - 8 - 8) := by
  simp only [bv_lin_norm]; exact h

-- already canonical: no progress
example (a : BitVec 64) (P : BitVec 64 → Prop) (h : P (a + 16)) : P (a + 16) := by
  fail_if_success simp only [bv_lin_norm]
  exact h
example (a : BitVec 64) (P : BitVec 64 → Prop) (h : P (a - 16)) : P (a - 16) := by
  fail_if_success simp only [bv_lin_norm]
  exact h

-- idempotent
example (a b : BitVec 64) (P : BitVec 64 → Prop) (h : P (a + b * 3 - 8)) :
    P (b + a - 8 + b + b) := by
  simp only [bv_lin_norm] at h ⊢
  fail_if_success simp only [bv_lin_norm]
  exact h

/-! ## Meta API -/

open Lean Meta Elab Term in
/-- info: (8, true) -/
#guard_msgs in
#eval show TermElabM _ from do
  let ty ← elabType (← `(BitVec 64))
  withLocalDeclD `a ty fun a => do
  let w := mkNatLit 64
  let lhs ← mkAppM ``HSub.hSub #[← mkAppM ``HAdd.hAdd #[a, mkBVLit w 16], mkBVLit w 8]
  let some (c, pf) ← diffConst? lhs a | throwError "no"
  let pfTy ← inferType pf
  let expected ← mkEq lhs (← mkAppM ``HAdd.hAdd #[a, mkBVLit w 8])
  return (c, ← isDefEq pfTy expected)

/-! ## Axioms -/

/-- info: 'ProofLib.BV.LinTests.chain30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain30

/-- info: 'ProofLib.BV.LinTests.b4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms b4

end ProofLib.BV.LinTests
