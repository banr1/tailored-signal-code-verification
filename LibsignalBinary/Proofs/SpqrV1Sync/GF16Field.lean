/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Algebra.Field.Defs
public import LibsignalBinary.Proofs.SpqrV1Sync.GF16Laws
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16

/-!
# Mathlib `Field GF16` Instance

Equips `LibsignalSpqrV1.GF16` (`GF(2 ^ 16)`) with a Mathlib `Field` instance backed directly by the
model operations (`GF16.add`, `GF16.mul`, `GF16.div`, `GF16.ZERO`, `GF16.ONE`, `-a = a`, and
`a⁻¹ = GF16.div GF16.ONE a`), using the algebraic laws proved in `GF16Laws.lean`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.GF16Field

open CryptoVerification.LibsignalSpqrV1
instance : Zero GF16 := ⟨GF16.ZERO⟩

instance : One GF16 := ⟨GF16.ONE⟩

instance : Add GF16 := ⟨GF16.add⟩

instance : Mul GF16 := ⟨GF16.mul⟩

/-- Characteristic 2: negation is the identity. -/
instance : Neg GF16 := ⟨id⟩

instance : Sub GF16 := ⟨GF16.sub⟩

/-- Multiplicative inverse `a⁻¹ = GF16.div GF16.ONE a` (sending `0⁻¹` to `0`). -/
instance : Inv GF16 := ⟨fun a => GF16.div GF16.ONE a⟩

instance : Div GF16 := ⟨GF16.div⟩

/-- Mathlib `Field` structure on `GF16` backed by the model operations. -/
instance instField : Field GF16 where
  add_assoc := add_assoc'
  zero_add := zero_add'
  add_zero := add_zero'
  add_comm := add_comm'
  neg_add_cancel := add_self'
  sub_eq_add_neg := fun _ _ => rfl
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  mul_comm := mul_comm'
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  exists_pair_ne := ⟨GF16.ZERO, GF16.ONE, zero_ne_one'⟩
  mul_inv_cancel := mul_inv_cancel'
  inv_zero := inv_zero'
  div_eq_mul_inv := div_eq_mul_inv'
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

@[simp] theorem add_eq (a b : GF16) : a + b = GF16.add a b := rfl

@[simp] theorem mul_eq (a b : GF16) : a * b = GF16.mul a b := rfl

@[simp] theorem div_eq (a b : GF16) : a / b = GF16.div a b := rfl

@[simp] theorem zero_eq : (0 : GF16) = GF16.ZERO := rfl

@[simp] theorem one_eq : (1 : GF16) = GF16.ONE := rfl

@[simp] theorem neg_eq (a : GF16) : -a = a := rfl

@[simp] theorem sub_eq (a b : GF16) : a - b = GF16.add a b := rfl

@[simp] theorem inv_eq (a : GF16) : a⁻¹ = GF16.div GF16.ONE a := rfl

end CryptoVerification.SpqrV1Sync.GF16Field
