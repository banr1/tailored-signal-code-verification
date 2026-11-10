/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Model.Instance

/-!
# List and `UInt32` helpers for receiver-chain updates

Auxiliary list last-element update and drop lemmas together with `UInt32`/`BitVec 32` comparison
and arithmetic rewrites.
-/

@[expose] public section

set_option autoImplicit false

namespace Proofs.libsignal.RngG.R3

open DY DY.Libsignal.Composed DY.Libsignal.TripleRatchet

theorem set_append_singleton_last {α : Type} (xs : List α) (x x' : α) :
    (xs ++ [x]).set ((xs ++ [x]).length - 1) x' = xs ++ [x'] := by
  induction xs with
  | nil => rfl
  | cons a xs' ih =>
    have hIdx : (a :: xs' ++ [x]).length - 1 = (xs' ++ [x]).length - 1 + 1 := by
      simp [List.length_append]
    rw [hIdx]
    exact congrArg (a :: ·) ih

theorem drop_append_singleton_of_le {α : Type} {xs : List α} {x : α} {k : Nat}
    (hk : k ≤ xs.length) :
    (xs ++ [x]).drop k = xs.drop k ++ [x] :=
  List.drop_append_of_le_length hk

theorem uint32_ofBitVec_le_iff (a : UInt32) (b : BitVec 32) :
    a ≤ UInt32.ofBitVec b ↔ a.toBitVec ≤ b := by
  rfl

theorem uint32_ofBitVec_ne_u32Max_of_ne_allOnes {b : BitVec 32}
    (hne : b ≠ BitVec.allOnes 32) : UInt32.ofBitVec b ≠ u32Max := by
  intro hEq
  apply hne
  have h1 : b = u32Max.toBitVec := congrArg UInt32.toBitVec hEq
  have h2 : u32Max.toBitVec = BitVec.allOnes 32 := by decide
  exact h1.trans h2

theorem uint32_ofBitVec_add_ofNat (a : UInt32) (j : Nat) :
    UInt32.ofBitVec (a.toBitVec + BitVec.ofNat 32 j) = a + UInt32.ofNat j := rfl

end Proofs.libsignal.RngG.R3
