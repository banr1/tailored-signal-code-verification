/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.CKA.LibsignalCKA

/-!
# Satisfiability of `X25519Model`

Toy two-point (`Pt = Bool`) consistency witness for `X25519Model`, together with bit-level checks
that `clamp256` is idempotent and enforces the RFC 7748 §5 bit masks.
-/

@[expose] public section

namespace CryptoGames.CKA.Tests

open CryptoGames CKA

example (x : BitVec 256) : clamp256 (clamp256 x) = clamp256 x := by
  ext i hi
  simp only [clamp256, BitVec.getElem_or, BitVec.getElem_and]
  cases x[i] <;> cases (~~~((7 : BitVec 256) ||| (1 : BitVec 256) <<< 255))[i] <;>
    cases ((1 : BitVec 256) <<< 254)[i] <;> rfl

/-- Clamping clears bits 0–2 and 255 and sets bit 254. -/
example (x : BitVec 256) :
    (clamp256 x).getLsbD 0 = false ∧ (clamp256 x).getLsbD 1 = false ∧
      (clamp256 x).getLsbD 2 = false ∧ (clamp256 x).getLsbD 255 = false ∧
      (clamp256 x).getLsbD 254 = true := by
  unfold clamp256
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and]
  have h0 : (~~~((7 : BitVec 256) ||| (1 : BitVec 256) <<< 255)).getLsbD 0 = false := by decide
  have h1 : (~~~((7 : BitVec 256) ||| (1 : BitVec 256) <<< 255)).getLsbD 1 = false := by decide
  have h2 : (~~~((7 : BitVec 256) ||| (1 : BitVec 256) <<< 255)).getLsbD 2 = false := by decide
  have h255 : (~~~((7 : BitVec 256) ||| (1 : BitVec 256) <<< 255)).getLsbD 255 = false := by decide
  have s0 : ((1 : BitVec 256) <<< 254).getLsbD 0 = false := by decide
  have s1 : ((1 : BitVec 256) <<< 254).getLsbD 1 = false := by decide
  have s2 : ((1 : BitVec 256) <<< 254).getLsbD 2 = false := by decide
  have s255 : ((1 : BitVec 256) <<< 254).getLsbD 255 = false := by decide
  have s254 : ((1 : BitVec 256) <<< 254).getLsbD 254 = true := by decide
  simp only [h0, h1, h2, h255, s0, s1, s2, s255, s254,
    Bool.and_false, Bool.or_false, Bool.or_true, and_self]

local instance : Zero Bool := ⟨false⟩

/-- Two-point toy `DHFun` whose `dh` ignores the scalar. -/
def toyD : DHFun (BitVec 256) Bool := ⟨true, fun _ P => P⟩

def toyEnc : Bool → List (BitVec 8) := fun b => if b then x25519Base else List.replicate 32 0

/-- Toy satisfiability witness for `X25519Model` with identity hooks. -/
example : X25519Model toyD toyEnc (fun _ u => u) (fun _ => x25519Base) where
  enc_injective := by intro a b h; cases a <;> cases b <;> simp_all [toyEnc, x25519Base]
  enc_length := by intro P; cases P <;> simp [toyEnc, x25519Base]
  enc_zero := rfl
  enc_base := rfl
  base_ne_zero := by decide
  hook := by intro x P; rfl
  pubKey_hook := by intro x; rfl
  dh_clamp := by intro x P; rfl
  dh_ne_zero := by intro _ P h; exact h

example : toyD.Commutes := fun _ _ => rfl

end CryptoGames.CKA.Tests
