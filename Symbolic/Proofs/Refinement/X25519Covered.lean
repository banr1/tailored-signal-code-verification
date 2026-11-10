/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.X25519
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
public import Symbolic.Specifications.Refinement.Concretization
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Little-endian arithmetic and X25519 public-key encoding variations

Establishes the bijection between byte lists and little-endian naturals (`leValue_leBytes`,
`leBytes_leValue`), shows `variantBytes` preserves length 32 and the RFC 7748 u-coordinate
(`variantBytes_spec`), and defines the 2-bit non-canonical variation index `keyVariation`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Refinement

open DY DY.Comparse DY.DiffieHellman DY.Literal DY.X25519
open DY.Libsignal.Composed.Refinement
export DY.Libsignal.Composed.Refinement (leBytes x25519UCoord variantBytes)

theorem length_leBytes : ∀ n w, (leBytes n w).length = n
  | 0, _ => rfl
  | n + 1, w => by simp [leBytes, length_leBytes n]

theorem leValue_leBytes : ∀ n w, leValue ((leBytes n w).map BitVec.toNat) = w % 256 ^ n
  | 0, w => by simp [leBytes, leValue, Nat.mod_one]
  | n + 1, w => by
    have h : w % 256 ^ (n + 1) = w % 256 + 256 * (w / 256 % 256 ^ n) := by
      rw [Nat.pow_succ', Nat.mod_mul]
    rw [h, leBytes, List.map_cons, leValue, leValue_leBytes n, BitVec.toNat_ofNat]

theorem leBytes_leValue : ∀ b : HwBytes, leBytes b.length (leValue (b.map BitVec.toNat)) = b
  | [] => rfl
  | x :: xs => by
    have hx := x.isLt
    simp only [List.length_cons, leBytes, List.map_cons, leValue]
    congr 1
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      omega
    · have :
          (x.toNat + 256 * leValue (xs.map BitVec.toNat)) / 256 =
            leValue (xs.map BitVec.toNat) := by
        omega
      rw [this, leBytes_leValue xs]

theorem leValue_lt : ∀ b : HwBytes, leValue (b.map BitVec.toNat) < 256 ^ b.length
  | [] => by simp [leValue]
  | x :: xs => by
    have hx := x.isLt
    have ih := leValue_lt xs
    simp only [List.map_cons, leValue, List.length_cons, Nat.pow_succ']
    simp only [BitVec.toNat] at hx
    omega

theorem p25519_lt : p25519 < 2 ^ 255 := by unfold p25519; omega

theorem p25519_pos : 0 < p25519 := by unfold p25519; omega

theorem uOf_lt (b : HwBytes) : x25519UCoord b < p25519 := Nat.mod_lt _ p25519_pos

theorem uOf_leBytes (w : Nat) (hw : w < 2 ^ 256) : x25519UCoord (leBytes 32 w) = w % 2 ^ 255 % p25519 := by
  unfold x25519UCoord uCoord
  rw [leValue_leBytes, Nat.mod_eq_of_lt (a := w) (b := 256 ^ 32) (by omega)]

theorem variantBytes_spec (b : HwBytes) (hb : b.length = 32) (v : Fin 4) :
    (variantBytes b v).length = 32 ∧ x25519UCoord (variantBytes b v) = x25519UCoord b := by
  unfold variantBytes
  simp only [hb, ↓reduceIte]
  refine ⟨length_leBytes _ _, ?_⟩
  have hu := uOf_lt b
  have hp := p25519_lt
  generalize x25519UCoord b = u at hu ⊢
  have key : ∀ u', u' < 2 ^ 255 → u' % p25519 = u →
      x25519UCoord (leBytes 32 (if v.val % 2 = 1 then u' + 2 ^ 255 else u')) = u := by
    intro u' h1 h2
    split
    · rw [uOf_leBytes _ (by omega), Nat.add_mod_right, Nat.mod_eq_of_lt h1, h2]
    · rw [uOf_leBytes _ (by omega), Nat.mod_eq_of_lt h1, h2]
  apply key
  · split <;> omega
  · split
    · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hu]
    · exact Nat.mod_eq_of_lt hu

def keyValue (b : HwBytes) : Nat := leValue (b.map BitVec.toNat)

/-- Non-canonical encoding bits of `b`: bit 0 records bit 255, and bit 1 records whether the low
255 bits are at least `p25519`. -/
def keyVariation (b : HwBytes) : Fin 4 :=
  if 2 ^ 255 ≤ keyValue b then (if p25519 ≤ keyValue b % 2 ^ 255 then 3 else 1)
  else (if p25519 ≤ keyValue b % 2 ^ 255 then 2 else 0)

end DY.Libsignal.Refinement

namespace DY.Libsignal.Composed.Refinement
export DY.Libsignal.Refinement (
  length_leBytes leValue_leBytes leBytes_leValue leValue_lt p25519_lt p25519_pos
  uOf_lt uOf_leBytes variantBytes_spec keyValue  keyVariation
)
end DY.Libsignal.Composed.Refinement

namespace DY.Libsignal.TripleRatchet.Refinement
export DY.Libsignal.Refinement (
  length_leBytes leValue_leBytes leBytes_leValue leValue_lt p25519_lt p25519_pos
  uOf_lt uOf_leBytes variantBytes_spec keyValue  keyVariation
)
export DY.Libsignal.Composed.Refinement (
  clampByte clamp x25519UCoord leBytes variantBytes ofByteArray litOf
  trItemEncode honestTrItems trFields trWireBytes spqrKeyBytes
  Ghost ConcretizedTerm gamma' gamma
)
end DY.Libsignal.TripleRatchet.Refinement
