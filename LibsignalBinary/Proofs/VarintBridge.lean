/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import Mathlib.Tactic.ToAdditive
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Equivalence Between `varintSlow` and `decodeVarint`

Proves `decodeVarint_eq_varintSlow`, showing that the hook-level LEB128 decoder `varintSlow`
(operating on `l.take 10` and returning `(val, bytesRead)`) agrees with the protobuf codec decoder
`decodeVarint` (returning `(val, remainingBytes)`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.VarintBridge

open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec

/-- The codec's varint loop returns a suffix of its input that is at least one byte shorter. -/
theorem decodeVarintAux_suffix :
    ∀ (l : List (BitVec 8)) (i : ℕ) (acc : BitVec 64) (v : BitVec 64) (r : List (BitVec 8)),
      decodeVarintAux i acc l = some (v, r) → ∃ k, 1 ≤ k ∧ k ≤ l.length ∧ r = l.drop k
  | [], _, _, _, _, h => by simp [decodeVarintAux] at h
  | b :: rest, i, acc, v, r, h => by
    simp only [decodeVarintAux] at h
    by_cases hb : b.toNat ≤ 0x7F
    · simp only [hb, ite_true] at h
      by_cases hi : i = 9 ∧ 0x02 ≤ b.toNat
      · simp [hi] at h
      · simp only [hi, ite_false, Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨1, le_refl _, by simp, by simp [h.2]⟩
    · simp only [hb, ite_false] at h
      by_cases hi : i = 9
      · simp [hi] at h
      · simp only [hi, ite_false] at h
        obtain ⟨k, hk1, hkl, hr⟩ := decodeVarintAux_suffix rest (i + 1) _ v r h
        exact ⟨k + 1, by omega, by simp; omega, by simp [hr]⟩

theorem mask_eq : (0x7f#8 : BitVec 8) = 0x7F := rfl

/-- The loop invariant: from byte `i ≤ 9`, `varintSlowAux` on the next `10 - i` bytes agrees with
the codec's loop on the whole rest, with byte count `i + (l.length - r.length)`. -/
theorem varintSlowAux_eq :
    ∀ (l : List (BitVec 8)) (i : ℕ) (acc : BitVec 64), i ≤ 9 →
      varintSlowAux i acc (l.take (10 - i)) =
        (decodeVarintAux i acc l).map (fun p => (p.1, i + (l.length - p.2.length)))
  | [], i, acc, _ => by simp [varintSlowAux, decodeVarintAux]
  | b :: rest, i, acc, hi9 => by
    have h10 : 10 - i = (9 - i) + 1 := by omega
    rw [h10, List.take_succ_cons]
    simp only [varintSlowAux, decodeVarintAux, mask_eq]
    by_cases hb : b.toNat ≤ 0x7F
    · simp only [hb, ite_true]
      by_cases hi : i = 9 ∧ 0x02 ≤ b.toNat
      · simp [hi]
      · simp only [hi, ite_false, Option.map_some, List.length_cons]
        congr 2
        omega
    · simp only [hb, ite_false]
      by_cases hi : i = 9
      · subst hi
        simp [varintSlowAux]
      · simp only [hi, ite_false]
        have hrec := varintSlowAux_eq rest (i + 1) (acc ||| ((b &&& 0x7F).zeroExtend 64 <<< (7 * i)))
          (by omega)
        have h9 : 9 - i = 10 - (i + 1) := by omega
        rw [h9, hrec]
        cases hd : decodeVarintAux (i + 1) (acc ||| ((b &&& 0x7F).zeroExtend 64 <<< (7 * i))) rest
          with
        | none => rfl
        | some p =>
          obtain ⟨k, hk1, hkl, hr⟩ := decodeVarintAux_suffix rest (i + 1) _ p.1 p.2 hd
          simp only [Option.map_some, List.length_cons, hr, List.length_drop]
          congr 2
          omega

/-- `varintSlow` agrees with `decodeVarint`: both fail on the same inputs, decode the same `BitVec 64`
value, and `varintSlow` reports `l.length - rest.length` consumed bytes. -/
theorem decodeVarint_eq_varintSlow (l : List (BitVec 8)) :
    varintSlow l = (decodeVarint l).map (fun p => (p.1, l.length - p.2.length)) := by
  have h := varintSlowAux_eq l 0 0#64 (by omega)
  simp only [Nat.sub_zero, Nat.zero_add] at h
  exact h

/-- Characterizes `varintSlow l = some (v, k)` as `decodeVarint l = some (v, l.drop k)` with `1 ≤ k ≤ min 10 l.length`. -/
theorem varintSlow_some_iff (l : List (BitVec 8)) (v : BitVec 64) (k : ℕ) :
    varintSlow l = some (v, k) ↔ 1 ≤ k ∧ k ≤ l.length ∧ decodeVarint l = some (v, l.drop k) := by
  rw [decodeVarint_eq_varintSlow]
  constructor
  · intro h
    cases hd : decodeVarint l with
    | none => simp [hd] at h
    | some p =>
      simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨j, hj1, hjl, hr⟩ := decodeVarintAux_suffix l 0 0 p.1 p.2 hd
      have hk : k = j := by rw [← h.2, hr, List.length_drop]; omega
      subst hk
      refine ⟨hj1, hjl, ?_⟩
      rw [← h.1, ← hr]
  · rintro ⟨hk1, hkl, hd⟩
    simp only [hd, Option.map_some, List.length_drop]
    congr 2
    omega

end CryptoVerification.LibsignalTripleRatchet.VarintBridge
