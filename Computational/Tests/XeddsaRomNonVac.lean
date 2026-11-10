/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.CwfPrimitives
public import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs
public import Computational.Proofs.SignalPqxdh.XeddsaRom.ForkingReduction
public import Computational.Proofs.SignalPqxdh.XeddsaRom.GapDhWithSignReduction
public import Computational.Proofs.SignalPqxdh.XeddsaRom.HvzkSim
public import Computational.Proofs.SignalPqxdh.XeddsaRom.Roundtrip
public meta import Computational.Proofs.SignalPqxdh.CwfPrimitives -- shake: keep
public meta import Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519 -- shake: keep
public meta import Computational.Proofs.SignalPqxdh.XeddsaRom.Statements -- shake: keep
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import VCVio.EvalDist.Monad.Basic

/-!
# Prime-Order `ZMod l25519` Non-Vacuity Witness for XEdDSA ROM Reductions

**Checked by Lean.**

Constructs `pZMod : Primitives` over `ZMod l25519` jointly satisfying `WellFormedPrimitivesδ`,
`CryptoWellFormedPrimitivesδ`, `KemDeltaCorrect pZMod 0`, `XeddsaCurveLaws`, and
`pZMod.sigSign = xeddsaSignRef pZMod`. Also provides bounded random-oracle adversary witnesses for
the `GapDhWithSignRo` and `GapSigEufCmaRo` reduction bounds, computable `#guard` roundtrip and
tamper-rejection checks on `pZModPre` across both sign-bit branches, and `#print axioms` guards.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Computational.Tests.XeddsaRomNonVac

open OracleComp OracleSpec
open _root_.SignalPqxdh
open SpecTests.SignalPqxdh
open Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519
open Computational.Proofs.SignalPqxdh.XeddsaRom.Statements
open Computational.Proofs.SignalPqxdh.XeddsaRom.Roundtrip
open Computational.Proofs.SignalPqxdh.XeddsaRom.HvzkSim
open Computational.Proofs.SignalPqxdh.XeddsaRom.GapDhWithSignReduction
open Computational.Proofs.SignalPqxdh.XeddsaRom.ForkingReduction

/-- Midpoint `(l25519 - 1) / 2` between even-sign (`1 ≤ x.val ≤ halfL25519`) and odd-sign
    (`halfL25519 < x.val < l25519`) representatives in `ZMod l25519`. -/
def halfL25519 : ℕ :=
  (l25519 - 1) / 2

theorem l25519_eq_two_mul_half_add_one : l25519 = 2 * halfL25519 + 1 := by
  unfold halfL25519 l25519
  decide

theorem halfL25519_lt_two_pow_252 : halfL25519 < 2 ^ 252 := by
  unfold halfL25519 l25519
  decide

def edSignZMod (x : ZMod l25519) : UInt8 :=
  if x.val ≤ halfL25519 then 0 else 1

/-- Unsigned magnitude `min x.val ((-x).val)` in `[0, halfL25519]`, invariant under negation. -/
def absZMod (x : ZMod l25519) : ℕ :=
  if x.val ≤ halfL25519 then x.val else l25519 - x.val

theorem absZMod_le_half (x : ZMod l25519) : absZMod x ≤ halfL25519 := by
  have hx : x.val < l25519 := x.val_lt
  have hl := l25519_eq_two_mul_half_add_one
  unfold absZMod
  split <;> omega

theorem absZMod_lt_two_pow_252 (x : ZMod l25519) : absZMod x < 2 ^ 252 :=
  lt_of_le_of_lt (absZMod_le_half x) halfL25519_lt_two_pow_252

theorem absZMod_eq_zero_iff (x : ZMod l25519) : absZMod x = 0 ↔ x = 0 := by
  have hx : x.val < l25519 := x.val_lt
  have hl := l25519_eq_two_mul_half_add_one
  unfold absZMod
  constructor
  · intro h
    apply ZMod.val_injective
    rw [ZMod.val_zero]
    split at h <;> omega
  · rintro rfl
    simp

theorem edSignZMod_bool (x : ZMod l25519) : edSignZMod x = 0 ∨ edSignZMod x = 1 := by
  unfold edSignZMod
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem edSignZMod_neg (x : ZMod l25519) (hx : x ≠ 0) : edSignZMod (-x) = 1 - edSignZMod x := by
  have hval_pos : 0 < x.val :=
    Nat.pos_of_ne_zero (fun h0 => hx (ZMod.val_injective l25519 (by simpa using h0)))
  have hval_lt : x.val < l25519 := x.val_lt
  have hl := l25519_eq_two_mul_half_add_one
  have hneg_val : (-x).val = l25519 - x.val := by
    rw [ZMod.neg_val]
    simp [hx]
  unfold edSignZMod
  rw [hneg_val]
  by_cases hle : x.val ≤ halfL25519
  · have hnot : ¬ (l25519 - x.val ≤ halfL25519) := by omega
    simp [hle, hnot]
  · have hle' : l25519 - x.val ≤ halfL25519 := by omega
    simp [hle, hle']

theorem absZMod_neg (x : ZMod l25519) : absZMod (-x) = absZMod x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hval_pos : 0 < x.val :=
      Nat.pos_of_ne_zero (fun h0 => hx (ZMod.val_injective l25519 (by simpa using h0)))
    have hval_lt : x.val < l25519 := x.val_lt
    have hl := l25519_eq_two_mul_half_add_one
    have hneg_val : (-x).val = l25519 - x.val := by
      rw [ZMod.neg_val]; simp [hx]
    unfold absZMod
    rw [hneg_val]
    by_cases hle : x.val ≤ halfL25519
    · have hnot : ¬ (l25519 - x.val ≤ halfL25519) := by omega
      simp [hle, hnot]; omega
    · have hle' : l25519 - x.val ≤ halfL25519 := by omega
      simp [hle, hle']

theorem absZMod_eq_iff (x y : ZMod l25519) : absZMod x = absZMod y ↔ x = y ∨ x = -y := by
  constructor
  · intro habs
    by_cases hx0 : x = 0
    · subst hx0
      rw [(absZMod_eq_zero_iff y).mp (by simpa [absZMod] using habs.symm)]
      exact Or.inl rfl
    · have hy0 : y ≠ 0 := by
        intro hy
        subst hy
        exact hx0 ((absZMod_eq_zero_iff x).mp (by simpa [absZMod] using habs))
      have hxv : x.val < l25519 := x.val_lt
      have hyv : y.val < l25519 := y.val_lt
      have hneg_y : (-y).val = l25519 - y.val := by rw [ZMod.neg_val]; simp [hy0]
      unfold absZMod at habs
      by_cases hx_le : x.val ≤ halfL25519 <;> by_cases hy_le : y.val ≤ halfL25519
      · simp only [hx_le, hy_le, ↓reduceIte] at habs
        exact Or.inl (ZMod.val_injective l25519 habs)
      · simp only [hx_le, hy_le, ↓reduceIte] at habs
        exact Or.inr (ZMod.val_injective l25519 (by rw [hneg_y, habs]))
      · simp only [hx_le, hy_le, ↓reduceIte] at habs
        exact Or.inr (ZMod.val_injective l25519 (by rw [hneg_y]; omega))
      · simp only [hx_le, hy_le, ↓reduceIte] at habs
        exact Or.inl (ZMod.val_injective l25519 (by omega))
  · rintro (rfl | rfl)
    · rfl
    · exact absZMod_neg y

/-- Compressed 32-byte Edwards encoding on `ZMod l25519`: `absZMod x` in bits `0..254` and
    `edSignZMod x` in bit `255`. -/
def compressEdZMod (x : ZMod l25519) : Bytes :=
  let raw := bytesOfNatLE 32 (absZMod x)
  raw.take 31 ++ [(raw.getD 31 (0 : UInt8) &&& (0x7F : UInt8)) ||| (edSignZMod x <<< 7)]

/-- 160-byte uncompressed Edwards point encoding on `ZMod l25519`. -/
def encodeEdZMod (x : ZMod l25519) : Bytes :=
  encodeScalarBytes x ++ List.replicate 128 0

def decodeEdZMod (pt : Bytes) : ZMod l25519 :=
  decodeScalarBytes (pt.take 32)

/-- Montgomery 32-byte `u`-coordinate encoding `absZMod x` (`±x` share the same coordinate). -/
def encodeMontZMod (x : ZMod l25519) : Bytes :=
  bytesOfNatLE 32 (absZMod x)

def isCanonMont32 (pk : Bytes) : Bool :=
  pk.length == 32 && decide (0 < natOfBytesLE pk ∧ natOfBytesLE pk ≤ halfL25519)

/-- Maps a canonical Montgomery key to its `edSign = 0` representative in `ZMod l25519`, and other
    inputs to `0`. -/
def decodeMont32 (pk : Bytes) : ZMod l25519 :=
  if isCanonMont32 pk then (natOfBytesLE pk : ZMod l25519) else 0

def pow8ZMod (p : Bytes) : Bytes :=
  if p.length == 32 then encodeMontZMod (decodeMont32 p) else List.replicate 32 0

def x25519BaseZMod (sk : Bytes) : Bytes :=
  encodeMontZMod (clampedScalarZMod sk)

def x25519ZMod (sk pk : Bytes) : Bytes :=
  encodeMontZMod (clampedScalarZMod sk * decodeMont32 (fitBytesRef 32 pk))

def montToEdZMod (u : Bytes) (b : UInt8) : Option Bytes :=
  if (b == 0 || b == 1) && isCanonMont32 u then
    let x₀ : ZMod l25519 := (natOfBytesLE u : ZMod l25519)
    some (if b == 0 then encodeEdZMod x₀ else encodeEdZMod (-x₀))
  else
    none

/-- Toy 64-byte SHA-512 compression function that XORs the state with both 64-byte halves of the
    128-byte block. -/
def sha512CompressZMod (st blk : Bytes) : Bytes :=
  fitBytes 64 (xorBytes (fitBytes 64 st) (xorBytes (fitBytes 64 blk) (fitBytes 64 (blk.drop 64))))

theorem byte31_lt_16_of_natOfBytesLE_lt {bs : Bytes} (hlt : natOfBytesLE bs < 2 ^ 252) :
    (bs.getD 31 0).toNat < 16 := by
  rw [getD_toNat_eq_div_mod]
  have hdiv : natOfBytesLE bs / 256 ^ 31 < 16 := by omega
  omega

theorem getD_31_bytesOfNatLE_lt_16 {n : ℕ} (hn : n < 2 ^ 252) :
    ((bytesOfNatLE 32 n).getD 31 0).toNat < 16 := by
  apply byte31_lt_16_of_natOfBytesLE_lt
  rw [natOfBytesLE_bytesOfNatLE, Nat.mod_eq_of_lt (by omega)]
  exact hn

theorem byte_lt_16_and_7f {b : UInt8} (hb : b.toNat < 16) : b &&& 0x7F = b := by
  have hcheck : ∀ i : Fin 16, UInt8.ofNat i.val &&& 0x7F = UInt8.ofNat i.val := by decide
  have heq : UInt8.ofNat b.toNat = b := UInt8.ofNat_toNat
  simpa [heq] using hcheck ⟨b.toNat, hb⟩

theorem byte_lt_16_and_80 {b : UInt8} (hb : b.toNat < 16) : b &&& 0x80 = 0 := by
  have hcheck : ∀ i : Fin 16, UInt8.ofNat i.val &&& 0x80 = 0 := by decide
  have heq : UInt8.ofNat b.toNat = b := UInt8.ofNat_toNat
  simpa [heq] using hcheck ⟨b.toNat, hb⟩

theorem byte_lt_16_and_7f_ne_7f {b : UInt8} (hb : b.toNat < 16) : (b &&& 0x7F == 0x7F) = false := by
  have hcheck : ∀ i : Fin 16, (UInt8.ofNat i.val &&& 0x7F == 0x7F) = false := by decide
  have heq : UInt8.ofNat b.toNat = b := UInt8.ofNat_toNat
  simpa [heq] using hcheck ⟨b.toNat, hb⟩

theorem scalarIsInRange_of_lt_two_pow_252 {bs : Bytes}
    (hlt : natOfBytesLE bs < 2 ^ 252) :
    (bs.getD 31 0 &&& 0x80) = 0 ∧ scalarIsInRange bs = true := by
  have hb16 : (bs.getD 31 0).toNat < 16 := byte31_lt_16_of_natOfBytesLE_lt hlt
  have h80 : (bs.getD 31 0 &&& 0x80) = 0 := byte_lt_16_and_80 hb16
  refine ⟨h80, ?_⟩
  unfold scalarIsInRange
  rw [h80, byte_lt_16_and_7f_ne_7f hb16]
  simp

theorem list32_take31_append_getD31 {bs : Bytes} (hlen : bs.length = 32) :
    bs.take 31 ++ [bs.getD 31 0] = bs := by
  have hlt : 31 < bs.length := by omega
  have hdrop : bs.drop 31 = [bs.getD 31 0] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
      List.drop_eq_getElem_cons hlt, List.drop_eq_nil_of_le (by omega)]
  conv_rhs => rw [← List.take_append_drop 31 bs, hdrop]

theorem compressEdZMod_len (x : ZMod l25519) : (compressEdZMod x).length = 32 := by
  unfold compressEdZMod
  have hlen : (bytesOfNatLE 32 (absZMod x)).length = 32 := bytesOfNatLE_length 32 _
  rw [List.length_append, List.length_take, hlen, List.length_singleton]
  omega

theorem compressEdZMod_getD_31 (x : ZMod l25519) :
    (compressEdZMod x).getD 31 0 =
      ((bytesOfNatLE 32 (absZMod x)).getD 31 (0 : UInt8) &&& (0x7F : UInt8)) |||
        (edSignZMod x <<< 7) := by
  unfold compressEdZMod
  have hlen : ((bytesOfNatLE 32 (absZMod x)).take 31).length = 31 := by
    rw [List.length_take, bytesOfNatLE_length]; decide
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [hlen]

theorem clearSignBit32_compressEdZMod (x : ZMod l25519) :
    clearSignBit32 (compressEdZMod x) = bytesOfNatLE 32 (absZMod x) := by
  set raw := bytesOfNatLE 32 (absZMod x)
  have hraw_len : raw.length = 32 := bytesOfNatLE_length 32 _
  have hb16 : (raw.getD 31 0).toNat < 16 := getD_31_bytesOfNatLE_lt_16 (absZMod_lt_two_pow_252 x)
  have htake31 : (compressEdZMod x).take 31 = raw.take 31 := by
    unfold compressEdZMod
    rw [List.take_append_of_le_length (by rw [List.length_take, hraw_len]; decide),
      List.take_take, Nat.min_self]
  have hclear : (compressEdZMod x).getD 31 0 &&& 0x7F = raw.getD 31 0 := by
    rw [compressEdZMod_getD_31]
    have h1 : ∀ a : UInt8,
        (((a &&& (0x7F : UInt8)) ||| ((0 : UInt8) <<< 7)) &&& (0x7F : UInt8)) = a &&& (0x7F : UInt8) := by
      decide
    have h2 : ∀ a : UInt8,
        (((a &&& (0x7F : UInt8)) ||| ((1 : UInt8) <<< 7)) &&& (0x7F : UInt8)) = a &&& (0x7F : UInt8) := by
      decide
    rcases edSignZMod_bool x with hs | hs <;> rw [hs]
    · rw [h1, byte_lt_16_and_7f hb16]
    · rw [h2, byte_lt_16_and_7f hb16]
  unfold clearSignBit32
  rw [htake31, hclear]
  exact list32_take31_append_getD31 hraw_len

theorem compressEdZMod_inRange (x : ZMod l25519) :
    scalarIsInRange (clearSignBit32 (compressEdZMod x)) = true := by
  rw [clearSignBit32_compressEdZMod]
  have hn : natOfBytesLE (bytesOfNatLE 32 (absZMod x)) = absZMod x := by
    rw [natOfBytesLE_bytesOfNatLE, Nat.mod_eq_of_lt (lt_trans (absZMod_lt_two_pow_252 x) (by decide))]
  exact (scalarIsInRange_of_lt_two_pow_252 (by rw [hn]; exact absZMod_lt_two_pow_252 x)).2

theorem compressEdZMod_signBit (x : ZMod l25519) :
    ((compressEdZMod x).getD 31 0 &&& 0x80) >>> 7 = edSignZMod x := by
  rw [compressEdZMod_getD_31]
  have h0 : ∀ a : UInt8,
      ((((a &&& (0x7F : UInt8)) ||| ((0 : UInt8) <<< 7)) &&& (0x80 : UInt8)) >>> 7) = 0 := by
    decide
  have h1 : ∀ a : UInt8,
      ((((a &&& (0x7F : UInt8)) ||| ((1 : UInt8) <<< 7)) &&& (0x80 : UInt8)) >>> 7) = 1 := by
    decide
  rcases edSignZMod_bool x with hs | hs <;> rw [hs]
  · exact h0 _
  · exact h1 _

theorem compressEdZMod_inj : Function.Injective compressEdZMod := by
  intro x y hxy
  have hclear := congrArg clearSignBit32 hxy
  rw [clearSignBit32_compressEdZMod, clearSignBit32_compressEdZMod] at hclear
  have habs : absZMod x = absZMod y := by
    have h1 := congrArg natOfBytesLE hclear
    rwa [natOfBytesLE_bytesOfNatLE, natOfBytesLE_bytesOfNatLE,
      Nat.mod_eq_of_lt (lt_trans (absZMod_lt_two_pow_252 x) (by decide)),
      Nat.mod_eq_of_lt (lt_trans (absZMod_lt_two_pow_252 y) (by decide))] at h1
  have hsign : edSignZMod x = edSignZMod y := by
    rw [← compressEdZMod_signBit x, ← compressEdZMod_signBit y, hxy]
  rcases (absZMod_eq_iff x y).mp habs with rfl | rfl
  · rfl
  · by_cases hy : y = 0
    · subst hy; simp
    · rw [edSignZMod_neg y hy] at hsign
      rcases edSignZMod_bool y with hs | hs <;> rw [hs] at hsign <;>
        exact False.elim (by revert hsign; decide)

theorem encodeEdZMod_len (x : ZMod l25519) : (encodeEdZMod x).length = 160 := by
  simp [encodeEdZMod, encodeScalarBytes_length]

theorem decodeEdZMod_encodeEdZMod (x : ZMod l25519) : decodeEdZMod (encodeEdZMod x) = x := by
  unfold decodeEdZMod encodeEdZMod
  rw [List.take_append_of_le_length (by rw [encodeScalarBytes_length]),
    List.take_of_length_le (by rw [encodeScalarBytes_length]),
    decodeScalarBytes_encodeScalarBytes]

theorem encodeMontZMod_len (x : ZMod l25519) : (encodeMontZMod x).length = 32 :=
  bytesOfNatLE_length 32 _

theorem encodeMontZMod_zero : encodeMontZMod 0 = List.replicate 32 0 := by
  have habs : absZMod 0 = 0 := by simp [absZMod]
  unfold encodeMontZMod
  rw [habs]
  exact bytesOfNatLE_zero 32

theorem encodeMontZMod_neg (x : ZMod l25519) : encodeMontZMod (-x) = encodeMontZMod x := by
  simp [encodeMontZMod, absZMod_neg]

theorem natOfBytesLE_encodeMontZMod (x : ZMod l25519) :
    natOfBytesLE (encodeMontZMod x) = absZMod x := by
  unfold encodeMontZMod
  rw [natOfBytesLE_bytesOfNatLE, Nat.mod_eq_of_lt (lt_trans (absZMod_lt_two_pow_252 x) (by decide))]

theorem encodeMontZMod_eq_iff (x y : ZMod l25519) :
    encodeMontZMod x = encodeMontZMod y ↔ x = y ∨ x = -y := by
  constructor
  · intro h
    have habs : absZMod x = absZMod y := by
      simpa only [natOfBytesLE_encodeMontZMod] using congrArg natOfBytesLE h
    exact (absZMod_eq_iff x y).mp habs
  · rintro (rfl | rfl)
    · rfl
    · exact encodeMontZMod_neg y

theorem encodeMontZMod_eq_zero_iff (x : ZMod l25519) :
    encodeMontZMod x = List.replicate 32 0 ↔ x = 0 := by
  rw [← encodeMontZMod_zero, encodeMontZMod_eq_iff]
  simp

theorem isCanonMont32_spec {pk : Bytes} :
    isCanonMont32 pk = true ↔
      pk.length = 32 ∧ 0 < natOfBytesLE pk ∧ natOfBytesLE pk ≤ halfL25519 := by
  simp only [isCanonMont32, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]

theorem isCanonMont32_encodeMontZMod_iff (x : ZMod l25519) :
    isCanonMont32 (encodeMontZMod x) = true ↔ x ≠ 0 := by
  rw [isCanonMont32_spec, encodeMontZMod_len, natOfBytesLE_encodeMontZMod]
  refine ⟨fun ⟨_, hpos, _⟩ hx => ?_, fun hx => ⟨rfl, ?_, absZMod_le_half x⟩⟩
  · subst hx; simp [absZMod] at hpos
  · exact Nat.pos_of_ne_zero (mt (absZMod_eq_zero_iff x).mp hx)

theorem decodeMont32_val_le_half (pk : Bytes) : (decodeMont32 pk).val ≤ halfL25519 := by
  unfold decodeMont32
  split <;> rename_i hc
  · obtain ⟨_, _, hle⟩ := isCanonMont32_spec.mp hc
    have hlt_l : natOfBytesLE pk < l25519 :=
      lt_trans (lt_of_le_of_lt hle halfL25519_lt_two_pow_252) two_pow_252_lt_l25519
    rw [ZMod.val_natCast_of_lt hlt_l]
    exact hle
  · simp

theorem decodeMont32_encodeMontZMod_cast (x : ZMod l25519) :
    decodeMont32 (encodeMontZMod x) = (absZMod x : ZMod l25519) := by
  by_cases hx : x = 0
  · subst hx
    have hnc : isCanonMont32 (encodeMontZMod 0) = false :=
      Bool.eq_false_iff.mpr (mt (isCanonMont32_encodeMontZMod_iff 0).mp (by simp))
    simp [decodeMont32, hnc, absZMod]
  · have hc : isCanonMont32 (encodeMontZMod x) = true :=
      (isCanonMont32_encodeMontZMod_iff x).mpr hx
    simp [decodeMont32, hc, natOfBytesLE_encodeMontZMod]

theorem decodeMont32_encodeMontZMod_pm (x : ZMod l25519) :
    decodeMont32 (encodeMontZMod x) = x ∨ decodeMont32 (encodeMontZMod x) = -x := by
  rw [decodeMont32_encodeMontZMod_cast]
  by_cases hle : x.val ≤ halfL25519
  · left
    have habs : absZMod x = x.val := by unfold absZMod; simp [hle]
    rw [habs, ZMod.natCast_zmod_val]
  · right
    have habs : absZMod x = l25519 - x.val := by unfold absZMod; simp [hle]
    rw [habs, Nat.cast_sub (le_of_lt x.val_lt), ZMod.natCast_self, zero_sub, ZMod.natCast_zmod_val]

theorem pow8ZMod_encodeMontZMod (x : ZMod l25519) :
    pow8ZMod (encodeMontZMod x) = encodeMontZMod x := by
  unfold pow8ZMod
  simp only [encodeMontZMod_len, beq_self_eq_true, ↓reduceIte]
  rcases decodeMont32_encodeMontZMod_pm x with hd | hd
  · rw [hd]
  · rw [hd, encodeMontZMod_neg]

theorem pow8ZMod_idemp (p : Bytes) : pow8ZMod (pow8ZMod p) = pow8ZMod p := by
  unfold pow8ZMod
  by_cases hp : p.length == 32
  · simp only [hp, ↓reduceIte]
    have h := pow8ZMod_encodeMontZMod (decodeMont32 p)
    unfold pow8ZMod at h
    exact h
  · simp only [hp, Bool.false_eq_true, ↓reduceIte, ← encodeMontZMod_zero]
    have h := pow8ZMod_encodeMontZMod 0
    unfold pow8ZMod at h
    exact h

theorem pow8ZMod_of_isCanonMont32 {pk : Bytes} (hc : isCanonMont32 pk = true) :
    pow8ZMod pk = pk := by
  obtain ⟨hlen, _, hle⟩ := isCanonMont32_spec.mp hc
  have hlt_l : natOfBytesLE pk < l25519 :=
    lt_trans (lt_of_le_of_lt hle halfL25519_lt_two_pow_252) two_pow_252_lt_l25519
  unfold pow8ZMod encodeMontZMod decodeMont32
  simp only [hlen, beq_self_eq_true, ↓reduceIte, hc, absZMod,
    ZMod.val_natCast_of_lt hlt_l, hle]
  conv_rhs => rw [← bytesOfNatLE_natOfBytesLE pk, hlen]

theorem x25519ZMod_encodeMontZMod (a : Bytes) (y : ZMod l25519) :
    x25519ZMod a (encodeMontZMod y) = encodeMontZMod (clampedScalarZMod a * y) := by
  unfold x25519ZMod
  have hfit : fitBytesRef 32 (encodeMontZMod y) = encodeMontZMod y := by
    unfold fitBytesRef
    rw [encodeMontZMod_len, List.take_of_length_le (by rw [encodeMontZMod_len]),
      Nat.sub_self, List.replicate_zero, List.append_nil]
  rw [hfit]
  rcases decodeMont32_encodeMontZMod_pm y with hd | hd
  · rw [hd]
  · rw [hd, mul_neg, encodeMontZMod_neg]

theorem x25519ZMod_congr_of_base_eq_any (a1 a2 pk : Bytes)
    (h : x25519BaseZMod a1 = x25519BaseZMod a2) :
    x25519ZMod a1 pk = x25519ZMod a2 pk := by
  unfold x25519BaseZMod at h
  unfold x25519ZMod
  rcases (encodeMontZMod_eq_iff _ _).mp h with hc | hc
  · rw [hc]
  · rw [hc, neg_mul, encodeMontZMod_neg]

/-- Leaf primitives over `ZMod l25519` with KEM, SPQR, SHA-256, and AES fields from
    `cwfLeafPrimitives`. -/
def pZModLeaf : Primitives :=
  { cwfLeafPrimitives with
    x25519 := x25519ZMod
    x25519Base := x25519BaseZMod
    isCanonical := isCanonMont32
    sigPkGen := x25519BaseZMod
    scalarMul := fun a b =>
      encodeScalarBytes (decodeScalarBytes (fitBytesRef 32 a) * decodeScalarBytes (fitBytesRef 32 b))
    scalarAdd := fun a b =>
      encodeScalarBytes (decodeScalarBytes (fitBytesRef 32 a) + decodeScalarBytes (fitBytesRef 32 b))
    scalarFromBytesModOrder := fun bs => encodeScalarBytes (decodeScalarBytes (fitBytesRef 32 bs))
    scalarFromWide := fun w => encodeScalarBytes (decodeScalarBytes (fitBytesRef 64 w))
    montToEd := montToEdZMod
    isTorsionFree := fun _ => true
    edNeg := fun pt => encodeEdZMod (-decodeEdZMod pt)
    doubleScalarMulBasepoint := fun h pt s =>
      encodeEdZMod (decodeScalarBytes (fitBytesRef 32 h) * decodeEdZMod pt +
        decodeScalarBytes (fitBytesRef 32 s))
    compress := fun pt => compressEdZMod (decodeEdZMod pt)
    sha512Compress := sha512CompressZMod
    pow8 := pow8ZMod }

def pZModStep1 : Primitives :=
  { pZModLeaf with
    sha512          := sha512Ref pZModLeaf
    hkdfDerive96    := hkdfDerive96Ref pZModLeaf
    rootCreateChain := rootCreateChainRef pZModLeaf
    chainKdfSeed    := chainKdfSeedRef pZModLeaf
    chainKdfNext    := chainKdfNextRef pZModLeaf
    deriveMsgKeys   := deriveMsgKeysRef pZModLeaf
    aeadEnc         := aes256CbcHmacEncRef pZModLeaf
    aeadDec         := aes256CbcHmacDecRef pZModLeaf }

/-- Computable pre-witness with reference KDF, AEAD, SHA-512, `xeddsaSignRef`, and
    `xeddsaVerifyRef` implementations. -/
def pZModPre : Primitives :=
  { pZModStep1 with
    sigSign   := xeddsaSignRef pZModStep1
    sigVerify := xeddsaVerifyRef pZModStep1 }

/-- Noncomputable extension of `pZModPre` with the classical `isValidDhTripleRef` DDH oracle;
    agrees definitionally with `pZModPre` on `sigSign` and `sigVerify`. -/
noncomputable def pZMod : Primitives :=
  { pZModPre with
    isValidDhTriple := fun X Y Z =>
      @decide (isValidDhTripleRef pZModPre X Y Z) (Classical.propDecidable _) }

private theorem sha256Ref_congr {P Q : Primitives} (h : P.sha256Compress = Q.sha256Compress) :
    sha256Ref P = sha256Ref Q := by
  funext msg; unfold sha256Ref sha256Step; rw [h]

private theorem sha512Ref_congr {P Q : Primitives} (h : P.sha512Compress = Q.sha512Compress) :
    sha512Ref P = sha512Ref Q := by
  funext msg; unfold sha512Ref sha512Step; rw [h]

private theorem hmacSha256Ref_congr {P Q : Primitives} (h : P.sha256Compress = Q.sha256Compress) :
    hmacSha256Ref P = hmacSha256Ref Q := by
  funext key msg; unfold hmacSha256Ref; rw [sha256Ref_congr h]

private theorem hkdfExtractRef_congr {P Q : Primitives} (h : P.sha256Compress = Q.sha256Compress) :
    hkdfExtractRef P = hkdfExtractRef Q := by
  funext salt? ikm; unfold hkdfExtractRef; rw [hmacSha256Ref_congr h]

private theorem hkdfDerive96Ref_congr {P Q : Primitives}
    (h : P.sha256Compress = Q.sha256Compress) :
    hkdfDerive96Ref P = hkdfDerive96Ref Q := by
  funext secrets; unfold hkdfDerive96Ref hkdfExpand96Ref
  rw [hkdfExtractRef_congr h, hmacSha256Ref_congr h]

private theorem rootCreateChainRef_congr {P Q : Primitives}
    (h : P.sha256Compress = Q.sha256Compress) :
    rootCreateChainRef P = rootCreateChainRef Q := by
  funext rk dh; unfold rootCreateChainRef
  rw [hkdfExtractRef_congr h, hmacSha256Ref_congr h]

private theorem chainKdfSeedRef_congr {P Q : Primitives}
    (h : P.sha256Compress = Q.sha256Compress) :
    chainKdfSeedRef P = chainKdfSeedRef Q := by
  funext ck; unfold chainKdfSeedRef; rw [hmacSha256Ref_congr h]

private theorem chainKdfNextRef_congr {P Q : Primitives}
    (h : P.sha256Compress = Q.sha256Compress) :
    chainKdfNextRef P = chainKdfNextRef Q := by
  funext ck; unfold chainKdfNextRef; rw [hmacSha256Ref_congr h]

private theorem deriveMsgKeysRef_congr {P Q : Primitives}
    (h : P.sha256Compress = Q.sha256Compress) :
    deriveMsgKeysRef P = deriveMsgKeysRef Q := by
  funext mkSeed salt?; unfold deriveMsgKeysRef
  rw [hkdfExtractRef_congr h, hmacSha256Ref_congr h]

private theorem aes256CbcHmacEncRef_congr {P Q : Primitives}
    (hsha : P.sha256Compress = Q.sha256Compress) (haes : P.aesEncBlock = Q.aesEncBlock) :
    aes256CbcHmacEncRef P = aes256CbcHmacEncRef Q := by
  funext mk ad pt; unfold aes256CbcHmacEncRef aes256CbcEncRef cbcEncBlocks
  rw [haes, hmacSha256Ref_congr hsha]

private theorem aes256CbcHmacDecRef_congr {P Q : Primitives}
    (hsha : P.sha256Compress = Q.sha256Compress) (haes : P.aesDecBlock = Q.aesDecBlock) :
    aes256CbcHmacDecRef P = aes256CbcHmacDecRef Q := by
  funext mk ad ctAndTag; unfold aes256CbcHmacDecRef aes256CbcDecRef cbcDecBlocks
  rw [haes, hmacSha256Ref_congr hsha]

private theorem xeddsaVerifyRef_congr {P Q : Primitives}
    (hmont : P.montToEd = Q.montToEd) (hcomp : P.compress = Q.compress)
    (hneg : P.edNeg = Q.edNeg) (hsha : P.sha512 = Q.sha512)
    (hwide : P.scalarFromWide = Q.scalarFromWide)
    (hmod : P.scalarFromBytesModOrder = Q.scalarFromBytesModOrder)
    (hdsmb : P.doubleScalarMulBasepoint = Q.doubleScalarMulBasepoint) :
    xeddsaVerifyRef P = xeddsaVerifyRef Q := by
  funext pk m sig; unfold xeddsaVerifyRef
  rw [hmont, hcomp, hneg, hsha, hwide, hmod, hdsmb]

private theorem xeddsaSignRef_congr {P Q : Primitives}
    (hbase : P.x25519Base = Q.x25519Base)
    (hmont : P.montToEd = Q.montToEd) (hcomp : P.compress = Q.compress)
    (hsha : P.sha512 = Q.sha512)
    (hwide : P.scalarFromWide = Q.scalarFromWide)
    (hmod : P.scalarFromBytesModOrder = Q.scalarFromBytesModOrder)
    (hmul : P.scalarMul = Q.scalarMul) (hadd : P.scalarAdd = Q.scalarAdd)
    (hdsmb : P.doubleScalarMulBasepoint = Q.doubleScalarMulBasepoint) :
    xeddsaSignRef P = xeddsaSignRef Q := by
  funext sk m rand; unfold xeddsaSignRef edBaseMul edDummy
  rw [hbase, hmont, hcomp, hsha, hwide, hmod, hmul, hadd, hdsmb]

private theorem isValidDhTripleRef_congr {P Q : Primitives}
    (hcan : P.isCanonical = Q.isCanonical)
    (hbase : P.x25519Base = Q.x25519Base) (hpow : P.pow8 = Q.pow8)
    (hx : P.x25519 = Q.x25519) (X Y Z : Bytes) :
    isValidDhTripleRef P X Y Z ↔ isValidDhTripleRef Q X Y Z := by
  unfold isValidDhTripleRef onCurveKey; rw [hcan, hbase, hpow, hx]

private theorem sampleKemKeyGen_congr {P Q : Primitives}
    (hkem : P.kemKeyGen = Q.kemKeyGen) :
    sampleKemKeyGen P = sampleKemKeyGen Q := by
  unfold sampleKemKeyGen; rw [hkem]

theorem pZMod_sigSign_eq_ref : pZMod.sigSign = xeddsaSignRef pZMod :=
  xeddsaSignRef_congr (P := pZModStep1) (Q := pZMod) rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem pZMod_sigVerify_eq_ref : pZMod.sigVerify = xeddsaVerifyRef pZMod :=
  xeddsaVerifyRef_congr (P := pZModStep1) (Q := pZMod) rfl rfl rfl rfl rfl rfl rfl

theorem fitBytesRef_32_encodeScalarBytes (x : ZMod l25519) :
    fitBytesRef 32 (encodeScalarBytes x) = encodeScalarBytes x := by
  unfold fitBytesRef
  rw [encodeScalarBytes_length, List.take_of_length_le (by rw [encodeScalarBytes_length]),
    Nat.sub_self, List.replicate_zero, List.append_nil]

def pZModCurveWitness : XeddsaCurveWitness pZMod where
  x25519Base_len := fun k => encodeMontZMod_len (clampedScalarZMod k)
  scalarMod_eq := fun _ => rfl
  scalarWide_eq := fun _ => rfl
  scalarAdd_eq := fun x y => by
    show encodeScalarBytes (decodeScalarBytes (fitBytesRef 32 (encodeScalarBytes x)) +
      decodeScalarBytes (fitBytesRef 32 (encodeScalarBytes y))) = encodeScalarBytes (x + y)
    rw [fitBytesRef_32_encodeScalarBytes, fitBytesRef_32_encodeScalarBytes,
      decodeScalarBytes_encodeScalarBytes, decodeScalarBytes_encodeScalarBytes]
  scalarMul_eq := fun x y => by
    show encodeScalarBytes (decodeScalarBytes (fitBytesRef 32 (encodeScalarBytes x)) *
      decodeScalarBytes (fitBytesRef 32 (encodeScalarBytes y))) = encodeScalarBytes (x * y)
    rw [fitBytesRef_32_encodeScalarBytes, fitBytesRef_32_encodeScalarBytes,
      decodeScalarBytes_encodeScalarBytes, decodeScalarBytes_encodeScalarBytes]
  RepresentsEd := fun x pt => pt = encodeEdZMod x
  compressEd := compressEdZMod
  edSign := edSignZMod
  edNeg_represents := by
    rintro x _ rfl
    show encodeEdZMod (-decodeEdZMod (encodeEdZMod x)) = encodeEdZMod (-x)
    rw [decodeEdZMod_encodeEdZMod]
  dsmb_represents := by
    rintro h y _ s rfl
    show encodeEdZMod (decodeScalarBytes (fitBytesRef 32 (encodeScalarBytes h)) *
      decodeEdZMod (encodeEdZMod y) +
      decodeScalarBytes (fitBytesRef 32 (encodeScalarBytes s))) = encodeEdZMod (h * y + s)
    rw [fitBytesRef_32_encodeScalarBytes, fitBytesRef_32_encodeScalarBytes,
      decodeScalarBytes_encodeScalarBytes, decodeScalarBytes_encodeScalarBytes,
      decodeEdZMod_encodeEdZMod]
  compress_of_represents := by
    rintro x _ rfl
    show compressEdZMod (decodeEdZMod (encodeEdZMod x)) = compressEdZMod x
    rw [decodeEdZMod_encodeEdZMod]
  compressEd_inj := compressEdZMod_inj
  compressEd_len := compressEdZMod_len
  compressEd_inRange := compressEdZMod_inRange
  edSign_bool := edSignZMod_bool
  edSign_neg := edSignZMod_neg
  compressEd_signBit := compressEdZMod_signBit
  montToEd_base := by
    intro sk b hb
    set a := clampedScalarZMod sk
    have ha0 : a ≠ 0 := clampedScalarZMod_ne_zero sk
    have hc : isCanonMont32 (encodeMontZMod a) = true :=
      (isCanonMont32_encodeMontZMod_iff a).mpr ha0
    have hb_cond : (b == 0 || b == 1) = true := by
      rcases hb with rfl | rfl <;> rfl
    have hx0_cast : (natOfBytesLE (encodeMontZMod a) : ZMod l25519) =
        if edSignZMod a = 0 then a else -a := by
      rw [natOfBytesLE_encodeMontZMod]
      by_cases hle : a.val ≤ halfL25519
      · have hs : edSignZMod a = 0 := by unfold edSignZMod; simp [hle]
        have habs : absZMod a = a.val := by unfold absZMod; simp [hle]
        simp [hs, habs]
      · have hs : edSignZMod a = 1 := by unfold edSignZMod; simp [hle]
        have habs : absZMod a = l25519 - a.val := by unfold absZMod; simp [hle]
        have hcast : ((l25519 - a.val : ℕ) : ZMod l25519) = -a := by
          rw [Nat.cast_sub (le_of_lt a.val_lt), ZMod.natCast_self, zero_sub, ZMod.natCast_zmod_val]
        simp [hs, habs, hcast]
    refine ⟨encodeEdZMod (if b == edSignZMod a then a else -a), ?_, rfl⟩
    show montToEdZMod (encodeMontZMod a) b =
      some (encodeEdZMod (if b == edSignZMod a then a else -a))
    unfold montToEdZMod
    rw [hb_cond, hc]
    simp only [Bool.and_self, ↓reduceIte, hx0_cast]
    rcases hb with rfl | rfl <;> rcases edSignZMod_bool a with hs | hs <;> simp [hs]
  x25519Base_eq_of_clamped_pm := by
    intro u1 u2 hpm
    exact (encodeMontZMod_eq_iff _ _).mpr hpm

theorem pZMod_xeddsaCurveLaws : XeddsaCurveLaws pZMod :=
  ⟨pZModCurveWitness⟩

theorem pZMod_isCanonical_eq_isCanonicalRef (pk : Bytes) :
    pZMod.isCanonical pk = isCanonicalRef pZMod pk := by
  show isCanonMont32 pk = isCanonicalRef pZMod pk
  unfold isCanonicalRef
  change isCanonMont32 pk =
    (if pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && scalarIsInRange pk then
      match montToEdZMod pk 0 with
      | some _ => true
      | none => false
    else false)
  by_cases hc : isCanonMont32 pk = true
  · obtain ⟨hlen, _, hle⟩ := isCanonMont32_spec.mp hc
    have hlt : natOfBytesLE pk < 2 ^ 252 := lt_of_le_of_lt hle halfL25519_lt_two_pow_252
    obtain ⟨h80, hrange⟩ := scalarIsInRange_of_lt_two_pow_252 hlt
    rw [hc, hlen, h80, hrange]
    simp [montToEdZMod, hc]
  · have hf : isCanonMont32 pk = false := Bool.eq_false_iff.mpr hc
    have hmont : montToEdZMod pk 0 = none := by simp [montToEdZMod, hf]
    rw [hf, hmont]
    split <;> rfl

theorem pZMod_x25519_comm (a b : Bytes) :
    x25519ZMod a (x25519BaseZMod b) = x25519ZMod b (x25519BaseZMod a) := by
  unfold x25519BaseZMod
  rw [x25519ZMod_encodeMontZMod, x25519ZMod_encodeMontZMod, mul_comm]

private theorem pZMod_isValidDhTriple_eq_ref (X Y Z : Bytes) :
    pZMod.isValidDhTriple X Y Z = true ↔ isValidDhTripleRef pZMod X Y Z :=
  (Iff.of_eq (@decide_eq_true_eq _ (Classical.propDecidable _))).trans
    (isValidDhTripleRef_congr (P := pZModPre) (Q := pZMod) rfl rfl rfl rfl X Y Z)

private theorem pZMod_ddh_symm (pk1 pk2 z : Bytes) :
    pZMod.isValidDhTriple pk1 pk2 z = pZMod.isValidDhTriple pk2 pk1 z := by
  rw [Bool.eq_iff_iff, pZMod_isValidDhTriple_eq_ref, pZMod_isValidDhTriple_eq_ref]
  unfold isValidDhTripleRef
  exact ⟨fun ⟨h1, h2, h⟩ => ⟨h2, h1, h.symm⟩, fun ⟨h2, h1, h⟩ => ⟨h1, h2, h.symm⟩⟩

private theorem pZMod_aesEncBlock_len (k blk : Bytes) :
    (pZMod.aesEncBlock k blk).length = 16 := by
  dsimp only [pZMod, pZModPre, pZModStep1, pZModLeaf, cwfLeafPrimitives, idealLeafPrimitives]
  rw [xorBytes_length, fitBytes_length, fitBytes_length]; rfl

private theorem pZMod_aesDecBlock_len (k blk : Bytes) :
    (pZMod.aesDecBlock k blk).length = 16 := by
  dsimp only [pZMod, pZModPre, pZModStep1, pZModLeaf, cwfLeafPrimitives, idealLeafPrimitives]
  rw [xorBytes_length, fitBytes_length, fitBytes_length]; rfl

private theorem pZMod_aesBlock_corr (k blk : Bytes) (hk : k.length = 32) (hb : blk.length = 16) :
    pZMod.aesDecBlock k (pZMod.aesEncBlock k blk) = blk := by
  have henc : pZMod.aesEncBlock = idealRoundtripPrimitives.aesEncBlock := rfl
  have hdec : pZMod.aesDecBlock = idealRoundtripPrimitives.aesDecBlock := rfl
  rw [hdec, henc]
  exact idealAesBlock_corr k blk hk hb

private theorem pZMod_canon_base (e : Bytes) :
    pZMod.isCanonical (pZMod.x25519Base e) = true := by
  have hc : pZMod.isCanonical = isCanonMont32 := rfl
  have hb : pZMod.x25519Base = fun k => encodeMontZMod (clampedScalarZMod k) := rfl
  rw [hc, hb]
  exact (isCanonMont32_encodeMontZMod_iff (clampedScalarZMod e)).mpr (clampedScalarZMod_ne_zero e)

theorem pZMod_ddh_consistent_onCurve (a pk z : Bytes) (hpk : onCurveKey pZMod pk) :
    pZMod.isValidDhTriple (pZMod.x25519Base a) pk z = true ↔
      pZMod.pow8 z = pZMod.pow8 (pZMod.x25519 a pk) := by
  rw [pZMod_isValidDhTriple_eq_ref]
  unfold isValidDhTripleRef
  have hbase_eq : pZMod.x25519Base = x25519BaseZMod := rfl
  have hpow_eq : pZMod.pow8 = pow8ZMod := rfl
  have hx_eq : pZMod.x25519 = x25519ZMod := rfl
  constructor
  · rintro ⟨_, _, ⟨a', hbase, hz⟩ | ⟨b, rfl, hz⟩⟩
    · rw [hbase_eq] at hbase
      rw [hpow_eq, hx_eq] at hz ⊢
      rwa [← x25519ZMod_congr_of_base_eq_any a a' pk hbase] at hz
    · rw [hbase_eq, hpow_eq, hx_eq] at hz ⊢
      rwa [pZMod_x25519_comm b a] at hz
  · intro hz
    exact ⟨Or.inl (pZMod_canon_base a), hpk, Or.inl ⟨a, rfl, hz⟩⟩

private theorem pZMod_canon_x25519 (a pk : Bytes) (_ : a.length = 32)
    (hcanon : pZMod.isCanonical pk = true) :
    pZMod.isCanonical (pZMod.x25519 a pk) = true := by
  have hc : pZMod.isCanonical = isCanonMont32 := rfl
  have hx : pZMod.x25519 = x25519ZMod := rfl
  rw [hc] at hcanon
  rw [hc, hx]
  obtain ⟨hlen, hpos, hle⟩ := isCanonMont32_spec.mp hcanon
  have hfit : fitBytesRef 32 pk = pk := by
    unfold fitBytesRef
    rw [hlen, List.take_of_length_le (by rw [hlen]), Nat.sub_self, List.replicate_zero,
      List.append_nil]
  have hdec_ne : decodeMont32 pk ≠ 0 := by
    unfold decodeMont32
    simp only [hcanon, ↓reduceIte]
    intro h0
    have hlt_l : natOfBytesLE pk < l25519 :=
      lt_trans (lt_of_le_of_lt hle halfL25519_lt_two_pow_252) two_pow_252_lt_l25519
    have hv := congrArg ZMod.val h0
    rw [ZMod.val_natCast_of_lt hlt_l, ZMod.val_zero] at hv
    omega
  unfold x25519ZMod
  rw [hfit, isCanonMont32_encodeMontZMod_iff]
  exact mul_ne_zero (clampedScalarZMod_ne_zero a) hdec_ne

private theorem pZMod_x25519_pow8_congr (a pk1 pk2 : Bytes)
    (h1 : pk1.length = 32) (h2 : pk2.length = 32)
    (hpow : pZMod.pow8 pk1 = pZMod.pow8 pk2) :
    pZMod.x25519 a pk1 = pZMod.x25519 a pk2 := by
  change pow8ZMod pk1 = pow8ZMod pk2 at hpow
  show x25519ZMod a pk1 = x25519ZMod a pk2
  have hfit1 : fitBytesRef 32 pk1 = pk1 := by
    unfold fitBytesRef
    rw [h1, List.take_of_length_le (by rw [h1]), Nat.sub_self, List.replicate_zero,
      List.append_nil]
  have hfit2 : fitBytesRef 32 pk2 = pk2 := by
    unfold fitBytesRef
    rw [h2, List.take_of_length_le (by rw [h2]), Nat.sub_self, List.replicate_zero,
      List.append_nil]
  unfold pow8ZMod at hpow
  simp only [h1, h2, beq_self_eq_true, ↓reduceIte] at hpow
  unfold x25519ZMod
  rw [hfit1, hfit2]
  rcases (encodeMontZMod_eq_iff _ _).mp hpow with hd | hd
  · rw [hd]
  · rw [hd, mul_neg, encodeMontZMod_neg]

private theorem pZMod_aead_corr (mk : MessageKeys) (ad pt : Bytes) :
    pZMod.aeadDec mk ad (pZMod.aeadEnc mk ad pt) = some pt := by
  have henc : pZMod.aeadEnc mk ad pt = aes256CbcHmacEncRef pZMod mk ad pt :=
    congrFun (congrFun (congrFun
      (aes256CbcHmacEncRef_congr (P := pZModLeaf) (Q := pZMod) rfl rfl) mk) ad) pt
  have hdec : ∀ ct, pZMod.aeadDec mk ad ct = aes256CbcHmacDecRef pZMod mk ad ct := fun ct =>
    congrFun (congrFun (congrFun
      (aes256CbcHmacDecRef_congr (P := pZModLeaf) (Q := pZMod) rfl rfl) mk) ad) ct
  rw [hdec, henc]
  exact aes256CbcHmac_roundtrip pZMod pZMod_aesEncBlock_len pZMod_aesBlock_corr mk ad pt

private theorem pZMod_kem_corr (seed r ss ct : Bytes)
    (hEnc : pZMod.kemEncaps (pZMod.kemKeyGen seed).1 r = some (ss, ct)) :
    pZMod.kemDecaps (pZMod.kemKeyGen seed).2 ct = some ss := by
  have henc' : pZMod.kemEncaps = cwfLeafPrimitives.kemEncaps := rfl
  have hdec' : pZMod.kemDecaps = cwfLeafPrimitives.kemDecaps := rfl
  have hkg' : pZMod.kemKeyGen = idealLeafPrimitives.kemKeyGen := rfl
  rw [henc', hkg'] at hEnc
  rw [hdec', hkg']
  dsimp only [cwfLeafPrimitives, idealLeafPrimitives] at hEnc ⊢
  have hpk : ((fitBytes 1568 (seed.take 32)).length == kyberPkLen) = true := by
    simp [fitBytes_length, kyberPkLen]
  rw [hpk] at hEnc
  simp only [↓reduceIte] at hEnc
  injection hEnc with hPair
  injection hPair with hSs hCt
  subst hSs; subst hCt
  have hct : ((fitBytes 32 r ++ List.replicate 1536 0).length == kyberCtLen) = true := by
    rw [List.length_append, fitBytes_length, List.length_replicate]; rfl
  rw [hct]
  simp only [↓reduceIte]
  congr 1
  have hlen : (fitBytes 32 r).length = 32 := fitBytes_length 32 r
  have htake : (fitBytes 32 r ++ List.replicate 1536 0).take 32 = fitBytes 32 r := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  rw [htake, fitBytes_of_length_eq hlen]

private theorem pZMod_sig_corr (sk msg r : Bytes) :
    pZMod.sigVerify (pZMod.sigPkGen sk) msg (pZMod.sigSign sk msg r) = true := by
  have hsig : pZMod.sigSign sk msg r = xeddsaSignRef pZMod sk msg r :=
    congrFun (congrFun (congrFun pZMod_sigSign_eq_ref sk) msg) r
  have hver : ∀ pk m s, pZMod.sigVerify pk m s = xeddsaVerifyRef pZMod pk m s :=
    fun pk m s => congrFun (congrFun (congrFun pZMod_sigVerify_eq_ref pk) m) s
  have hpk : pZMod.sigPkGen = pZMod.x25519Base := rfl
  rw [hver, hpk, hsig]
  exact xeddsaSignRef_correct pZMod_xeddsaCurveLaws sk msg r

private theorem pZMod_kemEncaps_len (pk r ss ct : Bytes)
    (hEnc : pZMod.kemEncaps pk r = some (ss, ct)) :
    ss.length = 32 ∧ ct.length = 1568 := by
  have henc' : pZMod.kemEncaps = cwfLeafPrimitives.kemEncaps := rfl
  rw [henc'] at hEnc
  dsimp only [cwfLeafPrimitives] at hEnc
  split at hEnc
  · injection hEnc with hPair
    injection hPair with hSs hCt
    subst hSs; subst hCt
    refine ⟨fitBytes_length 32 r, ?_⟩
    rw [List.length_append, fitBytes_length, List.length_replicate]
  · contradiction

private theorem pZMod_kemDecaps_len (sk ct ss : Bytes)
    (hDec : pZMod.kemDecaps sk ct = some ss) :
    ss.length = 32 := by
  have hdec' : pZMod.kemDecaps = cwfLeafPrimitives.kemDecaps := rfl
  rw [hdec'] at hDec
  dsimp only [cwfLeafPrimitives] at hDec
  split at hDec
  · injection hDec with hSs
    subst hSs
    exact fitBytes_length 32 (ct.take 32)
  · contradiction

private theorem pZMod_spqr_corr (pqrKey coins stA : Bytes) (salt? : Option Bytes) (pqMsg : Bytes)
    (hSend : pZMod.spqrInitSend pqrKey coins = some (stA, salt?, pqMsg)) :
    ∃ stB, pZMod.spqrInitRecv pqrKey pqMsg = some (stB, salt?) := by
  have hs : pZMod.spqrInitSend = idealLeafPrimitives.spqrInitSend := rfl
  have hr : pZMod.spqrInitRecv = idealLeafPrimitives.spqrInitRecv := rfl
  rw [hs] at hSend; rw [hr]
  dsimp only [idealLeafPrimitives] at hSend ⊢
  injection hSend with hTuple
  injection hTuple with _ hRest
  injection hRest with hSalt _
  exact ⟨pqrKey, by rw [← hSalt]⟩

private theorem pZMod_spqrInitRecv_salt_len (pqrKey pqMsg stB salt : Bytes)
    (hRecv : pZMod.spqrInitRecv pqrKey pqMsg = some (stB, some salt)) :
    salt.length ≤ 32 := by
  have hr : pZMod.spqrInitRecv = idealLeafPrimitives.spqrInitRecv := rfl
  rw [hr] at hRecv
  dsimp only [idealLeafPrimitives] at hRecv
  injection hRecv with hTuple
  injection hTuple with _ hSalt
  injection hSalt with hSalt
  rw [← hSalt]; simp

theorem pZMod_wellFormedδ : WellFormedPrimitivesδ pZMod where
  sha256Compress_len := fun _ _ => fitBytes_length 32 _
  sha512Compress_len := fun _ _ => fitBytes_length 64 _
  aesEncBlock_len := pZMod_aesEncBlock_len
  aesDecBlock_len := pZMod_aesDecBlock_len
  aesBlock_corr := pZMod_aesBlock_corr
  sha512_eq_ref := congrFun (sha512Ref_congr (P := pZModLeaf) (Q := pZMod) rfl)
  hkdfDerive96_eq_ref := congrFun (hkdfDerive96Ref_congr (P := pZModLeaf) (Q := pZMod) rfl)
  rootCreateChain_eq_ref := fun rk dh =>
    congrFun (congrFun (rootCreateChainRef_congr (P := pZModLeaf) (Q := pZMod) rfl) rk) dh
  chainKdfSeed_eq_ref := congrFun (chainKdfSeedRef_congr (P := pZModLeaf) (Q := pZMod) rfl)
  chainKdfNext_eq_ref := congrFun (chainKdfNextRef_congr (P := pZModLeaf) (Q := pZMod) rfl)
  deriveMsgKeys_eq_ref := fun mkSeed salt? =>
    congrFun (congrFun (deriveMsgKeysRef_congr (P := pZModLeaf) (Q := pZMod) rfl) mkSeed) salt?
  aeadEnc_eq_ref := fun mk ad pt =>
    congrFun (congrFun (congrFun
      (aes256CbcHmacEncRef_congr (P := pZModLeaf) (Q := pZMod) rfl rfl) mk) ad) pt
  aeadDec_eq_ref := fun mk ad ct =>
    congrFun (congrFun (congrFun
      (aes256CbcHmacDecRef_congr (P := pZModLeaf) (Q := pZMod) rfl rfl) mk) ad) ct
  x25519_clamp := fun sk pk => by
    show x25519ZMod (clampScalar25519 sk) pk = x25519ZMod sk pk
    simp [x25519ZMod, clampedScalarZMod_clamp]
  x25519Base_clamp := fun sk => by
    show x25519BaseZMod (clampScalar25519 sk) = x25519BaseZMod sk
    simp [x25519BaseZMod, clampedScalarZMod_clamp]
  x25519_base_ne_zero := fun a b _ _ => by
    show x25519ZMod a (x25519BaseZMod b) ≠ List.replicate 32 0
    unfold x25519BaseZMod
    rw [x25519ZMod_encodeMontZMod, ne_eq, encodeMontZMod_eq_zero_iff]
    exact mul_ne_zero (clampedScalarZMod_ne_zero a) (clampedScalarZMod_ne_zero b)
  x25519_zero_iff := fun a1 a2 pk _ _ _ => by
    show x25519ZMod a1 pk = List.replicate 32 0 ↔ x25519ZMod a2 pk = List.replicate 32 0
    unfold x25519ZMod
    rw [encodeMontZMod_eq_zero_iff, encodeMontZMod_eq_zero_iff,
      mul_eq_zero_iff_left (clampedScalarZMod_ne_zero a1),
      mul_eq_zero_iff_left (clampedScalarZMod_ne_zero a2)]
  kemDecaps_isSome := fun _ ct _ hct => by
    change (if ct.length == kyberCtLen then _ else none).isSome = true
    simp [hct, kyberCtLen]
  kemEncaps_isSome := fun pk _ hpk _ => by
    change (if pk.length == kyberPkLen then _ else none).isSome = true
    simp [hpk, kyberPkLen]
  x25519_comm := pZMod_x25519_comm
  canon_base := pZMod_canon_base
  canon_x25519 := pZMod_canon_x25519
  sigPkGen_eq_x25519Base := rfl
  pow8_idemp := pow8ZMod_idemp
  pow8_x25519_comm := fun a b => congrArg pow8ZMod (pZMod_x25519_comm a b)
  ddh_consistent := fun a b z =>
    pZMod_ddh_consistent_onCurve a (pZMod.x25519Base b) z (Or.inl (pZMod_canon_base b))
  ddh_consistent_left := fun a pk z hpk => pZMod_ddh_consistent_onCurve a pk z hpk
  ddh_symm := pZMod_ddh_symm
  isValidDhTriple_eq_ref := pZMod_isValidDhTriple_eq_ref
  x25519_pow8_congr := pZMod_x25519_pow8_congr
  x25519_congr_of_base_eq := fun a1 a2 pk _ _ _ h => x25519ZMod_congr_of_base_eq_any a1 a2 pk h
  canon_pow8_inj := fun pk1 pk2 h1 h2 hpow => by
    change isCanonMont32 pk1 = true at h1
    change isCanonMont32 pk2 = true at h2
    change pow8ZMod pk1 = pow8ZMod pk2 at hpow
    rwa [pow8ZMod_of_isCanonMont32 h1, pow8ZMod_of_isCanonMont32 h2] at hpow
  x25519_len := fun _ _ => encodeMontZMod_len _
  x25519Base_len := fun _ => encodeMontZMod_len _
  pow8_len := fun p => by
    have hp : pZMod.pow8 = pow8ZMod := rfl
    rw [hp]
    unfold pow8ZMod
    split
    · exact encodeMontZMod_len _
    · simp
  sha512_len := sha512Ref_length pZModLeaf
  scalarMul_len := fun _ _ => encodeScalarBytes_length _
  scalarAdd_len := fun _ _ => encodeScalarBytes_length _
  scalarFromBytesModOrder_len := fun _ => encodeScalarBytes_length _
  scalarFromWide_len := fun _ => encodeScalarBytes_length _
  montToEd_len := fun u s pt h => by
    change montToEdZMod u s = some pt at h
    unfold montToEdZMod at h
    split at h
    · injection h with hpt
      subst hpt
      split <;> exact encodeEdZMod_len _
    · contradiction
  edNeg_len := fun _ => encodeEdZMod_len _
  doubleScalarMulBasepoint_len := fun _ _ _ => encodeEdZMod_len _
  compress_len := fun _ => compressEdZMod_len _
  sigVerify_eq_xeddsaVerifyRef := fun pk m s =>
    congrFun (congrFun (congrFun pZMod_sigVerify_eq_ref pk) m) s
  isCanonical_eq_isCanonicalRef := pZMod_isCanonical_eq_isCanonicalRef
  kemKeyGen_valid := fun seed => by
    have hkg : pZMod.kemKeyGen = idealLeafPrimitives.kemKeyGen := rfl
    rw [hkg]
    exact ⟨fitBytes_length 1568 (seed.take 32), fitBytes_length 3168 seed⟩
  kemEncaps_len := pZMod_kemEncaps_len
  kemDecaps_len := pZMod_kemDecaps_len
  spqrInitSend_some := fun _ _ => rfl
  aead_corr := pZMod_aead_corr
  sig_corr := pZMod_sig_corr
  spqr_corr := pZMod_spqr_corr
  spqrInitRecv_salt_len := pZMod_spqrInitRecv_salt_len

theorem pZMod_wellFormed : WellFormedPrimitives pZMod :=
  { pZMod_wellFormedδ with kem_corr := pZMod_kem_corr }

theorem clampScalar25519_eq_of_clampedScalarZMod_eq {sk1 sk2 : Bytes}
    (h : clampedScalarZMod sk1 = clampedScalarZMod sk2) :
    clampScalar25519 sk1 = clampScalar25519 sk2 := by
  obtain ⟨k1, hk1_eq, _, hk1_hi⟩ := natOfBytesLE_clampScalar25519_bounds sk1
  obtain ⟨k2, hk2_eq, _, hk2_hi⟩ := natOfBytesLE_clampScalar25519_bounds sk2
  unfold clampedScalarZMod decodeScalarBytes at h
  rw [hk1_eq, hk2_eq, Nat.cast_mul, Nat.cast_mul,
    show ((8 : ℕ) : ZMod l25519) = (8 : ZMod l25519) from rfl] at h
  have hk_cast : (k1 : ZMod l25519) = (k2 : ZMod l25519) :=
    mul_left_cancel₀ eight_ne_zero_zmod_l25519 h
  have hk_eq : k1 = k2 := by
    have hv := congrArg ZMod.val hk_cast
    rwa [ZMod.val_natCast_of_lt (lt_trans hk1_hi two_pow_252_lt_l25519),
      ZMod.val_natCast_of_lt (lt_trans hk2_hi two_pow_252_lt_l25519)] at hv
  have hl1 : (clampScalar25519 sk1).length = 32 := _root_.SignalPqxdh.clampScalar25519_length sk1
  have hl2 : (clampScalar25519 sk2).length = 32 := _root_.SignalPqxdh.clampScalar25519_length sk2
  calc clampScalar25519 sk1
      = bytesOfNatLE 32 (natOfBytesLE (clampScalar25519 sk1)) := by
          conv_lhs => rw [← bytesOfNatLE_natOfBytesLE (clampScalar25519 sk1), hl1]
    _ = bytesOfNatLE 32 (natOfBytesLE (clampScalar25519 sk2)) := by
          rw [hk1_eq, hk2_eq, hk_eq]
    _ = clampScalar25519 sk2 := by
          conv_rhs => rw [← bytesOfNatLE_natOfBytesLE (clampScalar25519 sk2), hl2]

theorem pZMod_ec_coll_bound (targetPk : Bytes) :
    (𝒟[do
        let sk ← sampleScalar32
        pure (pZMod.pow8 (pZMod.x25519Base sk) == pZMod.pow8 targetPk)] {true}).toReal
      ≤ 1 / (2 : ℝ) ^ 250 := by
  let f : BitVec 256 → Bool :=
    fun w => pow8ZMod (x25519BaseZMod (word256ToBytes w)) == pow8ZMod targetPk
  change (𝒟[do
      let sk ← sampleScalar32
      pure (pow8ZMod (x25519BaseZMod sk) == pow8ZMod targetPk)] {true}).toReal
    ≤ 1 / (2 : ℝ) ^ 250
  have hexpr :
      (do
        let sk ← sampleScalar32
        pure (pow8ZMod (x25519BaseZMod sk) == pow8ZMod targetPk)) =
      (f <$> ($ᵗ BitVec 256)) := by
    simp [sampleScalar32, sampleBytes32, f, bind_pure_comp, Functor.map_map]
  rw [hexpr]
  refine le_trans (uniform256_map_bool_le f 64 ?_) (by norm_num)
  set S := Finset.univ.filter (fun w => f w = true)
  by_cases hne : S.Nonempty
  · obtain ⟨w0, hw0⟩ := hne
    have hw0_eq : pow8ZMod (x25519BaseZMod (word256ToBytes w0)) = pow8ZMod targetPk := by
      simpa [S, f] using hw0
    set c0 := clampedScalarZMod (word256ToBytes w0)
    have hc0_ne_neg : c0 ≠ -c0 := by
      intro h2c0
      have hc0_ne : c0 ≠ 0 := clampedScalarZMod_ne_zero (word256ToBytes w0)
      have hs := edSignZMod_neg c0 hc0_ne
      rw [← h2c0] at hs
      rcases edSignZMod_bool c0 with hb | hb <;> rw [hb] at hs <;>
        exact (by revert hs; decide)
    let tag : BitVec 256 → Bool × Fin 8 × Fin 4 := fun w =>
      (@decide (clampedScalarZMod (word256ToBytes w) = c0) (Classical.propDecidable _),
       ⟨w.toNat % 8, Nat.mod_lt _ (by decide)⟩,
       ⟨w.toNat / 2 ^ 254, Nat.div_lt_of_lt_mul (by have := w.isLt; omega)⟩)
    have hinj : Set.InjOn tag (S : Set (BitVec 256)) := by
      intro w1 hw1 w2 hw2 htag
      have hw1_eq : encodeMontZMod (clampedScalarZMod (word256ToBytes w1)) = encodeMontZMod c0 := by
        have h1 : pow8ZMod (x25519BaseZMod (word256ToBytes w1)) = pow8ZMod targetPk := by
          simpa [S, f] using hw1
        have h2 := h1.trans hw0_eq.symm
        simpa [x25519BaseZMod, pow8ZMod_encodeMontZMod] using h2
      have hw2_eq : encodeMontZMod (clampedScalarZMod (word256ToBytes w2)) = encodeMontZMod c0 := by
        have h1 : pow8ZMod (x25519BaseZMod (word256ToBytes w2)) = pow8ZMod targetPk := by
          simpa [S, f] using hw2
        have h2 := h1.trans hw0_eq.symm
        simpa [x25519BaseZMod, pow8ZMod_encodeMontZMod] using h2
      have hpm1 := (encodeMontZMod_eq_iff _ _).mp hw1_eq
      have hpm2 := (encodeMontZMod_eq_iff _ _).mp hw2_eq
      have htag_iff : (clampedScalarZMod (word256ToBytes w1) = c0) ↔
          (clampedScalarZMod (word256ToBytes w2) = c0) :=
        @decide_eq_decide _ _ (Classical.propDecidable _) (Classical.propDecidable _) |>.mp
          (congrArg Prod.fst htag)
      have hlo : w1.toNat % 8 = w2.toNat % 8 :=
        congrArg (fun p => p.2.1.val) htag
      have hhi : w1.toNat / 2 ^ 254 = w2.toNat / 2 ^ 254 :=
        congrArg (fun p => p.2.2.val) htag
      have hc_eq : clampedScalarZMod (word256ToBytes w1) = clampedScalarZMod (word256ToBytes w2) := by
        rcases hpm1 with hc1 | hc1 <;> rcases hpm2 with hc2 | hc2
        · exact hc1.trans hc2.symm
        · exfalso
          exact hc0_ne_neg (hc2.symm.trans (htag_iff.mp hc1)).symm
        · exfalso
          exact hc0_ne_neg (hc1.symm.trans (htag_iff.mpr hc2)).symm
        · exact hc1.trans hc2.symm
      have hcl_eq := clampScalar25519_eq_of_clampedScalarZMod_eq hc_eq
      have hcwf : cwfC (word256ToBytes w1) = cwfC (word256ToBytes w2) := by
        rw [← cwfC_clamp (word256ToBytes w1), ← cwfC_clamp (word256ToBytes w2), hcl_eq]
      exact cwfC_word_eq w1 w2 hcwf hlo hhi
    have hcard_le : S.card ≤ Fintype.card (Bool × Fin 8 × Fin 4) :=
      Finset.card_le_card_of_injOn tag (fun _ _ => Finset.mem_univ _) hinj
    have hcard64 : Fintype.card (Bool × Fin 8 × Fin 4) = 64 := by decide
    exact hcard_le.trans_eq hcard64
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

theorem pZMod_cryptoWellFormedδ : CryptoWellFormedPrimitivesδ pZMod :=
  { pZMod_wellFormedδ with
    ec_coll_bound := fun t => prob_le_one_div_two_pow_of_toReal (pZMod_ec_coll_bound t)
    kem_coll_bound := fun targetPk => prob_le_one_div_two_pow_of_toReal (by
      rw [sampleKemKeyGen_congr (P := pZMod) (Q := cwfPrimitives) rfl]
      exact cwfPrimitives_kem_coll_bound targetPk)
    x25519_inj_pow8 := fun a pk1 pk2 _ h1 h2 hx => by
      change x25519ZMod a pk1 = x25519ZMod a pk2 at hx
      show pow8ZMod pk1 = pow8ZMod pk2
      have hfit1 : fitBytesRef 32 pk1 = pk1 := by
        unfold fitBytesRef
        rw [h1, List.take_of_length_le (by rw [h1]), Nat.sub_self, List.replicate_zero,
          List.append_nil]
      have hfit2 : fitBytesRef 32 pk2 = pk2 := by
        unfold fitBytesRef
        rw [h2, List.take_of_length_le (by rw [h2]), Nat.sub_self, List.replicate_zero,
          List.append_nil]
      unfold x25519ZMod at hx
      rw [hfit1, hfit2] at hx
      unfold pow8ZMod
      simp only [h1, h2, beq_self_eq_true, ↓reduceIte]
      apply (encodeMontZMod_eq_iff _ _).mpr
      rcases (encodeMontZMod_eq_iff _ _).mp hx with hm | hm
      · exact Or.inl (mul_left_cancel₀ (clampedScalarZMod_ne_zero a) hm)
      · rw [← mul_neg] at hm
        exact Or.inr (mul_left_cancel₀ (clampedScalarZMod_ne_zero a) hm)
    pow8_base_len := fun p e hpow => by
      change pow8ZMod p = pow8ZMod (x25519BaseZMod e) at hpow
      unfold x25519BaseZMod at hpow
      rw [pow8ZMod_encodeMontZMod] at hpow
      by_contra hne
      have hp : pow8ZMod p = List.replicate 32 0 := by simp [pow8ZMod, hne]
      rw [hp] at hpow
      exact clampedScalarZMod_ne_zero e ((encodeMontZMod_eq_zero_iff _).mp hpow.symm)
    kemDecaps_len_reject := fun _ ct hct => by
      change (if ct.length == kyberCtLen then _ else none) = none
      simp [hct]
    kemEncaps_len_reject := fun pk _ hpk => by
      change (if pk.length == kyberPkLen then _ else none) = none
      simp [hpk] }

theorem pZMod_cryptoWellFormed : CryptoWellFormedPrimitives pZMod :=
  { pZMod_wellFormed, pZMod_cryptoWellFormedδ with }

theorem pZMod_kemDeltaCorrect : KemDeltaCorrect pZMod 0 := by
  unfold KemDeltaCorrect
  simp [kemHonestFail_eq_false_of_kem_corr pZMod_kem_corr]

/-- Joint satisfiability of the primitive, curve, KEM-correctness, and `xeddsaSignRef`
    hypotheses of the XEdDSA ROM reductions. -/
theorem xeddsaRom_hypotheses_satisfiable :
    ∃ P : Primitives,
      WellFormedPrimitivesδ P ∧
      CryptoWellFormedPrimitivesδ P ∧
      KemDeltaCorrect P 0 ∧
      XeddsaCurveLaws P ∧
      P.sigSign = xeddsaSignRef P :=
  ⟨pZMod, pZMod_wellFormedδ, pZMod_cryptoWellFormedδ, pZMod_kemDeltaCorrect,
    pZMod_xeddsaCurveLaws, pZMod_sigSign_eq_ref⟩

def romSignQuery (m : Bytes) : OracleComp XeddsaRomOracleSpec Bytes :=
  liftM (OracleSpec.query (spec := XeddsaRomOracleSpec) (.inr (.inl (.sign m))))

def romRoQuery (inp : Bytes) : OracleComp XeddsaRomOracleSpec Bytes :=
  liftM (OracleSpec.query (spec := XeddsaRomOracleSpec) (.inl (.inr inp)))

def romDdhQuery (q : DdhQuery) : OracleComp XeddsaRomOracleSpec Bool :=
  liftM (OracleSpec.query (spec := XeddsaRomOracleSpec) (.inr (.inr q)))

/-- Sample `GapDhWithSignRoAdv` that makes one `.sign`, one SHA-512 RO, and one `.ddh` query. -/
def sampleGapDhWithSignRoAdv : GapDhWithSignRoAdv where
  run := fun U V => do
    let sig ← romSignQuery [0x05]
    let d ← romRoQuery (U ++ V ++ sig)
    let _ ← romDdhQuery (U, V, d.take 32)
    return d.take 32
  q_ddh := 1
  q_sig := 1
  q_prim := 0
  q_ro := 1
  q_verify := 0
  q_prim_sigSign := 0

theorem sampleGapDhWithSignRoAdv_bounded : sampleGapDhWithSignRoAdv.Bounded := by
  unfold GapDhWithSignRoAdv.Bounded sampleGapDhWithSignRoAdv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro U V <;>
    simp [romSignQuery, romRoQuery, romDdhQuery, map_eq_bind_pure_comp,
      isQueryBoundP_query_bind_iff, isRomDdhChalQuery, isRomSigChalQuery, isRomPrimQuery,
      isRomDirectRoQuery, isRomPrimVerifyQuery, isRomPrimSigSignQuery]

/-- Sample `GapSigEufCmaRoAdv` that makes one `.sign`, one SHA-512 RO, and one `.ddh` query. -/
def sampleGapSigEufCmaRoAdv : GapSigEufCmaRoAdv where
  run := fun pk => do
    let sig ← romSignQuery [0x05]
    let _ ← romRoQuery (pk ++ sig)
    let _ ← romDdhQuery (pk, pk, pk)
    return ([0x08], sig)
  q_sig := 1
  q_ddh := 1
  q_prim := 0
  q_ro := 1
  q_verify := 0
  q_prim_sigSign := 0

theorem sampleGapSigEufCmaRoAdv_bounded : sampleGapSigEufCmaRoAdv.Bounded := by
  unfold GapSigEufCmaRoAdv.Bounded sampleGapSigEufCmaRoAdv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro pk <;>
    simp [romSignQuery, romRoQuery, romDdhQuery, map_eq_bind_pure_comp,
      isQueryBoundP_query_bind_iff, isRomDdhChalQuery, isRomSigChalQuery, isRomPrimQuery,
      isRomDirectRoQuery, isRomPrimVerifyQuery, isRomPrimSigSignQuery]

/-- Secret key whose clamped scalar has `edSignZMod = 0` (`4.5 · 2^252 mod l25519 < halfL25519`). -/
def skSignZero : Bytes :=
  List.replicate 31 0 ++ [0x48]

/-- Secret key whose clamped scalar has `edSignZMod = 1` (`4 · 2^252 mod l25519 > halfL25519`). -/
def skSignOne : Bytes :=
  List.replicate 32 0

def testMsg : Bytes :=
  [0x05] ++ List.ofFn (fun i : Fin 32 => UInt8.ofNat (i.val + 1))

def testRand : Bytes :=
  List.ofFn (fun i : Fin 64 => UInt8.ofNat (0xA0 + i.val))

def sigZero : Bytes := pZModPre.sigSign skSignZero testMsg testRand
def sigOne  : Bytes := pZModPre.sigSign skSignOne testMsg testRand

def flipByteAt (bs : Bytes) (idx : ℕ) (mask : UInt8) : Bytes :=
  bs.take idx ++ [bs.getD idx 0 ^^^ mask] ++ bs.drop (idx + 1)

def orByteAt (bs : Bytes) (idx : ℕ) (mask : UInt8) : Bytes :=
  bs.take idx ++ [bs.getD idx 0 ||| mask] ++ bs.drop (idx + 1)

#guard edSignZMod (clampedScalarZMod skSignZero) == 0
#guard edSignZMod (clampedScalarZMod skSignOne) == 1
#guard sigZero.length == 64 && ((sigZero.getD 63 0 &&& 0x80) >>> 7) == 0
#guard sigOne.length == 64 && ((sigOne.getD 63 0 &&& 0x80) >>> 7) == 1
#guard pZModPre.sigVerify (pZModPre.sigPkGen skSignZero) testMsg sigZero == true
#guard pZModPre.sigVerify (pZModPre.sigPkGen skSignOne) testMsg sigOne == true

-- Tamper rejection across both sign-bit branches: sign bit (byte 63, 0x80), message byte,
-- R commitment (byte 0), s response (byte 32), and reserved top bit (byte 63, 0x20).
#guard pZModPre.sigVerify (pZModPre.sigPkGen skSignZero) testMsg (flipByteAt sigZero 63 0x80) == false
#guard pZModPre.sigVerify (pZModPre.sigPkGen skSignOne) testMsg (flipByteAt sigOne 63 0x80) == false
#guard pZModPre.sigVerify (pZModPre.sigPkGen skSignZero) (flipByteAt testMsg 0 0x01) sigZero == false
#guard pZModPre.sigVerify (pZModPre.sigPkGen skSignOne) (flipByteAt testMsg 0 0x01) sigOne == false
#guard pZModPre.sigVerify (pZModPre.sigPkGen skSignZero) testMsg (flipByteAt sigZero 0 0x01) == false
#guard pZModPre.sigVerify (pZModPre.sigPkGen skSignOne) testMsg (flipByteAt sigOne 0 0x01) == false
#guard pZModPre.sigVerify (pZModPre.sigPkGen skSignZero) testMsg (flipByteAt sigZero 32 0x01) == false
#guard pZModPre.sigVerify (pZModPre.sigPkGen skSignOne) testMsg (flipByteAt sigOne 32 0x01) == false
#guard pZModPre.sigVerify (pZModPre.sigPkGen skSignZero) testMsg (orByteAt sigZero 63 0x20) == false
#guard pZModPre.sigVerify (pZModPre.sigPkGen skSignOne) testMsg (orByteAt sigOne 63 0x20) == false

theorem sample_gapDhWithSignRoBound1A :
    ∃ B₁ : GapDhAdv,
      B₁.Bounded ∧
      B₁.q_ddh ≤ 1 ∧
      B₁.q_prim ≤ 0 ∧
      GapDhWithSignRo pZMod pZMod.isValidDhTriple pZMod.pow8 sampleGapDhWithSignRoAdv ≤
        2 * GapDH pZMod pZMod.isValidDhTriple pZMod.pow8 B₁ + xeddsaSimLoss 1 1 :=
  gapDhWithSignRoBound1A_holds pZMod pZMod_wellFormedδ pZMod_xeddsaCurveLaws
    sampleGapDhWithSignRoAdv sampleGapDhWithSignRoAdv_bounded

theorem sample_gapDhWithSignRoBound1B :
    ∃ B₁_2run : GapDhAdv,
      B₁_2run.Bounded ∧
      B₁_2run.q_ddh ≤ 3 ∧
      B₁_2run.q_prim ≤ 0 ∧
      GapDhWithSignRo pZMod pZMod.isValidDhTriple pZMod.pow8 sampleGapDhWithSignRoAdv ≤
        GapDH pZMod pZMod.isValidDhTriple pZMod.pow8 B₁_2run + xeddsaSimLoss 1 1 :=
  gapDhWithSignRoBound1B_holds pZMod pZMod_wellFormedδ pZMod_xeddsaCurveLaws
    sampleGapDhWithSignRoAdv sampleGapDhWithSignRoAdv_bounded

theorem sample_gapSigEufCmaRoBoundQuad :
    ∃ B₂ : GapDhAdv,
      let q_H := xeddsaChalBudget 1 0 0
      let eps' := max 0
        (GapSigEufCmaRo pZMod pZMod.isValidDhTriple sampleGapSigEufCmaRoAdv -
          xeddsaSimLoss 1 q_H - xeddsaModLoss q_H)
      B₂.Bounded ∧
      B₂.q_ddh ≤ 2 ∧
      B₂.q_prim ≤ 1 ∧
      eps' * (eps' / ((q_H : ℝ) + 1) - 1 / (l25519 : ℝ)) ≤
        2 * GapDH pZMod pZMod.isValidDhTriple pZMod.pow8 B₂ :=
  gapSigEufCmaRoBoundQuad_holds pZMod pZMod_wellFormedδ pZMod_xeddsaCurveLaws
    sampleGapSigEufCmaRoAdv sampleGapSigEufCmaRoAdv_bounded

theorem sample_gapSigEufCmaRoBound :
    ∃ B₂ : GapDhAdv,
      let q_H := xeddsaChalBudget 1 0 0
      B₂.Bounded ∧
      B₂.q_ddh ≤ 2 ∧
      B₂.q_prim ≤ 1 ∧
      GapSigEufCmaRo pZMod pZMod.isValidDhTriple sampleGapSigEufCmaRoAdv ≤
        Real.sqrt (2 * ((q_H : ℝ) + 1) * GapDH pZMod pZMod.isValidDhTriple pZMod.pow8 B₂) +
          ((q_H : ℝ) + 1) / (l25519 : ℝ) +
          xeddsaSimLoss 1 q_H +
          xeddsaModLoss q_H :=
  gapSigEufCmaRoBound_holds pZMod pZMod_wellFormedδ pZMod_xeddsaCurveLaws
    sampleGapSigEufCmaRoAdv sampleGapSigEufCmaRoAdv_bounded

/--
info: 'Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519.prime_l25519' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519.prime_l25519

/--
info: 'Computational.Proofs.SignalPqxdh.XeddsaRom.Roundtrip.xeddsaSignRoundtrip_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Computational.Proofs.SignalPqxdh.XeddsaRom.Roundtrip.xeddsaSignRoundtrip_holds

/--
info: 'Computational.Proofs.SignalPqxdh.XeddsaRom.HvzkSim.gapDhWithSignRo_le_sim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Computational.Proofs.SignalPqxdh.XeddsaRom.HvzkSim.gapDhWithSignRo_le_sim

/--
info: 'Computational.Proofs.SignalPqxdh.XeddsaRom.HvzkSim.gapSigEufCmaRo_le_sim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Computational.Proofs.SignalPqxdh.XeddsaRom.HvzkSim.gapSigEufCmaRo_le_sim

/--
info: 'Computational.Proofs.SignalPqxdh.XeddsaRom.GapDhWithSignReduction.gapDhWithSignRoBound1A_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Computational.Proofs.SignalPqxdh.XeddsaRom.GapDhWithSignReduction.gapDhWithSignRoBound1A_holds

/--
info: 'Computational.Proofs.SignalPqxdh.XeddsaRom.GapDhWithSignReduction.gapDhWithSignRoBound1B_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Computational.Proofs.SignalPqxdh.XeddsaRom.GapDhWithSignReduction.gapDhWithSignRoBound1B_holds

/--
info: 'Computational.Proofs.SignalPqxdh.XeddsaRom.ForkingReduction.gapSigEufCmaRoBoundQuad_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Computational.Proofs.SignalPqxdh.XeddsaRom.ForkingReduction.gapSigEufCmaRoBoundQuad_holds

/--
info: 'Computational.Proofs.SignalPqxdh.XeddsaRom.ForkingReduction.gapSigEufCmaRoBound_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Computational.Proofs.SignalPqxdh.XeddsaRom.ForkingReduction.gapSigEufCmaRoBound_holds

/--
info: 'Computational.Tests.XeddsaRomNonVac.xeddsaRom_hypotheses_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms xeddsaRom_hypotheses_satisfiable

end Computational.Tests.XeddsaRomNonVac
