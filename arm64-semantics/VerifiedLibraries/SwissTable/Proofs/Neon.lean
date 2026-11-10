/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.SwissTable.Proofs.Group
import ProofLib.SepLogic.SymWP
import ProofLib.BV.ReflectROBDD

/-!
# SwissTable NEON `v.8b` Group Matching and `BitMask` Iteration

Characterizes the NEON `.8b` byte-comparison and `BitMask` bit-manipulation operations used by
SwissTable group probing and `reserve_rehash` tag normalization (`cmeq`, `cmlt`, `cmge`, `umaxv`,
`rbit` + `clz`, and `(m - 1) &&& m`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.SwissTable

open Arm64 ProofLib

/-- Construct an 8-bit bitset from 8 lane booleans. -/
def ofBits8 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : BitVec 8 :=
  (if b0 then 0x01#8 else 0#8) |||
  (if b1 then 0x02#8 else 0#8) |||
  (if b2 then 0x04#8 else 0#8) |||
  (if b3 then 0x08#8 else 0#8) |||
  (if b4 then 0x10#8 else 0#8) |||
  (if b5 then 0x20#8 else 0#8) |||
  (if b6 then 0x40#8 else 0#8) |||
  (if b7 then 0x80#8 else 0#8)

/-- Pack an 8-lane boolean predicate `p : Nat → Bool` into an 8-bit bitset `BitVec 8`. -/
def packPred8 (p : Nat → Bool) : BitVec 8 :=
  ofBits8 (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7)

private theorem getLsbD_condBit (c : Bool) (mask : BitVec 8) (j : Nat) :
    (if c then mask else 0#8).getLsbD j = (c && mask.getLsbD j) := by
  cases c <;> simp

theorem getLsbD_packPred8 (p : Nat → Bool) {j : Nat} (hj : j < 8) :
    (packPred8 p).getLsbD j = p j := by
  simp only [packPred8, ofBits8, BitVec.getLsbD_or, getLsbD_condBit]
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp
  | n + 8 => omega

/-- 8-bit bitset of lanes `j < 8` in `g` equal to `t`. -/
def eqBits8 (g : BitVec 64) (t : BitVec 8) : BitVec 8 :=
  packPred8 (fun j => getLane8 g j == t)

/-- 8-bit bitset of `EMPTY`/`DELETED` (`isSpecialTag`) lanes `j < 8` in `g`. -/
def specialBits8 (g : BitVec 64) : BitVec 8 :=
  packPred8 (fun j => isSpecialTag (getLane8 g j))

/-- 8-bit bitset of `FULL` (`isFullTag`) lanes `j < 8` in `g`. -/
def fullBits8 (g : BitVec 64) : BitVec 8 :=
  packPred8 (fun j => isFullTag (getLane8 g j))

theorem getLsbD_eqBits8 (g : BitVec 64) (t : BitVec 8) {j : Nat} (hj : j < 8) :
    (eqBits8 g t).getLsbD j = (getLane8 g j == t) :=
  getLsbD_packPred8 _ hj

theorem getLsbD_specialBits8 (g : BitVec 64) {j : Nat} (hj : j < 8) :
    (specialBits8 g).getLsbD j = isSpecialTag (getLane8 g j) :=
  getLsbD_packPred8 _ hj

theorem getLsbD_fullBits8 (g : BitVec 64) {j : Nat} (hj : j < 8) :
    (fullBits8 g).getLsbD j = isFullTag (getLane8 g j) :=
  getLsbD_packPred8 _ hj

/-- 64-bit word with byte lane `j` equal to `0xff#8` if `b[j]` else `0x00#8`
    (the 64-bit payload of NEON `.8b` comparisons `cmeq`, `cmlt`, `cmge`). -/
def byteMaskOfBits (b : BitVec 8) : BitVec 64 :=
  pack64
    (if b.getLsbD 0 then 0xff#8 else 0#8) (if b.getLsbD 1 then 0xff#8 else 0#8)
    (if b.getLsbD 2 then 0xff#8 else 0#8) (if b.getLsbD 3 then 0xff#8 else 0#8)
    (if b.getLsbD 4 then 0xff#8 else 0#8) (if b.getLsbD 5 then 0xff#8 else 0#8)
    (if b.getLsbD 6 then 0xff#8 else 0#8) (if b.getLsbD 7 then 0xff#8 else 0#8)

/-- 64-bit `BitMask` word with byte lane `j` equal to `0x80#8` if `b[j]` else `0x00#8`
    (the result of `fmov x, d` + `and(s) x, x, #0x8080808080808080`). -/
def highBitMaskOfBits (b : BitVec 8) : BitVec 64 :=
  pack64
    (if b.getLsbD 0 then 0x80#8 else 0#8) (if b.getLsbD 1 then 0x80#8 else 0#8)
    (if b.getLsbD 2 then 0x80#8 else 0#8) (if b.getLsbD 3 then 0x80#8 else 0#8)
    (if b.getLsbD 4 then 0x80#8 else 0#8) (if b.getLsbD 5 then 0x80#8 else 0#8)
    (if b.getLsbD 6 then 0x80#8 else 0#8) (if b.getLsbD 7 then 0x80#8 else 0#8)

theorem byteMaskOfBits_and_highBits (b : BitVec 8) :
    byteMaskOfBits b &&& 0x8080808080808080#64 = highBitMaskOfBits b := by
  simp only [byteMaskOfBits, highBitMaskOfBits, pack64]
  bv_robdd

@[simp]
theorem highBitMaskOfBits_zero : highBitMaskOfBits 0#8 = 0#64 := by decide

@[simp]
theorem byteMaskOfBits_zero : byteMaskOfBits 0#8 = 0#64 := by decide

theorem highBitMaskOfBits_eq_zero_iff (b : BitVec 8) :
    highBitMaskOfBits b = 0#64 ↔ b = 0#8 := by
  have h : (highBitMaskOfBits b == 0#64) = (b == 0#8) := by
    simp only [highBitMaskOfBits, pack64]
    bv_robdd
  simpa using congrArg (· = true) h

theorem byteMaskOfBits_eq_zero_iff (b : BitVec 8) :
    byteMaskOfBits b = 0#64 ↔ b = 0#8 := by
  have h : (byteMaskOfBits b == 0#64) = (b == 0#8) := by
    simp only [byteMaskOfBits, pack64]
    bv_robdd
  simpa using congrArg (· = true) h

theorem bv8_eq_zero_iff_forall (b : BitVec 8) :
    b = 0#8 ↔ ∀ j < 8, b.getLsbD j = false := by
  constructor
  · rintro rfl j _; simp
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simpa using h i hi

theorem bv8_ne_zero_iff_exists (b : BitVec 8) :
    b ≠ 0#8 ↔ ∃ j < 8, b.getLsbD j = true := by
  constructor
  · intro hne
    exact Classical.byContradiction fun hno => hne <|
      (bv8_eq_zero_iff_forall b).2 fun j hj =>
        match hbit : b.getLsbD j with
        | false => rfl
        | true => False.elim (hno ⟨j, hj, hbit⟩)
  · rintro ⟨j, _, hj⟩ rfl
    simp at hj

private theorem ctz_eq_of_first_true {w : Nat} (_hw : w < 2 ^ w) {x : BitVec w} {k : Nat}
    (_hk : k < w) (ht : x.getLsbD k = true) (hlo : ∀ i < k, x.getLsbD i = false) :
    x.ctz = BitVec.ofNat w k := by
  have hne : x ≠ BitVec.ofNat w 0 := by rintro rfl; simp at ht
  have h1 : x.getLsbD x.ctz.toNat = true := BitVec.getLsbD_true_ctz_of_ne_zero hne
  have hge : ¬ (x.ctz.toNat < k) := fun h => by rw [hlo _ h] at h1; cases h1
  have hle : ¬ (k < x.ctz.toNat) := fun h => by
    rw [BitVec.getLsbD_false_of_lt_ctz h] at ht; cases ht
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem clz_eq_of_highest_true {w : Nat} (hw : w < 2 ^ w)
    {x : BitVec w} {k : Nat} (hk : k < w) (ht : x.getLsbD k = true)
    (hhi : ∀ i, k < i → i < w → x.getLsbD i = false) :
    x.clz = BitVec.ofNat w (w - 1 - k) := by
  rw [BitVec.clz_eq_reverse_ctz]
  apply ctz_eq_of_first_true hw (by omega)
  · rw [BitVec.getLsbD_reverse, BitVec.getMsbD]
    have hsub : w - 1 - (w - 1 - k) = k := by omega
    simp [hk, show w - 1 - k < w by omega, hsub, ht]
  · intro i hi
    rw [BitVec.getLsbD_reverse, BitVec.getMsbD]
    have hiw : i < w := by omega
    have hgt : k < w - 1 - i := by omega
    simp [hiw, hhi (w - 1 - i) hgt (by omega)]

theorem getLane8_byteMaskOfBits (b : BitVec 8) {q : Nat} (hq : q < 8) :
    getLane8 (byteMaskOfBits b) q = if b.getLsbD q then 0xff#8 else 0#8 := by
  match q with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
    simp only [getLane8, byteMaskOfBits, pack64]
    bv_robdd
  | n + 8 => omega

theorem getLane8_highBitMaskOfBits (b : BitVec 8) {q : Nat} (hq : q < 8) :
    getLane8 (highBitMaskOfBits b) q = if b.getLsbD q then 0x80#8 else 0#8 := by
  match q with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
    simp only [getLane8, highBitMaskOfBits, pack64]
    bv_robdd
  | n + 8 => omega

private theorem getLsbD_byteMaskOfBits (b : BitVec 8) {i : Nat} (hi : i < 64) :
    (byteMaskOfBits b).getLsbD i = b.getLsbD (i / 8) := by
  have heq : (byteMaskOfBits b).getLsbD i =
      (getLane8 (byteMaskOfBits b) (i / 8)).getLsbD (i % 8) := by
    simp only [getLane8, BitVec.getLsbD_extractLsb']
    have h1 : i % 8 < 8 := by omega
    have h2 : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
    simp [h1, h2]
  rw [heq, getLane8_byteMaskOfBits b (by omega)]
  have hff : ∀ r < 8, (0xff#8).getLsbD r = true := by
    intro r hr
    match r with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => decide
    | n + 8 => omega
  cases b.getLsbD (i / 8) <;> simp [hff (i % 8) (by omega)]

private theorem getLsbD_highBitMaskOfBits (b : BitVec 8) {i : Nat} (hi : i < 64) :
    (highBitMaskOfBits b).getLsbD i = (decide (i % 8 = 7) && b.getLsbD (i / 8)) := by
  have heq : (highBitMaskOfBits b).getLsbD i =
      (getLane8 (highBitMaskOfBits b) (i / 8)).getLsbD (i % 8) := by
    simp only [getLane8, BitVec.getLsbD_extractLsb']
    have h1 : i % 8 < 8 := by omega
    have h2 : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
    simp [h1, h2]
  rw [heq, getLane8_highBitMaskOfBits b (by omega)]
  have hr : i % 8 < 8 := by omega
  have h0x80 : ∀ r < 8, (0x80#8).getLsbD r = decide (r = 7) := by
    intro r hr'
    match r with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => decide
    | n + 8 => omega
  cases b.getLsbD (i / 8) <;> simp [h0x80 _ hr]

theorem bv8_ctz_spec {b : BitVec 8} (hb : b ≠ 0#8) :
    b.ctz.toNat < 8 ∧
    b.getLsbD b.ctz.toNat = true ∧
    (∀ i < b.ctz.toNat, b.getLsbD i = false) := by
  have hlt : b.ctz < 8#8 := (BitVec.ctz_lt_iff_ne_zero (x := b)).2 hb
  rw [BitVec.lt_def] at hlt
  exact ⟨by simpa using hlt,
    BitVec.getLsbD_true_ctz_of_ne_zero hb,
    fun _ hi => BitVec.getLsbD_false_of_lt_ctz hi⟩

theorem bv8_clz_spec (b : BitVec 8) :
    (b = 0#8 → b.clz.toNat = 8) ∧
    (b ≠ 0#8 →
      b.clz.toNat < 8 ∧
      b.getLsbD (7 - b.clz.toNat) = true ∧
      (∀ j, 7 - b.clz.toNat < j → j < 8 → b.getLsbD j = false)) := by
  refine ⟨fun h0 => by subst h0; decide, fun hne => ?_⟩
  have hlt : b.clz < 8#8 := (BitVec.clz_lt_iff_ne_zero (x := b)).2 hne
  rw [BitVec.lt_def] at hlt
  have hlt8 : b.clz.toNat < 8 := by simpa using hlt
  refine ⟨hlt8, BitVec.getLsbD_true_clz_of_ne_zero (by omega) hne, ?_⟩
  intro j hj hj8
  have hrev := BitVec.clz_eq_reverse_ctz (x := b)
  have hctz : b.reverse.ctz.toNat = b.clz.toNat := congrArg BitVec.toNat hrev.symm
  have hfalse : b.reverse.getLsbD (7 - j) = false :=
    BitVec.getLsbD_false_of_lt_ctz (by omega)
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD] at hfalse
  have hsub : 8 - 1 - (7 - j) = j := by omega
  simpa [show 7 - j < 8 by omega, hsub] using hfalse

private theorem zero64_reverse_clz_lsr3 : (0#64).reverse.clz >>> 3 = 8#64 := by
  have hrev : (0#64).reverse = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp [BitVec.getLsbD_reverse]
  have hclz : (0#64).clz = 64#64 := (BitVec.clz_eq_iff_eq_zero (x := 0#64)).2 rfl
  rw [hrev, hclz]
  decide

theorem highBitMaskOfBits_lowestLane (b : BitVec 8) :
    (highBitMaskOfBits b).reverse.clz >>> 3 = BitVec.ofNat 64 b.ctz.toNat := by
  by_cases hb : b = 0#8
  · subst hb
    have h0 : (0#8).ctz.toNat = 8 := by decide
    simpa [h0] using zero64_reverse_clz_lsr3
  · rw [← BitVec.ctz_eq_reverse_clz]
    rcases bv8_ctz_spec hb with ⟨hj8, htrue, hlo⟩
    have hctz : (highBitMaskOfBits b).ctz = BitVec.ofNat 64 (8 * b.ctz.toNat + 7) := by
      apply ctz_eq_of_first_true (by decide) (by omega)
      · rw [getLsbD_highBitMaskOfBits b (by omega)]
        have h1 : (8 * b.ctz.toNat + 7) % 8 = 7 := by omega
        have h2 : (8 * b.ctz.toNat + 7) / 8 = b.ctz.toNat := by omega
        simp [h1, h2, htrue]
      · intro i hi
        rw [getLsbD_highBitMaskOfBits b (by omega)]
        by_cases hdiv : i / 8 < b.ctz.toNat
        · simp [hlo _ hdiv]
        · have hmod : i % 8 ≠ 7 := by omega
          simp [hmod]
    rw [hctz]
    apply BitVec.eq_of_toNat_eq
    have hlt64 : 8 * b.ctz.toNat + 7 < 2 ^ 64 := by omega
    have hj64 : b.ctz.toNat < 2 ^ 64 := by omega
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64, Nat.shiftRight_eq_div_pow]
    omega

theorem byteMaskOfBits_lowestLane (b : BitVec 8) :
    (byteMaskOfBits b).reverse.clz >>> 3 = BitVec.ofNat 64 b.ctz.toNat := by
  by_cases hb : b = 0#8
  · subst hb
    have h0 : (0#8).ctz.toNat = 8 := by decide
    simpa [h0] using zero64_reverse_clz_lsr3
  · rw [← BitVec.ctz_eq_reverse_clz]
    rcases bv8_ctz_spec hb with ⟨hj8, htrue, hlo⟩
    have hctz : (byteMaskOfBits b).ctz = BitVec.ofNat 64 (8 * b.ctz.toNat) := by
      apply ctz_eq_of_first_true (by decide) (by omega)
      · rw [getLsbD_byteMaskOfBits b (by omega)]
        have h2 : (8 * b.ctz.toNat) / 8 = b.ctz.toNat := by omega
        simp [h2, htrue]
      · intro i hi
        rw [getLsbD_byteMaskOfBits b (by omega)]
        exact hlo _ (by omega)
    rw [hctz]
    apply BitVec.eq_of_toNat_eq
    have hlt64 : 8 * b.ctz.toNat < 2 ^ 64 := by omega
    have hj64 : b.ctz.toNat < 2 ^ 64 := by omega
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64, Nat.shiftRight_eq_div_pow]
    omega

theorem byteMaskOfBits_clz_lsr3 (b : BitVec 8) :
    (byteMaskOfBits b).clz >>> 3 = BitVec.ofNat 64 b.clz.toNat := by
  by_cases hb : b = 0#8
  · subst hb
    have hclz : (0#64).clz = 64#64 := (BitVec.clz_eq_iff_eq_zero (x := 0#64)).2 rfl
    have h0 : (0#8).clz.toNat = 8 := by decide
    simp only [byteMaskOfBits_zero, hclz, h0]
    decide
  · rcases (bv8_clz_spec b).2 hb with ⟨hclz8, htrue, hhi⟩
    let j := 7 - b.clz.toNat
    have hj8 : j < 8 := by omega
    have hclz : (byteMaskOfBits b).clz = BitVec.ofNat 64 (63 - (8 * j + 7)) := by
      apply clz_eq_of_highest_true (by decide) (by omega)
      · rw [getLsbD_byteMaskOfBits b (by omega)]
        have hdiv : (8 * j + 7) / 8 = j := by omega
        rw [hdiv]
        exact htrue
      · intro i hgt hi64
        rw [getLsbD_byteMaskOfBits b hi64]
        exact hhi (i / 8) (by omega) (by omega)
    rw [hclz]
    apply BitVec.eq_of_toNat_eq
    have hval : 63 - (8 * j + 7) = 8 * b.clz.toNat := by omega
    rw [hval]
    have hlt64 : 8 * b.clz.toNat < 2 ^ 64 := by omega
    have hj64 : b.clz.toNat < 2 ^ 64 := by omega
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64, Nat.shiftRight_eq_div_pow]
    omega

theorem highBitMaskOfBits_clz_lsr3 (b : BitVec 8) :
    (highBitMaskOfBits b).clz >>> 3 = BitVec.ofNat 64 b.clz.toNat := by
  by_cases hb : b = 0#8
  · subst hb
    have hclz : (0#64).clz = 64#64 := (BitVec.clz_eq_iff_eq_zero (x := 0#64)).2 rfl
    have h0 : (0#8).clz.toNat = 8 := by decide
    simp only [highBitMaskOfBits_zero, hclz, h0]
    decide
  · rcases (bv8_clz_spec b).2 hb with ⟨hclz8, htrue, hhi⟩
    let j := 7 - b.clz.toNat
    have hj8 : j < 8 := by omega
    have hclz : (highBitMaskOfBits b).clz = BitVec.ofNat 64 (63 - (8 * j + 7)) := by
      apply clz_eq_of_highest_true (by decide) (by omega)
      · rw [getLsbD_highBitMaskOfBits b (by omega)]
        have hmod : (8 * j + 7) % 8 = 7 := by omega
        have hdiv : (8 * j + 7) / 8 = j := by omega
        rw [hmod, hdiv]
        simpa using htrue
      · intro i hgt hi64
        rw [getLsbD_highBitMaskOfBits b hi64]
        simp [hhi (i / 8) (by omega) (by omega)]
    rw [hclz]
    apply BitVec.eq_of_toNat_eq
    have hval : 63 - (8 * j + 7) = 8 * b.clz.toNat := by omega
    rw [hval]
    have hlt64 : 8 * b.clz.toNat < 2 ^ 64 := by omega
    have hj64 : b.clz.toNat < 2 ^ 64 := by omega
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64, Nat.shiftRight_eq_div_pow]
    omega

theorem highBitMaskOfBits_clear_lowest (b : BitVec 8) :
    (highBitMaskOfBits b - 1#64) &&& highBitMaskOfBits b =
      highBitMaskOfBits ((b - 1#8) &&& b) := by
  simp only [highBitMaskOfBits, pack64]
  bv_robdd

theorem bv8_clear_lowest_lt {b : BitVec 8} (hb : b ≠ 0#8) :
    ((b - 1#8) &&& b).toNat < b.toNat := by
  have hbpos : 1 ≤ b.toNat := by
    exact Classical.byContradiction fun h => hb (BitVec.eq_of_toNat_eq (by simp; omega))
  have hsub : (b - 1#8).toNat = b.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le]
    · simp
    · rw [BitVec.le_def]; simp; exact hbpos
  have hand : ((b - 1#8) &&& b).toNat ≤ (b - 1#8).toNat := by
    rw [BitVec.toNat_and]
    exact Nat.and_le_left
  omega

private theorem bv8_clear_imp (b : BitVec 8) {k : Nat} (hk : k < 8) :
    (!(b &&& ((1#8 <<< k) - 1#8) == 0#8) || !(b.getLsbD k) ||
      (((b - 1#8) &&& b) == (b &&& ~~~(1#8 <<< k)))) = true := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => bv_robdd
  | n + 8 => omega

theorem bv8_clear_lowest_eq (b : BitVec 8) :
    (b - 1#8) &&& b = b &&& ~~~(1#8 <<< b.ctz.toNat) := by
  by_cases hb : b = 0#8
  · subst hb; decide
  · rcases bv8_ctz_spec hb with ⟨hk8, htrue, hlo⟩
    have hbit : ∀ i < 8, (((1#8 <<< b.ctz.toNat) - 1#8)).getLsbD i = decide (i < b.ctz.toNat) := by
      intro i hi
      rcases (by omega : b.ctz.toNat = 0 ∨ b.ctz.toNat = 1 ∨ b.ctz.toNat = 2 ∨ b.ctz.toNat = 3 ∨
        b.ctz.toNat = 4 ∨ b.ctz.toNat = 5 ∨ b.ctz.toNat = 6 ∨ b.ctz.toNat = 7) with
        hk | hk | hk | hk | hk | hk | hk | hk <;>
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
        hi' | hi' | hi' | hi' | hi' | hi' | hi' | hi' <;>
      rw [hk, hi'] <;> decide
    have hmask : b &&& ((1#8 <<< b.ctz.toNat) - 1#8) = 0#8 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [BitVec.getLsbD_and, hbit i hi]
      by_cases hik : i < b.ctz.toNat
      · simp [hlo i hik]
      · simp [hik]
    have himp := bv8_clear_imp b hk8
    have hm : (b &&& ((1#8 <<< b.ctz.toNat) - 1#8) == 0#8) = true := beq_iff_eq.2 hmask
    simp only [hm, htrue, Bool.not_true, Bool.false_or, beq_iff_eq] at himp
    exact himp

theorem bv8_getLsbD_clear_lowest (b : BitVec 8) {j : Nat} (hj : j < 8) :
    ((b - 1#8) &&& b).getLsbD j = (b.getLsbD j && decide (j ≠ b.ctz.toNat)) := by
  rw [bv8_clear_lowest_eq, BitVec.getLsbD_and, BitVec.getLsbD_not]
  simp only [hj, decide_true, Bool.true_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
  by_cases hlt : j < b.ctz.toNat
  · have hne : j ≠ b.ctz.toNat := by omega
    simp [hj, hlt, hne]
  · by_cases heq : j = b.ctz.toNat
    · subst heq; simp [hj]
    · have hsub : j - b.ctz.toNat ≠ 0 := by omega
      simp [hj, hlt, heq, hsub]

/-- NEON `dup v0.8b, w_tag` + `cmeq v3.8b, v2.8b, v0.8b` + `fmov x, d3` equals
    `byteMaskOfBits (eqBits8 g (tag64.truncate 8))`. -/
theorem simd_cmeq_dup8_truncate64 (g tag64 : BitVec 64) :
    (zipLanes 8 (g.zeroExtend 128)
      (mapLanes 8 0#128 (fun _ => tag64.zeroExtend 128 &&& 0xff#128) 8)
      (fun a b => if a == b then 0xff#128 else 0#128) 8).truncate 64 =
    byteMaskOfBits (eqBits8 g (tag64.truncate 8)) := by
  simp only [zipLanes, mapLanes, laneMask_8, byteMaskOfBits, eqBits8, packPred8, ofBits8,
    getLane8, pack64]
  bv_robdd

/-- NEON `dup` + `cmeq` + `fmov` + `and(s) #0x8080808080808080` equals
    `highBitMaskOfBits (eqBits8 g (tag64.truncate 8))`. -/
theorem simd_cmeq_dup8_highMask (g tag64 : BitVec 64) :
    (zipLanes 8 (g.zeroExtend 128)
      (mapLanes 8 0#128 (fun _ => tag64.zeroExtend 128 &&& 0xff#128) 8)
      (fun a b => if a == b then 0xff#128 else 0#128) 8).truncate 64 &&&
      0x8080808080808080#64 =
    highBitMaskOfBits (eqBits8 g (tag64.truncate 8)) := by
  rw [simd_cmeq_dup8_truncate64, byteMaskOfBits_and_highBits]

/-- NEON `cmeq v.8b, v_g.8b, v_ff.8b` against `0xffffffffffffffffffffffffffffffff#128`
    (`movi v_ff.2d, #0xffffffffffffffff`). -/
theorem simd_cmeq_allOnes8 (g : BitVec 64) :
    zipLanes 8 (g.zeroExtend 128) 0xffffffffffffffffffffffffffffffff#128
      (fun a b => if a == b then 0xff#128 else 0#128) 8 =
    (byteMaskOfBits (eqBits8 g tagEmpty)).zeroExtend 128 := by
  simp only [zipLanes, laneMask_8, byteMaskOfBits, eqBits8, packPred8, ofBits8,
    getLane8, pack64, tagEmpty]
  bv_robdd

/-- NEON `umaxv b_d, v.8b` across `v = (byteMaskOfBits b).zeroExtend 128`. -/
def simdUmaxv8 (v : BitVec 128) : BitVec 128 :=
  Id.run do
    let mut cur : BitVec 128 := 0#128
    for i in [0:8] do
      let lane := (v >>> (i * 8)) &&& 0xff#128
      if BitVec.ult cur lane then
        cur := lane
    return cur

private theorem simdUmaxv8_unroll (v : BitVec 128) :
    simdUmaxv8 v =
      let c0 := if BitVec.ult 0#128 ((v >>> 0) &&& 0xff#128) then (v >>> 0) &&& 0xff#128 else 0#128
      let c1 := if BitVec.ult c0 ((v >>> 8) &&& 0xff#128) then (v >>> 8) &&& 0xff#128 else c0
      let c2 := if BitVec.ult c1 ((v >>> 16) &&& 0xff#128) then (v >>> 16) &&& 0xff#128 else c1
      let c3 := if BitVec.ult c2 ((v >>> 24) &&& 0xff#128) then (v >>> 24) &&& 0xff#128 else c2
      let c4 := if BitVec.ult c3 ((v >>> 32) &&& 0xff#128) then (v >>> 32) &&& 0xff#128 else c3
      let c5 := if BitVec.ult c4 ((v >>> 40) &&& 0xff#128) then (v >>> 40) &&& 0xff#128 else c4
      let c6 := if BitVec.ult c5 ((v >>> 48) &&& 0xff#128) then (v >>> 48) &&& 0xff#128 else c5
      if BitVec.ult c6 ((v >>> 56) &&& 0xff#128) then (v >>> 56) &&& 0xff#128 else c6 := by
  simp only [simdUmaxv8, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  have h : ∀ i (s : BitVec 128),
      (if s.ult (v >>> (i * 8) &&& 255#128) = true then
        (pure (ForInStep.yield (v >>> (i * 8) &&& 255#128)) : Id _)
       else pure (ForInStep.yield s)) =
      pure (ForInStep.yield
        (if s.ult (v >>> (i * 8) &&& 255#128) = true then v >>> (i * 8) &&& 255#128 else s)) := by
    intro i s; split <;> rfl
  simp only [h, List.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure]
  rfl

theorem simdUmaxv8_byteMaskOfBits (b : BitVec 8) :
    simdUmaxv8 ((byteMaskOfBits b).zeroExtend 128) =
      if b == 0#8 then 0#128 else 0xff#128 := by
  rw [simdUmaxv8_unroll]
  dsimp only
  simp only [byteMaskOfBits, pack64]
  bv_robdd

/-- NEON `cmlt v.8b, v_g.8b, #0` (`isSpecialTag` lane mask: `EMPTY` / `DELETED`). -/
theorem simd_cmlt_zero8 (g : BitVec 64) :
    mapLanes 8 (g.zeroExtend 128) (fun a => if a.getLsbD 7 then 0xff#128 else 0#128) 8 =
      (byteMaskOfBits (specialBits8 g)).zeroExtend 128 := by
  simp only [mapLanes, laneMask_8, byteMaskOfBits, specialBits8, packPred8, ofBits8,
    isSpecialTag, getLane8, pack64]
  bv_robdd

/-- NEON `cmge v.8b, v_g.8b, #0` (`isFullTag` lane mask: `FULL` tags `< 0x80`). -/
theorem simd_cmge_zero8 (g : BitVec 64) :
    mapLanes 8 (g.zeroExtend 128) (fun a => if !a.getLsbD 7 then 0xff#128 else 0#128) 8 =
      (byteMaskOfBits (fullBits8 g)).zeroExtend 128 := by
  simp only [mapLanes, laneMask_8, byteMaskOfBits, fullBits8, packPred8, ofBits8,
    isFullTag, getLane8, pack64]
  bv_robdd

/-- NEON `cmlt v.8b, v_g.8b, #0` + `orr #0x80` tag normalization in `reserve_rehash`, mapping
    `EMPTY`/`DELETED` (`isSpecialTag`) to `tagEmpty` (`0xff`) and `FULL` to `tagDeleted` (`0x80`). -/
theorem getLane8_byteMask_special_orr_0x80 (g : BitVec 64) {j : Nat} (hj : j < 8) :
    getLane8 (byteMaskOfBits (specialBits8 g) ||| 0x8080808080808080#64) j =
      if isSpecialTag (getLane8 g j) then tagEmpty else tagDeleted := by
  have hbits : ∀ b : BitVec 8,
      getLane8 (byteMaskOfBits b ||| 0x8080808080808080#64) j =
        if b.getLsbD j then tagEmpty else tagDeleted := by
    intro b
    match j with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
      simp only [getLane8, byteMaskOfBits, pack64, tagEmpty, tagDeleted]
      bv_robdd
    | n + 8 => omega
  rw [hbits (specialBits8 g), getLsbD_specialBits8 g hj]


end VerifiedLibraries.SwissTable
