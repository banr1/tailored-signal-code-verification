/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.AsciiNum

/-!
# ASCII Decimal Formatting and Parsing Lemmas

Step, chunk, bound, round-trip, and accumulator-loop bridge lemmas for the ASCII decimal integer
formatting and parsing definitions in `Arm64.Trusted.Spec.AsciiNum` (`natToDigits10`,
`formatDecimalNat`, `parseDecimalNat`, and `parseDecimalUInt`). Connects functional specifications
to tail-recursive byte accumulators and early-overflow machine loops.
-/

@[expose] public section

namespace ProofLib.AsciiNum

open Arm64

/-! ## Base-10 Digit Extraction -/

theorem natToDigits10Aux_fuel_irrel :
    ∀ (f1 f2 n : Nat) (acc : List Nat),
      n < f1 → n < f2 → natToDigits10Aux f1 n acc = natToDigits10Aux f2 n acc
  | 0, _, _, _, h1, _ => by omega
  | _, 0, _, _, _, h2 => by omega
  | f1 + 1, f2 + 1, n, acc, h1, h2 => by
    simp only [natToDigits10Aux]
    by_cases hn : n < 10
    · simp only [hn, ↓reduceIte]
    · simp only [hn, ↓reduceIte]
      exact natToDigits10Aux_fuel_irrel f1 f2 (n / 10) _ (by omega) (by omega)

theorem natToDigits10Aux_append :
    ∀ (fuel n : Nat) (acc : List Nat),
      n < fuel → natToDigits10Aux fuel n acc = natToDigits10Aux fuel n [] ++ acc
  | 0, _, _, h => by omega
  | fuel + 1, n, acc, h => by
    simp only [natToDigits10Aux]
    by_cases hn : n < 10
    · simp only [hn, ↓reduceIte, List.singleton_append]
    · simp only [hn, ↓reduceIte]
      rw [natToDigits10Aux_append fuel (n / 10) ((n % 10) :: acc) (by omega),
          natToDigits10Aux_append fuel (n / 10) [n % 10] (by omega),
          List.append_assoc, List.singleton_append]

@[simp] theorem natToDigits10_zero : natToDigits10 0 = [0] := rfl

theorem natToDigits10_of_lt_10 {n : Nat} (hn : n < 10) :
    natToDigits10 n = [n] := by
  unfold natToDigits10 natToDigits10Aux
  simp only [hn, ↓reduceIte, Nat.mod_eq_of_lt hn]

theorem natToDigits10_of_ge_10 {n : Nat} (hn : 10 ≤ n) :
    natToDigits10 n = natToDigits10 (n / 10) ++ [n % 10] := by
  unfold natToDigits10
  conv => lhs; unfold natToDigits10Aux
  have hlt : ¬ (n < 10) := by omega
  simp only [hlt, ↓reduceIte]
  rw [natToDigits10Aux_append n (n / 10) [n % 10] (by omega),
      natToDigits10Aux_fuel_irrel n (n / 10 + 1) (n / 10) [] (by omega) (by omega)]

@[simp] theorem natToDigits10_ne_nil (n : Nat) : natToDigits10 n ≠ [] := by
  by_cases hn : n < 10
  · rw [natToDigits10_of_lt_10 hn]; simp
  · rw [natToDigits10_of_ge_10 (by omega)]; simp

theorem natToDigits10_mem_lt_10 {n d : Nat} (hd : d ∈ natToDigits10 n) : d < 10 := by
  suffices ∀ (fuel m : Nat) (acc : List Nat),
      (∀ x ∈ acc, x < 10) → ∀ x ∈ natToDigits10Aux fuel m acc, x < 10 by
    exact this (n + 1) n [] (fun _ h => nomatch h) d hd
  intro fuel
  induction fuel with
  | zero => intro _ _ hacc x hx; exact hacc x hx
  | succ f ih =>
    intro m acc hacc x hx
    simp only [natToDigits10Aux] at hx
    have hmod : m % 10 < 10 := Nat.mod_lt m (by omega)
    have hacc' : ∀ y ∈ (m % 10) :: acc, y < 10 := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hmem
      · exact hmod
      · exact hacc y hmem
    split at hx
    · exact hacc' x hx
    · exact ih (m / 10) ((m % 10) :: acc) hacc' x hx

/-! ## Decimal Formatting -/

/-- Tail-recursive byte accumulator producing the same ASCII decimal bytes as
    `Arm64.natToDigits10Aux`. -/
def formatDecimalByteAux : Nat → Nat → List (BitVec 8) → List (BitVec 8)
  | 0, _, ds => ds
  | fuel + 1, n, ds =>
    let d : BitVec 8 := BitVec.ofNat 8 (0x30 + n % 10)
    let n' := n / 10
    if n' == 0 then d :: ds
    else formatDecimalByteAux fuel n' (d :: ds)

theorem formatDecimalByteAux_eq_map_natToDigits10Aux :
    ∀ (fuel n : Nat) (acc : List Nat),
      formatDecimalByteAux fuel n (acc.map fun d => BitVec.ofNat 8 (0x30 + d)) =
        (natToDigits10Aux fuel n acc).map fun d => BitVec.ofNat 8 (0x30 + d)
  | 0, _, _ => rfl
  | fuel + 1, n, acc => by
    simp only [formatDecimalByteAux, natToDigits10Aux]
    by_cases hn : n < 10
    · have hq : (n / 10 == 0) = true := beq_iff_eq.mpr (by omega)
      simp only [hq, hn, ↓reduceIte, List.map_cons]
    · have hq : (n / 10 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
      simp only [hq, Bool.false_eq_true, hn, ↓reduceIte]
      exact formatDecimalByteAux_eq_map_natToDigits10Aux fuel (n / 10) ((n % 10) :: acc)

theorem formatDecimalNat_eq_byteAux (n : Nat) :
    formatDecimalNat n = formatDecimalByteAux (n + 1) n [] :=
  (formatDecimalByteAux_eq_map_natToDigits10Aux (n + 1) n []).symm

@[simp] theorem formatDecimalNat_zero : formatDecimalNat 0 = [0x30#8] := rfl

theorem formatDecimalNat_of_lt_10 {n : Nat} (hn : n < 10) :
    formatDecimalNat n = [BitVec.ofNat 8 (0x30 + n)] := by
  simp [formatDecimalNat, natToDigits10_of_lt_10 hn]

theorem formatDecimalNat_of_ge_10 {n : Nat} (hn : 10 ≤ n) :
    formatDecimalNat n =
      formatDecimalNat (n / 10) ++ [BitVec.ofNat 8 (0x30 + n % 10)] := by
  simp [formatDecimalNat, natToDigits10_of_ge_10 hn]

@[simp] theorem formatDecimalNat_ne_nil (n : Nat) : formatDecimalNat n ≠ [] := by
  simp [formatDecimalNat]

theorem formatDecimalNat_two_digits {n : Nat} (hlo : 10 ≤ n) (hhi : n < 100) :
    formatDecimalNat n =
      [BitVec.ofNat 8 (0x30 + n / 10), BitVec.ofNat 8 (0x30 + n % 10)] := by
  rw [formatDecimalNat_of_ge_10 hlo, formatDecimalNat_of_lt_10 (by omega), List.singleton_append]

theorem formatDecimalNat_three_digits {n : Nat} (hlo : 100 ≤ n) (hhi : n < 1000) :
    formatDecimalNat n =
      [BitVec.ofNat 8 (0x30 + n / 100),
       BitVec.ofNat 8 (0x30 + (n % 100) / 10),
       BitVec.ofNat 8 (0x30 + n % 10)] := by
  rw [formatDecimalNat_of_ge_10 (by omega), formatDecimalNat_two_digits (by omega) (by omega)]
  have hmid : (n / 10) % 10 = (n % 100) / 10 := by omega
  rw [show n / 10 / 10 = n / 100 by omega, hmid]
  rfl

/-- Four zero-padded ASCII decimal digits of `r % 10000`. -/
def fourDecimalDigits (r : Nat) : List (BitVec 8) :=
  [BitVec.ofNat 8 (0x30 + (r / 100) / 10),
   BitVec.ofNat 8 (0x30 + (r / 100) % 10),
   BitVec.ofNat 8 (0x30 + (r % 100) / 10),
   BitVec.ofNat 8 (0x30 + (r % 100) % 10)]

@[simp] theorem fourDecimalDigits_length (r : Nat) : (fourDecimalDigits r).length = 4 := rfl

/-- Four-digit chunk decomposition (`10000 ≤ n`): `formatDecimalNat n` splits into
    `formatDecimalNat (n / 10000)` followed by `fourDecimalDigits (n % 10000)`. -/
theorem formatDecimalNat_div_10000 {n : Nat} (hn : 10000 ≤ n) :
    formatDecimalNat n = formatDecimalNat (n / 10000) ++ fourDecimalDigits (n % 10000) := by
  have h1 := formatDecimalNat_of_ge_10 (n := n) (by omega)
  have h2 := formatDecimalNat_of_ge_10 (n := n / 10) (by omega)
  have h3 := formatDecimalNat_of_ge_10 (n := n / 100) (by omega)
  have h4 := formatDecimalNat_of_ge_10 (n := n / 1000) (by omega)
  rw [show n / 10 / 10 = n / 100 by omega] at h2
  rw [show n / 100 / 10 = n / 1000 by omega] at h3
  rw [show n / 1000 / 10 = n / 10000 by omega] at h4
  rw [h1, h2, h3, h4]
  simp only [fourDecimalDigits, List.append_assoc, List.cons_append, List.nil_append]
  congr 1
  simp only [List.cons.injEq, and_true]
  exact ⟨congrArg (fun d => BitVec.ofNat 8 (0x30 + d)) (by omega),
         congrArg (fun d => BitVec.ofNat 8 (0x30 + d)) (by omega),
         congrArg (fun d => BitVec.ofNat 8 (0x30 + d)) (by omega),
         congrArg (fun d => BitVec.ofNat 8 (0x30 + d)) (by omega)⟩

theorem formatDecimalNat_of_1000_lt_10000 {n : Nat} (hlo : 1000 ≤ n) (hhi : n < 10000) :
    formatDecimalNat n = fourDecimalDigits n := by
  have h1 := formatDecimalNat_of_ge_10 (n := n) (by omega)
  have h2 := formatDecimalNat_three_digits (n := n / 10) (by omega) (by omega)
  rw [h1, h2]
  simp only [fourDecimalDigits, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨congrArg (fun d => BitVec.ofNat 8 (0x30 + d)) (by omega),
         congrArg (fun d => BitVec.ofNat 8 (0x30 + d)) (by omega),
         congrArg (fun d => BitVec.ofNat 8 (0x30 + d)) (by omega),
         congrArg (fun d => BitVec.ofNat 8 (0x30 + d)) (by omega)⟩

theorem formatDecimalNat_mem_ascii {n : Nat} {b : BitVec 8} (hb : b ∈ formatDecimalNat n) :
    0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39 := by
  rcases List.mem_map.mp hb with ⟨d, hd, rfl⟩
  have hlt := natToDigits10_mem_lt_10 hd
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem formatDecimalNat_mem_ascii_bv {n : Nat} {b : BitVec 8} (hb : b ∈ formatDecimalNat n) :
    0x30#8 ≤ b ∧ b ≤ 0x39#8 := by
  have ⟨hlo, hhi⟩ := formatDecimalNat_mem_ascii hb
  exact ⟨BitVec.le_def.mpr hlo, BitVec.le_def.mpr hhi⟩

theorem formatDecimalNat_not_mem_nl (n : Nat) : 0x0a#8 ∉ formatDecimalNat n := by
  intro hmem
  have ⟨hlo, _⟩ := formatDecimalNat_mem_ascii hmem
  simp at hlo

private theorem formatDecimalNat_length_lt_10000 {m : Nat} (hm : m < 10000) :
    1 ≤ (formatDecimalNat m).length ∧ (formatDecimalNat m).length ≤ 4 := by
  by_cases h1 : m < 10
  · rw [formatDecimalNat_of_lt_10 h1]; simp
  · by_cases h2 : m < 100
    · rw [formatDecimalNat_two_digits (by omega) h2]; simp
    · by_cases h3 : m < 1000
      · rw [formatDecimalNat_three_digits (by omega) h3]; simp
      · rw [formatDecimalNat_of_1000_lt_10000 (by omega) hm]; simp

theorem formatDecimalNat_length_bounds {n : Nat} (hn : n < 2 ^ 64) :
    1 ≤ (formatDecimalNat n).length ∧ (formatDecimalNat n).length ≤ 20 := by
  by_cases h1 : n < 10000
  · have ⟨hlo, hhi⟩ := formatDecimalNat_length_lt_10000 h1; omega
  · rw [formatDecimalNat_div_10000 (by omega), List.length_append, fourDecimalDigits_length]
    have hq1 : n / 10000 < 1844674407370956 := by omega
    by_cases h2 : n / 10000 < 10000
    · have ⟨hlo, hhi⟩ := formatDecimalNat_length_lt_10000 h2; omega
    · rw [formatDecimalNat_div_10000 (by omega), List.length_append, fourDecimalDigits_length]
      have hq2 : n / 10000 / 10000 < 184467440738 := by omega
      by_cases h3 : n / 10000 / 10000 < 10000
      · have ⟨hlo, hhi⟩ := formatDecimalNat_length_lt_10000 h3; omega
      · rw [formatDecimalNat_div_10000 (by omega), List.length_append, fourDecimalDigits_length]
        have hq3 : n / 10000 / 10000 / 10000 < 18446745 := by omega
        by_cases h4 : n / 10000 / 10000 / 10000 < 10000
        · have ⟨hlo, hhi⟩ := formatDecimalNat_length_lt_10000 h4; omega
        · rw [formatDecimalNat_div_10000 (by omega), List.length_append, fourDecimalDigits_length]
          have hq4 : n / 10000 / 10000 / 10000 / 10000 < 10000 := by omega
          have ⟨hlo, hhi⟩ := formatDecimalNat_length_lt_10000 hq4; omega

/-! ## Bounded Accumulator Parsing -/

@[simp] theorem parseDecimalNat_nil : parseDecimalNat [] = none := rfl
@[simp] theorem parseDecimalUInt_nil (width : Nat) : parseDecimalUInt width [] = none := rfl
@[simp] theorem parseDecimalU64_nil : parseDecimalU64 [] = none := rfl
@[simp] theorem parseDecimalU32_nil : parseDecimalU32 [] = none := rfl

/-- Unbounded ASCII decimal accumulator fold matching the body of `Arm64.parseDecimalNat`. -/
def parseDecimalNatFold (acc : Nat) (bs : List (BitVec 8)) : Option Nat :=
  bs.foldlM (init := acc) fun a b =>
    if 0x30#8 ≤ b && b ≤ 0x39#8 then
      some (a * 10 + (b.toNat - 0x30))
    else none

@[simp] theorem parseDecimalNatFold_nil (acc : Nat) :
    parseDecimalNatFold acc [] = some acc := rfl

theorem parseDecimalNat_of_nonempty {bs : List (BitVec 8)} (hne : bs ≠ []) :
    parseDecimalNat bs = parseDecimalNatFold 0 bs := by
  unfold parseDecimalNat parseDecimalNatFold
  rw [List.isEmpty_eq_false_iff.mpr hne]
  rfl

theorem parseDecimalNatFold_ge_acc :
    ∀ (bs : List (BitVec 8)) {acc n : Nat},
      parseDecimalNatFold acc bs = some n → acc ≤ n
  | [], _, _, h => by
    simp only [parseDecimalNatFold_nil, Option.some.injEq] at h
    omega
  | b :: rest, acc, n, h => by
    simp only [parseDecimalNatFold, List.foldlM_cons] at h
    by_cases hdig : (0x30#8 ≤ b && b ≤ 0x39#8) = true
    · simp only [hdig, ↓reduceIte, Option.bind_eq_bind, Option.bind_some] at h
      have hrec := parseDecimalNatFold_ge_acc rest h
      omega
    · simp only [hdig, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.bind_none,
        reduceCtorEq] at h

/-- Early-overflow ASCII decimal accumulator fold rejecting intermediate values `≥ bound`
    at each digit step. -/
def parseDecimalBoundedFold (bound acc : Nat) (bs : List (BitVec 8)) : Option Nat :=
  bs.foldlM (init := acc) fun a b =>
    if 0x30#8 ≤ b && b ≤ 0x39#8 then
      let next := a * 10 + (b.toNat - 0x30)
      if next < bound then some next else none
    else none

@[simp] theorem parseDecimalBoundedFold_nil (bound acc : Nat) :
    parseDecimalBoundedFold bound acc [] = some acc := rfl

/-- Because `parseDecimalNatFold` is monotone in its accumulator, rejecting intermediate values
    `≥ bound` at each step is equivalent to running the unbounded `parseDecimalNatFold` and
    checking `< bound` at the end (whenever the initial accumulator satisfies `acc < bound`). -/
theorem parseDecimalBoundedFold_eq :
    ∀ (bs : List (BitVec 8)) {bound acc : Nat},
      acc < bound →
      parseDecimalBoundedFold bound acc bs =
        match parseDecimalNatFold acc bs with
        | some n => if n < bound then some n else none
        | none => none
  | [], bound, acc, hacc => by
    simp [hacc]
  | b :: rest, bound, acc, _ => by
    simp only [parseDecimalBoundedFold, parseDecimalNatFold, List.foldlM_cons]
    by_cases hdig : (0x30#8 ≤ b && b ≤ 0x39#8) = true
    · simp only [hdig, ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
      by_cases hnext : acc * 10 + (b.toNat - 0x30) < bound
      · simp only [hnext, ↓reduceIte, Option.bind_some]
        exact parseDecimalBoundedFold_eq rest hnext
      · simp only [hnext, ↓reduceIte, Option.bind_none]
        change none = match parseDecimalNatFold (acc * 10 + (b.toNat - 0x30)) rest with
          | some n => if n < bound then some n else none
          | none => none
        cases htail : parseDecimalNatFold (acc * 10 + (b.toNat - 0x30)) rest with
        | none => rfl
        | some n =>
          have hge : acc * 10 + (b.toNat - 0x30) ≤ n := parseDecimalNatFold_ge_acc rest htail
          have hnot : ¬ (n < bound) := by omega
          simp [hnot]
    · simp [hdig]

theorem parseDecimalBoundedFold_lt {bound acc n : Nat} {bs : List (BitVec 8)}
    (hacc : acc < bound) (h : parseDecimalBoundedFold bound acc bs = some n) :
    n < bound := by
  rw [parseDecimalBoundedFold_eq bs hacc] at h
  cases hnat : parseDecimalNatFold acc bs with
  | none => simp [hnat] at h
  | some m =>
    simp only [hnat] at h
    by_cases hm : m < bound
    · simp only [hm, ↓reduceIte, Option.some.injEq] at h
      omega
    · simp [hm] at h

theorem parseDecimalUInt_eq_boundedFold (width : Nat) (bs : List (BitVec 8)) :
    parseDecimalUInt width bs =
      if bs.isEmpty then none
      else (parseDecimalBoundedFold (2 ^ width) 0 bs).map (BitVec.ofNat width) := by
  cases bs with
  | nil => rfl
  | cons b rest =>
    have hne : b :: rest ≠ [] := List.cons_ne_nil b rest
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, parseDecimalUInt,
      parseDecimalNat_of_nonempty hne]
    rw [parseDecimalBoundedFold_eq (b :: rest) (Nat.two_pow_pos width)]
    cases parseDecimalNatFold 0 (b :: rest) with
    | none => rfl
    | some n =>
      by_cases hn : n < 2 ^ width <;> simp [hn]

theorem parseDecimalUInt_of_nonempty (width : Nat) {bs : List (BitVec 8)} (hne : bs ≠ []) :
    parseDecimalUInt width bs =
      (parseDecimalBoundedFold (2 ^ width) 0 bs).map (BitVec.ofNat width) := by
  rw [parseDecimalUInt_eq_boundedFold, List.isEmpty_eq_false_iff.mpr hne]
  rfl

theorem parseDecimalU64_eq_boundedFold (bs : List (BitVec 8)) :
    parseDecimalU64 bs =
      if bs.isEmpty then none
      else (parseDecimalBoundedFold (2 ^ 64) 0 bs).map (BitVec.ofNat 64) :=
  parseDecimalUInt_eq_boundedFold 64 bs

theorem parseDecimalU64_of_nonempty {bs : List (BitVec 8)} (hne : bs ≠ []) :
    parseDecimalU64 bs =
      (parseDecimalBoundedFold (2 ^ 64) 0 bs).map (BitVec.ofNat 64) :=
  parseDecimalUInt_of_nonempty 64 hne

theorem parseDecimalU32_eq_boundedFold (bs : List (BitVec 8)) :
    parseDecimalU32 bs =
      if bs.isEmpty then none
      else (parseDecimalBoundedFold (2 ^ 32) 0 bs).map (BitVec.ofNat 32) :=
  parseDecimalUInt_eq_boundedFold 32 bs

theorem parseDecimalU32_of_nonempty {bs : List (BitVec 8)} (hne : bs ≠ []) :
    parseDecimalU32 bs =
      (parseDecimalBoundedFold (2 ^ 32) 0 bs).map (BitVec.ofNat 32) :=
  parseDecimalUInt_of_nonempty 32 hne

/-! ## Round-Trip Identities -/

theorem parseDecimalNatFold_append (acc : Nat) (xs ys : List (BitVec 8)) :
    parseDecimalNatFold acc (xs ++ ys) =
      (parseDecimalNatFold acc xs).bind (fun a => parseDecimalNatFold a ys) := by
  simp [parseDecimalNatFold, List.foldlM_append, Option.bind_eq_bind]

theorem parseDecimalNatFold_digit (acc : Nat) {d : Nat} (hd : d < 10) :
    parseDecimalNatFold acc [BitVec.ofNat 8 (0x30 + d)] = some (acc * 10 + d) := by
  unfold parseDecimalNatFold
  simp only [List.foldlM_cons, List.foldlM_nil]
  have hto : (BitVec.ofNat 8 (0x30 + d)).toNat = 0x30 + d := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hdig : (0x30#8 ≤ BitVec.ofNat 8 (0x30 + d) && BitVec.ofNat 8 (0x30 + d) ≤ 0x39#8) = true := by
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, BitVec.le_def, BitVec.le_def, hto]
    change 48 ≤ 0x30 + d ∧ 0x30 + d ≤ 57
    omega
  simp only [hdig, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, hto]
  exact congrArg some (by omega)

theorem parseDecimalNat_formatDecimalNat (n : Nat) :
    parseDecimalNat (formatDecimalNat n) = some n := by
  rw [parseDecimalNat_of_nonempty (formatDecimalNat_ne_nil n)]
  induction n using Nat.strongRecOn with
  | ind m ih =>
    by_cases hm : m < 10
    · rw [formatDecimalNat_of_lt_10 hm, parseDecimalNatFold_digit 0 hm]
      simp
    · rw [formatDecimalNat_of_ge_10 (by omega), parseDecimalNatFold_append,
          ih (m / 10) (by omega), Option.bind_some,
          parseDecimalNatFold_digit (m / 10) (Nat.mod_lt m (by omega))]
      exact congrArg some (by omega)

theorem parseDecimalUInt_formatDecimalNat {width : Nat} (v : BitVec width) :
    parseDecimalUInt width (formatDecimalNat v.toNat) = some v := by
  simp [parseDecimalUInt, parseDecimalNat_formatDecimalNat, v.isLt]

@[simp] theorem parseDecimalU64_formatDecimalNat (v : BitVec 64) :
    parseDecimalU64 (formatDecimalNat v.toNat) = some v :=
  parseDecimalUInt_formatDecimalNat v

@[simp] theorem parseDecimalU32_formatDecimalNat (v : BitVec 32) :
    parseDecimalU32 (formatDecimalNat v.toNat) = some v :=
  parseDecimalUInt_formatDecimalNat v

end ProofLib.AsciiNum
