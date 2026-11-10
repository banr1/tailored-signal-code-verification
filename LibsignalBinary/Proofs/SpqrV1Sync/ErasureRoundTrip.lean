/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16

/-!
# SPQR V1 Polynomial Erasure-Code End-to-End Round-Trip

Assembles the `GF(2 ^ 16)` polynomial erasure-code correctness proofs (`foldl_addChunk_spec`,
`decode_honest_chunks`, `runChunks_spec`, and `encode_decode_roundtrip`): encoding any even-length
message `msg` (`msg.length ≤ 2 ^ 20`), emitting `n` chunks via `runChunks`, and feeding any subset
containing at least `needed msg.length 0` distinct chunk indices (in arbitrary order and with
arbitrary duplicates) to a fresh `PolyDecoder` recovers `some msg`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1Sync.Erasure

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.GF16Field
open Polynomial

/-! ### Basic `GF16`, `idxPt`, `needed`, and `polyOf` algebra -/

private theorem constMul_eq (a b : GF16) : GF16.constMul a b = a * b := rfl

private theorem constSub_eq (a b : GF16) : GF16.constSub a b = a - b := rfl

private theorem constDivLoop_eq_divImplLoop :
    ∀ (n : Nat) (sq out : GF16),
      GF16.constDivLoop n sq out = ⟨GF16.divImplLoop n (GF16.mul sq sq).value out.value⟩
  | 0, sq, out => rfl
  | n + 1, sq, out => by
    simp only [GF16.constDivLoop, GF16.divImplLoop, mul2U16, constMul_eq]
    have hcomm : (⟨unaccelerated.mul (GF16.mul sq sq).value out.value⟩ : GF16) = out * (sq * sq) :=
      GF16Field.mul_comm' (sq * sq) out
    have hval : unaccelerated.mul (GF16.mul sq sq).value out.value = (out * (sq * sq)).value :=
      congrArg GF16.value hcomm
    rw [hval]
    exact constDivLoop_eq_divImplLoop n (sq * sq) (out * (sq * sq))

private theorem constDiv_eq (a b : GF16) : GF16.constDiv a b = a / b :=
  constDivLoop_eq_divImplLoop 15 b a

private theorem parallelMult_eq_map (a : GF16) :
    ∀ (cs : List GF16), parallelMult a cs = cs.map (fun c => a * c)
  | [] => rfl
  | [x] => by
    simp only [parallelMult, List.map]
    exact congrArg (· :: []) (GF16Field.mul_comm' x a)
  | x1 :: x2 :: rest => by
    simp only [parallelMult, mul2U16, List.map]
    rw [parallelMult_eq_map a rest]
    rfl

private theorem idxPt_injOn {n : Nat} (hn : n ≤ 2 ^ 16) :
    Set.InjOn idxPt ↑(Finset.range n) := by
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  have hval : BitVec.ofNat 16 i = BitVec.ofNat 16 j := congrArg GF16.value hij
  have hnat := congrArg BitVec.toNat hval
  simp only [BitVec.toNat_ofNat] at hnat
  omega

private theorem needed_le_2pow16 {len : Nat} (hlen : len ≤ 2 ^ 20) (j : Nat) :
    needed len j ≤ 2 ^ 16 := by
  unfold needed
  split <;> omega

private theorem needed_le_needed_zero (len j : Nat) :
    needed len j ≤ needed len 0 := by
  unfold needed
  split <;> split <;> omega

private theorem necessaryPoints_eq_needed {dec : PolyDecoder} {len : Nat}
    (hpts : dec.ptsNeeded = len / 2) (j : Nat) :
    dec.necessaryPoints j = needed len j := by
  simp [PolyDecoder.necessaryPoints, needed, hpts]

private theorem polyOf_nil : polyOf [] = 0 := by
  simp [polyOf]

private theorem polyOf_cons (c : GF16) (cs : List GF16) :
    polyOf (c :: cs) = C c + X * polyOf cs := by
  unfold polyOf
  rw [List.length_cons, Finset.sum_range_succ']
  simp only [List.getD_cons_zero, pow_zero, mul_one, List.getD_cons_succ, Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ']
  ring

private theorem polyOf_append (as bs : List GF16) :
    polyOf (as ++ bs) = polyOf as + X ^ as.length * polyOf bs := by
  induction as with
  | nil => simp [polyOf_nil]
  | cons a rest ih =>
    simp only [List.cons_append, List.length_cons, polyOf_cons, ih]
    rw [pow_succ', mul_add, ← mul_assoc]
    ring

private theorem polyOf_replicate_zero (n : Nat) :
    polyOf (List.replicate n GF16.ZERO) = 0 := by
  induction n with
  | zero => exact polyOf_nil
  | succ k ih =>
    rw [List.replicate_succ, polyOf_cons, ih]
    change C (0 : GF16) + X * 0 = 0
    simp

private theorem polyOf_map_mul (a : GF16) (cs : List GF16) :
    polyOf (cs.map (fun c => a * c)) = C a * polyOf cs := by
  induction cs with
  | nil => simp [polyOf_nil]
  | cons c rest ih =>
    simp only [List.map_cons, polyOf_cons, ih, map_mul]
    ring

private theorem polyOf_addAssignCoeffs :
    ∀ (as bs : List GF16), polyOf (Poly.addAssignCoeffs as bs) = polyOf as + polyOf bs
  | [], [] => by simp [Poly.addAssignCoeffs, polyOf_nil]
  | a :: as, [] => by simp [Poly.addAssignCoeffs, polyOf_nil]
  | [], b :: bs => by simp [Poly.addAssignCoeffs, polyOf_nil]
  | a :: as, b :: bs => by
    simp only [Poly.addAssignCoeffs, polyOf_cons, polyOf_addAssignCoeffs as bs]
    change C (a + b) + X * (polyOf as + polyOf bs) = (C a + X * polyOf as) + (C b + X * polyOf bs)
    rw [map_add]
    ring

private theorem degree_polyOf_lt :
    ∀ (cs : List GF16), (polyOf cs).degree < (cs.length : WithBot ℕ)
  | [] => by
    rw [polyOf_nil, List.length_nil, degree_zero]
    exact WithBot.bot_lt_coe 0
  | c :: cs => by
    rw [polyOf_cons, List.length_cons]
    have ih := degree_polyOf_lt cs
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt degree_C_le (Nat.cast_lt.mpr (Nat.zero_lt_succ _))
    · refine lt_of_le_of_lt (degree_mul_le _ _) ?_
      rw [degree_X]
      cases hdeg : (polyOf cs).degree with
      | bot =>
        simp only [WithBot.add_bot]
        exact WithBot.bot_lt_coe _
      | coe d =>
        rw [hdeg] at ih
        have hd : d < cs.length := Nat.cast_lt.mp ih
        change ((1 + d : ℕ) : WithBot ℕ) < ((cs.length + 1 : ℕ) : WithBot ℕ)
        exact Nat.cast_lt.mpr (by omega)

private theorem degree_msgPoly_lt {msg : List (BitVec 8)} (hlen : msg.length ≤ 2 ^ 20) (j : Nat) :
    (msgPoly msg j).degree < (needed msg.length j : WithBot ℕ) := by
  unfold msgPoly
  set n := needed msg.length j
  have hn : n ≤ 2 ^ 16 := needed_le_2pow16 hlen j
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, Finset.range_zero, Lagrange.interpolate_empty, degree_zero]
    exact WithBot.bot_lt_coe 0
  · have hle := Lagrange.degree_interpolate_le (fun k => msgVal msg (16 * k + j)) (idxPt_injOn hn)
    rw [Finset.card_range] at hle
    exact lt_of_le_of_lt hle (Nat.cast_lt.mpr (by omega))

private theorem eval_msgPoly_at_node {msg : List (BitVec 8)} (hlen : msg.length ≤ 2 ^ 20)
    (j k : Nat) (hk : k < needed msg.length j) :
    (msgPoly msg j).eval (idxPt k) = msgVal msg (16 * k + j) := by
  unfold msgPoly
  exact Lagrange.eval_interpolate_at_node _
    (idxPt_injOn (needed_le_2pow16 hlen j)) (Finset.mem_range.mpr hk)

/-! ### `Poly.computeAt` correctness -/

private theorem computeAtPowersLoop_spec (x : GF16) :
    ∀ (rem i : Nat) (xs : List GF16),
      2 ≤ i → xs.length = i → (∀ k, k < i → xs[k]? = some (x ^ k)) →
      ∃ xs', Poly.computeAtPowersLoop i rem xs = .ok xs' ∧
        xs'.length = i + rem ∧ (∀ k, k < i + rem → xs'[k]? = some (x ^ k))
  | 0, i, xs, _, hlen, hpow => ⟨xs, rfl, by omega, by simpa using hpow⟩
  | rem + 1, i, xs, hi, hlen, hpow => by
    have h1 : xs[i / 2]? = some (x ^ (i / 2)) := hpow (i / 2) (by omega)
    have h2 : xs[i / 2 + i % 2]? = some (x ^ (i / 2 + i % 2)) := hpow (i / 2 + i % 2) (by omega)
    simp only [Poly.computeAtPowersLoop, h1, h2]
    have hmul : GF16.mul (x ^ (i / 2)) (x ^ (i / 2 + i % 2)) = x ^ i := by
      change x ^ (i / 2) * x ^ (i / 2 + i % 2) = x ^ i
      rw [← pow_add]
      congr 1
      omega
    rw [hmul]
    have hlen' : (xs ++ [x ^ i]).length = i + 1 := by simp [hlen]
    have hpow' : ∀ k, k < i + 1 → (xs ++ [x ^ i])[k]? = some (x ^ k) := by
      intro k hk
      by_cases hki : k < i
      · rw [List.getElem?_append_left (by omega)]
        exact hpow k hki
      · have hkeq : k = i := by omega
        subst hkeq
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
    obtain ⟨xs', hok, hlen'', hpow''⟩ :=
      computeAtPowersLoop_spec x rem (i + 1) (xs ++ [x ^ i]) (by omega) hlen' hpow'
    exact ⟨xs', hok, by omega, fun k hk => hpow'' k (by omega)⟩

private theorem foldl_zip_powers_eq_eval (x : GF16) :
    ∀ (cs : List GF16) (n : Nat) (xs : List GF16) (acc : GF16),
      cs.length + n ≤ xs.length →
      (∀ k, k < cs.length → xs[n + k]? = some (x ^ (n + k))) →
      (cs.zip (xs.drop n)).foldl (fun out (a, b) => GF16.add out (GF16.mul a b)) acc =
        acc + x ^ n * (polyOf cs).eval x
  | [], n, xs, acc, _, _ => by
    simp only [List.zip_nil_left, List.foldl_nil, polyOf_nil, eval_zero]
    change acc = acc + x ^ n * 0
    ring
  | c :: cs, n, xs, acc, hlen, hpow => by
    have hn_lt : n < xs.length := by simp at hlen; omega
    have hdrop : xs.drop n = xs[n] :: xs.drop (n + 1) := List.drop_eq_getElem_cons hn_lt
    have hx0_opt : xs[n]? = some (x ^ n) := by simpa using hpow 0 (by simp)
    have hx0 : xs[n] = x ^ n := by
      rw [List.getElem?_eq_getElem hn_lt] at hx0_opt
      exact Option.some.inj hx0_opt
    rw [hdrop, List.zip_cons_cons, List.foldl_cons]
    have hlen' : cs.length + (n + 1) ≤ xs.length := by simp at hlen ⊢; omega
    have hpow' : ∀ k, k < cs.length → xs[(n + 1) + k]? = some (x ^ ((n + 1) + k)) := by
      intro k hk
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using hpow (k + 1) (by simp [hk])
    rw [foldl_zip_powers_eq_eval x cs (n + 1) xs (GF16.add acc (GF16.mul c xs[n])) hlen' hpow']
    rw [polyOf_cons, eval_add, eval_mul, eval_C, eval_X, hx0, pow_succ]
    change (acc + c * x ^ n) + (x ^ n * x) * (polyOf cs).eval x =
      acc + x ^ n * (c + x * (polyOf cs).eval x)
    ring

private theorem computeAt_eq_eval (p : Poly) (x : GF16) :
    p.computeAt x = .ok ((polyOf p.coefficients).eval x) := by
  unfold Poly.computeAt
  have hxs0_pow : ∀ k, k < 2 → ([GF16.ONE, x] : List GF16)[k]? = some (x ^ k) := by
    intro k hk
    match k, hk with
    | 0, _ => rfl
    | 1, _ =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, pow_one]
  by_cases hle : p.coefficients.length ≤ 2
  · simp only [hle, ↓reduceIte]
    change Except.ok ((p.coefficients.zip ([GF16.ONE, x].drop 0)).foldl
      (fun out (a, b) => GF16.add out (GF16.mul a b)) GF16.ZERO) = _
    rw [foldl_zip_powers_eq_eval x p.coefficients 0 [GF16.ONE, x] GF16.ZERO
      (by simp; omega) (fun k hk => by simpa using hxs0_pow k (by omega))]
    change Except.ok ((0 : GF16) + x ^ 0 * (polyOf p.coefficients).eval x) = _
    congr 1
    ring
  · simp only [hle, ↓reduceIte]
    obtain ⟨xs, hok, hxs_len, hxs_pow⟩ :=
      computeAtPowersLoop_spec x (p.coefficients.length - 2) 2 [GF16.ONE, x] (by omega) rfl hxs0_pow
    rw [hok]
    change Except.ok ((p.coefficients.zip (xs.drop 0)).foldl
      (fun out (a, b) => GF16.add out (GF16.mul a b)) GF16.ZERO) = _
    rw [foldl_zip_powers_eq_eval x p.coefficients 0 xs GF16.ZERO (by omega)
      (fun k hk => by simpa using hxs_pow k (by omega))]
    change Except.ok ((0 : GF16) + x ^ 0 * (polyOf p.coefficients).eval x) = _
    congr 1
    ring

/-! ### `Poly.lagrangeInterpolate` and `Poly.lagrangeInterpolatePt` -/

private theorem multXdiffAssignTrailingLoop_spec (d : GF16) :
    ∀ (rem i : Nat) (coeffs : List GF16),
      1 ≤ i → i + rem = coeffs.length →
      ∃ coeffs', Poly.multXdiffAssignTrailingLoop d i rem coeffs = .ok coeffs' ∧
        coeffs'.length = coeffs.length ∧
        (∀ k, k < coeffs.length →
          coeffs'.getD k GF16.ZERO =
            if k < i - 1 then coeffs.getD k GF16.ZERO
            else if k < coeffs.length - 1 then coeffs.getD k GF16.ZERO - coeffs.getD (k + 1) GF16.ZERO * d
            else coeffs.getD k GF16.ZERO)
  | 0, i, coeffs, hi, hlen => by
    refine ⟨coeffs, rfl, rfl, ?_⟩
    intro k hk
    by_cases hk1 : k < i - 1
    · simp [hk1]
    · have hk2 : ¬(k < coeffs.length - 1) := by omega
      simp [hk1, hk2]
  | rem + 1, i, coeffs, hi, hlen => by
    have hi_ne : (i == 0) = false := by
      cases i <;> simp at hi ⊢
    have hi_lt : i < coeffs.length := by omega
    have hip_lt : i - 1 < coeffs.length := by omega
    have hgi : coeffs[i]? = some (coeffs.getD i GF16.ZERO) := by
      rw [List.getElem?_eq_getElem hi_lt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_lt]
      rfl
    have hgip : coeffs[i - 1]? = some (coeffs.getD (i - 1) GF16.ZERO) := by
      rw [List.getElem?_eq_getElem hip_lt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hip_lt]
      rfl
    simp only [Poly.multXdiffAssignTrailingLoop, hi_ne, Bool.false_eq_true, ↓reduceIte, hgi, hgip]
    set c1 := coeffs.set (i - 1) (GF16.sub (coeffs.getD (i - 1) GF16.ZERO) (GF16.mul (coeffs.getD i GF16.ZERO) d))
    have hc1_len : c1.length = coeffs.length := List.length_set
    obtain ⟨coeffs', hok, hlen', hget'⟩ :=
      multXdiffAssignTrailingLoop_spec d rem (i + 1) c1 (by omega) (by omega)
    refine ⟨coeffs', hok, by omega, ?_⟩
    intro k hk
    have hget_c1 : ∀ m, m < coeffs.length →
        c1.getD m GF16.ZERO =
          if m = i - 1 then coeffs.getD (i - 1) GF16.ZERO - coeffs.getD i GF16.ZERO * d
          else coeffs.getD m GF16.ZERO := by
      intro m hm
      simp only [c1, List.getD_eq_getElem?_getD]
      by_cases hmeq : m = i - 1
      · subst hmeq
        simp only [↓reduceIte, List.getElem?_set_self hip_lt, Option.getD_some]
        rfl
      · simp only [hmeq, ↓reduceIte, List.getElem?_set_ne (Ne.symm hmeq)]
    rw [hget' k (by omega), hc1_len]
    by_cases hk1 : k < i - 1
    · have hk2 : k < (i + 1) - 1 := by omega
      simp only [hk1, hk2, ↓reduceIte, hget_c1 k hk]
      have : k ≠ i - 1 := by omega
      simp [this]
    · by_cases hk2 : k = i - 1
      · subst hk2
        have hlt1 : i - 1 < (i + 1) - 1 := by omega
        have hnlt : ¬(i - 1 < i - 1) := by omega
        have hlt2 : i - 1 < coeffs.length - 1 := by omega
        simp only [hlt1, hnlt, hlt2, ↓reduceIte, hget_c1 (i - 1) hip_lt]
        have heq : i - 1 + 1 = i := by omega
        rw [heq]
      · have hnlt1 : ¬(k < (i + 1) - 1) := by omega
        simp only [hk1, hnlt1, ↓reduceIte]
        by_cases hk3 : k < coeffs.length - 1
        · simp only [hk3, ↓reduceIte, hget_c1 k hk, hget_c1 (k + 1) (by omega)]
          have hne1 : k ≠ i - 1 := hk2
          have hne2 : k + 1 ≠ i - 1 := by omega
          simp [hne1, hne2]
        · simp only [hk3, ↓reduceIte, hget_c1 k hk]
          have hne1 : k ≠ i - 1 := hk2
          simp [hne1]

private theorem multXdiffAssignTrailing_polyOf (p : Poly) (s offset : Nat) (d : GF16)
    (hlen : p.coefficients.length = offset + 1)
    (hs1 : 1 ≤ s) (hso : s ≤ offset)
    (hzero : ∀ k, k < s → p.coefficients.getD k GF16.ZERO = 0) :
    ∃ p', p.multXdiffAssignTrailing s d = .ok p' ∧
      p'.coefficients.length = offset + 1 ∧
      (∀ k, k < s - 1 → p'.coefficients.getD k GF16.ZERO = 0) ∧
      X * polyOf p'.coefficients = (X - C d) * polyOf p.coefficients := by
  unfold Poly.multXdiffAssignTrailing
  have hnlt : ¬(s ≥ p.coefficients.length) := by omega
  simp only [hnlt, ↓reduceIte]
  obtain ⟨cs', hok, hlen', hget'⟩ :=
    multXdiffAssignTrailingLoop_spec d (p.coefficients.length - s) s p.coefficients hs1 (by omega)
  rw [hok]
  refine ⟨{ coefficients := cs' }, rfl, by dsimp; omega, ?_, ?_⟩
  · intro k hk
    rw [hget' k (by omega)]
    have : k < s - 1 := hk
    simp only [this, ↓reduceIte]
    exact hzero k (by omega)
  · set cs := p.coefficients
    have hcs0 : cs.getD 0 GF16.ZERO = 0 := hzero 0 (by omega)
    have hcs_oob : cs.getD (offset + 1) GF16.ZERO = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    have hshift : ∑ k ∈ Finset.range (offset + 1), C (cs.getD (k + 1) GF16.ZERO) * X ^ (k + 1) =
        polyOf cs := by
      unfold polyOf
      rw [Finset.sum_range_succ, hcs_oob]
      conv => rhs; rw [hlen, Finset.sum_range_succ']
      rw [hcs0]
      simp only [pow_zero, mul_one, map_zero, zero_mul, add_zero]
    have hlhs : X * polyOf cs' =
        ∑ k ∈ Finset.range (offset + 1),
          C (cs.getD k GF16.ZERO - cs.getD (k + 1) GF16.ZERO * d) * X ^ (k + 1) := by
      unfold polyOf
      rw [hlen', hlen, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk_lt : k < offset + 1 := Finset.mem_range.mp hk
      rw [hget' k (by omega), hlen]
      have hterm : C (cs.getD k GF16.ZERO - cs.getD (k + 1) GF16.ZERO * d) * X ^ (k + 1) =
          X * (C (if k < s - 1 then cs.getD k GF16.ZERO
            else if k < offset + 1 - 1 then cs.getD k GF16.ZERO - cs.getD (k + 1) GF16.ZERO * d
            else cs.getD k GF16.ZERO) * X ^ k) := by
        by_cases h1 : k < s - 1
        · simp only [h1, ↓reduceIte]
          rw [hzero k (by omega), hzero (k + 1) (by omega)]
          simp only [zero_mul, sub_zero, map_zero, mul_zero]
        · by_cases h2 : k < offset + 1 - 1
          · simp only [h1, h2, ↓reduceIte, pow_succ']
            ring
          · have hkeq : k = offset := by omega
            subst hkeq
            simp only [h1, h2, ↓reduceIte, hcs_oob, zero_mul, sub_zero, pow_succ']
            ring
      exact hterm.symm
    rw [hlhs]
    have hsplit :
        (∑ k ∈ Finset.range (offset + 1),
          C (cs.getD k GF16.ZERO - cs.getD (k + 1) GF16.ZERO * d) * X ^ (k + 1)) =
        (∑ k ∈ Finset.range (offset + 1), X * (C (cs.getD k GF16.ZERO) * X ^ k)) -
        C d * (∑ k ∈ Finset.range (offset + 1), C (cs.getD (k + 1) GF16.ZERO) * X ^ (k + 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_sub, map_mul, pow_succ']
      ring
    rw [hsplit, ← Finset.mul_sum, hshift]
    have hpoly : polyOf cs = ∑ k ∈ Finset.range (offset + 1), C (cs.getD k GF16.ZERO) * X ^ k := by
      unfold polyOf
      rw [hlen]
    rw [← hpoly]
    ring

private theorem lagrangeInterpolatePrepareLoop_spec (pts : List Pt) (offset : Nat)
    (hoff : offset = pts.length) :
    ∀ (rem k : Nat) (p : Poly),
      k + rem = offset →
      p.coefficients.length = offset + 1 →
      (∀ m, m < offset - k → p.coefficients.getD m GF16.ZERO = 0) →
      X ^ k * polyOf p.coefficients =
        X ^ offset * ∏ m ∈ Finset.range k, (X - C (pts.getD m default).x) →
      ∃ p', Poly.lagrangeInterpolatePrepareLoop pts offset k rem p = .ok p' ∧
        p'.coefficients.length = offset + 1 ∧
        polyOf p'.coefficients = ∏ m ∈ Finset.range offset, (X - C (pts.getD m default).x)
  | 0, k, p, hk, hlen, _, hpoly => by
    have hkeq : k = offset := by omega
    subst hkeq
    have hcancel : polyOf p.coefficients =
        ∏ m ∈ Finset.range k, (X - C (pts.getD m default).x) :=
      mul_left_cancel₀ (pow_ne_zero k X_ne_zero) hpoly
    exact ⟨p, rfl, hlen, hcancel⟩
  | rem + 1, k, p, hk, hlen, hzero, hpoly => by
    have hk_lt : k < pts.length := by omega
    have hget : pts[k]? = some (pts.getD k default) := by
      rw [List.getElem?_eq_getElem hk_lt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt]
      rfl
    have hnle : ¬(k > offset) := by omega
    simp only [Poly.lagrangeInterpolatePrepareLoop, hget, hnle, ↓reduceIte]
    obtain ⟨p1, hp1, hp1_len, hp1_zero, hp1_poly⟩ :=
      multXdiffAssignTrailing_polyOf p (offset - k) offset (pts.getD k default).x
        hlen (by omega) (by omega) hzero
    rw [hp1]
    have hzero' : ∀ m, m < offset - (k + 1) → p1.coefficients.getD m GF16.ZERO = 0 := by
      intro m hm
      exact hp1_zero m (by omega)
    have hpoly' : X ^ (k + 1) * polyOf p1.coefficients =
        X ^ offset * ∏ m ∈ Finset.range (k + 1), (X - C (pts.getD m default).x) := by
      calc
        X ^ (k + 1) * polyOf p1.coefficients
            = X ^ k * (X * polyOf p1.coefficients) := by rw [pow_succ, mul_assoc]
        _ = X ^ k * ((X - C (pts.getD k default).x) * polyOf p.coefficients) := by rw [hp1_poly]
        _ = (X ^ k * polyOf p.coefficients) * (X - C (pts.getD k default).x) := by ring
        _ = (X ^ offset * ∏ m ∈ Finset.range k, (X - C (pts.getD m default).x)) *
              (X - C (pts.getD k default).x) := by rw [hpoly]
        _ = X ^ offset * ∏ m ∈ Finset.range (k + 1), (X - C (pts.getD m default).x) := by
              rw [Finset.prod_range_succ, mul_assoc]
    exact lagrangeInterpolatePrepareLoop_spec pts offset hoff rem (k + 1) p1
      (by omega) hp1_len hzero' hpoly'

private theorem lagrangeInterpolatePrepare_spec (pts : List Pt) (hbound : pts.length ≤ 2 ^ 20) :
    ∃ p, Poly.lagrangeInterpolatePrepare pts = .ok p ∧
      p.coefficients.length = pts.length + 1 ∧
      polyOf p.coefficients = ∏ m ∈ Finset.range pts.length, (X - C (pts.getD m default).x) := by
  unfold Poly.lagrangeInterpolatePrepare
  have husize : ¬(pts.length + 1 > USIZE_MAX) := by
    unfold USIZE_MAX
    omega
  simp only [husize, ↓reduceIte]
  set p0 : Poly := { coefficients := List.replicate pts.length GF16.ZERO ++ [GF16.ONE] }
  have hp0_len : p0.coefficients.length = pts.length + 1 := by simp [p0]
  have hp0_zero : ∀ m, m < pts.length - 0 → p0.coefficients.getD m GF16.ZERO = 0 := by
    intro m hm
    simp only [p0, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp; omega)]
    rw [List.getElem?_replicate_of_lt (by omega)]
    rfl
  have hp0_poly : X ^ 0 * polyOf p0.coefficients =
      X ^ pts.length * ∏ m ∈ Finset.range 0, (X - C (pts.getD m default).x) := by
    simp only [p0, pow_zero, one_mul, Finset.range_zero, Finset.prod_empty, mul_one,
      polyOf_append, polyOf_replicate_zero, List.length_replicate, zero_add, polyOf_cons, polyOf_nil]
    change X ^ pts.length * (C (1 : GF16) + X * 0) = X ^ pts.length
    simp only [map_one, mul_zero, add_zero, mul_one]
  exact lagrangeInterpolatePrepareLoop_spec pts pts.length rfl pts.length 0 p0
    (by omega) hp0_len hp0_zero hp0_poly

private noncomputable def completePhi (pix scale : GF16) (len idx : Nat) (c : List GF16) : GF16[X] :=
  C scale * (∑ k ∈ Finset.range (idx + 1), C (c.getD k GF16.ZERO) * X ^ k) +
    (X - C pix) * (∑ k ∈ Finset.Ico (idx + 1) len, C (c.getD k GF16.ZERO) * X ^ (k - 1))

private theorem lagrangeCompleteDivLoop_spec (pix scale : GF16) (len : Nat) :
    ∀ (rem j : Nat) (c : List GF16),
      c.length = len →
      1 ≤ j → j + rem = len →
      ∃ c', Poly.lagrangeCompleteDivLoop pix scale len j rem c = .ok c' ∧
        c'.length = len ∧
        completePhi pix scale len 0 c' = completePhi pix scale len (len - j) c
  | 0, j, c, hlen, hj, hjrem => by
    have hjeq : len - j = 0 := by omega
    exact ⟨c, rfl, hlen, by rw [hjeq]⟩
  | rem + 1, j, c, hlen, hj, hjrem => by
    have hjle : ¬(j > len) := by omega
    set idx := len - j
    have hidx0 : (idx == 0) = false := beq_false_of_ne (by omega : idx ≠ 0)
    have hidx_lt : idx < c.length := by omega
    have hidxp_lt : idx - 1 < c.length := by omega
    have hg1 : c[idx]? = some (c.getD idx GF16.ZERO) := by
      rw [List.getElem?_eq_getElem hidx_lt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_lt]
      rfl
    have hg2 : c[idx - 1]? = some (c.getD (idx - 1) GF16.ZERO) := by
      rw [List.getElem?_eq_getElem hidxp_lt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidxp_lt]
      rfl
    simp only [Poly.lagrangeCompleteDivLoop, hjle, ↓reduceIte, idx, hidx0, Bool.false_eq_true, hg1, hg2]
    set c1 := c.set idx (GF16.mul (c.getD idx GF16.ZERO) scale)
    set c2 := c1.set (idx - 1) (GF16.add (c.getD (idx - 1) GF16.ZERO) (GF16.mul (c.getD idx GF16.ZERO) pix))
    have hc2_len : c2.length = len := by simp [c2, c1, hlen]
    obtain ⟨c', hok, hlen', hphi_ih⟩ :=
      lagrangeCompleteDivLoop_spec pix scale len rem (j + 1) c2 hc2_len (by omega) (by omega)
    refine ⟨c', hok, hlen', ?_⟩
    rw [hphi_ih]
    have hidx_step : len - (j + 1) = idx - 1 := by omega
    rw [hidx_step]
    have hc2_get : ∀ k, k < len →
        c2.getD k GF16.ZERO =
          if k = idx - 1 then c.getD (idx - 1) GF16.ZERO + c.getD idx GF16.ZERO * pix
          else if k = idx then c.getD idx GF16.ZERO * scale
          else c.getD k GF16.ZERO := by
      intro k hk
      simp only [c2, c1, List.getD_eq_getElem?_getD, List.getElem?_set]
      by_cases hk1 : k = idx - 1
      · subst hk1
        have h1 : idx - 1 < c.length := by omega
        simp [h1]
      · have hne1 : idx - 1 ≠ k := fun h => hk1 h.symm
        by_cases hk2 : k = idx
        · subst hk2
          simp [hne1, hk1, hidx_lt]
        · have hne2 : idx ≠ k := fun h => hk2 h.symm
          simp [hne1, hne2, hk1, hk2]
    unfold completePhi
    have hidx_pos : 1 ≤ idx := by omega
    have hr1 : idx - 1 + 1 = idx := by omega
    rw [hr1]
    have hsum1 :
        (∑ k ∈ Finset.range idx, C (c2.getD k GF16.ZERO) * X ^ k) =
        (∑ k ∈ Finset.range (idx - 1), C (c.getD k GF16.ZERO) * X ^ k) +
          C (c.getD (idx - 1) GF16.ZERO + c.getD idx GF16.ZERO * pix) * X ^ (idx - 1) := by
      conv => lhs; rw [← hr1]
      rw [Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        have hk_lt : k < idx - 1 := Finset.mem_range.mp hk
        rw [hc2_get k (by omega)]
        have h1 : k ≠ idx - 1 := by omega
        have h2 : k ≠ idx := by omega
        simp [h1, h2]
      · rw [hc2_get (idx - 1) (by omega)]
        simp
    have hsum2 :
        (∑ k ∈ Finset.Ico idx len, C (c2.getD k GF16.ZERO) * X ^ (k - 1)) =
        C (c.getD idx GF16.ZERO * scale) * X ^ (idx - 1) +
          ∑ k ∈ Finset.Ico (idx + 1) len, C (c.getD k GF16.ZERO) * X ^ (k - 1) := by
      have hico : Finset.Ico idx len = insert idx (Finset.Ico (idx + 1) len) := by
        ext k
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      rw [hico, Finset.sum_insert (by simp)]
      congr 1
      · rw [hc2_get idx (by omega)]
        have : idx ≠ idx - 1 := by omega
        simp [this]
      · apply Finset.sum_congr rfl
        intro k hk
        have hk_mem := Finset.mem_Ico.mp hk
        rw [hc2_get k (by omega)]
        have h1 : k ≠ idx - 1 := by omega
        have h2 : k ≠ idx := by omega
        simp [h1, h2]
    have hsum3 :
        (∑ k ∈ Finset.range (idx + 1), C (c.getD k GF16.ZERO) * X ^ k) =
        (∑ k ∈ Finset.range (idx - 1), C (c.getD k GF16.ZERO) * X ^ k) +
          C (c.getD (idx - 1) GF16.ZERO) * X ^ (idx - 1) +
          C (c.getD idx GF16.ZERO) * (X * X ^ (idx - 1)) := by
      conv => lhs; rw [Finset.sum_range_succ, ← hr1, Finset.sum_range_succ]
      rw [pow_succ' (X : GF16[X]) (idx - 1), hr1]
    rw [hsum1, hsum2, hsum3]
    simp only [map_add, map_mul]
    ring

private theorem lagrangeDenominator_eq_prod (pts : List Pt) (i : Nat)
    (hi : i < pts.length) (hnodup : (pts.map Pt.x).Nodup) :
    Poly.lagrangeDenominator (pts.getD i default).x pts =
      ∏ m ∈ (Finset.range pts.length).erase i, ((pts.getD i default).x - (pts.getD m default).x) := by
  unfold Poly.lagrangeDenominator
  have haux : ∀ (k : Nat) (acc : GF16), k ≤ pts.length →
      (pts.drop k).foldl (fun d pj => if (pts.getD i default).x == pj.x then d else GF16.mul d (GF16.sub (pts.getD i default).x pj.x)) acc =
        acc * ∏ m ∈ (Finset.Ico k pts.length).erase i, ((pts.getD i default).x - (pts.getD m default).x) := by
    intro k
    induction hrem : pts.length - k generalizing k with
    | zero =>
      intro acc hk
      have hkeq : k = pts.length := by omega
      subst hkeq
      simp only [List.drop_length, List.foldl_nil, Finset.Ico_self, Finset.erase_empty,
        Finset.prod_empty, mul_one]
    | succ r ih =>
      intro acc hk
      have hk_lt : k < pts.length := by omega
      have hdrop : pts.drop k = pts[k] :: pts.drop (k + 1) := List.drop_eq_getElem_cons hk_lt
      have hpk : pts[k] = pts.getD k default := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt]
        rfl
      rw [hdrop, List.foldl_cons, hpk]
      by_cases hki : k = i
      · subst hki
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [ih (k + 1) (by omega) acc (by omega)]
        congr 1
        have herase : (Finset.Ico (k + 1) pts.length).erase k = (Finset.Ico k pts.length).erase k := by
          ext m
          simp only [Finset.mem_erase, Finset.mem_Ico]
          omega
        rw [herase]
      · have hneq_x : (pts.getD i default).x ≠ (pts.getD k default).x := by
          intro heq
          have hnodup_idx := List.nodup_iff_injective_getElem.mp hnodup
          have hi' : i < (pts.map Pt.x).length := by simp [hi]
          have hk' : k < (pts.map Pt.x).length := by simp [hk_lt]
          have heq' : (pts.map Pt.x)[i] = (pts.map Pt.x)[k] := by
            simp only [List.getElem_map]
            have h1 : pts[i] = pts.getD i default := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
            have h2 : pts[k] = pts.getD k default := hpk
            rw [h1, h2, heq]
          exact hki (( @hnodup_idx ⟨i, hi'⟩ ⟨k, hk'⟩ heq' |> Fin.ext_iff.mp ).symm)
        have hbeq : ((pts.getD i default).x == (pts.getD k default).x) = false :=
          beq_false_of_ne hneq_x
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        rw [ih (k + 1) (by omega) _ (by omega)]
        have hico : (Finset.Ico k pts.length).erase i =
            insert k ((Finset.Ico (k + 1) pts.length).erase i) := by
          ext m
          simp only [Finset.mem_erase, Finset.mem_Ico, Finset.mem_insert]
          omega
        rw [hico, Finset.prod_insert (by simp)]
        change (acc * ((pts.getD i default).x - (pts.getD k default).x)) * _ = _
        ring
  have h0 := haux 0 GF16.ONE (Nat.zero_le _)
  have hico0 : Finset.Ico 0 pts.length = Finset.range pts.length := by ext; simp
  simp only [List.drop_zero, hico0] at h0
  rw [h0]
  change (1 : GF16) * _ = _
  exact one_mul _

private theorem lagrangeInterpolateComplete_spec (template : Poly) (pts : List Pt) (i : Nat)
    (hi : i < pts.length)
    (htlen : template.coefficients.length = pts.length + 1)
    (htpoly : polyOf template.coefficients = ∏ m ∈ Finset.range pts.length, (X - C (pts.getD m default).x))
    (hnodup : (pts.map Pt.x).Nodup) :
    ∃ working, template.lagrangeInterpolateComplete pts i = .ok working ∧
      working.coefficients.length = pts.length + 1 ∧
      (∀ k, k < pts.length →
        (polyOf (working.coefficients.drop 1)).eval (pts.getD k default).x =
          if k = i then (pts.getD i default).y else 0) := by
  unfold Poly.lagrangeInterpolateComplete
  have hgi : pts[i]? = some (pts.getD i default) := by
    rw [List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  have hnle1 : ¬(template.coefficients.length ≤ 1) := by omega
  simp only [hgi, hnle1, ↓reduceIte]
  set pix := (pts.getD i default).x
  set denom := Poly.lagrangeDenominator pix pts
  set scale := GF16.div (pts.getD i default).y denom
  obtain ⟨c', hok, hc'_len, hphi⟩ :=
    lagrangeCompleteDivLoop_spec pix scale (pts.length + 1) pts.length 1 template.coefficients
      htlen (by omega) (by omega)
  rw [show template.coefficients.length = pts.length + 1 from htlen]
  simp only [Nat.add_sub_cancel, hok]
  refine ⟨{ coefficients := c' }, rfl, hc'_len, ?_⟩
  have hphi_rhs : completePhi pix scale (pts.length + 1) (pts.length + 1 - 1) template.coefficients =
      C scale * polyOf template.coefficients := by
    unfold completePhi polyOf
    simp only [Nat.add_sub_cancel, htlen, Finset.Ico_self, Finset.sum_empty, mul_zero, add_zero]
  have hphi_lhs : completePhi pix scale (pts.length + 1) 0 c' =
      C (scale * c'.getD 0 GF16.ZERO) + (X - C pix) * polyOf (c'.drop 1) := by
    unfold completePhi polyOf
    simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, ← map_mul]
    congr 2
    have hdrop_len : (c'.drop 1).length = pts.length := by simp [hc'_len]
    rw [hdrop_len]
    have hico_sum : ∀ (n : Nat),
        (∑ k ∈ Finset.Ico 1 (n + 1), C (c'.getD k GF16.ZERO) * X ^ (k - 1)) =
        ∑ m ∈ Finset.range n, C ((c'.drop 1).getD m GF16.ZERO) * X ^ m := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hins : Finset.Ico 1 (n + 1 + 1) = insert (n + 1) (Finset.Ico 1 (n + 1)) := by
          ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
        rw [hins, Finset.sum_insert (by simp), Finset.sum_range_succ, ih, add_comm]
        simp only [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm 1 n]
    exact hico_sum pts.length
  rw [hphi_lhs, hphi_rhs, htpoly] at hphi
  have hc0_zero : scale * c'.getD 0 GF16.ZERO = 0 := by
    have hev := congrArg (Polynomial.eval pix) hphi
    have hev_prod : (∏ m ∈ Finset.range pts.length, (X - C (pts.getD m default).x)).eval pix = 0 := by
      rw [← Finset.mul_prod_erase (Finset.range pts.length) _ (Finset.mem_range.mpr hi)]
      simp only [eval_mul, eval_sub, eval_X, eval_C, pix, sub_self, zero_mul]
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero,
      hev_prod, mul_zero] at hev
    exact hev
  rw [hc0_zero, map_zero, zero_add] at hphi
  have hfact : C scale * ∏ m ∈ Finset.range pts.length, (X - C (pts.getD m default).x) =
      (X - C pix) * (C scale * ∏ m ∈ (Finset.range pts.length).erase i, (X - C (pts.getD m default).x)) := by
    rw [← Finset.mul_prod_erase (Finset.range pts.length) _ (Finset.mem_range.mpr hi)]
    ring
  rw [hfact] at hphi
  have hdrop_poly : polyOf (c'.drop 1) =
      C scale * ∏ m ∈ (Finset.range pts.length).erase i, (X - C (pts.getD m default).x) :=
    mul_left_cancel₀ (X_sub_C_ne_zero pix) hphi
  intro k hk
  rw [hdrop_poly, eval_mul, eval_C, Polynomial.eval_prod]
  by_cases hki : k = i
  · subst hki
    simp only [↓reduceIte]
    have hdenom_eq : denom =
        ∏ m ∈ (Finset.range pts.length).erase k, (pix - (pts.getD m default).x) :=
      lagrangeDenominator_eq_prod pts k hi hnodup
    have hprod_eq : (∏ x ∈ (Finset.range pts.length).erase k,
        (X - C (pts.getD x default).x).eval pix) = denom := by
      rw [hdenom_eq]
      apply Finset.prod_congr rfl
      intro m _
      simp only [eval_sub, eval_X, eval_C]
    rw [hprod_eq]
    have hdenom_ne : denom ≠ 0 := by
      rw [hdenom_eq]
      apply Finset.prod_ne_zero_iff.mpr
      intro m hm
      obtain ⟨hm_ne, hm_lt⟩ := Finset.mem_erase.mp hm
      rw [Finset.mem_range] at hm_lt
      rw [sub_ne_zero]
      intro heq
      have hnodup_idx := List.nodup_iff_injective_getElem.mp hnodup
      have hk' : k < (pts.map Pt.x).length := by simp [hi]
      have hm' : m < (pts.map Pt.x).length := by simp [hm_lt]
      have heq' : (pts.map Pt.x)[k] = (pts.map Pt.x)[m] := by
        simp only [List.getElem_map]
        have h1 : pts[k] = pts.getD k default := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
        have h2 : pts[m] = pts.getD m default := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm_lt]; rfl
        rw [h1, h2]
        exact heq
      exact hm_ne ((@hnodup_idx ⟨k, hk'⟩ ⟨m, hm'⟩ heq' |> Fin.ext_iff.mp).symm)
    change ((pts.getD k default).y / denom) * denom = (pts.getD k default).y
    exact div_mul_cancel₀ _ hdenom_ne
  · simp only [hki, ↓reduceIte]
    have hmem : k ∈ (Finset.range pts.length).erase i :=
      Finset.mem_erase.mpr ⟨hki, Finset.mem_range.mpr hk⟩
    rw [← Finset.mul_prod_erase _ _ hmem]
    simp only [eval_sub, eval_X, eval_C, sub_self, zero_mul, mul_zero]

private theorem lagrangeInterpolatePt_spec (pts : List Pt) (i : Nat)
    (hbound : pts.length ≤ 2 ^ 20) (hi : i < pts.length) (hnodup : (pts.map Pt.x).Nodup) :
    ∃ p, Poly.lagrangeInterpolatePt pts i = .ok p ∧
      p.coefficients.length = pts.length ∧
      (∀ k, k < pts.length →
        (polyOf p.coefficients).eval (pts.getD k default).x =
          if k = i then (pts.getD i default).y else 0) := by
  unfold Poly.lagrangeInterpolatePt
  obtain ⟨template, hprep, htlen, htpoly⟩ := lagrangeInterpolatePrepare_spec pts hbound
  obtain ⟨working, hcomp, hwlen, hweval⟩ :=
    lagrangeInterpolateComplete_spec template pts i hi htlen htpoly hnodup
  simp only [hprep, bind, Except.bind, hcomp]
  cases hw : working.coefficients with
  | nil => simp [hw] at hwlen
  | cons w0 rest =>
    have hdrop : working.coefficients.drop 1 = rest := by simp [hw]
    rw [hdrop] at hweval
    refine ⟨{ coefficients := rest }, rfl, by simp [hw] at hwlen; omega, hweval⟩

private theorem lagrangeAccumulateCoeffs_spec :
    ∀ (rem j : Nat) (out w : List GF16),
      j + rem = out.length →
      out.length + 1 = w.length →
      out.length ≤ 2 ^ 20 →
      ∃ out', Poly.lagrangeAccumulateCoeffs j rem out w = .ok out' ∧
        out'.length = out.length ∧
        (∀ k, k < out.length →
          out'.getD k GF16.ZERO =
            if j ≤ k then out.getD k GF16.ZERO + (w.drop 1).getD k GF16.ZERO
            else out.getD k GF16.ZERO)
  | 0, j, out, w, hj, _, _ => by
    refine ⟨out, rfl, rfl, ?_⟩
    intro k hk
    have : ¬(j ≤ k) := by omega
    simp [this]
  | rem + 1, j, out, w, hj, hlen, hbound => by
    have husize : ¬(j + 1 > USIZE_MAX) := by unfold USIZE_MAX; omega
    have hj_lt : j < out.length := by omega
    have hj1_lt : j + 1 < w.length := by omega
    have hgo : out[j]? = some (out.getD j GF16.ZERO) := by
      rw [List.getElem?_eq_getElem hj_lt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_lt]; rfl
    have hgw : w[j + 1]? = some ((w.drop 1).getD j GF16.ZERO) := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm 1 j]
      rw [List.getElem?_eq_getElem hj1_lt]
      rfl
    simp only [Poly.lagrangeAccumulateCoeffs, husize, ↓reduceIte, hgo, hgw]
    set out1 := out.set j (GF16.add (out.getD j GF16.ZERO) ((w.drop 1).getD j GF16.ZERO))
    obtain ⟨out', hok, hlen', hget'⟩ :=
      lagrangeAccumulateCoeffs_spec rem (j + 1) out1 w (by simp [out1]; omega)
        (by simp [out1]; omega) (by simp [out1]; omega)
    refine ⟨out', hok, by simp [out1] at hlen'; exact hlen', ?_⟩
    intro k hk
    rw [hget' k (by simp [out1]; exact hk)]
    by_cases hjk : k = j
    · subst hjk
      have hn : ¬(k + 1 ≤ k) := by omega
      simp only [hn, le_refl, ↓reduceIte, out1, List.getD_eq_getElem?_getD, List.getElem?_set_self hj_lt]
      rfl
    · by_cases hlt : j + 1 ≤ k
      · have hle : j ≤ k := by omega
        simp only [hlt, hle, ↓reduceIte, out1, List.getD_eq_getElem?_getD,
          List.getElem?_set_ne (Ne.symm hjk)]
      · have hnle : ¬(j ≤ k) := by omega
        simp only [hlt, hnle, ↓reduceIte, out1, List.getD_eq_getElem?_getD,
          List.getElem?_set_ne (Ne.symm hjk)]

private theorem lagrangeInterpolateLoop_spec (template : Poly) (pts : List Pt)
    (hbound : pts.length ≤ 2 ^ 20)
    (htlen : template.coefficients.length = pts.length + 1)
    (htpoly : polyOf template.coefficients = ∏ m ∈ Finset.range pts.length, (X - C (pts.getD m default).x))
    (hnodup : (pts.map Pt.x).Nodup) :
    ∀ (rem i : Nat) (out : List GF16),
      i + rem = pts.length →
      out.length = pts.length →
      ∃ out', Poly.lagrangeInterpolateLoop template pts i rem out = .ok out' ∧
        out'.length = pts.length ∧
        (∀ k, k < pts.length →
          (polyOf out').eval (pts.getD k default).x =
            (polyOf out).eval (pts.getD k default).x +
              if i ≤ k then (pts.getD k default).y else 0)
  | 0, i, out, hi, hlen => by
    refine ⟨out, rfl, hlen, ?_⟩
    intro k hk
    have : ¬(i ≤ k) := by omega
    simp only [this, ↓reduceIte, add_zero]
  | rem + 1, i, out, hi, hlen => by
    unfold Poly.lagrangeInterpolateLoop
    have hi_lt : i < pts.length := by omega
    obtain ⟨w, hw, hwlen, hweval⟩ :=
      lagrangeInterpolateComplete_spec template pts i hi_lt htlen htpoly hnodup
    obtain ⟨out1, hout1, hout1_len, hout1_get⟩ :=
      lagrangeAccumulateCoeffs_spec out.length 0 out w.coefficients
        (by omega) (by omega) (by omega)
    simp only [hw, bind, Except.bind, hout1]
    have hout1_poly : polyOf out1 = polyOf out + polyOf (w.coefficients.drop 1) := by
      unfold polyOf
      have hwdrop_len : (w.coefficients.drop 1).length = out.length := by simp [hwlen, hlen]
      rw [hout1_len, hwdrop_len, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hout1_get k (Finset.mem_range.mp hk)]
      simp only [Nat.zero_le, ↓reduceIte, map_add]
      ring
    obtain ⟨out', hout', hout'_len, hout'_eval⟩ :=
      lagrangeInterpolateLoop_spec template pts hbound htlen htpoly hnodup rem (i + 1) out1
        (by omega) (by omega)
    refine ⟨out', hout', hout'_len, ?_⟩
    intro k hk
    rw [hout'_eval k hk, hout1_poly, eval_add, hweval k hk]
    by_cases hki : k = i
    · subst hki
      have hn : ¬(k + 1 ≤ k) := by omega
      simp only [↓reduceIte, hn, le_refl]
      ring
    · by_cases hle : i + 1 ≤ k
      · have hle' : i ≤ k := by omega
        simp only [hki, hle, hle', ↓reduceIte]
        ring
      · have hnle : ¬(i ≤ k) := by omega
        simp only [hki, hle, hnle, ↓reduceIte]
        ring

private theorem lagrangeInterpolate_spec (pts : List Pt)
    (hbound : pts.length ≤ 2 ^ 20) (hnodup : (pts.map Pt.x).Nodup) :
    ∃ p, Poly.lagrangeInterpolate pts = .ok p ∧
      p.coefficients.length = pts.length ∧
      (∀ k, k < pts.length → (polyOf p.coefficients).eval (pts.getD k default).x = (pts.getD k default).y) := by
  unfold Poly.lagrangeInterpolate
  cases hpts : pts with
  | nil =>
    exact ⟨{ coefficients := [] }, rfl, rfl, fun _ hk => by simp at hk⟩
  | cons pt0 restPts =>
    rw [← hpts]
    have hne : pts.isEmpty = false := by simp [hpts]
    have hpos : 0 < pts.length := by simp [hpts]
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨template, hprep, htlen, htpoly⟩ := lagrangeInterpolatePrepare_spec pts hbound
    obtain ⟨w0, hw0, hw0_len, hw0_eval⟩ :=
      lagrangeInterpolateComplete_spec template pts 0 hpos htlen htpoly hnodup
    simp only [hprep, bind, Except.bind, hw0]
    cases hwc : w0.coefficients with
    | nil => simp [hwc] at hw0_len
    | cons head0 rest0 =>
      have hdrop0 : w0.coefficients.drop 1 = rest0 := by simp [hwc]
      have hrest0_len : rest0.length = pts.length := by simp [hwc] at hw0_len; omega
      obtain ⟨outCoeffs, hloop, hout_len, hout_eval⟩ :=
        lagrangeInterpolateLoop_spec template pts hbound htlen htpoly hnodup
          (pts.length - 1) 1 rest0 (by omega) hrest0_len
      simp only [hloop]
      refine ⟨{ coefficients := outCoeffs }, rfl, hout_len, ?_⟩
      intro k hk
      rw [hout_eval k hk, ← hdrop0, hw0_eval k hk]
      by_cases hk0 : k = 0
      · subst hk0
        have hn : ¬(1 ≤ 0) := by omega
        simp only [hn, ↓reduceIte, add_zero]
      · have hle : 1 ≤ k := by omega
        simp only [hk0, hle, ↓reduceIte, zero_add]

/-! ### `PolyConst` and `Poly.fromCompletePoints` -/

private theorem nodup_pt_x_ne {pts : List Pt} (hnodup : (pts.map Pt.x).Nodup)
    {i j : Nat} (hi : i < pts.length) (hj : j < pts.length) (hne : i ≠ j) :
    (pts.getD i default).x ≠ (pts.getD j default).x := by
  intro heq
  have hinj := List.nodup_iff_injective_getElem.mp hnodup
  have hi' : i < (pts.map Pt.x).length := by simp [hi]
  have hj' : j < (pts.map Pt.x).length := by simp [hj]
  have heq' : (pts.map Pt.x)[i] = (pts.map Pt.x)[j] := by
    simp only [List.getElem_map]
    rw [show pts[i] = pts.getD i default by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl]
    rw [show pts[j] = pts.getD j default by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl]
    exact heq
  exact hne (Fin.ext_iff.mp (@hinj ⟨i, hi'⟩ ⟨j, hj'⟩ heq'))

private theorem polyOf_zip_sub :
    ∀ (xs ys : List GF16), xs.length = ys.length →
      polyOf ((xs.zip ys).map fun (a, b) => GF16.constSub a b) = polyOf xs - polyOf ys
  | [], [], _ => by simp only [List.zip_nil_left, List.map_nil, polyOf_nil, sub_self]
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.zip_cons_cons, List.map_cons, polyOf_cons]
    rw [polyOf_zip_sub xs ys (Nat.succ.inj h), constSub_eq, map_sub]
    ring

private theorem polyConst_multXdiff_spec {n : Nat} (p : PolyConst n) (d : GF16) (deg : Nat)
    (hlen : p.coefficients.length = n) (hdeg : deg + 1 ≤ n)
    (hzero : ∀ k, deg ≤ k → p.coefficients.getD k GF16.ZERO = 0) :
    ∃ p', p.multXdiff d = .ok p' ∧ p'.coefficients.length = n ∧
      (∀ k, deg + 1 ≤ k → p'.coefficients.getD k GF16.ZERO = 0) ∧
      polyOf p'.coefficients = (X - C d) * polyOf p.coefficients := by
  unfold PolyConst.multXdiff
  have hn0 : (n == 0) = false := beq_false_of_ne (by omega : n ≠ 0)
  have htop_lt : n - 1 < p.coefficients.length := by omega
  have htop_zero : p.coefficients.getD (n - 1) GF16.ZERO = GF16.ZERO := hzero (n - 1) (by omega)
  have htop_get : p.coefficients[n - 1]? = some GF16.ZERO := by
    rw [List.getElem?_eq_getElem htop_lt, ← htop_zero, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem htop_lt]
    rfl
  simp only [hn0, Bool.false_eq_true, ↓reduceIte, htop_get, bne_self_eq_false]
  set cs := p.coefficients
  set xp : List GF16 := GF16.ZERO :: cs.take (n - 1)
  set dp : List GF16 := cs.map (fun c => GF16.constMul c d)
  set out : List GF16 := (xp.zip dp).map (fun (a, b) => GF16.constSub a b)
  have hxp_len : xp.length = n := by simp [xp, hlen]; omega
  have hdp_len : dp.length = n := by simp [dp, hlen]
  have hout_len : out.length = n := by simp [out, hxp_len, hdp_len]
  refine ⟨{ coefficients := out }, rfl, hout_len, ?_, ?_⟩
  · intro k hk
    dsimp only
    by_cases hkn : k < n
    · have hk_lt_cs : k < cs.length := by omega
      have hxp_k : xp[k]? = some 0 := by
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨m, rfl⟩
        simp only [xp, List.getElem?_cons_succ, List.getElem?_take, show m < n - 1 by omega, ↓reduceIte]
        rw [List.getElem?_eq_getElem (by omega : m < cs.length)]
        have hz := hzero m (by omega)
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at hz
        exact congrArg some hz
      have hdp_k : dp[k]? = some 0 := by
        simp only [dp, List.getElem?_map]
        rw [List.getElem?_eq_getElem hk_lt_cs]
        have hz := hzero k (by omega)
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt_cs] at hz
        simp only [Option.map_some, constMul_eq, show cs[k] = 0 from hz, zero_mul]
      have hout_k : out[k]? = some 0 := by
        simp only [out, List.getElem?_map]
        rw [show (xp.zip dp)[k]? = some ((0 : GF16), (0 : GF16)) by
          rw [List.getElem?_zip_eq_some]; exact ⟨hxp_k, hdp_k⟩]
        simp only [Option.map_some, constSub_eq, sub_self]
      rw [List.getD_eq_getElem?_getD, hout_k]; rfl
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  · rw [polyOf_zip_sub xp dp (by omega)]
    have hdrop : cs.drop (n - 1) = [GF16.ZERO] := by
      rw [List.drop_eq_getElem_cons htop_lt, List.drop_eq_nil_of_le (by omega)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htop_lt] at htop_zero
      exact congrArg (· :: []) htop_zero
    have hcs_eq : polyOf cs = polyOf (cs.take (n - 1)) := by
      conv => lhs; rw [← List.take_append_drop (n - 1) cs, hdrop, polyOf_append, polyOf_cons, polyOf_nil]
      change polyOf (cs.take (n - 1)) + X ^ (cs.take (n - 1)).length * (C (0 : GF16) + X * 0) = _
      simp only [map_zero, mul_zero, add_zero]
    have hxp_poly : polyOf xp = X * polyOf cs := by
      simp only [xp, polyOf_cons, ← hcs_eq]
      change C (0 : GF16) + X * polyOf cs = X * polyOf cs
      simp only [map_zero, zero_add]
    have hdp_poly : polyOf dp = C d * polyOf cs := by
      have : dp = cs.map (fun c => d * c) := List.map_congr_left (fun c _ => mul_comm c d)
      rw [this, polyOf_map_mul]
    rw [hxp_poly, hdp_poly]; ring

private theorem polyConst_lagrangeInterpolatePtLoop_spec (n : Nat) (pts : List Pt) (i : Nat)
    (hpts : pts.length = n) (hi : i < n) (hnodup : (pts.map Pt.x).Nodup) :
    let pix := (pts.getD i default).x
    ∀ (rem j : Nat) (p : PolyConst n) (denom : GF16),
      j + rem = n → p.coefficients.length = n →
      (∀ k, ((Finset.range j).erase i).card + 1 ≤ k → p.coefficients.getD k GF16.ZERO = 0) →
      polyOf p.coefficients = ∏ m ∈ (Finset.range j).erase i, (X - C (pts.getD m default).x) →
      denom = ∏ m ∈ (Finset.range j).erase i, (pix - (pts.getD m default).x) →
      ∃ p' denom', PolyConst.lagrangeInterpolatePtLoop n pts pix j rem p denom = .ok (p', denom') ∧
        p'.coefficients.length = n ∧
        polyOf p'.coefficients = ∏ m ∈ (Finset.range n).erase i, (X - C (pts.getD m default).x) ∧
        denom' = ∏ m ∈ (Finset.range n).erase i, (pix - (pts.getD m default).x) := by
  intro pix rem
  induction rem with
  | zero =>
    intro j p denom hj hlen _ hp hd
    have hjeq : j = n := by omega
    subst hjeq
    exact ⟨p, denom, rfl, hlen, hp, hd⟩
  | succ rem ih =>
    intro j p denom hj hlen hzero hp hd
    have hj_lt : j < pts.length := by omega
    have hgj : pts[j]? = some (pts.getD j default) := by
      rw [List.getElem?_eq_getElem hj_lt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_lt]; rfl
    simp only [PolyConst.lagrangeInterpolatePtLoop, hgj]
    by_cases hji : j = i
    · subst hji
      have hbeq : (pix == (pts.getD j default).x) = true := beq_self_eq_true _
      have herase : (Finset.range (j + 1)).erase j = (Finset.range j).erase j := by
        ext m; simp only [Finset.mem_erase, Finset.mem_range]; omega
      simp only [hbeq, ↓reduceIte]
      exact ih (j + 1) p denom (by omega) hlen (by rw [herase]; exact hzero)
        (by rw [herase]; exact hp) (by rw [herase]; exact hd)
    · have hne : pix ≠ (pts.getD j default).x :=
        nodup_pt_x_ne hnodup (by omega) hj_lt (Ne.symm hji)
      have hbeq : (pix == (pts.getD j default).x) = false := beq_false_of_ne hne
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      have hcard_lt : (((Finset.range j).erase i).card + 1) + 1 ≤ n := by
        by_cases hij : i < j
        · rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hij), Finset.card_range]; omega
        · rw [Finset.erase_eq_of_notMem (by simp; omega), Finset.card_range]; omega
      obtain ⟨p1, hp1, hp1_len, hp1_zero, hp1_poly⟩ :=
        polyConst_multXdiff_spec p (pts.getD j default).x (((Finset.range j).erase i).card + 1)
          hlen hcard_lt hzero
      simp only [hp1, bind, Except.bind]
      have herase : (Finset.range (j + 1)).erase i = insert j ((Finset.range j).erase i) := by
        ext m; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_insert]; omega
      have hj_notmem : j ∉ (Finset.range j).erase i := by simp
      exact ih (j + 1) p1 (GF16.constMul denom (GF16.constSub pix (pts.getD j default).x))
        (by omega) hp1_len
        (by rw [herase, Finset.card_insert_of_notMem hj_notmem]; exact hp1_zero)
        (by rw [herase, Finset.prod_insert hj_notmem, hp1_poly, hp])
        (by rw [herase, Finset.prod_insert hj_notmem, constMul_eq, constSub_eq, hd, mul_comm])

private theorem polyConst_lagrangeInterpolatePt_spec (n : Nat) (pts : List Pt) (i : Nat)
    (hn1 : 1 ≤ n) (hpts : pts.length = n) (hi : i < n) (hnodup : (pts.map Pt.x).Nodup) :
    ∃ pc, PolyConst.lagrangeInterpolatePt n pts i = .ok pc ∧
      pc.coefficients.length = n ∧
      (∀ k, k < n → (polyOf pc.coefficients).eval (pts.getD k default).x =
        if k = i then (pts.getD i default).y else 0) := by
  unfold PolyConst.lagrangeInterpolatePt
  have hi_lt : i < pts.length := by omega
  have hgi : pts[i]? = some (pts.getD i default) := by
    rw [List.getElem?_eq_getElem hi_lt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_lt]; rfl
  have hn0 : (n == 0) = false := beq_false_of_ne (by omega : n ≠ 0)
  simp only [hgi, hn0, Bool.false_eq_true, ↓reduceIte]
  set p0 : PolyConst n := { coefficients := GF16.ONE :: List.replicate (n - 1) GF16.ZERO }
  have hp0_len : p0.coefficients.length = n := by simp [p0]; omega
  have hp0_zero : ∀ k, ((Finset.range 0).erase i).card + 1 ≤ k → p0.coefficients.getD k GF16.ZERO = 0 := by
    intro k hk
    rcases Nat.exists_eq_succ_of_ne_zero (by simp at hk; omega : k ≠ 0) with ⟨m, rfl⟩
    simp only [p0, List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
    by_cases hmn : m < n - 1
    · rw [List.getElem?_replicate_of_lt hmn]; rfl
    · rw [List.getElem?_eq_none (by simp; omega)]; rfl
  have hp0_poly : polyOf p0.coefficients = ∏ m ∈ (Finset.range 0).erase i, (X - C (pts.getD m default).x) := by
    simp only [p0, polyOf_cons, polyOf_replicate_zero, Finset.range_zero, Finset.erase_empty, Finset.prod_empty]
    change C (1 : GF16) + X * 0 = 1
    simp only [map_one, mul_zero, add_zero]
  obtain ⟨p, denom, hloop, hp_len, hp_poly, hdenom⟩ :=
    polyConst_lagrangeInterpolatePtLoop_spec n pts i hpts hi hnodup n 0 p0 GF16.ONE
      (by omega) hp0_len hp0_zero hp0_poly (by simp)
  simp only [hloop, bind, Except.bind, pure, Except.pure]
  set scale := GF16.constDiv (pts.getD i default).y denom
  refine ⟨p.mult scale, rfl, by simp [PolyConst.mult, hp_len], ?_⟩
  have hmult_poly : polyOf (p.mult scale).coefficients = C scale * polyOf p.coefficients := by
    simp only [PolyConst.mult]
    have : p.coefficients.map (fun c => GF16.constMul c scale) = p.coefficients.map (fun c => scale * c) :=
      List.map_congr_left (fun c _ => mul_comm c scale)
    rw [this, polyOf_map_mul]
  intro k hk
  rw [hmult_poly, hp_poly, eval_mul, eval_C, Polynomial.eval_prod]
  by_cases hki : k = i
  · subst hki
    simp only [↓reduceIte]
    have hprod_eq : (∏ m ∈ (Finset.range n).erase k,
        (X - C (pts.getD m default).x).eval (pts.getD k default).x) = denom := by
      rw [hdenom]; apply Finset.prod_congr rfl; intro m _; simp only [eval_sub, eval_X, eval_C]
    rw [hprod_eq]
    have hdenom_ne : denom ≠ 0 := by
      rw [hdenom]; apply Finset.prod_ne_zero_iff.mpr; intro m hm
      obtain ⟨hm_ne, hm_lt⟩ := Finset.mem_erase.mp hm
      exact sub_ne_zero.mpr (nodup_pt_x_ne hnodup hi_lt (by rw [hpts]; exact Finset.mem_range.mp hm_lt) (Ne.symm hm_ne))
    have hscale_eq : scale = (pts.getD k default).y / denom := constDiv_eq _ _
    rw [hscale_eq]
    exact div_mul_cancel₀ _ hdenom_ne
  · simp only [hki, ↓reduceIte]
    have hmem : k ∈ (Finset.range n).erase i := Finset.mem_erase.mpr ⟨hki, Finset.mem_range.mpr hk⟩
    rw [← Finset.mul_prod_erase _ _ hmem]
    simp only [eval_sub, eval_X, eval_C, sub_self, zero_mul, mul_zero]

private theorem list_mapM_loop_spec {α β : Type} (f : α → Except PolyPanic β) :
    ∀ (xs : List α) (acc : List β),
      (∀ a ∈ xs, ∃ b, f a = .ok b) →
      ∃ ys, List.mapM.loop f xs acc = .ok (acc.reverse ++ ys) ∧ ys.length = xs.length ∧
        ∀ i (hi : i < xs.length) (hy : i < ys.length), f xs[i] = .ok ys[i]
  | [], acc, _ => ⟨[], by simp [List.mapM.loop, pure, Except.pure], rfl, fun _ h _ => by simp at h⟩
  | x :: xs, acc, h => by
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys, hlen, hget⟩ :=
      list_mapM_loop_spec f xs (y :: acc) (fun a ha => h a (List.mem_cons_of_mem x ha))
    refine ⟨y :: ys, ?_, by simp [hlen], ?_⟩
    · simp only [List.mapM.loop, bind, Except.bind, hy]
      simpa [List.reverse_cons, List.append_assoc] using hys
    · intro i hi hyi
      rcases i with _ | i
      · exact hy
      · exact hget i (by simp at hi; omega) (by simp at hyi; omega)

private theorem list_mapM_spec {α β : Type} (f : α → Except PolyPanic β) (P : α → β → Prop)
    (xs : List α) (h : ∀ a ∈ xs, ∃ b, f a = .ok b ∧ P a b) :
    ∃ ys, xs.mapM f = .ok ys ∧ ys.length = xs.length ∧
      ∀ i (hi : i < xs.length) (hy : i < ys.length), P xs[i] ys[i] := by
  obtain ⟨ys, hys, hlen, hget⟩ := list_mapM_loop_spec f xs [] (fun a ha => let ⟨b, hb, _⟩ := h a ha; ⟨b, hb⟩)
  refine ⟨ys, by simpa [List.mapM] using hys, hlen, fun i hi hy => ?_⟩
  obtain ⟨b, hb, hpb⟩ := h xs[i] (List.getElem_mem hi)
  have heq : Except.ok ys[i] = Except.ok b := (hget i hi hy).symm.trans hb
  exact Except.ok.inj heq ▸ hpb

private def IsCompleteBasis (n : Nat) (polys : List Poly) : Prop :=
  polys.length = n ∧ ∀ i (hi : i < polys.length),
    polys[i].coefficients.length = n ∧
    ∀ k, k < n → (polyOf polys[i].coefficients).eval (idxPt k) = if k = i then 1 else 0

private theorem ones_nodup (n : Nat) (hn : n ≤ 2 ^ 16) :
    (((List.range n).map (fun i => ({ x := idxPt i, y := GF16.ONE } : Pt))).map Pt.x).Nodup := by
  have hmap : (((List.range n).map (fun i => ({ x := idxPt i, y := GF16.ONE } : Pt))).map Pt.x) =
      (List.range n).map idxPt := by simp [List.map_map, Function.comp_def]
  rw [hmap, List.nodup_map_iff_inj_on List.nodup_range]
  intro a ha b hb hab
  exact idxPt_injOn hn (by simpa using ha) (by simpa using hb) hab

private theorem constBasis_spec (n : Nat) (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ 16) :
    ∃ cps, lagrangePolysForCompletePoints n = .ok cps ∧ IsCompleteBasis n (constPolysToPolys cps) := by
  unfold lagrangePolysForCompletePoints
  set ones : List Pt := (List.range n).map (fun i => { x := idxPt i, y := GF16.ONE })
  have hones_len : ones.length = n := by simp [ones]
  have hones_get : ∀ k, k < n → ones.getD k default = { x := idxPt k, y := GF16.ONE } := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [ones, hk])]
    simp [ones]
  have hnodup : (ones.map Pt.x).Nodup := ones_nodup n hn
  obtain ⟨cps, hcps, hcps_len, hcps_spec⟩ :=
    list_mapM_spec (fun i => PolyConst.lagrangeInterpolatePt n ones i)
      (fun i pc => pc.coefficients.length = n ∧
        ∀ k, k < n → (polyOf pc.coefficients).eval (idxPt k) = if k = i then 1 else 0)
      (List.range n) (by
        intro i hi
        have hi_lt : i < n := List.mem_range.mp hi
        obtain ⟨pc, hpc, hlen, hev⟩ := polyConst_lagrangeInterpolatePt_spec n ones i hn1 hones_len hi_lt hnodup
        refine ⟨pc, hpc, hlen, fun k hk => ?_⟩
        have h := hev k hk
        rw [hones_get k hk, hones_get i hi_lt] at h
        exact h)
  refine ⟨cps, hcps, by simp [constPolysToPolys, hcps_len], ?_⟩
  intro i hi
  have hi_n : i < n := by simp [constPolysToPolys, hcps_len] at hi; exact hi
  have hi_cps : i < cps.length := by simp at hcps_len; omega
  have hspec := hcps_spec i (by simp [hi_n]) hi_cps
  simp only [List.getElem_range] at hspec
  simpa [constPolysToPolys, PolyConst.toPoly] using hspec

private theorem enumeratePts_spec :
    ∀ (ys : List GF16) (s : Nat),
      Poly.checkCompletePoints s (PolyEncoder.enumeratePts s ys) = true ∧
      (PolyEncoder.enumeratePts s ys).length = ys.length ∧
      (∀ k, k < ys.length →
        (PolyEncoder.enumeratePts s ys).getD k default = { x := idxPt (s + k), y := ys.getD k GF16.ZERO })
  | [], _ => ⟨rfl, rfl, fun _ h => by simp at h⟩
  | y :: ys, s => by
    obtain ⟨hchk, hlen, hget⟩ := enumeratePts_spec ys (s + 1)
    refine ⟨?_, by simp [PolyEncoder.enumeratePts, hlen], ?_⟩
    · simp only [PolyEncoder.enumeratePts, Poly.checkCompletePoints, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, hchk]
    · intro k hk
      rcases k with _ | k
      · simp [PolyEncoder.enumeratePts, idxPt]
      · simp only [PolyEncoder.enumeratePts, List.getD_cons_succ]
        rw [hget k (by simp at hk; omega)]
        congr 2; omega

private theorem length_addAssignCoeffs :
    ∀ (as bs : List GF16), (Poly.addAssignCoeffs as bs).length = max as.length bs.length
  | [], [] => rfl
  | _ :: _, [] => by simp [Poly.addAssignCoeffs]
  | [], _ :: _ => by simp [Poly.addAssignCoeffs]
  | _ :: as, _ :: bs => by
    simp only [Poly.addAssignCoeffs, List.length_cons, length_addAssignCoeffs as bs]
    omega

private theorem lagrangeSum_spec (ys : List GF16) (polys : List Poly) (hb : IsCompleteBasis ys.length polys) :
    (Poly.lagrangeSum (PolyEncoder.enumeratePts 0 ys) polys).coefficients.length = ys.length ∧
      ∀ k, k < ys.length →
        (polyOf (Poly.lagrangeSum (PolyEncoder.enumeratePts 0 ys) polys).coefficients).eval (idxPt k) =
          ys.getD k GF16.ZERO := by
  obtain ⟨_, hpts_len, hpts_get⟩ := enumeratePts_spec ys 0
  obtain ⟨hpolys_len, hpolys_spec⟩ := hb
  have haux : ∀ (m : Nat) (acc : Poly), m ≤ ys.length →
      acc.coefficients.length = (if m = 0 then 0 else ys.length) →
      let res := (((PolyEncoder.enumeratePts 0 ys).drop m).zip (polys.drop m)).foldl (fun out (pt, poly) =>
        out.addAssign (poly.multAssign pt.y)) acc
      res.coefficients.length = ys.length ∧
        ∀ k, k < ys.length → (polyOf res.coefficients).eval (idxPt k) =
          (polyOf acc.coefficients).eval (idxPt k) + if m ≤ k then ys.getD k GF16.ZERO else 0 := by
    intro m
    induction hrem : ys.length - m generalizing m with
    | zero =>
      intro acc hm hacclen
      have hmeq : m = ys.length := by omega
      subst hmeq
      have hdrop : (PolyEncoder.enumeratePts 0 ys).drop ys.length = [] := List.drop_eq_nil_of_le (by omega)
      simp only [hdrop, List.zip_nil_left, List.foldl_nil]
      refine ⟨by split at hacclen <;> omega, fun k hk => ?_⟩
      have : ¬(ys.length ≤ k) := by omega
      simp only [this, ↓reduceIte, add_zero]
    | succ r ih =>
      intro acc hm hacclen
      have hm_lt : m < ys.length := by omega
      have hm_pts : m < (PolyEncoder.enumeratePts 0 ys).length := by omega
      have hm_pol : m < polys.length := by omega
      have hd1 := List.drop_eq_getElem_cons hm_pts
      have hd2 := List.drop_eq_getElem_cons hm_pol
      simp only [hd1, hd2, List.zip_cons_cons, List.foldl_cons]
      have hpm_len : polys[m].coefficients.length = ys.length := (hpolys_spec m hm_pol).1
      have hpm_eval := (hpolys_spec m hm_pol).2
      set acc1 := acc.addAssign (polys[m].multAssign (PolyEncoder.enumeratePts 0 ys)[m].y)
      have hacc1_len : acc1.coefficients.length = (if m + 1 = 0 then 0 else ys.length) := by
        simp only [acc1, Poly.addAssign, Poly.multAssign, parallelMult_eq_map,
          length_addAssignCoeffs, List.length_map, hacclen, hpm_len, Nat.succ_ne_zero, ↓reduceIte]
        by_cases hm0 : m = 0 <;> simp [hm0]
      obtain ⟨hlen_res, heval_res⟩ := ih (m + 1) (by omega) acc1 (by omega) hacc1_len
      refine ⟨hlen_res, fun k hk => ?_⟩
      rw [heval_res k hk]
      have hptm : (PolyEncoder.enumeratePts 0 ys)[m] = { x := idxPt m, y := ys.getD m GF16.ZERO } := by
        have h := hpts_get m hm_lt
        rw [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm_pts] at h
        exact h
      have hacc1_poly : polyOf acc1.coefficients =
          polyOf acc.coefficients + C (ys.getD m GF16.ZERO) * polyOf polys[m].coefficients := by
        simp only [acc1, Poly.addAssign, Poly.multAssign, polyOf_addAssignCoeffs,
          parallelMult_eq_map, polyOf_map_mul, hptm]
      rw [hacc1_poly, eval_add, eval_mul, eval_C, hpm_eval k hk]
      by_cases hkm : k = m
      · subst hkm
        have hn : ¬(k + 1 ≤ k) := by omega
        simp only [↓reduceIte, hn, le_refl, mul_one, add_zero]
      · by_cases hle : m + 1 ≤ k
        · have hle' : m ≤ k := by omega
          simp only [hkm, hle, hle', ↓reduceIte, mul_zero, add_zero]
        · have hnle : ¬(m ≤ k) := by omega
          simp only [hkm, hle, hnle, ↓reduceIte, mul_zero, add_zero]
  unfold Poly.lagrangeSum
  have h0 := haux 0 (Poly.zero (PolyEncoder.enumeratePts 0 ys).length) (Nat.zero_le _) (by simp [Poly.zero])
  simp only [List.drop_zero] at h0
  refine ⟨h0.1, fun k hk => ?_⟩
  rw [h0.2 k hk]
  simp only [Poly.zero, polyOf_nil, eval_zero, Nat.zero_le, ↓reduceIte, zero_add]

private theorem fromCompletePoints_enumeratePts (ys : List GF16) (hn : ys.length ≤ 2 ^ 16) :
    ∃ p, Poly.fromCompletePoints (PolyEncoder.enumeratePts 0 ys) = .ok (.ok p) ∧
      p.coefficients.length = ys.length ∧
      ∀ k, k < ys.length →
        (polyOf p.coefficients).eval (idxPt k) = ys.getD k GF16.ZERO := by
  unfold Poly.fromCompletePoints
  obtain ⟨hchk, hpts_len, hpts_get⟩ := enumeratePts_spec ys 0
  simp only [hchk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hpts_len]
  have hconst : ∀ m, ys.length = m → 1 ≤ m → m ≤ 2 ^ 16 →
      ∃ p, ((do
        let cps ← lagrangePolysForCompletePoints m
        let polys ← pure (constPolysToPolys cps)
        pure (Except.ok (Poly.lagrangeSum (PolyEncoder.enumeratePts 0 ys) polys)) :
          Except PolyPanic (Except Unit Poly))) = .ok (.ok p) ∧
        p.coefficients.length = ys.length ∧
        ∀ k, k < ys.length → (polyOf p.coefficients).eval (idxPt k) = ys.getD k GF16.ZERO := by
    intro m hm hm1 hmn
    obtain ⟨cps, hcps, hb⟩ := constBasis_spec m hm1 hmn
    simp only [hcps, bind, Except.bind, pure, Except.pure]
    have hb' : IsCompleteBasis ys.length (constPolysToPolys cps) := hm ▸ hb
    have ⟨hlen, hev⟩ := lagrangeSum_spec ys (constPolysToPolys cps) hb'
    exact ⟨_, rfl, hlen, hev⟩
  by_cases h0 : ys.length = 0
  · simp only [h0, beq_self_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    have hb : IsCompleteBasis ys.length [] := ⟨h0.symm, fun _ h => by simp at h⟩
    have ⟨hlen, hev⟩ := lagrangeSum_spec ys [] hb
    exact ⟨_, rfl, h0 ▸ hlen, fun k hk => by omega⟩
  · simp only [beq_false_of_ne h0, Bool.false_eq_true, ↓reduceIte]
    by_cases h1 : ys.length = 1
    · simp only [h1, beq_self_eq_true, ↓reduceIte, COMPLETE_POINTS_POLYS_1]
      simpa [h1] using hconst 1 h1 (by omega) (by omega)
    · simp only [beq_false_of_ne h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : ys.length = 3
      · simp only [h3, beq_self_eq_true, ↓reduceIte, COMPLETE_POINTS_POLYS_3]
        simpa [h3] using hconst 3 h3 (by omega) (by omega)
      · simp only [beq_false_of_ne h3, Bool.false_eq_true, ↓reduceIte]
        by_cases h5 : ys.length = 5
        · simp only [h5, beq_self_eq_true, ↓reduceIte, COMPLETE_POINTS_POLYS_5]
          simpa [h5] using hconst 5 h5 (by omega) (by omega)
        · simp only [beq_false_of_ne h5, Bool.false_eq_true, ↓reduceIte]
          by_cases h30 : ys.length = 30
          · simp only [h30, beq_self_eq_true, ↓reduceIte, COMPLETE_POINTS_POLYS_30]
            simpa [h30] using hconst 30 h30 (by omega) (by omega)
          · simp only [beq_false_of_ne h30, Bool.false_eq_true, ↓reduceIte]
            by_cases h34 : ys.length = 34
            · simp only [h34, beq_self_eq_true, ↓reduceIte, COMPLETE_POINTS_POLYS_34]
              simpa [h34] using hconst 34 h34 (by omega) (by omega)
            · simp only [beq_false_of_ne h34, Bool.false_eq_true, ↓reduceIte]
              by_cases h36 : ys.length = 36
              · simp only [h36, beq_self_eq_true, ↓reduceIte, COMPLETE_POINTS_POLYS_36]
                simpa [h36] using hconst 36 h36 (by omega) (by omega)
              · simp only [beq_false_of_ne h36, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
                set ones := (PolyEncoder.enumeratePts 0 ys).map (fun pt => ({ x := pt.x, y := GF16.ONE } : Pt))
                have hones_eq : ones = (List.range ys.length).map (fun i => { x := idxPt i, y := GF16.ONE }) := by
                  apply List.ext_getElem (by simp [ones, hpts_len])
                  intro k hk1 _
                  simp only [ones, List.getElem_map, List.getElem_range]
                  have hk_ys : k < ys.length := by simp [ones, hpts_len] at hk1; exact hk1
                  have hk_pts : k < (PolyEncoder.enumeratePts 0 ys).length := by omega
                  have h := hpts_get k hk_ys
                  rw [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_pts] at h
                  simp only [Option.getD_some] at h
                  simp [h]
                have hones_get : ∀ k, k < ys.length → ones.getD k default = { x := idxPt k, y := GF16.ONE } := by
                  intro k hk
                  rw [hones_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hk])]
                  simp
                have hnodup : (ones.map Pt.x).Nodup := hones_eq ▸ ones_nodup ys.length hn
                have hones_len : ones.length = ys.length := by simp [hones_eq]
                obtain ⟨polys, hpol, hpol_len, hpol_spec⟩ :=
                  list_mapM_spec (fun i => Poly.lagrangeInterpolatePt ones i)
                    (fun i p => p.coefficients.length = ys.length ∧
                      ∀ k, k < ys.length → (polyOf p.coefficients).eval (idxPt k) = if k = i then 1 else 0)
                    (List.range ys.length) (by
                      intro i hi
                      have hi_lt : i < ys.length := List.mem_range.mp hi
                      obtain ⟨p, hp, hlen, hev⟩ :=
                        lagrangeInterpolatePt_spec ones i (by omega) (by omega) hnodup
                      refine ⟨p, hp, by omega, fun k hk => ?_⟩
                      have h := hev k (by omega)
                      rw [hones_get k hk, hones_get i hi_lt] at h
                      exact h)
                simp only [hpol]
                have hb : IsCompleteBasis ys.length polys := by
                  refine ⟨by simp at hpol_len; exact hpol_len, fun i hi => ?_⟩
                  have hi_lt : i < ys.length := by simp at hpol_len; omega
                  have hs := hpol_spec i (by simp [hi_lt]) hi
                  simpa using hs
                have ⟨hlen, hev⟩ := lagrangeSum_spec ys polys hb
                exact ⟨_, rfl, hlen, hev⟩

/-! ### Sender (`encodeBytes_spec`, `nextChunk_spec`, `runChunks_spec`) -/

private def encPts (msg : List (BitVec 8)) (i : Nat) : List Point :=
  (List.range 16).map fun j => ⟨(List.range (needed (2 * i) j)).map fun k => msgVal msg (16 * k + j)⟩

private theorem needed_step (i j : Nat) (hj : j < 16) :
    needed (2 * (i + 1)) j = if j = i % 16 then needed (2 * i) j + 1 else needed (2 * i) j := by
  unfold needed; by_cases h : j = i % 16 <;> simp only [h, ↓reduceIte] <;> split <;> split <;> omega

private theorem needed_self_mod (i : Nat) : needed (2 * i) (i % 16) = i / 16 := by
  unfold needed; split <;> omega

private theorem distributeMsgChunks_spec (msg : List (BitVec 8)) :
    ∀ (rem i : Nat), 2 * (i + rem) = msg.length →
      PolyEncoder.distributeMsgChunks i (msg.drop (2 * i)) (encPts msg i) = .ok (encPts msg (i + rem))
  | 0, i, hlen => by
    rw [List.drop_eq_nil_of_le (by omega), Nat.add_zero]; rfl
  | rem + 1, i, hlen => by
    have h0 : 2 * i < msg.length := by omega
    have h1 : 2 * i + 1 < msg.length := by omega
    rw [List.drop_eq_getElem_cons h0, List.drop_eq_getElem_cons h1]
    have hlen_pts : (encPts msg i).length = 16 := by simp [encPts]
    have hpoly_lt : i % 16 < (encPts msg i).length := by rw [hlen_pts]; omega
    have hget_poly : (encPts msg i)[i % 16]? = some ((encPts msg i)[i % 16]'hpoly_lt) :=
      List.getElem?_eq_getElem hpoly_lt
    simp only [PolyEncoder.distributeMsgChunks, hlen_pts, hget_poly]
    have hgf : GF16.new ((msg[2 * i].zeroExtend 16 <<< 8) + msg[2 * i + 1].zeroExtend 16) = msgVal msg i := by
      unfold msgVal
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
      rfl
    have hset : (encPts msg i).set (i % 16)
        { value := ((encPts msg i)[i % 16]'hpoly_lt).value ++ [msgVal msg i] } = encPts msg (i + 1) := by
      apply List.ext_getElem (by simp [encPts])
      intro j hj1 hj2
      have hj16 : j < 16 := by simp [encPts] at hj1; exact hj1
      by_cases hjeq : j = i % 16
      · subst hjeq
        simp only [List.getElem_set_self, encPts, List.getElem_map, List.getElem_range]
        rw [needed_step i (i % 16) (by omega)]
        simp only [↓reduceIte, List.range_succ, List.map_append, List.map_singleton]
        rw [needed_self_mod, show 16 * (i / 16) + i % 16 = i by omega]
      · rw [List.getElem_set_ne (by omega)]
        simp only [encPts, List.getElem_map, List.getElem_range, needed_step i j hj16, hjeq, ↓reduceIte]
    simp only [hgf, hset, show 2 * i + 1 + 1 = 2 * (i + 1) by omega]
    rw [show i + (rem + 1) = i + 1 + rem by omega]
    exact distributeMsgChunks_spec msg rem (i + 1) (by omega)

private theorem encodeBytes_spec (msg : List (BitVec 8)) (heven : msg.length % 2 = 0)
    (hlen : msg.length ≤ 2 ^ 20) :
    PolyEncoder.encodeBytes msg = .ok (.ok { idx := 0#32, s := .points (msgPoints msg) }) := by
  unfold PolyEncoder.encodeBytes PolyEncoder.encodeBytesBase
  have hev : (msg.length % 2 != 0) = false := by simp [heven]
  have hgt : ¬(msg.length > (1 <<< 16) * NUM_POLYS) := by unfold NUM_POLYS CHUNK_SIZE; omega
  simp only [hev, Bool.false_eq_true, ↓reduceIte, hgt]
  have hinit : (List.replicate NUM_POLYS ({ value := [] } : Point)) = encPts msg 0 := by
    apply List.ext_getElem (by simp [NUM_POLYS, CHUNK_SIZE, encPts])
    intro j _ _
    have hn0 : needed 0 j = 0 := by unfold needed; simp
    simp [encPts, hn0]
  rw [hinit]
  have hd := distributeMsgChunks_spec msg (msg.length / 2) 0 (by omega)
  simp only [Nat.mul_zero, List.drop_zero, Nat.zero_add] at hd
  have hend : encPts msg (msg.length / 2) = msgPoints msg := by
    unfold encPts msgPoints; rw [show 2 * (msg.length / 2) = msg.length by omega]
  simp only [hd, hend, bind, Except.bind, pure, Except.pure]

private theorem pointsToPolysLoop_spec (msg : List (BitVec 8)) (hlen : msg.length ≤ 2 ^ 20) :
    ∀ (rem i : Nat) (acc : List Poly),
      i + rem = 16 → acc.length = i →
      (∀ j (hj : j < acc.length),
        acc[j].coefficients.length = needed msg.length j ∧ polyOf acc[j].coefficients = msgPoly msg j) →
      ∃ polys, PolyEncoder.pointsToPolysLoop (msgPoints msg) i rem acc = .ok polys ∧
        polys.length = 16 ∧
        ∀ j (hj : j < polys.length),
          polys[j].coefficients.length = needed msg.length j ∧ polyOf polys[j].coefficients = msgPoly msg j
  | 0, i, acc, hi, hacc, hspec => ⟨acc, rfl, by omega, hspec⟩
  | rem + 1, i, acc, hi, hacc, hspec => by
    have hi16 : i < 16 := by omega
    have hmp_len : (msgPoints msg).length = 16 := by simp [msgPoints]
    have hgi : (msgPoints msg)[i]? = some ((msgPoints msg)[i]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have hys_eq : ((msgPoints msg)[i]'(by omega)).value =
        (List.range (needed msg.length i)).map (fun k => msgVal msg (16 * k + i)) := by
      simp [msgPoints]
    have hys_len : ((msgPoints msg)[i]'(by omega)).value.length = needed msg.length i := by simp [hys_eq]
    obtain ⟨p, hp, hp_len, hp_ev⟩ :=
      fromCompletePoints_enumeratePts ((msgPoints msg)[i]'(by omega)).value
        (hys_len ▸ needed_le_2pow16 hlen i)
    simp only [PolyEncoder.pointsToPolysLoop, hgi, hp, bind, Except.bind]
    have hp_poly : polyOf p.coefficients = msgPoly msg i := by
      apply Lagrange.eq_interpolate_of_eval_eq _ (idxPt_injOn (needed_le_2pow16 hlen i))
      · rw [Finset.card_range, ← hys_len, ← hp_len]; exact degree_polyOf_lt p.coefficients
      · intro k hk
        have hk_lt : k < needed msg.length i := Finset.mem_range.mp hk
        rw [hp_ev k (hys_len ▸ hk_lt), hys_eq, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by simp [hk_lt])]
        simp
    refine pointsToPolysLoop_spec msg hlen rem (i + 1) (acc ++ [p]) (by omega) (by simp [hacc]) ?_
    intro j hj
    by_cases hji : j < i
    · rw [List.getElem_append_left (by omega)]; exact hspec j (by omega)
    · have hjeq : j = i := by simp [hacc] at hj; omega
      subst hjeq
      have hlast : (acc ++ [p])[acc.length]'(by simp) = p := by simp
      simpa [hacc, hlast, hys_len] using And.intro hp_len hp_poly

private theorem pointAt_spec (msg : List (BitVec 8)) (hlen : msg.length ≤ 2 ^ 20)
    (e : PolyEncoder) (he : EncInv msg e) (poly polyIdx : Nat)
    (hpoly : poly < 16) (_hidx : polyIdx < 2 ^ 16) :
    ∃ e', e.pointAt poly polyIdx = .ok (e', (msgPoly msg poly).eval (idxPt polyIdx)) ∧
      e'.idx = e.idx ∧ EncInv msg e' := by
  unfold PolyEncoder.pointAt
  rcases he with hpts | ⟨polys, hpol, hpol_len, hpol_spec⟩
  · have hmp_len : (msgPoints msg).length = 16 := by simp [msgPoints]
    have hgp : (msgPoints msg)[poly]? = some ((msgPoints msg)[poly]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have hval_eq : ((msgPoints msg)[poly]'(by omega)).value =
        (List.range (needed msg.length poly)).map (fun k => msgVal msg (16 * k + poly)) := by
      simp [msgPoints]
    by_cases hlt : polyIdx < needed msg.length poly
    · have hgidx : ((msgPoints msg)[poly]'(by omega)).value[polyIdx]? =
          some (msgVal msg (16 * polyIdx + poly)) := by
        rw [hval_eq, List.getElem?_eq_getElem (by simp [hlt])]; simp
      simp only [hpts, hgp, hgidx, pure, Except.pure]
      exact ⟨e, by rw [eval_msgPoly_at_node hlen poly polyIdx hlt], rfl, Or.inl hpts⟩
    · have hgidx : ((msgPoints msg)[poly]'(by omega)).value[polyIdx]? = none :=
        List.getElem?_eq_none (by simp [hval_eq]; omega)
      obtain ⟨polys, hloop, hplen, hpspec⟩ :=
        pointsToPolysLoop_spec msg hlen 16 0 [] rfl rfl (fun _ h => by simp at h)
      have hgpol : polys[poly]? = some (polys[poly]'(by omega)) := List.getElem?_eq_getElem (by omega)
      have hcomp := computeAt_eq_eval (polys[poly]'(by omega)) (idxPt polyIdx)
      have hnum : NUM_POLYS = 16 := rfl
      simp only [hpts, hgp, hgidx, hnum, hloop, bind, Except.bind, pure, Except.pure,
        hgpol, idxPt] at hcomp ⊢
      rw [hcomp, (hpspec poly (by omega)).2]
      exact ⟨{ e with s := .polys polys }, rfl, rfl, Or.inr ⟨polys, rfl, hplen, hpspec⟩⟩
  · have hgpol : polys[poly]? = some (polys[poly]'(by omega)) := List.getElem?_eq_getElem (by omega)
    have hcomp := computeAt_eq_eval (polys[poly]'(by omega)) (idxPt polyIdx)
    simp only [hpol, bind, Except.bind, pure, Except.pure, hgpol, idxPt] at hcomp ⊢
    rw [hcomp, (hpol_spec poly (by omega)).2]
    exact ⟨e, rfl, rfl, Or.inr ⟨polys, hpol, hpol_len, hpol_spec⟩⟩

private theorem chunkAtLoop_spec (msg : List (BitVec 8)) (hlen : msg.length ≤ 2 ^ 20) (idx : BitVec 16) :
    ∀ (rem i : Nat) (e : PolyEncoder) (_hi : i + rem = 16), EncInv msg e →
      ∃ e' vec, PolyEncoder.chunkAtLoop idx i rem e = .ok (e', vec) ∧
        e'.idx = e.idx ∧ EncInv msg e' ∧
        ∀ k (hk : k < 2 * rem), vec.get ⟨k, hk⟩ = (chunkData msg idx).get ⟨2 * i + k, by omega⟩
  | 0, _, e, _, he => ⟨e, List.Vector.nil, rfl, rfl, he, fun _ hk => by omega⟩
  | rem + 1, i, e, hi, he => by
    have hi16 : i < 16 := by omega
    have hmod : (idx.toNat * 16 + i) % 16 = i := by omega
    have hdiv : (idx.toNat * 16 + i) / 16 = idx.toNat := by omega
    obtain ⟨e1, hp, he1_idx, he1⟩ := pointAt_spec msg hlen e he i idx.toNat hi16 idx.isLt
    obtain ⟨e2, tail, htail, he2_idx, he2, hvec⟩ := chunkAtLoop_spec msg hlen idx rem (i + 1) e1 (by omega) he1
    simp only [PolyEncoder.chunkAtLoop, hmod, hdiv, hp, bind, Except.bind, htail, pure, Except.pure]
    refine ⟨e2, _, rfl, he2_idx.trans he1_idx, he2, ?_⟩
    intro k hk
    rcases k with _ | _ | k
    · simp [chunkData, chunkVal, List.Vector.get_ofFn]
    · have hdiv2 : (2 * i + 1) / 2 = i := by omega
      have hmod2 : ¬((2 * i + 1) % 2 = 0) := by omega
      simp only [chunkData, chunkVal, List.Vector.get_ofFn, hdiv2, hmod2, ↓reduceIte]
      rfl
    · have ht := hvec k (by omega)
      change tail.get ⟨k, by omega⟩ = _
      rw [ht]; congr 1; ext; dsimp; omega

private theorem nextChunk_spec (msg : List (BitVec 8)) (hlen : msg.length ≤ 2 ^ 20)
    (e : PolyEncoder) (he : EncInv msg e) :
    ∃ e', e.nextChunk =
        .ok (e', { index := e.idx.setWidth 16, data := chunkData msg (e.idx.setWidth 16) }) ∧
      e'.idx = e.idx + 1#32 ∧ EncInv msg e' := by
  unfold PolyEncoder.nextChunk PolyEncoder.chunkAt
  obtain ⟨e1, vec, hloop, he1_idx, he1, hvec⟩ := chunkAtLoop_spec msg hlen (e.idx.setWidth 16) 16 0 e rfl he
  have hvec_eq : vec = chunkData msg (e.idx.setWidth 16) := by
    apply List.Vector.ext; intro ⟨k, hk⟩; simpa using hvec k hk
  simp only [hloop, hvec_eq, bind, Except.bind, pure, Except.pure]
  refine ⟨{ e1 with idx := e1.idx + 1#32 }, rfl, by rw [he1_idx], ?_⟩
  rcases he1 with hpts | ⟨polys, hpol, hplen, hpspec⟩
  · exact Or.inl hpts
  · exact Or.inr ⟨polys, hpol, hplen, hpspec⟩

/-! ### Receiver (`SortedSetPt`, `addChunk_spec`, `decodedMessage_spec`) and round-trip -/

private def SortedInv (xs : List Pt) : Prop :=
  (xs.map fun pt => pt.x.value.toNat).Pairwise (· < ·)

private theorem sortedInv_nodup_x {xs : List Pt} (hs : SortedInv xs) : (xs.map Pt.x).Nodup := by
  have h1 : ((xs.map Pt.x).map fun g => g.value.toNat).Nodup := by
    have heq : ((xs.map Pt.x).map fun g => g.value.toNat) = (xs.map fun pt => pt.x.value.toNat) := by
      simp [List.map_map, Function.comp_def]
    rw [heq]; exact List.Pairwise.imp ne_of_lt hs
  exact List.Nodup.of_map _ h1

private theorem gf16_eq_of_toNat_eq {a b : GF16} (h : a.value.toNat = b.value.toNat) : a = b := by
  cases a; cases b; exact congrArg GF16.mk (BitVec.eq_of_toNat_eq h)

private theorem pt_cmp_lt_iff {a b : Pt} : Pt.cmp a b = .lt ↔ a.x.value.toNat < b.x.value.toNat :=
  compare_lt_iff_lt

private theorem pt_cmp_eq_iff {a b : Pt} : Pt.cmp a b = .eq ↔ a.x = b.x := by
  rw [Pt.cmp, compare_eq_iff_eq]
  exact ⟨gf16_eq_of_toNat_eq, fun h => by rw [h]⟩

private theorem pt_cmp_gt_iff {a b : Pt} : Pt.cmp a b = .gt ↔ b.x.value.toNat < a.x.value.toNat :=
  compare_gt_iff_gt

private theorem binarySearchAux_shift (t : Pt) :
    ∀ (xs : List Pt) (idx : Nat),
      SortedSetPt.binarySearchAux t idx xs =
        match SortedSetPt.binarySearchAux t 0 xs with
        | .ok k => .ok (idx + k)
        | .error k => .error (idx + k)
  | [], idx => by simp [SortedSetPt.binarySearchAux]
  | pt :: rest, idx => by
    simp only [SortedSetPt.binarySearchAux]
    cases Pt.cmp pt t with
    | lt =>
      rw [binarySearchAux_shift t rest (idx + 1), binarySearchAux_shift t rest 1]
      cases SortedSetPt.binarySearchAux t 0 rest <;> simp [Nat.add_assoc]
    | eq => simp
    | gt => simp

private theorem binarySearch_spec (t : Pt) :
    ∀ (xs : List Pt), SortedInv xs →
      match SortedSetPt.binarySearchAux t 0 xs with
      | .ok k => ∃ (hk : k < xs.length), xs[k].x = t.x
      | .error ins => ins ≤ xs.length ∧
          (∀ p ∈ xs.take ins, p.x.value.toNat < t.x.value.toNat) ∧
          (∀ p ∈ xs.drop ins, t.x.value.toNat < p.x.value.toNat)
  | [], _ => ⟨Nat.zero_le _, by simp, by simp⟩
  | pt :: rest, hs => by
    have hcons := List.pairwise_cons.mp hs
    have hhd : ∀ q ∈ rest, pt.x.value.toNat < q.x.value.toNat := by
      intro q hq; exact hcons.1 _ (List.mem_map_of_mem hq)
    have htl : SortedInv rest := hcons.2
    simp only [SortedSetPt.binarySearchAux]
    cases hcmp : Pt.cmp pt t with
    | lt =>
      have hlt := pt_cmp_lt_iff.mp hcmp
      rw [binarySearchAux_shift t rest 1]
      have ih := binarySearch_spec t rest htl
      cases hres : SortedSetPt.binarySearchAux t 0 rest with
      | ok k =>
        rw [hres] at ih; obtain ⟨hk, hkx⟩ := ih
        exact ⟨by simp; omega, by simpa [Nat.add_comm 1 k] using hkx⟩
      | error ins =>
        rw [hres] at ih; obtain ⟨hins, htake, hdrop⟩ := ih
        refine ⟨by simp; omega, ?_, ?_⟩
        · intro p hp
          rw [Nat.add_comm 1 ins, List.take_succ_cons] at hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact hlt
          · exact htake p hp'
        · intro p hp
          rw [Nat.add_comm 1 ins, List.drop_succ_cons] at hp
          exact hdrop p hp
    | eq => exact ⟨by simp, pt_cmp_eq_iff.mp hcmp⟩
    | gt =>
      have hgt := pt_cmp_gt_iff.mp hcmp
      refine ⟨Nat.zero_le _, by simp, ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact hgt
      · exact Nat.lt_trans hgt (hhd p hp')

private theorem replace_spec (s : SortedSetPt) (e : Pt) (hs : SortedInv s.vec) :
    SortedInv (s.replace e).1.vec ∧ (∀ p ∈ (s.replace e).1.vec, p = e ∨ p ∈ s.vec) ∧
      s.vec.length ≤ (s.replace e).1.vec.length ∧
      ((∀ p ∈ s.vec, p.x ≠ e.x) → (s.replace e).1.vec.length = s.vec.length + 1) := by
  dsimp only [SortedSetPt.replace, SortedSetPt.binarySearch]
  have hbs := binarySearch_spec e s.vec hs
  cases hres : SortedSetPt.binarySearchAux e 0 s.vec with
  | ok k =>
    dsimp only
    rw [hres] at hbs; obtain ⟨hk, hkx⟩ := hbs
    have hmap_eq : ((s.vec.set k e).map fun p => p.x.value.toNat) =
        (s.vec.map fun p => p.x.value.toNat) := by
      apply List.ext_getElem (by simp)
      intro m hm1 hm2
      simp only [List.getElem_map]
      by_cases hmk : m = k
      · subst hmk; simp [hkx]
      · rw [List.getElem_set_ne (Ne.symm hmk)]
    refine ⟨by unfold SortedInv; rw [hmap_eq]; exact hs, ?_, by simp, ?_⟩
    · intro p hp; exact (List.mem_or_eq_of_mem_set hp).symm
    · intro hne; exact absurd hkx (hne s.vec[k] (List.getElem_mem hk))
  | error ins =>
    dsimp only
    rw [hres] at hbs; obtain ⟨hins, htake, hdrop⟩ := hbs
    have hsplit : s.vec.take ins ++ s.vec.drop ins = s.vec := List.take_append_drop ins s.vec
    have hpair_split := hs; rw [← hsplit] at hpair_split
    unfold SortedInv at hpair_split
    rw [List.map_append, List.pairwise_append] at hpair_split
    obtain ⟨hptake, hpdrop, _⟩ := hpair_split
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold SortedInv
      rw [List.map_append, List.map_cons, List.pairwise_append]
      refine ⟨hptake, List.pairwise_cons.mpr ⟨?_, hpdrop⟩, ?_⟩
      · intro b hb
        rcases List.mem_map.mp hb with ⟨q, hq, rfl⟩
        exact hdrop q hq
      · intro a ha b hb
        rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact htake p hp
        · rcases List.mem_map.mp hb' with ⟨q, hq, rfl⟩
          exact Nat.lt_trans (htake p hp) (hdrop q hq)
    · intro p hp
      rcases List.mem_append.mp hp with hp1 | hp2
      · exact Or.inr (List.mem_of_mem_take hp1)
      · rcases List.mem_cons.mp hp2 with rfl | hp3
        · exact Or.inl rfl
        · exact Or.inr (List.mem_of_mem_drop hp3)
    · simp; omega
    · intro _; simp; omega

private theorem push_spec (s : SortedSetPt) (e : Pt) (hs : SortedInv s.vec) :
    SortedInv (s.push e).1.vec ∧ (∀ p ∈ (s.push e).1.vec, p = e ∨ p ∈ s.vec) ∧
      s.vec.length ≤ (s.push e).1.vec.length ∧
      ((∀ p ∈ s.vec, p.x ≠ e.x) → (s.push e).1.vec.length = s.vec.length + 1) := by
  unfold SortedSetPt.push
  cases hlast : s.vec.getLast? with
  | none =>
    dsimp only
    have hnil : s.vec = [] := List.getLast?_eq_none_iff.mp hlast
    rw [hnil]
    exact ⟨by simp [SortedInv], fun p hp => Or.inl (by simpa using hp), by simp, fun _ => rfl⟩
  | some last =>
    dsimp only
    have hne : s.vec ≠ [] := fun h => by simp [h] at hlast
    have hlast_eq : last = s.vec.getLast hne := by
      rw [List.getLast?_eq_some_getLast hne] at hlast; exact (Option.some.inj hlast).symm
    have hlast_mem : last ∈ s.vec := hlast_eq ▸ List.getLast_mem hne
    have hdl : s.vec.dropLast ++ [last] = s.vec := hlast_eq ▸ List.dropLast_append_getLast hne
    have hs_dl := hs; rw [← hdl] at hs_dl; unfold SortedInv at hs_dl
    rw [List.map_append, List.map_singleton, List.pairwise_append] at hs_dl
    obtain ⟨hp_dl, _, hlt_last⟩ := hs_dl
    cases hcmp : Pt.cmp e last with
    | gt =>
      dsimp only
      have hgt := pt_cmp_gt_iff.mp hcmp
      refine ⟨?_, ?_, by simp, fun _ => by simp⟩
      · unfold SortedInv
        rw [List.map_append, List.map_singleton, List.pairwise_append]
        refine ⟨hs, by simp, fun a ha b hb => ?_⟩
        have hb_eq : b = e.x.value.toNat := by simpa using hb
        subst hb_eq
        rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
        rw [← hdl] at hp
        rcases List.mem_append.mp hp with hp1 | hp2
        · exact Nat.lt_trans (hlt_last _ (List.mem_map_of_mem hp1) _ (by simp)) hgt
        · have : p = last := by simpa using hp2
          subst this; exact hgt
      · intro p hp
        rcases List.mem_append.mp hp with hp1 | hp2
        · exact Or.inr hp1
        · exact Or.inl (by simpa using hp2)
    | eq =>
      dsimp only
      have heq := pt_cmp_eq_iff.mp hcmp
      have hmap_eq : ((s.vec.dropLast ++ [e]).map fun p => p.x.value.toNat) =
          (s.vec.map fun p => p.x.value.toNat) := by
        calc ((s.vec.dropLast ++ [e]).map fun p => p.x.value.toNat)
          _ = (s.vec.dropLast.map fun p => p.x.value.toNat) ++ [last.x.value.toNat] := by
                rw [List.map_append, List.map_singleton, heq]
          _ = ((s.vec.dropLast ++ [last]).map fun p => p.x.value.toNat) := by
                rw [List.map_append, List.map_singleton]
          _ = (s.vec.map fun p => p.x.value.toNat) := by rw [hdl]
      have hlen_eq : (s.vec.dropLast ++ [e]).length = s.vec.length := by
        have := congrArg List.length hdl; simp at this ⊢; omega
      refine ⟨by unfold SortedInv; rw [hmap_eq]; exact hs, ?_, by omega, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with hp1 | hp2
        · exact Or.inr (List.dropLast_subset _ hp1)
        · exact Or.inl (by simpa using hp2)
      · intro hne_all; exact absurd heq.symm (hne_all last hlast_mem)
    | lt =>
      dsimp only
      exact replace_spec s e hs

private theorem u16_reconstruct (v : BitVec 16) :
    (((v >>> 8).setWidth 8).zeroExtend 16 <<< 8) + (v.setWidth 8).zeroExtend 16 = v := by
  apply BitVec.eq_of_toNat_eq
  have hv := v.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  omega

private theorem u16ToBeBytes_msgVal (msg : List (BitVec 8)) (i : Nat) (hi : 2 * i + 1 < msg.length) :
    u16ToBeBytes (msgVal msg i).value = [msg[2 * i]'(by omega), msg[2 * i + 1]'hi] := by
  unfold u16ToBeBytes msgVal GF16.new
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : 2 * i < msg.length),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp only [Option.getD_some]
  set b0 := msg[2 * i]'(by omega)
  set b1 := msg[2 * i + 1]'hi
  have hb0 := b0.isLt
  have hb1 := b1.isLt
  congr 1
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_shiftLeft]
    omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_shiftLeft]
    omega

private theorem addChunkLoop_spec (msg : List (BitVec 8)) (c : Chunk)
    (hc : c.data = chunkData msg c.index) (S : Finset Nat) :
    ∀ (rem i : Nat) (dec : PolyDecoder), i + rem = 16 →
      dec.ptsNeeded = msg.length / 2 → dec.isComplete = false → dec.pts.length = 16 →
      (∀ j (hj : j < dec.pts.length), SortedInv dec.pts[j].vec) →
      (∀ j (hj : j < dec.pts.length), ∀ pt ∈ dec.pts[j].vec, pt.y = (msgPoly msg j).eval pt.x) →
      (∀ j (hj : j < dec.pts.length), ∀ pt ∈ dec.pts[j].vec,
        ∃ idx ∈ (if j < i then insert c.index.toNat S else S), idx < 2 ^ 16 ∧ pt.x = idxPt idx) →
      (∀ j (hj : j < dec.pts.length),
        min (if j < i then (insert c.index.toNat S).card else S.card) (needed msg.length j) ≤
          dec.pts[j].vec.length) →
      ∃ dec', PolyDecoder.addChunkLoop c i rem dec = .ok dec' ∧ DecInv msg (insert c.index.toNat S) dec'
  | 0, i, dec, hi, hpts, hcomp, hlen16, hsort, hon, hat, hen => by
    have hi16 : i = 16 := by omega
    subst hi16
    refine ⟨dec, rfl, ⟨hpts, hcomp, hlen16, hsort, hon, ?_, ?_⟩⟩
    · intro j hj pt hpt; simpa [show j < 16 by omega] using hat j hj pt hpt
    · intro j hj; simpa [show j < 16 by omega] using hen j hj
  | rem + 1, i, dec, hi, hpts, hcomp, hlen16, hsort, hon, hat, hen => by
    have hi16 : i < 16 := by omega
    have hmod : (c.index.toNat * 16 + i) % 16 = i := by omega
    have hdiv : (c.index.toNat * 16 + i) / 16 = c.index.toNat := by omega
    have hgi : dec.pts[i]? = some (dec.pts[i]'(by omega)) := List.getElem?_eq_getElem (by omega)
    have hnec : dec.necessaryPoints i = needed msg.length i := necessaryPoints_eq_needed hpts i
    simp only [PolyDecoder.addChunkLoop, hmod, hdiv, hgi, hnec]
    set x := GF16.new (BitVec.ofNat 16 c.index.toNat)
    have hx_eq : x = idxPt c.index.toNat := rfl
    set y1 := c.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩
    set y2 := c.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩
    set y := GF16.new ((y1.zeroExtend 16 <<< 8) + y2.zeroExtend 16)
    have hy_eq : y = (msgPoly msg i).eval x := by
      have hy1 : y1 = (((chunkVal msg c.index i).value >>> 8).setWidth 8) := by
        simp only [y1, hc, chunkData, List.Vector.get_ofFn]
        have h1 : ((i * 2) % 32) / 2 = i := by omega
        have h2 : ((i * 2) % 32) % 2 = 0 := by omega
        simp only [h1, h2, ↓reduceIte]
      have hy2 : y2 = ((chunkVal msg c.index i).value.setWidth 8) := by
        simp only [y2, hc, chunkData, List.Vector.get_ofFn]
        have h1 : ((i * 2 + 1) % 32) / 2 = i := by omega
        have h2 : ¬(((i * 2 + 1) % 32) % 2 = 0) := by omega
        simp only [h1, h2, ↓reduceIte]
      simp only [y, hy1, hy2, u16_reconstruct, GF16.new, chunkVal, hx_eq]
    have hi_lt_len : i < dec.pts.length := by omega
    by_cases hcond : (c.index.toNat < needed msg.length i || (dec.pts[i]'hi_lt_len).len < needed msg.length i) = true
    · simp only [hcond, ↓reduceIte]
      obtain ⟨hs'_sort, hs'_mem, hs'_le, hs'_fresh⟩ :=
        push_spec (dec.pts[i]'hi_lt_len) { x := x, y := y } (hsort i hi_lt_len)
      set s' := ((dec.pts[i]'hi_lt_len).push { x := x, y := y }).1
      set dec1 : PolyDecoder := { dec with pts := dec.pts.set i s' }
      have hlen1 : dec1.pts.length = 16 := by simp [dec1, hlen16]
      refine addChunkLoop_spec msg c hc S rem (i + 1) dec1 (by omega) hpts hcomp hlen1 ?_ ?_ ?_ ?_
      · intro j hj; simp only [dec1]
        by_cases hji : i = j
        · subst hji; simpa using hs'_sort
        · rw [List.getElem_set_ne hji]; exact hsort j (by omega)
      · intro j hj pt hpt; simp only [dec1] at hpt
        by_cases hji : i = j
        · subst hji; simp only [List.getElem_set_self] at hpt
          rcases hs'_mem pt hpt with rfl | hprev
          · exact hy_eq
          · exact hon i hi_lt_len pt hprev
        · rw [List.getElem_set_ne hji] at hpt
          exact hon j (by omega) pt hpt
      · intro j hj pt hpt; simp only [dec1] at hpt
        by_cases hji : i = j
        · subst hji; simp only [List.getElem_set_self, Nat.lt_succ_self, ↓reduceIte] at hpt ⊢
          rcases hs'_mem pt hpt with rfl | hprev
          · exact ⟨c.index.toNat, Finset.mem_insert_self _ _, c.index.isLt, rfl⟩
          · obtain ⟨idx, hidxS, hlt16, hpx⟩ := hat i hi_lt_len pt hprev
            simp only [lt_irrefl, ↓reduceIte] at hidxS
            exact ⟨idx, Finset.mem_insert_of_mem hidxS, hlt16, hpx⟩
        · rw [List.getElem_set_ne hji] at hpt
          have hiff : (j < i + 1) ↔ (j < i) := by omega
          simpa [hiff] using hat j (by omega) pt hpt
      · intro j hj; simp only [dec1]
        by_cases hji : i = j
        · subst hji; simp only [List.getElem_set_self, Nat.lt_succ_self, ↓reduceIte]
          have hen_i := hen i hi_lt_len; simp only [lt_irrefl, ↓reduceIte] at hen_i
          by_cases hmemS : c.index.toNat ∈ S
          · rw [Finset.insert_eq_of_mem hmemS]
            exact le_trans hen_i hs'_le
          · rw [Finset.card_insert_of_notMem hmemS]
            have hfresh : ∀ p ∈ (dec.pts[i]'hi_lt_len).vec, p.x ≠ x := by
              intro p hp heqx
              obtain ⟨idx, hidxS, hlt16, hpx⟩ := hat i hi_lt_len p hp
              simp only [lt_irrefl, ↓reduceIte] at hidxS
              have hidx_eq : idx = c.index.toNat :=
                idxPt_injOn (le_refl _) (Finset.mem_range.mpr hlt16) (Finset.mem_range.mpr c.index.isLt)
                  (hpx.symm.trans heqx)
              exact hmemS (hidx_eq ▸ hidxS)
            rw [hs'_fresh hfresh]; omega
        · rw [List.getElem_set_ne hji]
          have hiff : (j < i + 1) ↔ (j < i) := by omega
          simpa [hiff] using hen j (by omega)
    · have hcond_f :
          (c.index.toNat < needed msg.length i || (dec.pts[i]'hi_lt_len).len < needed msg.length i) = false :=
        Bool.eq_false_iff.mpr hcond
      simp only [hcond_f, Bool.false_eq_true, ↓reduceIte]
      have hge_nec : needed msg.length i ≤ (dec.pts[i]'hi_lt_len).vec.length := by
        have hnot_lt : ¬((dec.pts[i]'hi_lt_len).len < needed msg.length i) := by
          intro hlt; rw [decide_eq_true hlt, Bool.or_true] at hcond_f; cases hcond_f
        unfold SortedSetPt.len at hnot_lt; omega
      refine addChunkLoop_spec msg c hc S rem (i + 1) dec (by omega) hpts hcomp hlen16 hsort hon ?_ ?_
      · intro j hj pt hpt
        obtain ⟨idx, hidxS, hlt16, hpx⟩ := hat j hj pt hpt
        by_cases hji : i = j
        · subst hji; simp only [lt_irrefl, ↓reduceIte] at hidxS
          simp only [Nat.lt_succ_self, ↓reduceIte]
          exact ⟨idx, Finset.mem_insert_of_mem hidxS, hlt16, hpx⟩
        · have hiff : (j < i + 1) ↔ (j < i) := by omega
          simpa [hiff] using ⟨idx, hidxS, hlt16, hpx⟩
      · intro j hj
        by_cases hji : i = j
        · subst hji; simp only [Nat.lt_succ_self, ↓reduceIte]; omega
        · have hiff : (j < i + 1) ↔ (j < i) := by omega
          simpa [hiff] using hen j hj

private theorem addChunk_spec (msg : List (BitVec 8)) (S : Finset Nat) (dec : PolyDecoder)
    (hdec : DecInv msg S dec) (c : Chunk) (hc : c.data = chunkData msg c.index) :
    ∃ dec', dec.addChunk c = .ok dec' ∧ DecInv msg (insert c.index.toNat S) dec' := by
  unfold PolyDecoder.addChunk
  exact addChunkLoop_spec msg c hc S 16 0 dec rfl hdec.ptsNeeded hdec.notComplete hdec.len
    hdec.sorted hdec.onPoly
    (fun j hj pt hpt => by simpa using hdec.atNode j hj pt hpt)
    (fun j hj => by simpa using hdec.enough j hj)

/-- Adding honest chunks of `msg` preserves `DecInv` and accumulates their indices. -/
theorem foldl_addChunk_spec (msg : List (BitVec 8)) (_hlen : msg.length ≤ 2 ^ 20) :
    ∀ (rcv : List Chunk) (S : Finset Nat) (dec : PolyDecoder), DecInv msg S dec →
      (∀ c ∈ rcv, c.data = chunkData msg c.index) →
      ∃ dec', rcv.foldlM PolyDecoder.addChunk dec = .ok dec' ∧
        DecInv msg (S ∪ (rcv.map fun c => c.index.toNat).toFinset) dec'
  | [], S, dec, hdec, _ => ⟨dec, rfl, by simpa using hdec⟩
  | c :: rcv, S, dec, hdec, hhon => by
    obtain ⟨dec1, h1, hdec1⟩ := addChunk_spec msg S dec hdec c (hhon c List.mem_cons_self)
    obtain ⟨dec', hrest, hdec'⟩ :=
      foldl_addChunk_spec msg _hlen rcv (insert c.index.toNat S) dec1 hdec1
        (fun c' hc' => hhon c' (List.mem_cons_of_mem c hc'))
    have hfold : (c :: rcv).foldlM PolyDecoder.addChunk dec = .ok dec' := by
      simp only [List.foldlM_cons, h1, bind, Except.bind, hrest]
    have hset_eq : insert c.index.toNat S ∪ (rcv.map fun c => c.index.toNat).toFinset =
        S ∪ ((c :: rcv).map fun c => c.index.toNat).toFinset := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert, List.map_cons, List.toFinset_cons]
      tauto
    exact ⟨dec', hfold, hset_eq ▸ hdec'⟩

private theorem collectPointsVecs_enough (msg : List (BitVec 8)) (S : Finset Nat) (dec : PolyDecoder)
    (hdec : DecInv msg S dec) (henough : needed msg.length 0 ≤ S.card) :
    ∀ (rem i : Nat) (pv : List (List Pt)), i + rem = 16 → pv.length = i →
      (∀ j (hj : j < pv.length) (hjd : j < dec.pts.length),
        pv[j] = dec.pts[j].vec.take (needed msg.length j)) →
      ∃ pv', PolyDecoder.collectPointsVecs dec i rem false pv = .ok (false, pv') ∧
        pv'.length = 16 ∧
        ∀ j (hj : j < pv'.length) (hjd : j < dec.pts.length),
          pv'[j] = dec.pts[j].vec.take (needed msg.length j)
  | 0, i, pv, hi, hpv, hspec => ⟨pv, rfl, by omega, hspec⟩
  | rem + 1, i, pv, hi, hpv, hspec => by
    have hi_lt : i < dec.pts.length := by have := hdec.len; omega
    have hgi : dec.pts[i]? = some (dec.pts[i]'hi_lt) := List.getElem?_eq_getElem hi_lt
    have hnec : dec.necessaryPoints i = needed msg.length i := necessaryPoints_eq_needed hdec.ptsNeeded i
    have hle_i : needed msg.length i ≤ S.card := Nat.le_trans (needed_le_needed_zero _ _) henough
    have hen_i := hdec.enough i hi_lt
    have hnlt : ¬((dec.pts[i]'hi_lt).len < needed msg.length i) := by
      simp only [SortedSetPt.len]; omega
    simp only [PolyDecoder.collectPointsVecs, hgi, hnec, hnlt, ↓reduceIte, SortedSetPt.asSlice]
    refine collectPointsVecs_enough msg S dec hdec henough rem (i + 1)
      (pv ++ [(dec.pts[i]'hi_lt).vec.take (needed msg.length i)]) (by omega) (by simp [hpv]) ?_
    intro j hj hjd
    by_cases hji : j < i
    · rw [List.getElem_append_left (by omega)]; exact hspec j (by omega) hjd
    · have hjeq : j = i := by simp [hpv] at hj; omega
      subst hjeq; subst hpv; simp

private theorem slice_lagrangeInterpolate_eq_msgPoly (msg : List (BitVec 8)) (hlen : msg.length ≤ 2 ^ 20)
    (S : Finset Nat) (dec : PolyDecoder) (hdec : DecInv msg S dec)
    (henough : needed msg.length 0 ≤ S.card) (j : Nat) (hj : j < 16) :
    let hjd : j < dec.pts.length := by have := hdec.len; omega
    let slice := (dec.pts[j]'hjd).vec.take (needed msg.length j)
    ∃ p, Poly.lagrangeInterpolate slice = .ok p ∧ polyOf p.coefficients = msgPoly msg j := by
  intro hjd slice
  have hle_j : needed msg.length j ≤ S.card := Nat.le_trans (needed_le_needed_zero _ _) henough
  have hen_j := hdec.enough j hjd
  have hsl_len : slice.length = needed msg.length j := by simp [slice]; omega
  have hsl_bound : slice.length ≤ 2 ^ 20 := by
    have := needed_le_2pow16 hlen j; omega
  have hsl_sort : SortedInv slice := by
    have hsplit : slice ++ (dec.pts[j]'hjd).vec.drop (needed msg.length j) = (dec.pts[j]'hjd).vec :=
      List.take_append_drop _ _
    have hs := hdec.sorted j hjd
    rw [← hsplit, List.map_append, List.pairwise_append] at hs
    exact hs.1
  have hsl_nodup : (slice.map Pt.x).Nodup := sortedInv_nodup_x hsl_sort
  obtain ⟨p, hp, hp_len, hp_ev⟩ := lagrangeInterpolate_spec slice hsl_bound hsl_nodup
  refine ⟨p, hp, ?_⟩
  have hinj : Set.InjOn (fun k => (slice.getD k default).x) ↑(Finset.range (needed msg.length j)) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    exact nodup_pt_x_ne hsl_nodup (by omega) (by omega) hne hab
  apply Polynomial.eq_of_degree_sub_lt_of_eval_index_eq (Finset.range (needed msg.length j)) hinj
  · rw [Finset.card_range]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · rw [← hsl_len, ← hp_len]; exact degree_polyOf_lt p.coefficients
    · exact degree_msgPoly_lt hlen j
  · intro k hk
    have hk_lt : k < needed msg.length j := Finset.mem_range.mp hk
    have hk_sl : k < slice.length := by omega
    rw [hp_ev k hk_sl]
    have hmem_sl : slice[k] ∈ (dec.pts[j]'hjd).vec := List.mem_of_mem_take (List.getElem_mem hk_sl)
    have hget_eq : slice.getD k default = slice[k] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_sl]; rfl
    rw [hget_eq]
    exact hdec.onPoly j hjd slice[k] hmem_sl

private theorem decodedMessageLoop_spec (msg : List (BitVec 8)) (heven : msg.length % 2 = 0)
    (hlen : msg.length ≤ 2 ^ 20) (S : Finset Nat) (dec : PolyDecoder)
    (hdec : DecInv msg S dec) (henough : needed msg.length 0 ≤ S.card)
    (pv : List (List Pt)) (hpv_len : pv.length = 16)
    (hpv : ∀ j (hj : j < pv.length) (hjd : j < dec.pts.length),
      pv[j] = dec.pts[j].vec.take (needed msg.length j)) :
    ∀ (rem i : Nat) (polys : List (Option Poly)),
      i + rem = msg.length / 2 →
      polys.length = 16 →
      (∀ j (hj : j < polys.length) (p : Poly), polys[j] = some p → polyOf p.coefficients = msgPoly msg j) →
      ∃ polys', PolyDecoder.decodedMessageLoop dec pv i rem polys (msg.take (2 * i)) =
        .ok (polys', msg.take (2 * (i + rem)))
  | 0, i, polys, _, _, _ => ⟨polys, by simp [PolyDecoder.decodedMessageLoop]⟩
  | rem + 1, i, polys, hi, hpol_len, hpol_inv => by
    have hi_half : i < msg.length / 2 := by omega
    have hlen16 := hdec.len
    have hpoly16 : i % 16 < 16 := by omega
    have hpoly_d : i % 16 < dec.pts.length := by omega
    have hg_pts : dec.pts[i % 16]? = some (dec.pts[i % 16]'hpoly_d) := List.getElem?_eq_getElem hpoly_d
    have hpolyIdx_lt : i / 16 < needed msg.length (i % 16) := by
      unfold needed; split <;> omega
    have hev_node : (msgPoly msg (i % 16)).eval (idxPt (i / 16)) = msgVal msg i := by
      rw [eval_msgPoly_at_node hlen (i % 16) (i / 16) hpolyIdx_lt]
      congr 1; omega
    have hfinish : ∀ polys1 : List (Option Poly), polys1.length = 16 →
        (∀ j (hj : j < polys1.length) (p : Poly), polys1[j] = some p → polyOf p.coefficients = msgPoly msg j) →
        ∃ polys', PolyDecoder.decodedMessageLoop dec pv (i + 1) rem polys1
          (msg.take (2 * i) ++ u16ToBeBytes (msgVal msg i).value) =
          .ok (polys', msg.take (2 * (i + (rem + 1)))) := by
      intro polys1 hp1_len hp1_inv
      have htake_step : msg.take (2 * i) ++ u16ToBeBytes (msgVal msg i).value = msg.take (2 * (i + 1)) := by
        rw [u16ToBeBytes_msgVal msg i (by omega)]
        have h1 : msg.take (2 * i + 1) = msg.take (2 * i) ++ [msg[2 * i]'(by omega)] := List.take_succ_eq_append_getElem (by omega)
        have h2 : msg.take (2 * i + 2) = msg.take (2 * i + 1) ++ [msg[2 * i + 1]'(by omega)] := List.take_succ_eq_append_getElem (by omega)
        rw [show 2 * (i + 1) = 2 * i + 2 by omega, h2, h1, List.append_assoc]; rfl
      rw [htake_step, show i + (rem + 1) = i + 1 + rem by omega]
      exact decodedMessageLoop_spec msg heven hlen S dec hdec henough pv hpv_len hpv rem (i + 1) polys1
        (by omega) hp1_len hp1_inv
    rw [PolyDecoder.decodedMessageLoop]
    simp only [hg_pts]
    dsimp only [SortedSetPt.binarySearch]
    let pt : Pt := { x := GF16.new (BitVec.ofNat 16 (i / 16)), y := GF16.ZERO }
    have hpt_x : pt.x = idxPt (i / 16) := rfl
    have hbs := binarySearch_spec pt (dec.pts[i % 16]'hpoly_d).vec (hdec.sorted (i % 16) hpoly_d)
    cases hres : SortedSetPt.binarySearchAux pt 0 (dec.pts[i % 16]'hpoly_d).vec with
    | ok idx =>
      dsimp only
      rw [hres] at hbs; obtain ⟨hidx, hfx⟩ := hbs
      rw [List.getElem?_eq_getElem hidx]
      have fy := hdec.onPoly (i % 16) hpoly_d _ (List.getElem_mem hidx)
      rw [hfx, hpt_x, hev_node] at fy
      simp only [pure, Except.pure, fy]
      exact hfinish polys hpol_len hpol_inv
    | error _ =>
      dsimp only
      have hg_pol : polys[i % 16]? = some (polys[i % 16]'(by omega)) := List.getElem?_eq_getElem (by omega)
      simp only [hg_pol]
      cases hopt : polys[i % 16]'(by omega) with
      | some p =>
        have hp_eq : polyOf p.coefficients = msgPoly msg (i % 16) := hpol_inv (i % 16) (by omega) p hopt
        have hcomp : p.computeAt (GF16.new (BitVec.ofNat 16 (i / 16))) = .ok (msgVal msg i) := by
          rw [computeAt_eq_eval, hp_eq]; exact congrArg Except.ok hev_node
        simp only [bind, Except.bind, pure, Except.pure, hg_pol, hopt, hcomp]
        exact hfinish polys hpol_len hpol_inv
      | none =>
        have hg_pv : pv[i % 16]? = some (pv[i % 16]'(by omega)) := List.getElem?_eq_getElem (by omega)
        obtain ⟨interp, hinterp, hinterp_eq⟩ :=
          slice_lagrangeInterpolate_eq_msgPoly msg hlen S dec hdec henough (i % 16) hpoly16
        rw [← hpv (i % 16) (by omega) hpoly_d] at hinterp
        have hset_get : (polys.set (i % 16) (some interp))[i % 16]? = some (some interp) := by
          rw [List.getElem?_set_self (by omega)]
        have hcomp : interp.computeAt (GF16.new (BitVec.ofNat 16 (i / 16))) = .ok (msgVal msg i) := by
          rw [computeAt_eq_eval, hinterp_eq]; exact congrArg Except.ok hev_node
        simp only [hg_pv, hinterp, bind, Except.bind, pure, Except.pure, hset_get, hcomp]
        refine hfinish (polys.set (i % 16) (some interp)) (by simp [hpol_len]) ?_
        intro j hj p hpj
        by_cases hjp : j = i % 16
        · subst hjp; simp only [List.getElem_set_self] at hpj
          exact (Option.some.inj hpj) ▸ hinterp_eq
        · rw [List.getElem_set_ne (Ne.symm hjp)] at hpj
          exact hpol_inv j (by simp [hpol_len] at hj; omega) p hpj

private theorem decodedMessage_spec (msg : List (BitVec 8)) (heven : msg.length % 2 = 0)
    (hlen : msg.length ≤ 2 ^ 20) (S : Finset Nat) (dec : PolyDecoder)
    (hdec : DecInv msg S dec) (henough : needed msg.length 0 ≤ S.card) :
    dec.decodedMessage = .ok (some msg) := by
  unfold PolyDecoder.decodedMessage
  obtain ⟨pv, hcoll, hpv_len, hpv⟩ := collectPointsVecs_enough msg S dec hdec henough 16 0 [] rfl rfl
    (fun _ h _ => by simp at h)
  have husize : ¬(msg.length / 2 * 2 > USIZE_MAX) := by unfold USIZE_MAX; omega
  obtain ⟨polys', hloop⟩ :=
    decodedMessageLoop_spec msg heven hlen S dec hdec henough pv hpv_len hpv
      (msg.length / 2) 0 (List.replicate 16 none) (by omega) (by simp)
      (fun _ _ _ h => by rw [List.getElem_replicate] at h; cases h)
  simp only [Nat.mul_zero, List.take_zero, Nat.zero_add, show 2 * (msg.length / 2) = msg.length by omega,
    List.take_length] at hloop
  simp only [hdec.notComplete, Bool.false_eq_true, ↓reduceIte, hdec.len, hcoll, bind, Except.bind,
    hdec.ptsNeeded, husize, hloop, pure, Except.pure]

private theorem new_decInv (msg : List (BitVec 8)) (heven : msg.length % 2 = 0) :
    ∃ dec0, PolyDecoder.new msg.length = .ok (.ok dec0) ∧ DecInv msg ∅ dec0 := by
  unfold PolyDecoder.new PolyDecoder.newWithPolyCount
  have hev : (msg.length % 2 != 0) = false := by simp [heven]
  simp only [hev, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
  refine ⟨_, rfl, ⟨rfl, rfl, by simp, ?_, ?_, ?_, ?_⟩⟩
  · intro j _; rw [List.getElem_replicate]; simp [SortedSetPt.new]
  · intro j _ pt hpt; rw [List.getElem_replicate] at hpt; simp [SortedSetPt.new] at hpt
  · intro j _ pt hpt; rw [List.getElem_replicate] at hpt; simp [SortedSetPt.new] at hpt
  · intro j _; rw [List.getElem_replicate]; simp [SortedSetPt.new]

/-- A fresh decoder receiving honest chunks with at least `needed msg.length 0` distinct indices
reconstructs `some msg`. -/
theorem decode_honest_chunks (msg : List (BitVec 8)) (heven : msg.length % 2 = 0)
    (hlen : msg.length ≤ 2 ^ 20) (rcv : List Chunk)
    (hhonest : ∀ c ∈ rcv, c.data = chunkData msg c.index)
    (henough : needed msg.length 0 ≤ (rcv.map fun c => c.index.toNat).toFinset.card) :
    ∃ dec0 dec, PolyDecoder.new msg.length = .ok (.ok dec0) ∧
      rcv.foldlM PolyDecoder.addChunk dec0 = .ok dec ∧
      dec.decodedMessage = .ok (some msg) := by
  obtain ⟨dec0, hnew, hdec0⟩ := new_decInv msg heven
  obtain ⟨dec, hfold, hdec⟩ := foldl_addChunk_spec msg hlen rcv ∅ dec0 hdec0 hhonest
  rw [Finset.empty_union] at hdec
  exact ⟨dec0, dec, hnew, hfold, decodedMessage_spec msg heven hlen _ dec hdec henough⟩

/-- Emits `n` consecutive chunks from `PolyEncoder.nextChunk`. -/
def runChunks : Nat → PolyEncoder → Except PolyPanic (PolyEncoder × List Chunk)
  | 0, e => .ok (e, [])
  | n + 1, e => do
    let (e1, c) ← e.nextChunk
    let (e2, cs) ← runChunks n e1
    return (e2, c :: cs)

/-- The `n` consecutive 16-bit chunk indices emitted by `runChunks n` starting from counter `i`. -/
def honestIdxs : Nat → BitVec 32 → List (BitVec 16)
  | 0, _ => []
  | n + 1, i => i.setWidth 16 :: honestIdxs n (i + 1#32)

/-- `runChunks n` emits honest chunks at `honestIdxs n e.idx` and preserves `EncInv`. -/
theorem runChunks_spec (msg : List (BitVec 8)) (hlen : msg.length ≤ 2 ^ 20) :
    ∀ (n : Nat) (e : PolyEncoder), EncInv msg e →
      ∃ e', runChunks n e =
          .ok (e', (honestIdxs n e.idx).map fun idx => { index := idx, data := chunkData msg idx }) ∧
        EncInv msg e'
  | 0, e, he => ⟨e, rfl, he⟩
  | n + 1, e, he => by
    obtain ⟨e1, hnext, he1_idx, he1⟩ := nextChunk_spec msg hlen e he
    obtain ⟨e2, hrun, he2⟩ := runChunks_spec msg hlen n e1 he1
    simp only [runChunks, honestIdxs, List.map_cons, hnext, bind, Except.bind, hrun, he1_idx, pure, Except.pure]
    exact ⟨e2, rfl, he2⟩

/-- End-to-end erasure-code round-trip: any sublist of emitted chunks containing at least
`needed msg.length 0` distinct indices decodes to `some msg`. -/
theorem encode_decode_roundtrip (msg : List (BitVec 8)) (heven : msg.length % 2 = 0)
    (hlen : msg.length ≤ 2 ^ 20) (n : Nat) :
    ∃ e0 e cs, PolyEncoder.encodeBytes msg = .ok (.ok e0) ∧ runChunks n e0 = .ok (e, cs) ∧
      cs = (honestIdxs n 0#32).map (fun idx => { index := idx, data := chunkData msg idx }) ∧
      ∀ rcv : List Chunk, (∀ c ∈ rcv, c ∈ cs) →
        needed msg.length 0 ≤ (rcv.map fun c => c.index.toNat).toFinset.card →
        ∃ dec0 dec, PolyDecoder.new msg.length = .ok (.ok dec0) ∧
          rcv.foldlM PolyDecoder.addChunk dec0 = .ok dec ∧
          dec.decodedMessage = .ok (some msg) := by
  have henc := encodeBytes_spec msg heven hlen
  set e0 : PolyEncoder := { idx := 0#32, s := .points (msgPoints msg) }
  obtain ⟨e, hrun, _⟩ := runChunks_spec msg hlen n e0 (Or.inl rfl)
  refine ⟨e0, e, _, henc, hrun, rfl, ?_⟩
  intro rcv hsub henough
  refine decode_honest_chunks msg heven hlen rcv ?_ henough
  intro c hc
  rcases List.mem_map.mp (hsub c hc) with ⟨idx, _, rfl⟩
  rfl

end CryptoVerification.SpqrV1Sync.Erasure
