/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.ConstPolys
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.LagrangeSum

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1Sync.Erasure.FromCompletePoints

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.GF16Field
open CryptoVerification.SpqrV1Sync.Erasure
open CryptoVerification.SpqrV1Sync.Erasure.LagrangeSum
open CryptoVerification.SpqrV1Sync.Erasure.ConstPolys
open Polynomial

@[simp] theorem length_enumeratePts (k : Nat) (ys : List GF16) :
    (PolyEncoder.enumeratePts k ys).length = ys.length := by
  induction ys generalizing k with
  | nil => rfl
  | cons y ys ih =>
    simp [PolyEncoder.enumeratePts, ih (k + 1)]

theorem getElem_enumeratePts (k : Nat) (ys : List GF16) (i : Nat) (hi : i < ys.length) :
    (PolyEncoder.enumeratePts k ys)[i]'(by simpa using hi) =
      { x := idxPt (k + i), y := ys[i]'hi } := by
  induction ys generalizing k i with
  | nil => contradiction
  | cons y ys ih =>
    cases i with
    | zero =>
      simp [PolyEncoder.enumeratePts, idxPt]
    | succ i =>
      have hi' : i < ys.length := by simpa using hi
      simp only [PolyEncoder.enumeratePts, List.getElem_cons_succ, ih (k + 1) i hi']
      have hk : k + 1 + i = k + (i + 1) := by omega
      rw [hk]

theorem checkCompletePoints_enumeratePts (k : Nat) (ys : List GF16) :
    Poly.checkCompletePoints k (PolyEncoder.enumeratePts k ys) = true := by
  induction ys generalizing k with
  | nil => rfl
  | cons y ys ih =>
    simp [PolyEncoder.enumeratePts, Poly.checkCompletePoints, ih (k + 1)]

theorem map_ones_enumeratePts_range' (k : Nat) (ys : List GF16) :
    (PolyEncoder.enumeratePts k ys).map (fun pt : Pt => ({ x := pt.x, y := GF16.ONE } : Pt)) =
      (List.range' k ys.length).map
        (fun i => ({ x := GF16.new (BitVec.ofNat 16 i), y := GF16.ONE } : Pt)) := by
  induction ys generalizing k with
  | nil => rfl
  | cons y ys ih =>
    simp [PolyEncoder.enumeratePts, List.range'_succ, ih (k + 1)]

theorem map_ones_enumeratePts_zero (ys : List GF16) :
    (PolyEncoder.enumeratePts 0 ys).map (fun pt : Pt => ({ x := pt.x, y := GF16.ONE } : Pt)) =
      onesPts ys.length := by
  rw [map_ones_enumeratePts_range', onesPts, List.range_eq_range']

theorem onesPts_succ (m : Nat) :
    onesPts (m + 1) = onesPts m ++ [{ x := idxPt m, y := GF16.ONE }] := by
  simp [onesPts, List.range_succ, idxPt]

@[simp] theorem length_onesPts (m : Nat) : (onesPts m).length = m := by
  simp [onesPts]

theorem getElem_onesPts {n i : Nat} (hi : i < n) :
    (onesPts n)[i]'(by simpa using hi) = { x := idxPt i, y := GF16.ONE } := by
  simp [onesPts, idxPt]

theorem lagrangeDenominator_onesPts (m i : Nat) (hm : m < 2 ^ 16) (hi : i < 2 ^ 16) :
    Poly.lagrangeDenominator (idxPt i) (onesPts m) =
      ∏ j ∈ (Finset.range m).erase i, (idxPt i - idxPt j) := by
  induction m with
  | zero =>
    simp [Poly.lagrangeDenominator, onesPts, ← one_eq]
  | succ m ih =>
    have hm' : m < 2 ^ 16 := by omega
    unfold Poly.lagrangeDenominator
    rw [onesPts_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (if idxPt i == idxPt m then
        Poly.lagrangeDenominator (idxPt i) (onesPts m)
      else
        GF16.mul (Poly.lagrangeDenominator (idxPt i) (onesPts m))
          (GF16.sub (idxPt i) (idxPt m))) =
      ∏ j ∈ (Finset.range (m + 1)).erase i, (idxPt i - idxPt j)
    rw [ih hm']
    by_cases him : i = m
    · subst him
      have herase : (Finset.range (i + 1)).erase i = (Finset.range i).erase i := by
        rw [Finset.range_add_one, Finset.erase_insert_eq_erase]
      simp [herase]
    · have hbeq : (idxPt i == idxPt m) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        exact him ((idxPt_inj_of_lt hi hm').mp heq)
      have herase : (Finset.range (m + 1)).erase i = insert m ((Finset.range m).erase i) := by
        rw [Finset.range_add_one, Finset.erase_insert_of_ne (Ne.symm him)]
      have hm_not_mem : m ∉ (Finset.range m).erase i := by simp
      have hsub : GF16.sub (idxPt i) (idxPt m) = idxPt i - idxPt m := rfl
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      rw [herase, Finset.prod_insert hm_not_mem, ← mul_eq, hsub, mul_comm]

theorem eraseIdx_append_singleton {α : Type} (xs : List α) (x : α) (i : Nat) :
    (xs ++ [x]).eraseIdx i =
      if i = xs.length then xs.eraseIdx i else xs.eraseIdx i ++ [x] := by
  by_cases hlt : i < xs.length
  · have hne : i ≠ xs.length := by omega
    simp only [hne, ↓reduceIte, List.eraseIdx_append_of_lt_length hlt]
  · by_cases heq : i = xs.length
    · subst heq
      simp only [↓reduceIte, List.eraseIdx_append_of_length_le (Nat.le_refl _), Nat.sub_self,
        List.eraseIdx_cons_zero, List.append_nil, List.eraseIdx_of_length_le (Nat.le_refl _)]
    · have hgt : xs.length < i := by omega
      have hsub : i - xs.length ≥ 1 := by omega
      have hx : ([x] : List α).eraseIdx (i - xs.length) = [x] := by
        apply List.eraseIdx_of_length_le
        simp [hsub]
      simp only [heq, ↓reduceIte,
        List.eraseIdx_append_of_length_le (Nat.le_of_lt hgt), hx,
        List.eraseIdx_of_length_le (Nat.le_of_lt hgt)]

theorem prod_eraseIdx_onesPts (m i : Nat) :
    (((onesPts m).eraseIdx i).map fun pt => X - C pt.x).prod =
      ∏ j ∈ (Finset.range m).erase i, (X - C (idxPt j)) := by
  induction m with
  | zero =>
    simp [onesPts]
  | succ m ih =>
    rw [onesPts_succ, eraseIdx_append_singleton, length_onesPts]
    by_cases him : i = m
    · subst him
      have herase : (Finset.range (i + 1)).erase i = (Finset.range i).erase i := by
        rw [Finset.range_add_one, Finset.erase_insert_eq_erase]
      simp [herase, ih]
    · simp only [him, ↓reduceIte, List.map_append, List.prod_append,
        List.map_singleton, List.prod_singleton, ih]
      have herase : (Finset.range (m + 1)).erase i = insert m ((Finset.range m).erase i) := by
        rw [Finset.range_add_one, Finset.erase_insert_of_ne (Ne.symm him)]
      have hm_not_mem : m ∉ (Finset.range m).erase i := by simp
      rw [herase, Finset.prod_insert hm_not_mem, mul_comm]

theorem constPolysToPolys_lagrangePolys_spec (pts : List Pt) (n : Nat) (hn : n < 2 ^ 16)
    (hpts_n : pts.length = n) :
    ∃ polys : List Poly,
      (do
        let cps ← lagrangePolysForCompletePoints n
        let polys ← pure (constPolysToPolys cps)
        pure (Except.ok (Poly.lagrangeSum pts polys)) :
          Except PolyPanic (Except Unit Poly)) =
        .ok (.ok (Poly.lagrangeSum pts polys)) ∧
      polys.length = pts.length ∧
      ∀ i (hi : i < polys.length),
        polys[i].coefficients.length = pts.length ∧
        polyOf polys[i].coefficients = Lagrange.basis (Finset.range pts.length) idxPt i := by
  rcases lagrangePolysForCompletePoints_spec_aux n hn with ⟨cps, hcps, hlen, hspec⟩
  refine ⟨constPolysToPolys cps, ?_, ?_, ?_⟩
  · simp [hcps, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp [constPolysToPolys, hlen, hpts_n]
  · intro i hi
    have hi' : i < cps.length := by simpa [constPolysToPolys] using hi
    simpa [constPolysToPolys, PolyConst.toPoly, hpts_n] using hspec i hi'

theorem fallback_lagrangePolys_spec
    (hpt : ∀ (pts : List Pt) (i : Nat) (hi : i < pts.length), pts.length < 2 ^ 16 →
      ∃ p : Poly, Poly.lagrangeInterpolatePt pts i = .ok p ∧
        p.coefficients.length = pts.length ∧
        polyOf p.coefficients =
          C (GF16.div pts[i].y (Poly.lagrangeDenominator pts[i].x pts)) *
            ((pts.eraseIdx i).map fun pt => X - C pt.x).prod)
    (pts : List Pt) (hn : pts.length < 2 ^ 16) :
    ∃ polys : List Poly,
      (do
        let polys ← (List.range pts.length).mapM
          (fun i => Poly.lagrangeInterpolatePt (onesPts pts.length) i)
        pure (Except.ok (Poly.lagrangeSum pts polys)) :
          Except PolyPanic (Except Unit Poly)) =
        .ok (.ok (Poly.lagrangeSum pts polys)) ∧
      polys.length = pts.length ∧
      ∀ i (hi : i < polys.length),
        polys[i].coefficients.length = pts.length ∧
        polyOf polys[i].coefficients = Lagrange.basis (Finset.range pts.length) idxPt i := by
  have hmapM :
      ∃ polys : List Poly,
        (List.range pts.length).mapM
          (fun i => Poly.lagrangeInterpolatePt (onesPts pts.length) i) = .ok polys ∧
        polys.length = pts.length ∧
        ∀ i (hi : i < polys.length),
          polys[i].coefficients.length = pts.length ∧
          polyOf polys[i].coefficients = Lagrange.basis (Finset.range pts.length) idxPt i := by
    apply range_mapM_except_ok pts.length
      (fun i => Poly.lagrangeInterpolatePt (onesPts pts.length) i)
      (fun i p => p.coefficients.length = pts.length ∧
        polyOf p.coefficients = Lagrange.basis (Finset.range pts.length) idxPt i)
    intro i hi
    have hi_len : i < (onesPts pts.length).length := by simpa using hi
    have hn_len : (onesPts pts.length).length < 2 ^ 16 := by simpa using hn
    rcases hpt (onesPts pts.length) i hi_len hn_len with ⟨p, hp, hplen, hppoly⟩
    refine ⟨p, hp, by simpa using hplen, ?_⟩
    rw [hppoly, getElem_onesPts hi, lagrangeDenominator_onesPts pts.length i hn (Nat.lt_trans hi hn),
      prod_eraseIdx_onesPts pts.length i, ← inv_eq, lagrange_basis_eq_C_inv_mul_prod]
  rcases hmapM with ⟨polys, hpolys, hlen, hspec⟩
  refine ⟨polys, ?_, hlen, hspec⟩
  simp [hpolys, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem fromCompletePoints_polys_spec
    (hpt : ∀ (pts : List Pt) (i : Nat) (hi : i < pts.length), pts.length < 2 ^ 16 →
      ∃ p : Poly, Poly.lagrangeInterpolatePt pts i = .ok p ∧
        p.coefficients.length = pts.length ∧
        polyOf p.coefficients =
          C (GF16.div pts[i].y (Poly.lagrangeDenominator pts[i].x pts)) *
            ((pts.eraseIdx i).map fun pt => X - C pt.x).prod)
    (pts : List Pt) (hchk : Poly.checkCompletePoints 0 pts = true)
    (hn : pts.length < 2 ^ 16)
    (hones : pts.map (fun pt => { x := pt.x, y := GF16.ONE }) = onesPts pts.length) :
    ∃ polys : List Poly,
      Poly.fromCompletePoints pts = .ok (.ok (Poly.lagrangeSum pts polys)) ∧
      polys.length = pts.length ∧
      ∀ i (hi : i < polys.length),
        polys[i].coefficients.length = pts.length ∧
        polyOf polys[i].coefficients = Lagrange.basis (Finset.range pts.length) idxPt i := by
  unfold Poly.fromCompletePoints
  rw [hchk]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases h0 : (pts.length == 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases h1 : (pts.length == 1)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases h3 : (pts.length == 3)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases h5 : (pts.length == 5)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases h30 : (pts.length == 30)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases h34 : (pts.length == 34)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              cases h36 : (pts.length == 36)
              · simp only [Bool.false_eq_true, ↓reduceIte, hones]
                exact fallback_lagrangePolys_spec hpt pts hn
              · have hn36 : pts.length = 36 := beq_iff_eq.mp h36
                simpa [COMPLETE_POINTS_POLYS_36] using
                  constPolysToPolys_lagrangePolys_spec pts 36 (by decide) hn36
            · have hn34 : pts.length = 34 := beq_iff_eq.mp h34
              simpa [COMPLETE_POINTS_POLYS_34] using
                constPolysToPolys_lagrangePolys_spec pts 34 (by decide) hn34
          · have hn30 : pts.length = 30 := beq_iff_eq.mp h30
            simpa [COMPLETE_POINTS_POLYS_30] using
              constPolysToPolys_lagrangePolys_spec pts 30 (by decide) hn30
        · have hn5 : pts.length = 5 := beq_iff_eq.mp h5
          simpa [COMPLETE_POINTS_POLYS_5] using
            constPolysToPolys_lagrangePolys_spec pts 5 (by decide) hn5
      · have hn3 : pts.length = 3 := beq_iff_eq.mp h3
        simpa [COMPLETE_POINTS_POLYS_3] using
          constPolysToPolys_lagrangePolys_spec pts 3 (by decide) hn3
    · have hn1 : pts.length = 1 := beq_iff_eq.mp h1
      simpa [COMPLETE_POINTS_POLYS_1] using
        constPolysToPolys_lagrangePolys_spec pts 1 (by decide) hn1
  · have hn0 : pts.length = 0 := beq_iff_eq.mp h0
    refine ⟨[], rfl, by simp [hn0], ?_⟩
    intro i hi
    contradiction

theorem sum_map_range (m : Nat) (f : Nat → GF16[X]) :
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, Finset.sum_range_succ, ih]

theorem fromCompletePoints_spec_aux
    (hpt : ∀ (pts : List Pt) (i : Nat) (hi : i < pts.length), pts.length < 2 ^ 16 →
      ∃ p : Poly, Poly.lagrangeInterpolatePt pts i = .ok p ∧
        p.coefficients.length = pts.length ∧
        polyOf p.coefficients =
          C (GF16.div pts[i].y (Poly.lagrangeDenominator pts[i].x pts)) *
            ((pts.eraseIdx i).map fun pt => X - C pt.x).prod)
    (ys : List GF16) (hlen : ys.length < 2 ^ 16) :
    ∃ p : Poly, Poly.fromCompletePoints (PolyEncoder.enumeratePts 0 ys) = .ok (.ok p) ∧
      p.coefficients.length = ys.length ∧
      polyOf p.coefficients =
        Lagrange.interpolate (Finset.range ys.length) idxPt (fun k => ys.getD k GF16.ZERO) := by
  have hchk : Poly.checkCompletePoints 0 (PolyEncoder.enumeratePts 0 ys) = true :=
    checkCompletePoints_enumeratePts 0 ys
  have hpts_len : (PolyEncoder.enumeratePts 0 ys).length = ys.length :=
    length_enumeratePts 0 ys
  have hones : (PolyEncoder.enumeratePts 0 ys).map (fun pt => { x := pt.x, y := GF16.ONE }) =
      onesPts (PolyEncoder.enumeratePts 0 ys).length := by
    rw [map_ones_enumeratePts_zero, hpts_len]
  rcases fromCompletePoints_polys_spec hpt (PolyEncoder.enumeratePts 0 ys) hchk (by omega) hones with
    ⟨polys, hfrom, hpolys_len, hpolys_spec⟩
  have hm : ∀ p ∈ polys, p.coefficients.length = ys.length := by
    intro p hp
    rcases List.getElem_of_mem hp with ⟨i, hi, rfl⟩
    rw [← hpts_len]
    exact (hpolys_spec i hi).1
  have hsum := lagrangeSum_spec_aux (PolyEncoder.enumeratePts 0 ys) polys ys.length (by omega) hm
  refine ⟨Poly.lagrangeSum (PolyEncoder.enumeratePts 0 ys) polys, hfrom, ?_, ?_⟩
  · rw [hsum.1]
    by_cases hp : polys = []
    · subst hp
      simp only [List.length_nil] at hpolys_len
      simp [← hpts_len, ← hpolys_len]
    · simp [hp]
  · rw [hsum.2, Lagrange.interpolate_apply]
    have hmap_eq :
        (((PolyEncoder.enumeratePts 0 ys).zip polys).map fun q => C q.1.y * polyOf q.2.coefficients) =
          (List.range ys.length).map (fun k =>
            C (ys.getD k GF16.ZERO) * Lagrange.basis (Finset.range ys.length) idxPt k) := by
      apply List.ext_getElem
      · simp [hpts_len, hpolys_len]
      · intro i hi1 hi2
        have hi : i < ys.length := by simpa using hi2
        have hi_polys : i < polys.length := by omega
        simp only [List.getElem_map, List.getElem_zip, List.getElem_range]
        have hpt_i := getElem_enumeratePts 0 ys i hi
        have hy_i : ((PolyEncoder.enumeratePts 0 ys)[i]'(by omega)).y = ys.getD i GF16.ZERO := by
          rw [hpt_i, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
        have hpoly_i : polyOf (polys[i]'hi_polys).coefficients =
            Lagrange.basis (Finset.range ys.length) idxPt i := by
          rw [← hpts_len]
          exact (hpolys_spec i hi_polys).2
        rw [hy_i, hpoly_i]
    rw [hmap_eq, sum_map_range]

end CryptoVerification.SpqrV1Sync.Erasure.FromCompletePoints
