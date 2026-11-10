/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.LagrangeSum

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1Sync.Erasure.ConstPolys

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.GF16Field
open CryptoVerification.SpqrV1Sync.Erasure
open CryptoVerification.SpqrV1Sync.Erasure.LagrangeSum
open Polynomial

theorem idxPt_inj_of_lt {i j : Nat} (hi : i < 2 ^ 16) (hj : j < 2 ^ 16) :
    idxPt i = idxPt j ↔ i = j := by
  constructor
  · intro h
    unfold idxPt GF16.new at h
    injection h with hbv
    have hnat := congrArg BitVec.toNat hbv
    simp only [BitVec.toNat_ofNat] at hnat
    omega
  · rintro rfl
    rfl

theorem polyOf_append_zero (cs : List GF16) :
    polyOf (cs ++ [GF16.ZERO]) = polyOf cs := by
  induction cs with
  | nil =>
    simp [polyOf_cons, ← zero_eq]
  | cons c cs ih =>
    simp [polyOf_cons, ih]

theorem polyOf_replicate_zero (k : Nat) :
    polyOf (List.replicate k GF16.ZERO) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, polyOf_cons, ih, ← zero_eq]
    simp

theorem polyOf_one_cons_replicate_zero (k : Nat) :
    polyOf (GF16.ONE :: List.replicate k GF16.ZERO) = 1 := by
  simp [polyOf_cons, polyOf_replicate_zero, ← one_eq]

theorem polyOf_zip_constSub (as bs : List GF16) (h : as.length = bs.length) :
    polyOf ((as.zip bs).map fun (a, b) => GF16.constSub a b) = polyOf as - polyOf bs := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => simp
    | cons _ _ => simp at h
  | cons a as ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      have hlen : as.length = bs.length := by simpa using h
      simp only [List.zip_cons_cons, List.map_cons, polyOf_cons, ih bs hlen]
      have hsub : GF16.constSub a b = a - b := rfl
      rw [hsub, map_sub]
      ring

theorem zip_append_eq {α β : Type} (as1 as2 : List α) (bs1 bs2 : List β)
    (h : as1.length = bs1.length) :
    (as1 ++ as2).zip (bs1 ++ bs2) = as1.zip bs1 ++ as2.zip bs2 := by
  induction as1 generalizing bs1 with
  | nil =>
    cases bs1 with
    | nil => simp
    | cons _ _ => simp at h
  | cons a as1 ih =>
    cases bs1 with
    | nil => simp at h
    | cons b bs1 =>
      simp only [List.cons_append, List.zip_cons_cons, ih bs1 (by simpa using h)]

theorem zip_replicate_zero_constSub (r : Nat) :
    ((List.replicate r GF16.ZERO).zip (List.replicate r GF16.ZERO)).map
      (fun (a, b) => GF16.constSub a b) = List.replicate r GF16.ZERO := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have h0 : GF16.constSub GF16.ZERO GF16.ZERO = GF16.ZERO := by decide
    simp only [List.replicate_succ, List.zip_cons_cons, List.map_cons, h0, ih]

theorem map_replicate_zero_constMul (r : Nat) (d : GF16) :
    (List.replicate r GF16.ZERO).map (fun c => GF16.constMul c d) =
      List.replicate r GF16.ZERO := by
  rw [List.map_replicate, constMul_eq_mul, zero_mul']

def Padded (n r : Nat) (p : PolyConst n) : Prop :=
  ∃ cs : List GF16, cs.length + r = n ∧ p.coefficients = cs ++ List.replicate r GF16.ZERO

theorem Padded.length {n r : Nat} {p : PolyConst n} (h : Padded n r p) :
    p.coefficients.length = n := by
  rcases h with ⟨cs, hlen, hp⟩
  simp [hp, hlen]

theorem multXdiff_spec {n r : Nat} (p : PolyConst n) (d : GF16)
    (hpad : Padded n (r + 1) p) :
    ∃ p' : PolyConst n, p.multXdiff d = .ok p' ∧
      Padded n r p' ∧
      polyOf p'.coefficients = polyOf p.coefficients * (X - C d) := by
  rcases hpad with ⟨cs, hlen, hp⟩
  have hn0 : (n == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  let pre : List GF16 := cs ++ List.replicate r GF16.ZERO
  have hpre_len : pre.length = n - 1 := by
    simp only [pre, List.length_append, List.length_replicate]
    omega
  have hp_pre : p.coefficients = pre ++ [GF16.ZERO] := by
    rw [hp, List.replicate_succ', List.append_assoc]
  have htop : p.coefficients[n - 1]? = some GF16.ZERO := by
    rw [hp_pre, ← hpre_len, List.getElem?_append_right (Nat.le_refl _)]
    simp
  have htake : p.coefficients.take (n - 1) = pre := by
    rw [hp_pre, ← hpre_len, List.take_left]
  let as1 : List GF16 := GF16.ZERO :: cs
  let bs1 : List GF16 := (cs ++ [GF16.ZERO]).map (fun c => GF16.constMul c d)
  let cs' : List GF16 := (as1.zip bs1).map (fun (a, b) => GF16.constSub a b)
  let xp : List GF16 := GF16.ZERO :: pre
  let dp : List GF16 := p.coefficients.map (fun c => GF16.constMul c d)
  let out : List GF16 := (xp.zip dp).map (fun (a, b) => GF16.constSub a b)
  refine ⟨{ coefficients := out }, ?_, ?_, ?_⟩
  · unfold PolyConst.multXdiff
    simp [hn0, htop, htake, Pure.pure, Except.pure, xp, dp, out]
  · refine ⟨cs', ?_, ?_⟩
    · simp only [cs', as1, bs1, List.length_map, List.length_zip, List.length_cons,
        List.length_append]
      omega
    · have hxp_eq : xp = as1 ++ List.replicate r GF16.ZERO := by
        simp [xp, pre, as1]
      have hdp_eq : dp = bs1 ++ List.replicate r GF16.ZERO := by
        have hp_split : p.coefficients = (cs ++ [GF16.ZERO]) ++ List.replicate r GF16.ZERO := by
          rw [hp, List.replicate_succ, ← List.singleton_append, ← List.append_assoc]
        simp only [dp, hp_split, List.map_append, bs1, map_replicate_zero_constMul]
      have hab_len : as1.length = bs1.length := by
        simp [as1, bs1]
      simp only [out, hxp_eq, hdp_eq, zip_append_eq as1 _ bs1 _ hab_len, List.map_append,
        zip_replicate_zero_constSub, cs']
  · have hxp_dp_len : xp.length = dp.length := by
      have hplen : p.coefficients.length = n := by
        simp [hp, ← hlen]
      simp only [xp, dp, List.length_cons, hpre_len, List.length_map, hplen]
      omega
    rw [polyOf_zip_constSub xp dp hxp_dp_len]
    have hpoly_xp : polyOf xp = X * polyOf p.coefficients := by
      simp only [xp, polyOf_cons, ← zero_eq, map_zero, zero_add]
      rw [hp_pre, polyOf_append_zero]
    have hpoly_dp : polyOf dp = C d * polyOf p.coefficients := by
      simp only [dp, constMul_eq_mul, polyOf_map_mul_right]
    rw [hpoly_xp, hpoly_dp]
    ring

def onesPts (n : Nat) : List Pt :=
  (List.range n).map (fun i => { x := GF16.new (BitVec.ofNat 16 i), y := GF16.ONE })

theorem getElem?_onesPts {n j : Nat} (hj : j < n) :
    (onesPts n)[j]? = some { x := idxPt j, y := GF16.ONE } := by
  simp [onesPts, hj, idxPt]

theorem lagrangeInterpolatePtLoop_spec (n i : Nat) (hn : n < 2 ^ 16) (hi : i < n) :
    ∀ (rem j : Nat) (p : PolyConst n) (denom : GF16),
      j + rem = n →
      Padded n (if i < j then rem else rem - 1) p →
      polyOf p.coefficients = ∏ k ∈ (Finset.range j).erase i, (X - C (idxPt k)) →
      denom = ∏ k ∈ (Finset.range j).erase i, (idxPt i - idxPt k) →
      ∃ pFinal : PolyConst n, ∃ denomFinal : GF16,
        PolyConst.lagrangeInterpolatePtLoop n (onesPts n) (idxPt i) j rem p denom =
          .ok (pFinal, denomFinal) ∧
        pFinal.coefficients.length = n ∧
        polyOf pFinal.coefficients = ∏ k ∈ (Finset.range n).erase i, (X - C (idxPt k)) ∧
        denomFinal = ∏ k ∈ (Finset.range n).erase i, (idxPt i - idxPt k)
  | 0, j, p, denom, hjrem, hpad, hp, hdenom => by
    have hjn : j = n := by omega
    subst hjn
    refine ⟨p, denom, rfl, hpad.length, hp, hdenom⟩
  | rem + 1, j, p, denom, hjrem, hpad, hp, hdenom => by
    have hjn : j < n := by omega
    have hget := getElem?_onesPts hjn
    by_cases hij : i = j
    · subst hij
      have hbeq : (idxPt i == idxPt i) = true := beq_self_eq_true _
      have hpad' : Padded n (if i < i + 1 then rem else rem - 1) p := by
        have heq : (if i < i then rem + 1 else rem + 1 - 1) = (if i < i + 1 then rem else rem - 1) := by
          simp
        rwa [← heq]
      have herase : (Finset.range (i + 1)).erase i = (Finset.range i).erase i := by
        rw [Finset.range_add_one, Finset.erase_insert_eq_erase]
      unfold PolyConst.lagrangeInterpolatePtLoop
      simp only [hget, hbeq, ↓reduceIte]
      exact lagrangeInterpolatePtLoop_spec n i hn hi rem (i + 1) p denom (by omega) hpad'
        (by rw [herase, hp]) (by rw [herase, hdenom])
    · have hbeq : (idxPt i == idxPt j) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        exact hij ((idxPt_inj_of_lt (Nat.lt_trans hi hn) (Nat.lt_trans hjn hn)).mp heq)
      have hr_eq : (if i < j then rem + 1 else rem + 1 - 1) = (if i < j + 1 then rem else rem - 1) + 1 := by
        split <;> split <;> omega
      rw [hr_eq] at hpad
      rcases multXdiff_spec p (idxPt j) hpad with ⟨p', hp', hpad', hpoly'⟩
      have herase : (Finset.range (j + 1)).erase i = insert j ((Finset.range j).erase i) := by
        rw [Finset.range_add_one, Finset.erase_insert_of_ne (Ne.symm hij)]
      have hj_not_mem : j ∉ (Finset.range j).erase i := by
        simp
      have hpoly_next : polyOf p'.coefficients =
          ∏ k ∈ (Finset.range (j + 1)).erase i, (X - C (idxPt k)) := by
        rw [herase, Finset.prod_insert hj_not_mem, hpoly', hp, mul_comm]
      have hdenom_next : GF16.constMul denom (GF16.constSub (idxPt i) (idxPt j)) =
          ∏ k ∈ (Finset.range (j + 1)).erase i, (idxPt i - idxPt k) := by
        have hcs : GF16.constSub (idxPt i) (idxPt j) = idxPt i - idxPt j := rfl
        rw [herase, Finset.prod_insert hj_not_mem, constMul_eq_mul, ← mul_eq, hcs, hdenom, mul_comm]
      unfold PolyConst.lagrangeInterpolatePtLoop
      simp only [hget, hbeq, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, hp']
      exact lagrangeInterpolatePtLoop_spec n i hn hi rem (j + 1) p'
        (GF16.constMul denom (GF16.constSub (idxPt i) (idxPt j)))
        (by omega) hpad' hpoly_next hdenom_next

theorem lagrange_basis_eq_C_inv_mul_prod (s : Finset Nat) (v : Nat → GF16) (i : Nat) :
    Lagrange.basis s v i =
      C ((∏ j ∈ s.erase i, (v i - v j))⁻¹) * ∏ j ∈ s.erase i, (X - C (v j)) := by
  unfold Lagrange.basis Lagrange.basisDivisor
  rw [Finset.prod_mul_distrib, ← map_prod, ← Finset.prod_inv_distrib]

theorem polyConst_lagrangeInterpolatePt_spec (n i : Nat) (hn : n < 2 ^ 16) (hi : i < n) :
    ∃ cp : PolyConst n, PolyConst.lagrangeInterpolatePt n (onesPts n) i = .ok cp ∧
      cp.coefficients.length = n ∧
      polyOf cp.coefficients = Lagrange.basis (Finset.range n) idxPt i := by
  have hget := getElem?_onesPts hi
  have hn0 : (n == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  let p0 : PolyConst n := { coefficients := GF16.ONE :: List.replicate (n - 1) GF16.ZERO }
  have hp0_pad : Padded n (if i < 0 then n else n - 1) p0 := by
    refine ⟨[GF16.ONE], ?_, ?_⟩
    · simp; omega
    · simp [p0]
  have hp0_poly : polyOf p0.coefficients = ∏ k ∈ (Finset.range 0).erase i, (X - C (idxPt k)) := by
    simp [p0, polyOf_one_cons_replicate_zero]
  have hd0 : GF16.ONE = ∏ k ∈ (Finset.range 0).erase i, (idxPt i - idxPt k) := by
    simp [← one_eq]
  rcases lagrangeInterpolatePtLoop_spec n i hn hi n 0 p0 GF16.ONE (by omega) hp0_pad hp0_poly hd0
    with ⟨pFinal, denomFinal, hloop, hlenFinal, hpolyFinal, hdenomFinal⟩
  let m := GF16.constDiv GF16.ONE denomFinal
  refine ⟨pFinal.mult m, ?_, ?_, ?_⟩
  · unfold PolyConst.lagrangeInterpolatePt
    simp [hget, hn0, Bind.bind, Except.bind, Pure.pure, Except.pure, p0, hloop, m]
  · simp [PolyConst.mult, hlenFinal]
  · simp only [PolyConst.mult, constMul_eq_mul, polyOf_map_mul_right, hpolyFinal]
    have hm : m = denomFinal⁻¹ := by
      simp [m, constDiv_eq_div, inv_eq]
    rw [hm, hdenomFinal, lagrange_basis_eq_C_inv_mul_prod]

theorem range_mapM_except_ok {ε β : Type} (n : Nat) (f : Nat → Except ε β)
    (P : Nat → β → Prop)
    (hf : ∀ i, i < n → ∃ y, f i = .ok y ∧ P i y) :
    ∃ ys : List β, (List.range n).mapM f = .ok ys ∧ ys.length = n ∧
      ∀ i (hi : i < ys.length), P i (ys[i]'hi) := by
  have haux : ∀ (xs : List Nat), (∀ x ∈ xs, ∃ y, f x = .ok y ∧ P x y) →
      ∃ ys : List β, xs.mapM f = .ok ys ∧ ∃ hlen : ys.length = xs.length,
        ∀ k (hk : k < ys.length), P (xs[k]'(hlen ▸ hk)) (ys[k]'hk) := by
    intro xs
    induction xs with
    | nil =>
      intro _
      refine ⟨[], rfl, ⟨rfl, ?_⟩⟩
      intro k hk
      contradiction
    | cons x xs ih =>
      intro hxs
      rcases hxs x List.mem_cons_self with ⟨y, hy, hPy⟩
      rcases ih (fun x' hx' => hxs x' (List.mem_cons_of_mem x hx')) with ⟨ys, hys, ⟨hlen, hPys⟩⟩
      refine ⟨y :: ys, ?_, ⟨by simp [hlen], ?_⟩⟩
      · simp [List.mapM_cons, hy, hys, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · intro k hk
        cases k with
        | zero => exact hPy
        | succ k =>
          have hk' : k < ys.length := by simpa using hk
          exact hPys k hk'
  rcases haux (List.range n) (fun i hi => hf i (List.mem_range.mp hi)) with ⟨ys, hys, ⟨hlen, hPys⟩⟩
  refine ⟨ys, hys, by simpa using hlen, ?_⟩
  intro i hi
  have hP := hPys i hi
  simpa using hP

theorem lagrangePolysForCompletePoints_spec_aux (n : Nat) (hn : n < 2 ^ 16) :
    ∃ cps, lagrangePolysForCompletePoints n = .ok cps ∧ cps.length = n ∧
      ∀ i (h : i < cps.length), cps[i].coefficients.length = n ∧
        polyOf cps[i].coefficients = Lagrange.basis (Finset.range n) idxPt i := by
  unfold lagrangePolysForCompletePoints
  exact range_mapM_except_ok n (fun i => PolyConst.lagrangeInterpolatePt n (onesPts n) i)
    (fun i cp => cp.coefficients.length = n ∧
      polyOf cp.coefficients = Lagrange.basis (Finset.range n) idxPt i)
    (fun i hi => polyConst_lagrangeInterpolatePt_spec n i hn hi)

end CryptoVerification.SpqrV1Sync.Erasure.ConstPolys
