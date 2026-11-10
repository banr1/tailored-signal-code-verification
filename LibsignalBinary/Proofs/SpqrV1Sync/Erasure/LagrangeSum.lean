/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1Sync.Erasure.LagrangeSum

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.GF16Field
open CryptoVerification.SpqrV1Sync.Erasure
open Polynomial

@[simp] theorem polyOf_nil : polyOf [] = 0 := by
  simp [polyOf]

theorem polyOf_cons (c : GF16) (cs : List GF16) :
    polyOf (c :: cs) = C c + X * polyOf cs := by
  unfold polyOf
  simp only [List.length_cons]
  rw [Finset.sum_range_succ', add_comm]
  simp only [List.getD_cons_zero, pow_zero, mul_one, List.getD_cons_succ]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem length_addAssignCoeffs (as bs : List GF16) :
    (Poly.addAssignCoeffs as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil =>
    cases bs <;> simp [Poly.addAssignCoeffs]
  | cons a as ih =>
    cases bs with
    | nil => simp [Poly.addAssignCoeffs]
    | cons b bs =>
      simp only [Poly.addAssignCoeffs, List.length_cons, ih bs]
      omega

theorem polyOf_addAssignCoeffs (as bs : List GF16) :
    polyOf (Poly.addAssignCoeffs as bs) = polyOf as + polyOf bs := by
  induction as generalizing bs with
  | nil =>
    cases bs <;> simp [Poly.addAssignCoeffs]
  | cons a as ih =>
    cases bs with
    | nil => simp [Poly.addAssignCoeffs]
    | cons b bs =>
      simp only [Poly.addAssignCoeffs, polyOf_cons, ih bs, ← add_eq, map_add, mul_add]
      abel

theorem polyOf_map_mul_right (m : GF16) (cs : List GF16) :
    polyOf (cs.map fun c => GF16.mul c m) = C m * polyOf cs := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, polyOf_cons, ih]
    rw [← mul_eq, mul_comm c m, map_mul]
    ring

private theorem parallelMult_eq_map (a : GF16) (xs : List GF16) :
    parallelMult a xs = xs.map (fun x => GF16.mul x a) := by
  match xs with
  | [] => rfl
  | [x] => rfl
  | x1 :: x2 :: rest =>
    simp only [parallelMult, mul2U16, List.map_cons]
    rw [GF16Field.mul_comm' x1 a, GF16Field.mul_comm' x2 a, parallelMult_eq_map a rest]
    rfl

theorem polyOf_multAssign (p : Poly) (m : GF16) :
    polyOf (p.multAssign m).coefficients = C m * polyOf p.coefficients := by
  simp only [Poly.multAssign, parallelMult_eq_map, polyOf_map_mul_right]

theorem length_multAssign (p : Poly) (m : GF16) :
    (p.multAssign m).coefficients.length = p.coefficients.length := by
  simp [Poly.multAssign, parallelMult_eq_map]

private def lagrangeStep (out : Poly) (q : Pt × Poly) : Poly :=
  out.addAssign (q.2.multAssign q.1.y)

private theorem foldl_lagrangeStep_polyOf (qs : List (Pt × Poly)) (acc : Poly) :
    polyOf (qs.foldl lagrangeStep acc).coefficients =
      polyOf acc.coefficients +
        (qs.map fun q => C q.1.y * polyOf q.2.coefficients).sum := by
  induction qs generalizing acc with
  | nil => simp
  | cons q qs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    simp only [lagrangeStep, Poly.addAssign, polyOf_addAssignCoeffs, polyOf_multAssign, add_assoc]

private theorem foldl_lagrangeStep_length_of_len (m : Nat) (qs : List (Pt × Poly)) (acc : Poly)
    (hacc : acc.coefficients.length = m)
    (hqs : ∀ q ∈ qs, q.2.coefficients.length = m) :
    (qs.foldl lagrangeStep acc).coefficients.length = m := by
  induction qs generalizing acc with
  | nil => exact hacc
  | cons q qs ih =>
    apply ih
    · simp only [lagrangeStep, Poly.addAssign, length_addAssignCoeffs, length_multAssign,
        hacc, hqs q List.mem_cons_self, max_self]
    · intro q' hq'
      exact hqs q' (List.mem_cons_of_mem q hq')

private theorem foldl_lagrangeStep_length_zero (m : Nat) (qs : List (Pt × Poly)) (cap : Nat)
    (hqs : ∀ q ∈ qs, q.2.coefficients.length = m) :
    (qs.foldl lagrangeStep (Poly.zero cap)).coefficients.length =
      if qs = [] then 0 else m := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    simp only [List.foldl_cons, reduceCtorEq, ↓reduceIte]
    apply foldl_lagrangeStep_length_of_len m qs
    · simp only [lagrangeStep, Poly.addAssign, Poly.zero, length_addAssignCoeffs,
        List.length_nil, length_multAssign, hqs q List.mem_cons_self, Nat.zero_max]
    · intro q' hq'
      exact hqs q' (List.mem_cons_of_mem q hq')

theorem lagrangeSum_spec_aux (pts : List Pt) (polys : List Poly) (m : Nat)
    (hlen : pts.length = polys.length) (hm : ∀ p ∈ polys, p.coefficients.length = m) :
    (Poly.lagrangeSum pts polys).coefficients.length = (if polys = [] then 0 else m) ∧
      polyOf (Poly.lagrangeSum pts polys).coefficients =
        ((pts.zip polys).map fun q => C q.1.y * polyOf q.2.coefficients).sum := by
  have hfold : Poly.lagrangeSum pts polys =
      (pts.zip polys).foldl lagrangeStep (Poly.zero pts.length) := rfl
  have hqs : ∀ q ∈ pts.zip polys, q.2.coefficients.length = m := by
    intro q hq
    exact hm q.2 (List.of_mem_zip hq).2
  have hzip_nil : (pts.zip polys = []) ↔ (polys = []) := by
    cases pts with
    | nil =>
      cases polys with
      | nil => simp
      | cons _ _ => simp at hlen
    | cons _ _ =>
      cases polys with
      | nil => simp
      | cons _ _ => simp
  rw [hfold]
  refine ⟨?_, ?_⟩
  · rw [foldl_lagrangeStep_length_zero m (pts.zip polys) pts.length hqs]
    by_cases hp : polys = []
    · simp [hp]
    · have hzn : pts.zip polys ≠ [] := mt hzip_nil.mp hp
      simp [hp, hzn]
  · rw [foldl_lagrangeStep_polyOf, Poly.zero, polyOf_nil, zero_add]

end CryptoVerification.SpqrV1Sync.Erasure.LagrangeSum
