/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.Prepare

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1Sync.Erasure.Complete

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.GF16Field
open CryptoVerification.SpqrV1Sync.Erasure.Prepare
open Polynomial

theorem prod_map_eq_mul_eraseIdx {α M : Type*} [CommMonoid M] (f : α → M) :
    ∀ (xs : List α) (i : Nat) (hi : i < xs.length),
      (xs.map f).prod = f xs[i] * ((xs.eraseIdx i).map f).prod
  | [], _, hi => by contradiction
  | _ :: _, 0, _ => by simp
  | x :: xs, i + 1, hi => by
    have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
    simp only [List.map_cons, List.prod_cons, List.getElem_cons_succ, List.eraseIdx_cons_succ,
      prod_map_eq_mul_eraseIdx f xs i hi']
    rw [← mul_assoc, mul_comm (f x), mul_assoc]

private theorem list_eq_append_last {α : Type*} :
    ∀ (xs : List α) (n : Nat), xs.length = n + 1 →
      ∃ (init : List α) (last : α), xs = init ++ [last] ∧ init.length = n
  | [], _, h => by simp at h
  | [x], 0, _ => ⟨[], x, rfl, rfl⟩
  | [x], n + 1, h => by simp at h
  | x :: y :: xs, 0, h => by simp at h
  | x :: y :: xs, n + 1, h => by
    have h' : (y :: xs).length = n + 1 := by simpa using h
    obtain ⟨init, last, heq, hlen⟩ := list_eq_append_last (y :: xs) n h'
    exact ⟨x :: init, last, by simp [heq], by simp [hlen]⟩

theorem lagrangeCompleteDivLoop_spec (pix scale : GF16) (len : Nat) :
    ∀ (rem : Nat) (pre : List GF16) (cur : GF16) (q : List GF16) (j : Nat),
      pre.length = rem →
      j = q.length + 1 →
      len = rem + 1 + q.length →
      ∃ (r : GF16) (q' : List GF16),
        Poly.lagrangeCompleteDivLoop pix scale len j rem
          (pre ++ cur :: q.map (fun c => GF16.mul c scale)) =
          .ok (r :: q'.map (fun c => GF16.mul c scale)) ∧
        q'.length = rem + q.length ∧
        C r + (X - C pix) * polyOf q' =
          polyOf (pre ++ [cur]) + (X - C pix) * X ^ rem * polyOf q := by
  intro rem
  induction rem with
  | zero =>
    intro pre cur q j hpre hj hlen
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
    subst hnil
    refine ⟨cur, q, ?_, by omega, ?_⟩
    · simp [Poly.lagrangeCompleteDivLoop]
    · simp
  | succ m ih =>
    intro pre cur q j hpre hj hlen
    obtain ⟨init, prev, rfl, hinit⟩ := list_eq_append_last pre m hpre
    let suf := q.map (fun c => GF16.mul c scale)
    have hnotgt : ¬ (j > len) := by omega
    have hidx : len - j = m + 1 := by omega
    have hsub1 : m + 1 - 1 = m := by omega
    have hcoeffs : (init ++ [prev]) ++ cur :: suf = init ++ prev :: cur :: suf := by
      simp [List.append_assoc]
    have hget_idx : (init ++ prev :: cur :: suf)[m + 1]? = some cur := by
      rw [← hinit, List.getElem?_append_right (by omega)]
      have : init.length + 1 - init.length = 1 := by omega
      rw [this]
      rfl
    have hget_prev : (init ++ prev :: cur :: suf)[m]? = some prev := by
      rw [← hinit, List.getElem?_append_right (Nat.le_refl _)]
      simp
    have hset1 : (init ++ prev :: cur :: suf).set (m + 1) (GF16.mul cur scale) =
        init ++ prev :: GF16.mul cur scale :: suf := by
      rw [← hinit, List.set_append_right _ _ (by omega)]
      have : init.length + 1 - init.length = 1 := by omega
      rw [this]
      rfl
    have hset2 : (init ++ prev :: GF16.mul cur scale :: suf).set m
        (GF16.add prev (GF16.mul cur pix)) =
        init ++ (GF16.add prev (GF16.mul cur pix)) :: (cur :: q).map (fun c => GF16.mul c scale) := by
      rw [← hinit, List.set_append_right _ _ (Nat.le_refl _)]
      simp [suf]
    rw [hcoeffs, Poly.lagrangeCompleteDivLoop]
    simp only [hnotgt, ↓reduceIte, hidx, beq_iff_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      hsub1, hget_idx, hget_prev, hset1, hset2]
    obtain ⟨r, q', hloop, hq'len, hpoly⟩ :=
      ih init (GF16.add prev (GF16.mul cur pix)) (cur :: q) (j + 1) hinit (by simp [hj]) (by simp [hlen]; omega)
    refine ⟨r, q', hloop, by simp at hq'len; omega, ?_⟩
    rw [hpoly]
    simp only [List.append_assoc, List.singleton_append, polyOf_append, hinit, polyOf_cons,
      polyOf_nil, ← add_eq, ← mul_eq, map_add, map_mul, pow_succ']
    generalize (X : GF16[X]) ^ m = xm
    ring

theorem lagrangeInterpolateComplete_spec (pts : List Pt) (t : Poly) (i : Nat) (hi : i < pts.length)
    (hlen : t.coefficients.length = pts.length + 1)
    (ht : polyOf t.coefficients = (pts.map fun pt => X - C pt.x).prod) :
    ∃ w : Poly, t.lagrangeInterpolateComplete pts i = .ok w ∧
      w.coefficients.length = pts.length + 1 ∧
      polyOf w.coefficients.tail =
        C (GF16.div pts[i].y (Poly.lagrangeDenominator pts[i].x pts)) *
          ((pts.eraseIdx i).map fun pt => X - C pt.x).prod := by
  unfold Poly.lagrangeInterpolateComplete
  have hget : pts[i]? = some pts[i] := List.getElem?_eq_getElem hi
  have hnotle : ¬ (t.coefficients.length ≤ 1) := by omega
  obtain ⟨pre, cur, hcoeffs, hpre⟩ := list_eq_append_last t.coefficients pts.length hlen
  let scale := GF16.div pts[i].y (Poly.lagrangeDenominator pts[i].x pts)
  have hsub : t.coefficients.length - 1 = pts.length := by omega
  obtain ⟨r, q', hloop, hq'len, hpoly⟩ :=
    lagrangeCompleteDivLoop_spec pts[i].x scale t.coefficients.length
      pts.length pre cur [] 1 hpre rfl (by omega)
  simp only [List.map_nil, polyOf_nil, mul_zero, add_zero] at hloop hpoly
  rw [← hcoeffs] at hloop hpoly
  rw [hget]
  simp only [hnotle, ↓reduceIte, hsub]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [hloop]
  dsimp only
  refine ⟨{ coefficients := r :: q'.map (fun c => GF16.mul c scale) }, rfl, ?_, ?_⟩
  · simp [hq'len]
  · simp only [List.tail_cons, polyOf_map_mul]
    have hprod : (pts.map fun pt => X - C pt.x).prod =
        (X - C pts[i].x) * ((pts.eraseIdx i).map fun pt => X - C pt.x).prod :=
      prod_map_eq_mul_eraseIdx (fun pt : Pt => X - C pt.x) pts i hi
    have heq : C r + (X - C pts[i].x) * polyOf q' =
        (X - C pts[i].x) * ((pts.eraseIdx i).map fun pt => X - C pt.x).prod := by
      rw [hpoly, ht, hprod]
    have hr0 : r = 0 := by
      have heval := congrArg (Polynomial.eval pts[i].x) heq
      simp only [eval_add, eval_C, eval_mul, eval_sub, eval_X, sub_self, zero_mul, add_zero] at heval
      exact heval
    rw [hr0, map_zero, zero_add] at heq
    have hq' : polyOf q' = ((pts.eraseIdx i).map fun pt => X - C pt.x).prod :=
      mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero pts[i].x) heq
    rw [hq']

end CryptoVerification.SpqrV1Sync.Erasure.Complete
