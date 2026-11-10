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

namespace CryptoVerification.SpqrV1Sync.Erasure.Prepare

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.GF16Field
open Polynomial

@[simp] theorem polyOf_nil : polyOf [] = 0 := by
  simp [polyOf]

@[simp] theorem polyOf_cons (c : GF16) (cs : List GF16) :
    polyOf (c :: cs) = C c + X * polyOf cs := by
  unfold polyOf
  rw [List.length_cons, Finset.sum_range_succ']
  simp only [List.getD, List.getElem?_cons_zero, Option.getD_some, pow_zero, mul_one,
    List.getElem?_cons_succ, pow_succ']
  rw [add_comm, Finset.mul_sum]
  have hsum : (∑ k ∈ Finset.range cs.length, C (cs[k]?.getD GF16.ZERO) * (X * X ^ k)) =
      ∑ k ∈ Finset.range cs.length, X * (C (cs[k]?.getD GF16.ZERO) * X ^ k) :=
    Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _
  rw [hsum]

@[simp] theorem polyOf_singleton (c : GF16) : polyOf [c] = C c := by
  simp [polyOf_cons]

theorem polyOf_append (as bs : List GF16) :
    polyOf (as ++ bs) = polyOf as + X ^ as.length * polyOf bs := by
  induction as with
  | nil => simp
  | cons a as ih =>
    rw [List.cons_append, polyOf_cons, ih, polyOf_cons, List.length_cons, pow_succ']
    generalize (X : GF16[X]) ^ as.length = xm
    ring

@[simp] theorem polyOf_replicate_zero (n : Nat) :
    polyOf (List.replicate n GF16.ZERO) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, polyOf_cons, ih, ← zero_eq, map_zero, mul_zero, add_zero]

theorem polyOf_map_mul (cs : List GF16) (s : GF16) :
    polyOf (cs.map (fun c => GF16.mul c s)) = C s * polyOf cs := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, polyOf_cons, ih, polyOf_cons, ← mul_eq, map_mul]
    ring

/-- Pure functional model of one `multXdiffAssignTrailingLoop` pass over `a :: cs`. -/
def xdiffStep (d : GF16) : GF16 → List GF16 → List GF16
  | a, [] => [a]
  | a, c :: cs => GF16.sub a (GF16.mul c d) :: xdiffStep d c cs

@[simp] theorem length_xdiffStep (d a : GF16) (cs : List GF16) :
    (xdiffStep d a cs).length = cs.length + 1 := by
  induction cs generalizing a with
  | nil => rfl
  | cons c cs ih => simp [xdiffStep, ih]

theorem polyOf_xdiffStep (d a : GF16) (cs : List GF16) :
    polyOf (xdiffStep d a cs) = C a + (X - C d) * polyOf cs := by
  induction cs generalizing a with
  | nil => simp [xdiffStep]
  | cons c cs ih =>
    rw [xdiffStep, polyOf_cons, ih, polyOf_cons]
    have hsub : GF16.sub a (GF16.mul c d) = a - c * d := rfl
    rw [hsub, map_sub, map_mul]
    ring

theorem multXdiffAssignTrailingLoop_eq_xdiffStep (d : GF16) (cs : List GF16) :
    ∀ (pre : List GF16) (a : GF16),
      Poly.multXdiffAssignTrailingLoop d (pre.length + 1) cs.length (pre ++ a :: cs) =
        .ok (pre ++ xdiffStep d a cs) := by
  induction cs with
  | nil =>
    intro pre a
    simp [Poly.multXdiffAssignTrailingLoop, xdiffStep]
  | cons c cs ih =>
    intro pre a
    have hget0 : (pre ++ a :: c :: cs)[pre.length]? = some a := by
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp
    have hget1 : (pre ++ a :: c :: cs)[pre.length + 1]? = some c := by
      rw [List.getElem?_append_right (by omega)]
      have hsub : pre.length + 1 - pre.length = 1 := by omega
      rw [hsub]
      rfl
    have hset : (pre ++ a :: c :: cs).set pre.length (GF16.sub a (GF16.mul c d)) =
        (pre ++ [GF16.sub a (GF16.mul c d)]) ++ c :: cs := by
      rw [List.set_append_right _ _ (Nat.le_refl _)]
      simp [List.append_assoc]
    rw [List.length_cons, Poly.multXdiffAssignTrailingLoop]
    simp only [beq_iff_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, hget1, hget0, hset]
    have hidx : pre.length + 1 + 1 = (pre ++ [GF16.sub a (GF16.mul c d)]).length + 1 := by simp
    rw [hidx, ih (pre ++ [GF16.sub a (GF16.mul c d)]) c]
    simp [List.append_assoc, xdiffStep]

theorem multXdiffAssignTrailing_replicate (m : Nat) (acc : List GF16) (hacc : 0 < acc.length)
    (d : GF16) :
    Poly.multXdiffAssignTrailing
      { coefficients := List.replicate (m + 1) GF16.ZERO ++ acc } (m + 1) d =
      .ok { coefficients := List.replicate m GF16.ZERO ++ xdiffStep d GF16.ZERO acc } := by
  unfold Poly.multXdiffAssignTrailing
  have hnotge : ¬ (m + 1 ≥ (List.replicate (m + 1) GF16.ZERO ++ acc).length) := by
    rw [List.length_append, List.length_replicate]
    omega
  have hsub : (List.replicate (m + 1) GF16.ZERO ++ acc).length - (m + 1) = acc.length := by
    simp
  have hsplit : List.replicate (m + 1) GF16.ZERO ++ acc =
      List.replicate m GF16.ZERO ++ GF16.ZERO :: acc := by
    rw [List.replicate_succ', List.append_assoc]
    rfl
  simp only [hnotge, ↓reduceIte, hsub]
  rw [hsplit]
  have hm : m + 1 = (List.replicate m GF16.ZERO).length + 1 := by simp
  rw [hm, multXdiffAssignTrailingLoop_eq_xdiffStep]
  rfl

theorem lagrangeInterpolatePrepareLoop_spec (pts : List Pt) :
    ∀ (rem i : Nat) (acc : List GF16),
      i + rem = pts.length →
      acc.length = i + 1 →
      polyOf acc = ((pts.take i).map fun pt => X - C pt.x).prod →
      ∃ t : Poly,
        Poly.lagrangeInterpolatePrepareLoop pts pts.length i rem
          { coefficients := List.replicate rem GF16.ZERO ++ acc } = .ok t ∧
        t.coefficients.length = pts.length + 1 ∧
        polyOf t.coefficients = (pts.map fun pt => X - C pt.x).prod := by
  intro rem
  induction rem with
  | zero =>
    intro i acc hsum hlen hpoly
    have hi : i = pts.length := by omega
    subst hi
    refine ⟨{ coefficients := acc }, ?_, hlen, ?_⟩
    · simp [Poly.lagrangeInterpolatePrepareLoop]
    · simpa [List.take_length] using hpoly
  | succ m ih =>
    intro i acc hsum hlen hpoly
    have hi_lt : i < pts.length := by omega
    have hnotgt : ¬ (i > pts.length) := by omega
    have hsub : pts.length - i = m + 1 := by omega
    have hget : pts[i]? = some pts[i] := List.getElem?_eq_getElem hi_lt
    have hacc_pos : 0 < acc.length := by omega
    rw [Poly.lagrangeInterpolatePrepareLoop, hget]
    simp only [hnotgt, ↓reduceIte, hsub]
    have hstep := multXdiffAssignTrailing_replicate m acc hacc_pos pts[i].x
    rw [hstep]
    dsimp only [Bind.bind, Except.bind]
    apply ih (i + 1) (xdiffStep pts[i].x GF16.ZERO acc)
    · omega
    · simp [hlen]
    · have htake : pts.take (i + 1) = pts.take i ++ [pts[i]] := by
        rw [List.take_add_one, hget]
        rfl
      rw [polyOf_xdiffStep, ← zero_eq, map_zero, zero_add, hpoly, mul_comm,
        htake, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]

theorem lagrangeInterpolatePrepare_spec_usize (pts : List Pt) (hlen : pts.length + 1 ≤ USIZE_MAX) :
    ∃ t : Poly, Poly.lagrangeInterpolatePrepare pts = .ok t ∧
      t.coefficients.length = pts.length + 1 ∧
      polyOf t.coefficients = (pts.map fun pt => X - C pt.x).prod := by
  unfold Poly.lagrangeInterpolatePrepare
  have hnotgt : ¬ (pts.length + 1 > USIZE_MAX) := by omega
  simp only [hnotgt, ↓reduceIte]
  exact lagrangeInterpolatePrepareLoop_spec pts pts.length 0 [GF16.ONE]
    (Nat.zero_add _) rfl (by simp [← one_eq])

theorem lagrangeInterpolatePrepare_spec (pts : List Pt) (hlen : pts.length < 2 ^ 16) :
    ∃ t : Poly, Poly.lagrangeInterpolatePrepare pts = .ok t ∧
      t.coefficients.length = pts.length + 1 ∧
      polyOf t.coefficients = (pts.map fun pt => X - C pt.x).prod := by
  apply lagrangeInterpolatePrepare_spec_usize
  unfold USIZE_MAX
  omega

end CryptoVerification.SpqrV1Sync.Erasure.Prepare
