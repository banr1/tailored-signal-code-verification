/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs
import LibsignalBinary.Proofs.SpqrV1Sync.ErasurePoly

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1Sync.Erasure.PointAt

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.GF16Field
open CryptoVerification.SpqrV1Sync.Erasure
open Polynomial

theorem needed_lt_two_pow_16 {len : Nat} (hlen : len ≤ 2 ^ 20) (j : Nat) :
    needed len j < 2 ^ 16 := by
  unfold needed
  split <;> omega

@[simp] theorem msgPoints_length (msg : List (BitVec 8)) :
    (msgPoints msg).length = 16 := by
  simp [msgPoints]

theorem msgPoints_getElem (msg : List (BitVec 8)) (j : Nat) (hj : j < 16) :
    (msgPoints msg)[j]'(by simp [hj]) =
      ⟨(List.range (needed msg.length j)).map fun k => msgVal msg (16 * k + j)⟩ := by
  simp [msgPoints]

theorem msgPoints_getElem? (msg : List (BitVec 8)) (j : Nat) (hj : j < 16) :
    (msgPoints msg)[j]? =
      some ⟨(List.range (needed msg.length j)).map fun k => msgVal msg (16 * k + j)⟩ := by
  have hlen : j < (msgPoints msg).length := by simp [hj]
  rw [List.getElem?_eq_getElem hlen, msgPoints_getElem msg j hj]

theorem eval_msgPoly_at_node (msg : List (BitVec 8)) (hlen : msg.length ≤ 2 ^ 20)
    (j idx : Nat) (hidx : idx < needed msg.length j) :
    (msgPoly msg j).eval (idxPt idx) = msgVal msg (16 * idx + j) := by
  unfold msgPoly
  have hinj : Set.InjOn idxPt (Finset.range (needed msg.length j)) :=
    idxPt_injOn (needed msg.length j) (Nat.le_of_lt (needed_lt_two_pow_16 hlen j))
  exact Lagrange.eval_interpolate_at_node (fun k => msgVal msg (16 * k + j)) hinj
    (Finset.mem_range.mpr hidx)

theorem fromCompletePoints_msgPoints_elem (msg : List (BitVec 8)) (hlen : msg.length ≤ 2 ^ 20)
    (i : Nat) :
    let ys := (List.range (needed msg.length i)).map fun k => msgVal msg (16 * k + i)
    ∃ p : Poly, Poly.fromCompletePoints (PolyEncoder.enumeratePts 0 ys) = .ok (.ok p) ∧
      p.coefficients.length = needed msg.length i ∧
      polyOf p.coefficients = msgPoly msg i := by
  intro ys
  have hys_len : ys.length = needed msg.length i := by simp [ys]
  have hys_lt : ys.length < 2 ^ 16 := by
    rw [hys_len]
    exact needed_lt_two_pow_16 hlen i
  obtain ⟨p, hp_ok, hp_len, hp_poly⟩ := fromCompletePoints_spec ys hys_lt
  refine ⟨p, hp_ok, hp_len.trans hys_len, ?_⟩
  rw [hp_poly, hys_len]
  unfold msgPoly
  apply Lagrange.interpolate_eq_of_values_eq_on
  intro k hk
  have hk_lt : k < needed msg.length i := Finset.mem_range.mp hk
  have hk_ys : k < ys.length := by omega
  simp [ys, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_ys]

theorem pointsToPolysLoop_spec (msg : List (BitVec 8)) (hlen : msg.length ≤ 2 ^ 20) :
    ∀ (rem i : Nat) (acc : List Poly),
      i + rem = 16 →
      acc.length = i →
      (∀ k (hk : k < acc.length),
        acc[k].coefficients.length = needed msg.length k ∧
          polyOf acc[k].coefficients = msgPoly msg k) →
      ∃ polys : List Poly,
        PolyEncoder.pointsToPolysLoop (msgPoints msg) i rem acc = .ok polys ∧
          polys.length = 16 ∧
          ∀ k (hk : k < polys.length),
            polys[k].coefficients.length = needed msg.length k ∧
              polyOf polys[k].coefficients = msgPoly msg k
  | 0, i, acc, hsum, hacc_len, hacc => by
    have hi : i = 16 := by omega
    subst hi
    exact ⟨acc, rfl, hacc_len, hacc⟩
  | rem + 1, i, acc, hsum, hacc_len, hacc => by
    have hi : i < 16 := by omega
    obtain ⟨p, hp_ok, hp_len, hp_poly⟩ := fromCompletePoints_msgPoints_elem msg hlen i
    have hstep :
        PolyEncoder.pointsToPolysLoop (msgPoints msg) i (rem + 1) acc =
          PolyEncoder.pointsToPolysLoop (msgPoints msg) (i + 1) rem (acc ++ [p]) := by
      simp [PolyEncoder.pointsToPolysLoop, msgPoints_getElem? msg i hi, hp_ok, Bind.bind, Except.bind]
    rw [hstep]
    apply pointsToPolysLoop_spec msg hlen rem (i + 1) (acc ++ [p]) (by omega)
    · simp [hacc_len]
    · intro k hk
      rw [List.length_append, List.length_singleton, hacc_len] at hk
      by_cases hki : k < i
      · have hk_acc : k < acc.length := by omega
        rw [List.getElem_append_left hk_acc]
        exact hacc k hk_acc
      · have hkeq : k = i := by omega
        subst hkeq
        have hk_ge : acc.length ≤ k := by omega
        simp [List.getElem_append_right hk_ge, hacc_len, hp_len, hp_poly]

theorem pointAt_polys_eval (msg : List (BitVec 8)) (e : PolyEncoder) (polys : List Poly)
    (he_s : e.s = .polys polys) (hpolys_len : polys.length = 16)
    (hpolys : ∀ k (hk : k < polys.length),
      polys[k].coefficients.length = needed msg.length k ∧
        polyOf polys[k].coefficients = msgPoly msg k)
    (j idx : Nat) (hj : j < 16) :
    e.pointAt j idx = .ok (e, (msgPoly msg j).eval (idxPt idx)) := by
  rcases e with ⟨e_idx, e_s⟩
  dsimp at he_s
  subst he_s
  have hj_len : j < polys.length := by omega
  have hp_get : polys[j]? = some polys[j] := List.getElem?_eq_getElem hj_len
  have hcomp := computeAt_spec polys[j] (idxPt idx)
  have hpoly_eq : polyOf polys[j].coefficients = msgPoly msg j := (hpolys j hj_len).2
  unfold PolyEncoder.pointAt
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [hp_get]
  dsimp only
  rw [show GF16.new (BitVec.ofNat 16 idx) = idxPt idx from rfl, hcomp, hpoly_eq]

theorem pointAt_spec_impl (msg : List (BitVec 8)) (e : PolyEncoder) (he : EncInv msg e)
    (hlen : msg.length ≤ 2 ^ 20) (j idx : Nat) (hj : j < 16) (_hidx : idx < 2 ^ 16) :
    ∃ e', e.pointAt j idx = .ok (e', (msgPoly msg j).eval (idxPt idx)) ∧
      EncInv msg e' ∧ e'.idx = e.idx := by
  rcases he with he_pts | ⟨polys, he_polys, hpolys_len, hpolys⟩
  · rcases e with ⟨e_idx, e_s⟩
    dsimp at he_pts
    subst he_pts
    by_cases hlt : idx < needed msg.length j
    · refine ⟨{ idx := e_idx, s := .points (msgPoints msg) }, ?_, Or.inl rfl, rfl⟩
      have hpt : (msgPoints msg)[j]? =
          some ⟨(List.range (needed msg.length j)).map fun k => msgVal msg (16 * k + j)⟩ :=
        msgPoints_getElem? msg j hj
      have hval :
          ((List.range (needed msg.length j)).map fun k => msgVal msg (16 * k + j))[idx]? =
            some (msgVal msg (16 * idx + j)) := by
        have hlen_map :
            idx < ((List.range (needed msg.length j)).map fun k => msgVal msg (16 * k + j)).length := by
          simp [hlt]
        rw [List.getElem?_eq_getElem hlen_map]
        simp
      unfold PolyEncoder.pointAt
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
      rw [hpt]
      dsimp only
      rw [hval]
      rw [eval_msgPoly_at_node msg hlen j idx hlt]
    · obtain ⟨polys, hloop, hpolys_len, hpolys⟩ :=
        pointsToPolysLoop_spec msg hlen 16 0 [] rfl rfl (by intro k hk; simp at hk)
      let e' : PolyEncoder := { idx := e_idx, s := .polys polys }
      refine ⟨e', ?_, Or.inr ⟨polys, rfl, hpolys_len, hpolys⟩, rfl⟩
      have hpt : (msgPoints msg)[j]? =
          some ⟨(List.range (needed msg.length j)).map fun k => msgVal msg (16 * k + j)⟩ :=
        msgPoints_getElem? msg j hj
      have hval :
          ((List.range (needed msg.length j)).map fun k => msgVal msg (16 * k + j))[idx]? =
            none := by
        apply List.getElem?_eq_none
        simp
        omega
      have hj_len : j < polys.length := by omega
      have hp_get : polys[j]? = some polys[j] := List.getElem?_eq_getElem hj_len
      have hcomp := computeAt_spec polys[j] (idxPt idx)
      have hpoly_eq : polyOf polys[j].coefficients = msgPoly msg j := (hpolys j hj_len).2
      unfold PolyEncoder.pointAt
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
      rw [hpt]
      dsimp only
      rw [hval]
      have hnum : NUM_POLYS = 16 := rfl
      rw [hnum, hloop]
      dsimp only
      rw [hp_get]
      dsimp only
      rw [show GF16.new (BitVec.ofNat 16 idx) = idxPt idx from rfl, hcomp, hpoly_eq]
  · refine ⟨e, ?_, Or.inr ⟨polys, he_polys, hpolys_len, hpolys⟩, rfl⟩
    exact pointAt_polys_eval msg e polys he_polys hpolys_len hpolys j idx hj

end CryptoVerification.SpqrV1Sync.Erasure.PointAt
