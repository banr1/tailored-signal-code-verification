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

namespace CryptoVerification.SpqrV1Sync.Erasure

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.GF16Field
open Polynomial

namespace IdxPt

theorem idxPt_injOn_proof (n : Nat) (hn : n ≤ 2 ^ 16) : Set.InjOn idxPt (Finset.range n) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_range] at ha hb
  have hval : (idxPt a).value = (idxPt b).value := congrArg GF16.value hab
  simp only [idxPt, GF16.new] at hval
  have hnat := congrArg BitVec.toNat hval
  simp only [BitVec.toNat_ofNat] at hnat
  omega

end IdxPt

namespace DegreePolyOf

theorem degree_polyOf_lt_proof (cs : List GF16) : (polyOf cs).degree < cs.length := by
  unfold polyOf
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe cs.length)).mpr ?_
  intro k hk
  rw [Finset.mem_range] at hk
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le k (cs.getD k GF16.ZERO)) ?_
  exact WithBot.coe_lt_coe.mpr hk

end DegreePolyOf

namespace ComputeAt

theorem computeAtPowersLoop_eq (x : GF16) :
    ∀ (rem i : Nat), 2 ≤ i →
      Poly.computeAtPowersLoop i rem ((List.range i).map (x ^ ·)) =
        .ok ((List.range (i + rem)).map (x ^ ·))
  | 0, i, _ => by
    simp [Poly.computeAtPowersLoop]
  | rem + 1, i, hi => by
    have h1 : i / 2 < i := by omega
    have h2 : i / 2 + i % 2 < i := by omega
    have hadd : i / 2 + (i / 2 + i % 2) = i := by omega
    rw [Poly.computeAtPowersLoop]
    simp only [List.getElem?_map, List.getElem?_range h1, List.getElem?_range h2, Option.map_some,
      ← mul_eq, ← pow_add, hadd]
    have Happ : (List.range i).map (x ^ ·) ++ [x ^ i] = (List.range (i + 1)).map (x ^ ·) := by
      rw [List.range_succ, List.map_append, List.map_singleton]
    rw [Happ, computeAtPowersLoop_eq x rem (i + 1) (by omega)]
    rw [Nat.add_right_comm, Nat.add_assoc]

theorem foldl_add_mul_eq_sum :
    ∀ (pairs : List (GF16 × GF16)) (init : GF16),
      pairs.foldl (fun out (a, b) => GF16.add out (GF16.mul a b)) init =
        init + (pairs.map (fun (a, b) => a * b)).sum
  | [], init => by
    rw [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | (a, b) :: rest, init => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [foldl_add_mul_eq_sum rest (init.add (a.mul b)), ← mul_eq a b, ← add_eq init (a * b), add_assoc]

theorem sum_range_eq_list_sum (f : Nat → GF16) :
    ∀ n : Nat, (∑ k ∈ Finset.range n, f k) = ((List.range n).map f).sum
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton, sum_range_eq_list_sum f n]

theorem map_zip_range_pow (cs : List GF16) (x : GF16) :
    ((cs.zip ((List.range cs.length).map (x ^ ·))).map (fun (a, b) => a * b)) =
      (List.range cs.length).map (fun k => cs.getD k GF16.ZERO * x ^ k) := by
  apply List.ext_getElem
  · simp
  · intro k hk1 hk2
    simp only [List.length_map, List.length_range] at hk2
    simp [List.getD_eq_getElem?_getD, hk2]

theorem zip_two_eq_zip_range (cs : List GF16) (x : GF16) (hlen : cs.length ≤ 2) :
    cs.zip [GF16.ONE, x] = cs.zip ((List.range cs.length).map (x ^ ·)) := by
  rcases cs with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, cs⟩⟩⟩
  · rfl
  · simp [List.range_succ]
  · simp [List.range_succ]
  · simp only [List.length_cons] at hlen
    omega

theorem computeAt_spec_proof (p : Poly) (x : GF16) :
    p.computeAt x = .ok ((polyOf p.coefficients).eval x) := by
  unfold Poly.computeAt
  have hxs0 : ([GF16.ONE, x] : List GF16) = (List.range 2).map (x ^ ·) := by
    simp [List.range_succ]
  have hzip :
      (do
        let xs ←
          if p.coefficients.length ≤ 2 then .ok [GF16.ONE, x]
          else Poly.computeAtPowersLoop 2 (p.coefficients.length - 2) [GF16.ONE, x]
        let pairs := p.coefficients.zip xs
        pure (pairs.foldl (fun out (a, b) => GF16.add out (GF16.mul a b)) GF16.ZERO) :
          Except PolyPanic GF16) =
        .ok ((p.coefficients.zip ((List.range p.coefficients.length).map (x ^ ·))).foldl
          (fun out (a, b) => GF16.add out (GF16.mul a b)) GF16.ZERO) := by
    split_ifs with hle
    · simp only [bind, Except.bind, pure, Except.pure, zip_two_eq_zip_range p.coefficients x hle]
    · rw [hxs0, computeAtPowersLoop_eq x (p.coefficients.length - 2) 2 (by omega)]
      have hlen : 2 + (p.coefficients.length - 2) = p.coefficients.length := by omega
      simp only [hlen, bind, Except.bind, pure, Except.pure]
  rw [hzip]
  congr 1
  rw [foldl_add_mul_eq_sum, ← zero_eq, zero_add, map_zip_range_pow, ← sum_range_eq_list_sum]
  unfold polyOf
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]

end ComputeAt

end CryptoVerification.SpqrV1Sync.Erasure
