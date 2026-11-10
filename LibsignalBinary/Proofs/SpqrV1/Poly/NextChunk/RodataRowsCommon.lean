/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.GF16Fast

/-!
# Pure Evaluators for Precomputed `.rodata` Lagrange Basis Tables

**Checked by Lean.**

Boolean equality evaluators and `completePointsPolys_eq_of_fast` bridge for kernel verification of
`COMPLETE_POINTS_POLYS_{1,3,5,30,34,36}`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open CryptoVerification.LibsignalSpqrV1

/-- The `x = 0, 1, ..., n - 1`, `y = 1` point list used by `lagrangePolysForCompletePoints n`. -/
def completeOnes (n : Nat) : List Pt :=
  (List.range n).map (fun i => { x := GF16.new (BitVec.ofNat 16 i), y := GF16.ONE })

theorem lagrangePolysForCompletePoints_eq_mapM (n : Nat) :
    lagrangePolysForCompletePoints n =
      (List.range n).mapM (fun i => PolyConst.lagrangeInterpolatePt n (completeOnes n) i) := rfl

theorem except_mapM_nil {ε α β : Type} (f : α → Except ε β) :
    ([] : List α).mapM f = .ok [] := rfl

theorem except_mapM_cons {ε α β : Type} (f : α → Except ε β) (x : α) (xs : List α)
    (y : β) (ys : List β) (hy : f x = .ok y) (hys : xs.mapM f = .ok ys) :
    (x :: xs).mapM f = .ok (y :: ys) := by
  simp [List.mapM_cons, hy, hys, bind, Except.bind, pure, Except.pure]

def gf16ListBeq : List GF16 → List GF16 → Bool
  | [], [] => true
  | a :: as, b :: bs =>
    match Nat.beq a.value.toNat b.value.toNat with
    | true => gf16ListBeq as bs
    | false => false
  | _, _ => false

theorem eq_of_gf16ListBeq :
    ∀ {xs ys : List GF16}, gf16ListBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | _ :: _, [], h => nomatch h
  | [], _ :: _, h => nomatch h
  | ⟨a⟩ :: as, ⟨b⟩ :: bs, h => by
    dsimp only [gf16ListBeq] at h
    cases hb : Nat.beq a.toNat b.toNat with
    | false => rw [hb] at h; nomatch h
    | true =>
      rw [hb] at h
      rw [BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hb), eq_of_gf16ListBeq h]

def polyConstListBeq {n : Nat} : List (PolyConst n) → List (PolyConst n) → Bool
  | [], [] => true
  | a :: as, b :: bs =>
    match gf16ListBeq a.coefficients b.coefficients with
    | true => polyConstListBeq as bs
    | false => false
  | _, _ => false

theorem eq_of_polyConstListBeq {n : Nat} :
    ∀ {xs ys : List (PolyConst n)}, polyConstListBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | _ :: _, [], h => nomatch h
  | [], _ :: _, h => nomatch h
  | ⟨a⟩ :: as, ⟨b⟩ :: bs, h => by
    dsimp only [polyConstListBeq] at h
    cases hb : gf16ListBeq a b with
    | false => rw [hb] at h; nomatch h
    | true =>
      rw [hb] at h
      rw [eq_of_gf16ListBeq hb, eq_of_polyConstListBeq h]

def exceptPolysOkBeq {n : Nat} (r : Except PolyPanic (List (PolyConst n)))
    (ys : List (PolyConst n)) : Bool :=
  match r with
  | .ok xs => polyConstListBeq xs ys
  | .error _ => false

/-- Prove `lagrangePolysForCompletePoints n = .ok ys` in one fast kernel `Bool` evaluation. -/
theorem completePointsPolys_eq_of_fast (n : Nat) (ys : List (PolyConst n))
    (h : exceptPolysOkBeq (GF16Fast.lagrangePolysForCompletePointsFast n) ys = true) :
    lagrangePolysForCompletePoints n = .ok ys := by
  rw [GF16Fast.lagrangePolysForCompletePoints_eq_fast]
  cases hr : GF16Fast.lagrangePolysForCompletePointsFast n with
  | error _ => rw [hr] at h; nomatch h
  | ok xs =>
    rw [hr] at h
    exact congrArg Except.ok (eq_of_polyConstListBeq h)

end CryptoVerification.SpqrV1.Poly.NextChunk
