/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.Complete
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.ComputeAt
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.FromCompletePoints
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.Interpolate
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.InterpolatePt
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.LagrangeSum
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.Prepare

/-!
# Polynomial Evaluation and Lagrange Interpolation over `GF16`

Equivalence between the polynomial routines in `LibsignalSpqrV1.Poly` (`Poly.computeAt`,
`Poly.lagrangeInterpolate`, `lagrangePolysForCompletePoints`, `Poly.lagrangeInterpolatePt`,
`Poly.lagrangeSum`, and `Poly.fromCompletePoints`) and Mathlib's `Polynomial.eval` and
`Lagrange.interpolate` over `Field GF16`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Erasure

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.GF16Field
open Polynomial

/-- `idxPt` is injective on `Finset.range n` for `n ≤ 2 ^ 16`. -/
theorem idxPt_injOn (n : Nat) (hn : n ≤ 2 ^ 16) : Set.InjOn idxPt (Finset.range n) :=
  IdxPt.idxPt_injOn_proof n hn

/-- `Poly.computeAt` evaluates `polyOf p.coefficients` at `x` without panicking. -/
theorem computeAt_spec (p : Poly) (x : GF16) :
    p.computeAt x = .ok ((polyOf p.coefficients).eval x) :=
  ComputeAt.computeAt_spec_proof p x

/-- `Poly.lagrangeInterpolatePrepare` computes the monic nodal polynomial `∏ (X - C pt.x)` with
`pts.length + 1` coefficients. -/
theorem lagrangeInterpolatePrepare_spec (pts : List Pt) (hlen : pts.length < 2 ^ 16) :
    ∃ t : Poly, Poly.lagrangeInterpolatePrepare pts = .ok t ∧
      t.coefficients.length = pts.length + 1 ∧
      polyOf t.coefficients = (pts.map fun pt => X - C pt.x).prod :=
  Prepare.lagrangeInterpolatePrepare_spec pts hlen

/-- `Poly.lagrangeInterpolateComplete` divides the nodal template `∏ (X - C pt.x)` by `X - C x_i`
and scales by `y_i / lagrangeDenominator x_i pts` in coefficients `[1..]`. -/
theorem lagrangeInterpolateComplete_spec (pts : List Pt) (t : Poly) (i : Nat) (hi : i < pts.length)
    (hlen : t.coefficients.length = pts.length + 1)
    (ht : polyOf t.coefficients = (pts.map fun pt => X - C pt.x).prod) :
    ∃ w : Poly, t.lagrangeInterpolateComplete pts i = .ok w ∧
      w.coefficients.length = pts.length + 1 ∧
      polyOf w.coefficients.tail =
        C (GF16.div pts[i].y (Poly.lagrangeDenominator pts[i].x pts)) *
          ((pts.eraseIdx i).map fun pt => X - C pt.x).prod :=
  Complete.lagrangeInterpolateComplete_spec pts t i hi hlen ht

/-- For distinct evaluation nodes, `Poly.lagrangeInterpolate` returns the unique polynomial of
degree `< pts.length` interpolating `pts`. -/
theorem lagrangeInterpolate_spec (pts : List Pt) (hnd : (pts.map Pt.x).Nodup) :
    ∃ p : Poly, Poly.lagrangeInterpolate pts = .ok p ∧
      p.coefficients.length = pts.length ∧
      ∀ pt ∈ pts, (polyOf p.coefficients).eval pt.x = pt.y :=
  Interpolate.lagrangeInterpolate_spec pts hnd

/-- `polyOf cs` has degree strictly less than `cs.length`. -/
theorem degree_polyOf_lt (cs : List GF16) : (polyOf cs).degree < cs.length :=
  DegreePolyOf.degree_polyOf_lt_proof cs

/-- `lagrangePolysForCompletePoints n` computes the Lagrange basis polynomials for nodes
`idxPt 0, …, idxPt (n - 1)`. -/
theorem lagrangePolysForCompletePoints_spec (n : Nat) (hn : n < 2 ^ 16) :
    ∃ cps, lagrangePolysForCompletePoints n = .ok cps ∧ cps.length = n ∧
      ∀ i (h : i < cps.length), cps[i].coefficients.length = n ∧
        polyOf cps[i].coefficients = Lagrange.basis (Finset.range n) idxPt i :=
  ConstPolys.lagrangePolysForCompletePoints_spec_aux n hn

/-- `Poly.lagrangeInterpolatePt` computes the `i`-th Lagrange basis polynomial for `pts`. -/
theorem lagrangeInterpolatePt_spec (pts : List Pt) (i : Nat) (hi : i < pts.length)
    (hlen : pts.length < 2 ^ 16) :
    ∃ p : Poly, Poly.lagrangeInterpolatePt pts i = .ok p ∧
      p.coefficients.length = pts.length ∧
      polyOf p.coefficients =
        C (GF16.div pts[i].y (Poly.lagrangeDenominator pts[i].x pts)) *
          ((pts.eraseIdx i).map fun pt => X - C pt.x).prod := by
  rcases lagrangeInterpolatePrepare_spec pts hlen with ⟨t, ht, ht_len, ht_poly⟩
  rcases lagrangeInterpolateComplete_spec pts t i hi ht_len ht_poly with ⟨w, hw, hw_len, hw_poly⟩
  exact InterpolatePt.lagrangeInterpolatePt_of_prepare_complete pts i hi t w ht hw hw_len hw_poly

/-- `Poly.lagrangeSum` computes the linear combination `∑ i, C y_i * polys[i]`. -/
theorem lagrangeSum_spec (pts : List Pt) (polys : List Poly) (m : Nat)
    (hlen : pts.length = polys.length) (hm : ∀ p ∈ polys, p.coefficients.length = m) :
    (Poly.lagrangeSum pts polys).coefficients.length = (if polys = [] then 0 else m) ∧
      polyOf (Poly.lagrangeSum pts polys).coefficients =
        ((pts.zip polys).map fun q => C q.1.y * polyOf q.2.coefficients).sum :=
  LagrangeSum.lagrangeSum_spec_aux pts polys m hlen hm

/-- `Poly.fromCompletePoints` on `(idxPt k, ys[k])` returns the Lagrange interpolant of length
`ys.length`, covering both the precomputed-basis sizes (`1, 3, 5, 30, 34, 36`) and the fallback. -/
theorem fromCompletePoints_spec (ys : List GF16) (hlen : ys.length < 2 ^ 16) :
    ∃ p : Poly, Poly.fromCompletePoints (PolyEncoder.enumeratePts 0 ys) = .ok (.ok p) ∧
      p.coefficients.length = ys.length ∧
      polyOf p.coefficients =
        Lagrange.interpolate (Finset.range ys.length) idxPt (fun k => ys.getD k GF16.ZERO) :=
  FromCompletePoints.fromCompletePoints_spec_aux lagrangeInterpolatePt_spec ys hlen

end CryptoVerification.SpqrV1Sync.Erasure
