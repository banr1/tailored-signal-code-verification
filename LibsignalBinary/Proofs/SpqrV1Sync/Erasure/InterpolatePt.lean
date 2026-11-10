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

namespace CryptoVerification.SpqrV1Sync.Erasure.InterpolatePt

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.GF16Field
open CryptoVerification.SpqrV1Sync.Erasure
open Polynomial

theorem lagrangeInterpolatePt_of_prepare_complete
    (pts : List Pt) (i : Nat) (hi : i < pts.length)
    (t w : Poly)
    (ht : Poly.lagrangeInterpolatePrepare pts = .ok t)
    (hw : t.lagrangeInterpolateComplete pts i = .ok w)
    (hw_len : w.coefficients.length = pts.length + 1)
    (hw_poly : polyOf w.coefficients.tail =
      C (GF16.div pts[i].y (Poly.lagrangeDenominator pts[i].x pts)) *
        ((pts.eraseIdx i).map fun pt => X - C pt.x).prod) :
    ∃ p : Poly, Poly.lagrangeInterpolatePt pts i = .ok p ∧
      p.coefficients.length = pts.length ∧
      polyOf p.coefficients =
        C (GF16.div pts[i].y (Poly.lagrangeDenominator pts[i].x pts)) *
          ((pts.eraseIdx i).map fun pt => X - C pt.x).prod := by
  cases hwc : w.coefficients with
  | nil =>
    simp [hwc] at hw_len
  | cons c0 rest =>
    refine ⟨{ coefficients := rest }, ?_, ?_, ?_⟩
    · unfold Poly.lagrangeInterpolatePt
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, ht, hw, hwc]
    · simp only [hwc, List.length_cons, Nat.add_right_cancel_iff] at hw_len
      exact hw_len
    · simpa [hwc] using hw_poly

end CryptoVerification.SpqrV1Sync.Erasure.InterpolatePt
