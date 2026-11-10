/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.KeyInd1KeyRoSplit
public import Computational.Specifications.Assumptions.Assumptions
import VCVio.CryptoFoundations.SecExp.Measure

/-!
# Non-Vacuity Witnesses for `KeyIndRoGap`, `GapSigEufCma`, and `GapDhWithSign`

**Checked by Lean.** Non-vacuity checks for the random-oracle gap predicate `KeyIndRoGap` and the
joint one-key assumptions `GapSigEufCma` and `GapDhWithSign`. Proves that `KeyIndRoGap S P A 1`
holds unconditionally, that a query-free constant adversary achieves gap `0`, and that query-free
adversaries satisfy `GapSigEufCmaAdv.Bounded` and `GapDhWithSignAdv.Bounded` with advantages in
`[0, 1]`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh

open OracleComp OracleSpec ENNReal MeasureTheory

private theorem boolBias_coin_eq_const (b₀ : Bool) :
    𝒟[(do
      let secb ← ($ᵗ Bool : ProbComp Bool)
      return (b₀ == secb) : ProbComp Bool)].boolBias = 0 := by
  have hEq :
      (do
        let secb ← ($ᵗ Bool : ProbComp Bool)
        return (b₀ == secb) : ProbComp Bool) =
      (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let z ← if b then pure b₀ else pure b₀
        return (b == z)) := by
    congr 1; funext b; cases b <;> cases b₀ <;> rfl
  rw [hEq, evalDist_boolBias_bind_uniformBool, Measure.boolDist_self]

private theorem boolBias_le_one (E : ProbComp Bool) :
    𝒟[E].boolBias ≤ 1 := by
  have had : ENNReal.absDiff (𝒟[E] {true}) (1 / 2) ≤ 1 / 2 := by
    refine ENNReal.absDiff_le_iff.mpr ⟨?_, le_add_self⟩
    calc 𝒟[E] {true} ≤ 1 := measure_le_one 𝒟[E] {true}
      _ = 1 / 2 + 1 / 2 := (ENNReal.add_halves 1).symm
  rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure 𝒟[E]]
  calc 2 * ENNReal.absDiff (𝒟[E] {true}) (1 / 2)
      ≤ 2 * (1 / 2) := by gcongr
    _ = 1 / 2 + 1 / 2 := two_mul (1 / 2)
    _ = 1 := ENNReal.add_halves 1

/-- `KeyIndRoGap S P A 1` holds unconditionally because every `boolBias` advantage lies in `[0, 1]`. -/
theorem keyIndRoGap_one (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    KeyIndRoGap S P A 1 := by
  unfold KeyIndRoGap
  calc KeyInd1KeyRealAdvantage S P A
      ≤ 1 := boolBias_le_one (pqxdhKeyInd1KeyRealExp S P A)
    _ ≤ KeyInd1KeyRoAdvantage S P A + 1 := le_add_self

/-- Query-free `KeyInd` adversary that always outputs `b₀`. -/
def constKeyIndAdversary (S : Setup) (b₀ : Bool) : KeyIndAdversary S :=
  { run := pure b₀ }

theorem keyInd1KeyRoAdvantage_constKeyIndAdversary (S : Setup) (P : Primitives) (b₀ : Bool) :
    KeyInd1KeyRoAdvantage S P (constKeyIndAdversary S b₀) = 0 := by
  unfold KeyInd1KeyRoAdvantage pqxdhKeyInd1KeyExpForHandshake constKeyIndAdversary
  simp only [simulateQ_pure, StateT.run_pure, KeyIndState.empty, List.all_nil, Bool.and_self,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
  exact boolBias_coin_eq_const b₀

theorem keyInd1KeyRealAdvantage_constKeyIndAdversary (S : Setup) (P : Primitives) (b₀ : Bool) :
    KeyInd1KeyRealAdvantage S P (constKeyIndAdversary S b₀) = 0 := by
  unfold KeyInd1KeyRealAdvantage pqxdhKeyInd1KeyRealExp pqxdhKeyInd1KeyExpForHandshake
    constKeyIndAdversary
  simp only [simulateQ_pure, StateT.run_pure, KeyIndState.empty, List.all_nil, Bool.and_self,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
  exact boolBias_coin_eq_const b₀

theorem keyIndRoGap_zero_const (S : Setup) (P : Primitives) (b₀ : Bool) :
    KeyIndRoGap S P (constKeyIndAdversary S b₀) 0 := by
  unfold KeyIndRoGap
  rw [keyInd1KeyRealAdvantage_constKeyIndAdversary, keyInd1KeyRoAdvantage_constKeyIndAdversary]
  simp

/-- Query-free `GapSigEufCmaAdv` witness returning `(mStar, sigStar)`. -/
def constGapSigEufCmaAdv (mStar sigStar : Bytes) : GapSigEufCmaAdv where
  run    := fun _ => pure (mStar, sigStar)
  q_sig  := 0
  q_ddh  := 0
  q_prim := 0

theorem constGapSigEufCmaAdv_bounded (mStar sigStar : Bytes) :
    (constGapSigEufCmaAdv mStar sigStar).Bounded :=
  ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial⟩

theorem gapSigEufCma_le_one (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (A : GapSigEufCmaAdv) :
    0 ≤ GapSigEufCma P isValidDhTriple A ∧ GapSigEufCma P isValidDhTriple A ≤ 1 :=
  ⟨zero_le, measure_le_one _ _⟩

theorem gapSigEufCma_const_reject_verify (P : Primitives)
    (hV : ∀ pk m sg, P.sigVerify pk m sg = false)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (mStar sigStar : Bytes) :
    GapSigEufCma P isValidDhTriple (constGapSigEufCmaAdv mStar sigStar) = 0 := by
  unfold GapSigEufCma gapSigEufCmaExp constGapSigEufCmaAdv
  simp [hV]

/-- Query-free `GapDhWithSignAdv` witness returning `z`. -/
def constGapDhWithSignAdv (z : Bytes) : GapDhWithSignAdv where
  run    := fun _ _ => pure z
  q_ddh  := 0
  q_sig  := 0
  q_prim := 0

theorem constGapDhWithSignAdv_bounded (z : Bytes) :
    (constGapDhWithSignAdv z).Bounded :=
  ⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

theorem gapDhWithSign_le_one (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pow8 : Bytes → Bytes) (A : GapDhWithSignAdv) :
    0 ≤ GapDhWithSign P isValidDhTriple pow8 A ∧ GapDhWithSign P isValidDhTriple pow8 A ≤ 1 :=
  ⟨zero_le, measure_le_one _ _⟩

end SignalPqxdh
