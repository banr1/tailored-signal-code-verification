/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ToMathlib.MeasureTheory.Measure.Bool

/-!
# Bias Bound Under Bounded Boolean Distance

Proves `boolBias_le_add_two_mul_of_boolDist_le`: for probability measures `μ` and `ν` on `Bool`
with `μ.boolDist ν ≤ ε`, `μ.boolBias ≤ ν.boolBias + 2 * ε`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.Oom.Bias

open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

/-- If `μ.boolDist ν ≤ ε`, then `μ.boolBias ≤ ν.boolBias + 2 * ε`. -/
theorem boolBias_le_add_two_mul_of_boolDist_le (μ ν : Measure Bool) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ε : ℝ≥0∞) (h : μ.boolDist ν ≤ ε) :
    μ.boolBias ≤ ν.boolBias + 2 * ε := by
  rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure μ,
    Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure ν]
  calc 2 * ENNReal.absDiff (μ {true}) (1 / 2)
      ≤ 2 * (ENNReal.absDiff (ν {true}) (1 / 2) + ENNReal.absDiff (μ {true}) (ν {true})) := by
        gcongr
        rw [add_comm]
        exact ENNReal.absDiff_triangle _ _ _
    _ = 2 * ENNReal.absDiff (ν {true}) (1 / 2) + 2 * μ.boolDist ν := by
        rw [mul_add, Measure.boolDist]
    _ ≤ 2 * ENNReal.absDiff (ν {true}) (1 / 2) + 2 * ε := by gcongr

end Computational.Proofs.LibsignalCli.Oom.Bias
