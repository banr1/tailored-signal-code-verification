/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Assumptions.KeyInd1KeyRo

/-!
# Chaining `KeyIndRoGap` with One-Key `KeyInd1KeyRoAdvantage` Bounds

**Checked by Lean.** Chains the random-oracle idealization gap `KeyIndRoGap` additively with upper
bounds on `KeyInd1KeyRoAdvantage` to bound `KeyInd1KeyRealAdvantage`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh

open scoped ENNReal

theorem keyInd1KeyRealAdvantage_le_of_roGap {S : Setup} {P : Primitives} {A : KeyIndAdversary S}
    {ε_ro : ℝ≥0∞} (hRo : KeyIndRoGap S P A ε_ro) :
    KeyInd1KeyRealAdvantage S P A ≤ KeyInd1KeyRoAdvantage S P A + ε_ro :=
  hRo

theorem keyInd1KeyRealAdvantage_le_of_roGap_and_bound {S : Setup} {P : Primitives}
    {A : KeyIndAdversary S} {ε_ro B : ℝ≥0∞}
    (hRo : KeyIndRoGap S P A ε_ro) (hB : KeyInd1KeyRoAdvantage S P A ≤ B) :
    KeyInd1KeyRealAdvantage S P A ≤ B + ε_ro :=
  le_trans hRo (add_le_add hB le_rfl)

end SignalPqxdh
