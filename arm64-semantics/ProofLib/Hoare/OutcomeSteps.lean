/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.SubroutineOk
import ProofLib.Hoare.Model

/-!
# Trace-Carrying Outcome Consequence Rule

Provides `Arm64.reaches_outcome.mono_outcome_steps`, an outcome consequence rule for
`reaches_outcome` whose continuation receives `Steps prog s sf` alongside
`SubroutineOutcome spec₁ x R₁ s0 sf` without exposing raw `Steps` in the conclusion.
-/

set_option autoImplicit false

namespace Arm64

@[expose] public section

/-- Outcome consequence rule for `reaches_outcome` whose continuation may use the `Steps` trace
    from `s` to the outcome state. The conclusion stays a sealed `reaches_outcome`, so no raw
    `Steps` fact is exposed to callers (like `subroutine_ok.no_fault_before_outcome`). -/
theorem reaches_outcome.mono_outcome_steps {α β : Type} {prog : Program}
    {spec₁ : Spec α} {spec₂ : Spec β} {x : α} {y : β} {R₁ R₂ : SepProp} {s0 s : State}
    (h : reaches_outcome prog spec₁ x R₁ s0 s)
    (hm : ∀ sf, Steps prog s sf → SubroutineOutcome spec₁ x R₁ s0 sf →
      SubroutineOutcome spec₂ y R₂ s0 sf) :
    reaches_outcome prog spec₂ y R₂ s0 s := by
  refine reaches_outcome_iff.mpr fun hL => ?_
  rcases reaches_outcome_iff.mp h hL with ⟨sf, hsteps, hout⟩
  exact ⟨sf, hsteps, hm sf hsteps hout⟩

end

end Arm64
