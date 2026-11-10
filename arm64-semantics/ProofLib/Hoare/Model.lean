/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
import all Arm64.Trusted.Spec.Hoare

/-!
# Hoare Judgment Characterizations

Provides `iff` characterizations of the sealed definitions `reaches_outcome` and `subroutine_ok`
from `Arm64.Trusted.Spec.Hoare` in terms of `Steps` and `SubroutineOutcome`. Only `Arm64` and
`ProofLib` modules may privately import this file (`check-trust-guards`).
-/

namespace Arm64

public section

/-- Unfolds `reaches_outcome` to existence of a `Steps` trace ending in `SubroutineOutcome`
whenever `prog.CodeLoaded s.mem` holds. -/
theorem reaches_outcome_iff {prog : Program} {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 s : State} :
    reaches_outcome prog spec x R s0 s ↔
      (prog.CodeLoaded s.mem → ∃ sf, Steps prog s sf ∧ SubroutineOutcome spec x R s0 sf) :=
  Iff.rfl

/-- Unfolds `subroutine_ok` to `reaches_outcome` from every SP-aligned running entry state
satisfying the framed precondition. -/
theorem subroutine_ok_iff {α : Type} {prog : Program} {entry_pc : BitVec 64} {spec : Spec α} :
    subroutine_ok prog entry_pc spec ↔
      ∀ (x : α) (R : SepProp) (s0 : State),
        s0.pc = entry_pc →
        s0.status = .Running →
        (s0.mem ⊨ spec.pre x s0 ∗ R) →
        s0.spAligned = true →
        reaches_outcome prog spec x R s0 s0 :=
  Iff.rfl

end

end Arm64
