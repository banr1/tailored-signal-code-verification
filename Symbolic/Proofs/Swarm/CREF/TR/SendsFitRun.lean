/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces
public import Mathlib.Algebra.Group.Nat.Defs
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Wire-Length Bound Predicate on Sent Machine Events

Defines `SendsFit`, bounding every `.send m` event in a machine-event trace to length `< 2 ^ 64`,
and proves closure under empty and appended traces.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR

cref_open
open DY.Libsignal DY.Libsignal.HwEvents

/-- Every `.send m` event in `acc` has length `< 2 ^ 64`. -/
def SendsFit (acc : List MachineEvent) : Prop :=
  ∀ m : HwBytes, .send m ∈ acc → m.length < 2 ^ 64

theorem sendsFit_nil : SendsFit [] := fun _ h => nomatch h

theorem sendsFit_append {acc₁ acc₂ : List MachineEvent}
    (h₁ : SendsFit acc₁) (h₂ : SendsFit acc₂) : SendsFit (acc₁ ++ acc₂) := by
  intro m hm; rcases List.mem_append.mp hm with h | h
  · exact h₁ m h
  · exact h₂ m h

end Symbolic.Swarm.CREF.TR
