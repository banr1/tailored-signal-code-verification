/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil

/-!
# Initial Clean Explanation Witness

Proves `init_w : UAInitWSpec`, showing that the empty CLI event list admits a clean explanation
`(g₀, [], [])` reading no colliding term whenever `ProtocolSetupWF r` and `SemReady interp' r S`
hold.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.InitW

open _root_.DY.Libsignal.Composed.Refinement (Ghost MatchesEventsClassical)
open Symbolic.Proofs.Swarm.UA.Defs (UAInitWSpec)
open Symbolic.Swarm.CREF (TR.setupRandoms_length TR.setupTrace_reachable)

/-- The empty CLI event list has an explanation that reads no colliding term. -/
theorem init_w : UAInitWSpec := by
  intro interp' r S hwf hS
  let g₀ : Ghost := ⟨r.fresh, fun _ => []⟩
  refine ⟨g₀, [], [], ⟨hS g₀ (fun _ _ => rfl), ?_, ?_, .nil (fun _ h => nomatch h)⟩, ?_⟩
  · exact ⟨(fun _ hv => nomatch hv), fun _ => Or.inl rfl, fun _ hv => nomatch hv⟩
  · refine ⟨TR.setupRandoms_length r hwf.1, TR.setupTrace_reachable r, trivial, ?_⟩
    intro i _ _ _ _ _ _ _ hi
    simp at hi
  · rintro ⟨evs₁, ev, evs₂, _, _, _, _, _, _, _, _, heq, -⟩
    simp at heq

end Symbolic.Proofs.Swarm.UA.InitW
