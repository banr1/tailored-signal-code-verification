/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Lemmas
public import Symbolic.Proofs.Swarm.CREF.Xpl.Faithful
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach
import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix
import VCVio.Prelude.Core

/-!
# Move-Boundary Prefix Reachability for Pre-Key Receive

Exports `rpk_prefix_reachable`, establishing trace reachability at move-prefix boundaries under
`MatchedPrefix`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)

/-- Move-boundary prefix reachability for `MatchedPrefix` explanations. -/
theorem rpk_prefix_reachable {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {acc : List MachineEvent} :
    ∀ g ms, MatchedPrefix interpretation r S who g ms acc →
      ∀ ms₀ δ, ms = ms₀ ++ δ → (runTraceMoves r ms₀).Reachable reachability :=
  fun _ _ h => matchedPrefix_prefix_reachable h

end Symbolic.Swarm.CREF
