/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.RefinementPreservation
import Symbolic.Proofs.Swarm.CREF.Cli.TopEvents

/-!
# CLI Whole-Protocol Refinement Preservation

Transfers the ten whole-protocol symbolic security properties along `CompRefinesCli` to
`SignalSessionSecureFor` over CLI runs from provisioned directories (`initDirs`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.SignalSession (Inputs Outcome)

/-- Refinement preservation over CLI runs from provisioned directories (`initDirs`). -/
theorem comp_refinement_preservation_cli {ω : Type}
    (Agree : ExternInterpretation → ω → Prop)
    (R : ExternInterpretation → ω → Inputs → Option Outcome → Prop) :
    CompRefinementPreservationCli Agree R :=
  DY.Libsignal.Composed.Refinement.Cli.comp_refinement_preservation_cli Agree R

/-- Quantified whole-protocol refinement preservation over CLI runs. -/
theorem comp_refinement_preservation_cli_proof :
    ∀ {ω : Type} (Agree : ExternInterpretation → ω → Prop)
      (R : ExternInterpretation → ω → Inputs → Option Outcome → Prop),
      CompRefinementPreservationCli Agree R :=
  @comp_refinement_preservation_cli

/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.comp_refinement_preservation_cli_proof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms comp_refinement_preservation_cli_proof

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli
