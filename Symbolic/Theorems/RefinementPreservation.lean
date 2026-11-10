/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.RefinementPreservation
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RefinementPreservation

/-!
# Security Preservation Across CLI Trace Refinement

**Trusted: the statement.**

Proves `comp_refinement_preservation_cli` (`CompRefinementPreservationCli Agree R`,
`Symbolic/Specifications/Refinement/RefinementPreservation.lean`): for any hook agreement predicate
`Agree` and CLI run relation `R`, if the ten symbolic security properties hold in the composed model
and `R` refines the model from `initDirs`, then all ten properties hold on guarded, coin-fresh
hardware execution traces against `HwAttackerKnows` up to cryptographic collisions.

Instantiating `Agree` and `R` with `HooksMatchInterpretation` and `elfRelPlaced mpl mmpl elf`
(`Symbolic/Specifications/Refinement/ElfBinding.lean`) combines
`Symbolic/Theorems/ModelSecurity.lean` with `comp_refines_cli_placed`
(`Symbolic/Theorems/Refinement.lean`) to yield `signal_session_secure_placed`
(`Symbolic/Theorems/Security.lean`).
-/

@[expose] public section

set_option autoImplicit false

namespace Proven.RefinementPreservation

open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.SignalSession (Inputs Outcome)
open DY.Libsignal.Composed.Refinement.Cli (CompRefinementPreservationCli)

/-- Generic security preservation over CLI runs (`CompRefinementPreservationCli Agree R`,
`Symbolic/Specifications/Refinement/RefinementPreservation.lean`): the ten composed model security
theorems together with trace refinement (`CompRefinesCli Agree R`) imply binary-level security on
all guarded, coin-fresh traces (`SignalSessionSecureFor Agree R`,
`Symbolic/Specifications/Security/Binary.lean`). -/
theorem comp_refinement_preservation_cli {ω : Type} (Agree : ExternInterpretation → ω → Prop)
    (R : ExternInterpretation → ω → Inputs → Option Outcome → Prop) :
    CompRefinementPreservationCli Agree R :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Cli.comp_refinement_preservation_cli_proof Agree R

end Proven.RefinementPreservation
