/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.RefinementPreservation

/-!
# Comparator challenge: refinement preservation (`Symbolic/Theorems/RefinementPreservation.lean`)

**Trusted: the statement.** The theorem below has the same name and the same statement, byte for
byte, as the theorem of `Symbolic/Theorems/RefinementPreservation.lean`, with `sorry` as its proof.
It imports only the specification module that `RefinementPreservation.lean` imports publicly. See
`comparator/README.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace Proven.RefinementPreservation

open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.SignalSession (Inputs Outcome)
open DY.Libsignal.Composed.Refinement.Cli (CompRefinementPreservationCli)

theorem comp_refinement_preservation_cli {ω : Type} (Agree : ExternInterpretation → ω → Prop)
    (R : ExternInterpretation → ω → Inputs → Option Outcome → Prop) :
    CompRefinementPreservationCli Agree R :=
  sorry

end Proven.RefinementPreservation
