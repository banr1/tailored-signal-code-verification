/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Binary

/-!
# Refinement Preservation over `libsignal-cli` Runs

**Trusted: definitions used by the statement.**

States `CompRefinementPreservationCli`: if the ten symbolic security queries
(`Security.AllModelSecurityQueriesHold`) hold and runs under `(Agree, R)` refine the symbolic model
(`CompRefinesCli Agree R`), then those ten security properties hold on guarded, coin-fresh hardware
traces (`SignalSessionSecureFor Agree R`).
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Security (SignalSessionSecureFor)
open CryptoVerification.SignalSession (Inputs Outcome)

/-- Preservation of the composed security bundle across trace refinement for run relation `R`. -/
def CompRefinementPreservationCli {ω : Type} (Agree : ExternInterpretation → ω → Prop)
    (R : ExternInterpretation → ω → Inputs → Option Outcome → Prop) : Prop :=
  Security.AllModelSecurityQueriesHold → CompRefinesCli Agree R → SignalSessionSecureFor Agree R

end DY.Libsignal.Composed.Refinement.Cli
