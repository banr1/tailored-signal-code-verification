/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.AsmLevelSecurity
public import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RefinementKElf

/-!
# Relocatable Assembly-Level Security for `cliElfBytes` from `H2KGhostArms`

**Checked by Lean.**

Derives `SignalSessionSecurePlaced cliElfBytes` from `H2KGhostArms` via
`signal_session_secure_placed_of_binary_refines` and `RefinementKElf.comp_refines_cli_placed_proofK`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli.AsmLevelSecurityKElf

open CryptoVerification.SignalSession (cliElfBytes)
open DY.Libsignal.Composed.Security (SignalSessionSecurePlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms (H2KGhostArms)
open Symbolic.Proofs.TopLevelHelpers.Composed.Cli (signal_session_secure_placed_of_binary_refines)
open Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RefinementKElf (comp_refines_cli_placed_proofK)

/-- Relocatable two-placement assembly-level CLI security for `cliElfBytes` from `H2KGhostArms`. -/
theorem signal_session_secure_placed_proofK :
    H2KGhostArms → SignalSessionSecurePlaced cliElfBytes :=
  fun hG => signal_session_secure_placed_of_binary_refines (comp_refines_cli_placed_proofK hG)

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli.AsmLevelSecurityKElf
