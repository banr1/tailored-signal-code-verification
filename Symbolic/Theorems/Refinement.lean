/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliElf
public import Symbolic.Specifications.Refinement.ElfBinding
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RefinementElf

/-!
# Trace Refinement for the `libsignal-cli` Binary

**Trusted: the statement.**

Proves `comp_refines_cli_placed` (`CompRefinesCliBinaryPlaced cliElfBytes`,
`Symbolic/Specifications/Refinement/ElfBinding.lean`), built by `lake build CliElfLib`. Across every
pair of multi-block placements `(mpl, mmpl)` linked in `cliElfBytes`
(`LibsignalBinary/Specifications/SignalSession/CliElf.lean`), the compiled AArch64 `libsignal-cli`
binary refines the composed `PQXDH ∘ SPQR ∘ Triple Ratchet` symbolic model up to cryptographic byte
collisions, and every reachable guarded CLI call terminates with a process outcome
(`CliElfProgressPlaced`: no fault, trap, or divergence; `SIGABRT` aborts terminate the trace at
`CliTraces.stop`).

Combined with `Symbolic/Theorems/ModelSecurity.lean` via `comp_refinement_preservation_cli`
(`Symbolic/Theorems/RefinementPreservation.lean`), this yields `signal_session_secure_placed`
(`Symbolic/Theorems/Security.lean`). Non-vacuity of the extern and hook hypotheses is proved in
`Symbolic/Tests/ExternWitness.lean`; placement witnesses and symbol-label gate A (`A-LINK`,
`Computational/docs/TRUSTED_BASE.md`) are exported in `Symbolic/Theorems/Security.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Proven.Refinement

open CryptoVerification.SignalSession (cliElfBytes)
open DY.Libsignal.Composed.Refinement.Cli (CompRefinesCliBinaryPlaced)

/-- Relocatable trace refinement and progress for the SHA-256-pinned `libsignal-cli` AArch64 binary
(`CompRefinesCliBinaryPlaced cliElfBytes`, `Symbolic/Specifications/Refinement/ElfBinding.lean`).
For every pair of multi-block placements `mpl` (`libsignalSessionLib.LinkedAt cliElfBytes mpl`) and
`mmpl` (`VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl`), `cliElfBytes` parses as an ELF
image satisfying `CliElfCodeMatchesPlaced mpl mmpl`, every reachable guarded CLI call terminates
with a process outcome (`CliElfProgressPlaced mpl mmpl`), and under any valid cryptographic extern
interpretation and matching CLI hooks, every guarded execution trace of `cliRunPlacedSig mpl mmpl`
from `initDirs` is explained by a reachable model run (`Explains`) or encounters a cryptographic
collision after an explained prefix (`CollisionAfterExplainedPrefix`). -/
theorem comp_refines_cli_placed :
    CompRefinesCliBinaryPlaced cliElfBytes :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Cli.comp_refines_cli_placed_proof

end Proven.Refinement
