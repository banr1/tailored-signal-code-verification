/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliElf
public import LibsignalBinary.Specifications.SignalSession.CliLabels
public import Symbolic.Specifications.Security.Binary
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.AsmLevelSecurityElf

/-!
# Symbolic Security of the `libsignal-cli` Binary

**Trusted: the statement.**

Main symbolic security theorem for the SHA-256-pinned AArch64 `libsignal-cli` binary
(`cliElfBytes`, `LibsignalBinary/Specifications/SignalSession/CliElf.lean`), covering PQXDH session
setup with SPQR V1 composed with the Triple Ratchet. Built by `lake build CliElfLib`; see
`Symbolic/README.md` for the proof architecture.

`signal_session_secure_placed` combines:
- `Symbolic/Theorems/ModelSecurity.lean`: the ten protocol security properties in the composed
  symbolic model;
- `Symbolic/Theorems/Refinement.lean` (`comp_refines_cli_placed`): relocatable trace refinement and
  progress of `cliElfBytes` up to cryptographic collisions;
- `Symbolic/Theorems/RefinementPreservation.lean` (`comp_refinement_preservation_cli`): transfer of
  the ten security properties across trace refinement.

Non-vacuity of the extern and hook hypotheses is proved by `comp_externsSatisfiable_cli`
(`Symbolic/Tests/ExternWitness.lean`), and placement non-vacuity by `libsignal_cli_elf_linked_in`
and `libsignal_cli_elf_mallocng_linked_in`.

**Trusted computing base.** Lean's kernel checks code bytes, relocations, addresses, and segment
layout directly against `cliElfBytes` (`Placed.CliElfCodeMatchesPlaced` / `InElf`,
`cliElf_linkedAt_unique`). Symbol-name labels rest on the trusted `.o` extractor
(`libsignal_cli_labels_from_objects`, assumption A-LINK in `Computational/docs/TRUSTED_BASE.md`).
-/

@[expose] public section

set_option autoImplicit false

namespace Proven.Security

open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib CliLabelsFromObjects)
open DY.Libsignal.Composed.Security (SignalSessionSecurePlaced)

/-- Relocatable symbolic security and progress for the SHA-256-pinned `libsignal-cli` AArch64
binary (`SignalSessionSecurePlaced cliElfBytes`, `Symbolic/Specifications/Security/Binary.lean`).
For every pair of multi-block placements `mpl` (`libsignalSessionLib.LinkedAt cliElfBytes mpl`) and
`mmpl` (`VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl`), `cliElfBytes` parses as an
AArch64 ELF image satisfying `CliElfCodeMatchesPlaced mpl mmpl`, every reachable guarded CLI call
terminates with a process outcome (`CliElfProgressPlaced mpl mmpl`), and under any valid
cryptographic extern interpretation and matching CLI hooks, every guarded, coin-fresh execution
trace of `cliRunPlacedSig mpl mmpl` from `initDirs` is either explained by a reachable model run
with all ten protocol security queries holding against `HwAttackerKnows`, or encounters a
cryptographic collision after an explained prefix on which all ten queries hold over that prefix's
`vis` (`SignalSessionSecureFor`, `Symbolic/Specifications/Security/Binary.lean`). -/
theorem signal_session_secure_placed :
    SignalSessionSecurePlaced cliElfBytes :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Cli.signal_session_secure_placed_proof

/-- Session placement witness: `cliElfBytes` links `libsignalSessionLib` at a concrete multi-block
placement (`libsignalSessionLib.LinkedIn cliElfBytes`). -/
theorem libsignal_cli_elf_linked_in : libsignalSessionLib.LinkedIn cliElfBytes :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Cli.libsignal_cli_elf_linked_in_proof

/-- Allocator placement witness: `cliElfBytes` links the musl `mallocng` allocator library
`VerifiedLibraries.mallocngLib` at a concrete multi-block placement
(`VerifiedLibraries.mallocngLib.LinkedIn cliElfBytes`), discharging both `LinkedAt` hypotheses
(`mpl` and `mmpl`) together with `libsignal_cli_elf_linked_in`. -/
theorem libsignal_cli_elf_mallocng_linked_in :
    VerifiedLibraries.mallocngLib.LinkedIn cliElfBytes :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Cli.libsignal_cli_elf_mallocng_linked_in_proof

/-- **Label gate A** (`CliLabelsFromObjects`,
`LibsignalBinary/Specifications/SignalSession/CliLabels.lean`): the symbol names interpreted by
`SignalSessionSecurePlaced cliElfBytes` and `CompRefinesCliBinaryPlaced cliElfBytes` (hooked
externs, `SIGABRT` panic externs, and SPQR CPU-probe statics) match the symbol names extracted from
the pre-link `.o` objects. -/
theorem libsignal_cli_labels_from_objects : CliLabelsFromObjects :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Cli.libsignal_cli_labels_from_objects_proof

end Proven.Security
