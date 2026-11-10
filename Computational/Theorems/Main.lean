/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.SignalSession.CliLabels
public import Computational.Proofs.LibsignalCli.ElfHeadlinePq

/-!
# Lemma 4 and Main Theorem: Computational Correctness and Security of the `libsignal-cli` Binary

**Trusted: the statement.** Built by `lake build CliElfLib`. Each theorem below states a
proposition from `Computational/Specifications/` or `LibsignalBinary/Specifications/` on the
SHA-256-pinned AArch64 binary `cliElfBytes`
(`LibsignalBinary/Specifications/SignalSession/CliElf.lean`) and is proved by a corresponding
`*_proof` theorem in `Computational/Proofs/`. See `Computational/docs/TRUSTED_BASE.md` for the
trusted definitions and kernel axioms of each theorem, and `Computational/docs/DEVIATIONS.md` for
the specification deviations referenced below.

Lemmas 1–3 (`Computational/Theorems/Lemmas.lean`), relocatable Lemma 4, and freedom from
`.OutOfMemory` in PQXDH mode imply the relocatable Main Theorem (`main_of_lemmas_placed`,
`Computational/Proofs/LibsignalCli/MainOfLemmas.lean`); for `cliElfBytes`, `.OutOfMemory` freedom is
discharged unconditionally under the 1 GiB dynamic-mapping budget (DEV-CLI12, retired).

| Result | Theorem | Statement | Proof |
|---|---|---|---|
| Lemma 4 | `libsignal_cli_pq_binary_correct_placed` | `CliPqxdhBinaryCorrectPlaced cliElfBytes` (`LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean`) | `Computational/Proofs/LibsignalCli/ElfHeadlinePq.lean` |
| Main Theorem | `libsignal_cli_pq_secure_elf_binary_placed` | `CliPqxdhBinaryCorrectAndSecurePlaced cliElfBytes` (`Computational/Specifications/LibsignalCli/StatementPqElf.lean`) | `Computational/Proofs/LibsignalCli/ElfHeadlinePq.lean` |
| Session placement witness | `libsignal_cli_elf_linked_in` | `libsignalSessionLib.LinkedIn cliElfBytes` (`LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean`) | `Computational/Proofs/LibsignalCli/ElfHeadlinePq.lean` |
| Allocator placement witness | `libsignal_cli_elf_mallocng_linked_in` | `VerifiedLibraries.mallocngLib.LinkedIn cliElfBytes` (`VerifiedLibraries/Mallocng/Spec/PlacedLib.lean`) | `Computational/Proofs/LibsignalCli/ElfHeadlinePq.lean` |
| Label gate A | `libsignal_cli_labels_from_objects` | `CliLabelsFromObjects` (`LibsignalBinary/Specifications/SignalSession/CliLabels.lean`) | `Computational/Proofs/LibsignalCli/ElfHeadlinePq.lean` |

**Trusted computing base.** Lean's kernel checks code bytes, relocations, addresses, and segment
layout directly against `cliElfBytes` (`Placed.CliElfCodeMatchesPlaced` / `InElf`,
`cliElf_linkedAt_unique`). Symbol-name labels rest on the trusted `.o` extractor
(`libsignal_cli_labels_from_objects`, assumption A-LINK in `Computational/docs/TRUSTED_BASE.md`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

/-- **Lemma 4 (binary refinement, relocatable)** (`CliPqxdhBinaryCorrectPlaced cliElfBytes`,
`LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean`). For every multi-block placement
`mpl` linked in `cliElfBytes` (`libsignalSessionLib.LinkedAt cliElfBytes mpl`), `cliElfBytes` parses
as an AArch64 ELF satisfying `Placed.CliElfCodeMatchesPlaced mpl`, and for all hook implementations
`W` and model extras `X`, the relocatable process `Placed.cliRunPlacedSig mpl` satisfies
`CliSpecPqxdh` and `CliSpecPqxdhNoMatch` (DEV-CLI11) at primitives `⟨W.C, W.Q⟩` (SPQR V1) or
terminates with `.OutOfMemory` (`CliReachesOOMPlaced`, DEV-CLI15). -/
theorem libsignal_cli_pq_binary_correct_placed :
    CliPqxdhBinaryCorrectPlaced cliElfBytes :=
  libsignal_cli_pq_binary_correct_placed_proof

/-- **Session placement witness.** `cliElfBytes` links `libsignalSessionLib` at a concrete
multi-block placement (`libsignalSessionLib.LinkedIn cliElfBytes`). -/
theorem libsignal_cli_elf_linked_in : libsignalSessionLib.LinkedIn cliElfBytes :=
  libsignal_cli_elf_linked_in_proof

/-- **Allocator placement witness.** `cliElfBytes` links the musl `mallocng` allocator library
`VerifiedLibraries.mallocngLib` at a concrete multi-block placement
(`VerifiedLibraries.mallocngLib.LinkedIn cliElfBytes`), discharging both `LinkedAt` hypotheses
(`mpl` and `mmpl`) together with `libsignal_cli_elf_linked_in`. -/
theorem libsignal_cli_elf_mallocng_linked_in :
    VerifiedLibraries.mallocngLib.LinkedIn cliElfBytes :=
  libsignal_cli_elf_mallocng_linked_in_proof

/-- **Label gate A** (`CliLabelsFromObjects`,
`LibsignalBinary/Specifications/SignalSession/CliLabels.lean`). The symbol names interpreted by the
placed theorems (hooked externs, `SIGABRT` panic externs, and SPQR CPU-probe statics) match the
symbol names extracted from the pre-link `.o` objects. -/
theorem libsignal_cli_labels_from_objects : CliLabelsFromObjects :=
  libsignal_cli_labels_from_objects_proof

end CryptoVerification.SignalSession

namespace CryptoVerification.LibsignalCli

open CryptoVerification.SignalSession (cliElfBytes)

/-- **Main Theorem (binary correctness and security, relocatable)**
(`CliPqxdhBinaryCorrectAndSecurePlaced cliElfBytes`,
`Computational/Specifications/LibsignalCli/StatementPqElf.lean`). Across every pair of multi-block
placements `(mpl, mmpl)` linked in `cliElfBytes` (`libsignalSessionLib.LinkedAt cliElfBytes mpl`,
`VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl`), `cliElfBytes` parses as an AArch64 ELF,
satisfies `CliPqxdhElfCorrectPlaced mpl mmpl` (allowing `.OutOfMemory` per DEV-CLI15), and for every
point type `Pt`, setup `S`, and plaintext length `ℓ` satisfies `CliPqxdhElfSecurePlaced mpl mmpl`
for all hooks `W` and model extras `X` meeting the primitive hypotheses (with no `.OutOfMemory`
hypothesis; DEV-CLI12, retired). -/
theorem libsignal_cli_pq_secure_elf_binary_placed :
    CliPqxdhBinaryCorrectAndSecurePlaced cliElfBytes :=
  libsignal_cli_pq_secure_elf_binary_placed_proof

end CryptoVerification.LibsignalCli
