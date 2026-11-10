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
public import LibsignalBinary.Specifications.SignalSession.CliElf

/-!
# Comparator challenge: Lemma 4 and the Main Theorem (`Computational/Theorems/Main.lean`)

**Trusted: the statements.** Each theorem below has the same name and the same statement, byte for
byte, as the theorem of `Computational/Theorems/Main.lean` (lake library `CliElfLib`), with `sorry`
as its proof. It imports the three specification modules that `Main.lean` imports publicly, plus
`LibsignalBinary.Specifications.SignalSession.CliElf` for `cliElfBytes`, which `Main.lean` gets
through its public import of `Computational.Proofs.LibsignalCli.ElfHeadlinePq` (which this challenge
must not import). It imports no proof module. See `comparator/README.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

theorem libsignal_cli_pq_binary_correct_placed :
    CliPqxdhBinaryCorrectPlaced cliElfBytes :=
  sorry

theorem libsignal_cli_elf_linked_in : libsignalSessionLib.LinkedIn cliElfBytes :=
  sorry

theorem libsignal_cli_elf_mallocng_linked_in :
    VerifiedLibraries.mallocngLib.LinkedIn cliElfBytes :=
  sorry

theorem libsignal_cli_labels_from_objects : CliLabelsFromObjects :=
  sorry

end CryptoVerification.SignalSession

namespace CryptoVerification.LibsignalCli

open CryptoVerification.SignalSession (cliElfBytes)

theorem libsignal_cli_pq_secure_elf_binary_placed :
    CliPqxdhBinaryCorrectAndSecurePlaced cliElfBytes :=
  sorry

end CryptoVerification.LibsignalCli
