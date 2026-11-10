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

/-!
# Comparator challenge: symbolic security of the binary (`Symbolic/Theorems/Security.lean`)

**Trusted: the statements.** Each theorem below has the same name and the same statement, byte for
byte, as the theorem of `Symbolic/Theorems/Security.lean` (lake library `CliElfLib`), with `sorry`
as its proof. It imports the specification modules that `Security.lean` imports publicly, and no
proof module. See `comparator/README.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace Proven.Security

open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib CliLabelsFromObjects)
open DY.Libsignal.Composed.Security (SignalSessionSecurePlaced)

theorem signal_session_secure_placed :
    SignalSessionSecurePlaced cliElfBytes :=
  sorry

theorem libsignal_cli_elf_linked_in : libsignalSessionLib.LinkedIn cliElfBytes :=
  sorry

theorem libsignal_cli_elf_mallocng_linked_in :
    VerifiedLibraries.mallocngLib.LinkedIn cliElfBytes :=
  sorry

theorem libsignal_cli_labels_from_objects : CliLabelsFromObjects :=
  sorry

end Proven.Security
