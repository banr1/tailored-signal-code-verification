/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Binary
public import Symbolic.Proofs.SpecLemmas.ElfBindingFixed

/-!
# Fixed-Image Symbolic Binary Security Predicate

**Checked by Lean.** Defines the fixed-image symbolic binary security predicate
`SignalSessionSecure` in terms of `SignalSessionSecureFor` and `elfRel`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Security

open Arm64.Process (ElfImage)
open DY.Libsignal.Composed.Refinement.Cli (CliElfProgress HooksMatchInterpretation elfRel)
open CryptoVerification.SignalSession (CliElfCodeMatches)

/-- Symbolic security and fault-freedom on every reachable guarded run of the fixed-image ELF
binary `bytes`. -/
def SignalSessionSecure (bytes : List (BitVec 8)) : Prop :=
  ∃ elf : ElfImage, ElfImage.parse bytes = .ok elf ∧ CliElfCodeMatches elf ∧
    CliElfProgress elf ∧
    SignalSessionSecureFor HooksMatchInterpretation (elfRel elf)

end DY.Libsignal.Composed.Security
