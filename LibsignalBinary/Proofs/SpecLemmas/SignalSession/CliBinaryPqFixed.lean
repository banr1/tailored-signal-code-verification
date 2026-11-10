/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryFixed
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq

@[expose] public section

set_option autoImplicit false

/-!
# Fixed-Image PQXDH-Mode CLI Specification

**Checked by Lean.** Fixed-image whole-process correctness predicates (`CliPqxdhElfCorrect`,
`CliPqxdhBinaryCorrect`) for the `signal-session` ELF in PQXDH mode.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.E2E


/-- Whole-process PQXDH-mode correctness of `elf`: `CliElfCodeMatches elf` holds, and for all hooks
`W` and unreached primitives `X`, `cliRunAbortOnPanic elf W` satisfies `CliSpecPqxdh` and
`CliSpecPqxdhNoMatch` at `⟨W.C, W.Q⟩`. -/
def CliPqxdhElfCorrect (elf : ElfImage) : Prop :=
  CliElfCodeMatches elf ∧
  ∀ W : CliHooks, ∀ X : UnreachedPqxdhPrimitives,
    CliSpecPqxdh (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩ ∧
    CliSpecPqxdhNoMatch (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩

/-- Bytes `bytes` parse via `ElfImage.parse` into an ELF image satisfying `CliPqxdhElfCorrect`. -/
def CliPqxdhBinaryCorrect (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliPqxdhElfCorrect elf


end CryptoVerification.SignalSession
