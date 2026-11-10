/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.BugInjectionMutant
public import GeneratedLean.BugInjectionMutantImage
public import ProofLib.Process
public import ProofLib.ProgramReflection

/-!
# Mutant ELF Parsing

Proves that `ElfImage.parse` on the SHA-pinned `mutantCliElfBytes` overlay yields
`mutantCliElfImage` via `ElfImage.parse_of_fastParse`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.MutantParse

open Arm64.Process (ElfImage)
open ProofLib.ProgramReflection
open CryptoVerification.BugInjection (mutantCliElfBytes mutantCliElfImage)

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 1600000 in
/-- Parsing the pinned mutant ELF bytes yields `mutantCliElfImage`. -/
theorem mutantCliElf_parse : ElfImage.parse mutantCliElfBytes = .ok mutantCliElfImage :=
  ElfImage.parse_of_fastParse (by rfl_kernel)

theorem mutantCliElf_eq_of_parse {elf : ElfImage}
    (h : ElfImage.parse mutantCliElfBytes = .ok elf) : elf = mutantCliElfImage :=
  Except.ok.inj (h.symm.trans mutantCliElf_parse)

end Symbolic.BugInjection.Disproofs.Impl.MutantParse
