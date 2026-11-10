/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.BugInjectionMutantImage
public import ProofLib.ProgramReflection
public meta import GeneratedLean.BugInjectionMutantImage
public meta import ProofLib.ProgramReflection

/-!
# Symbol-Character Table for `mutantCliElfImage`

Reflects `mutantCliElfImage.symbols` into `List (List Char × BitVec 64)` via `assoc_chars_of%`
(under `CV_BUG_INJECTION=<bug>`) and proves `mutantCliElf_symbols_eq` by kernel reduction.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.MutantLink.MutantSymChars

open Arm64 ProofLib.ProgramReflection
open CryptoVerification.BugInjection (mutantCliElfImage)

noncomputable def mutantCliElfSyms : List (String × BitVec 64) := mutantCliElfImage.symbols

noncomputable def mutantCliElfSymChars : List (List Char × BitVec 64) :=
  assoc_chars_of% mutantCliElfSyms

theorem mutantCliElf_symbols_eq :
    mutantCliElfImage.symbols = toStringAssoc mutantCliElfSymChars := by
  rfl_kernel

end Symbolic.BugInjection.Disproofs.Impl.MutantLink.MutantSymChars
