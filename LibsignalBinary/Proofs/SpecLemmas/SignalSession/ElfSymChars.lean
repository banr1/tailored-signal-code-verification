/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
public import ProofLib.ProgramReflection
public meta import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
public meta import ProofLib.ProgramReflection

/-!
# Interned Symbol-Character Table for `cliElfImage`

Reflects `cliElfImage.symbols` into `List (List Char × BitVec 64)` once for reuse across
placed ELF symbol-resolution modules.
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars

open Arm64 ProofLib.ProgramReflection
open CryptoVerification.SignalSession (cliElfImage)

noncomputable def cliElfSyms : List (String × BitVec 64) := cliElfImage.symbols

set_option maxRecDepth 4000000 in
noncomputable def cliElfSymChars : List (List Char × BitVec 64) :=
  assoc_chars_of% cliElfSyms

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 1600000 in
theorem cliElf_symbols_eq :
    cliElfImage.symbols = toStringAssoc cliElfSymChars := by
  rfl_kernel

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars
