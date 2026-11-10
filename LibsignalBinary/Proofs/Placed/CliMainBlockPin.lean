/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import ProofLib.ProgramReflection

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Placed.CliMainBlockPin

open ProofLib.ProgramReflection
open CryptoVerification.SignalSession (libsignalSessionLib)

set_option maxRecDepth 2000000 in
/-- Pins `main` at offset `0` of block `617` on the stock `cli.elf` layout
(`Placed.libsignalSessionLib_main_block` leaves the block index abstract for mutant binaries). -/
theorem libsignalSessionLib_main_block_clean :
    Arm64.Obj.lookupBlockSym "main" libsignalSessionLib.blocks = some (617, 0) := by
  rfl_kernel

end LibsignalBinary.Proofs.Placed.CliMainBlockPin
