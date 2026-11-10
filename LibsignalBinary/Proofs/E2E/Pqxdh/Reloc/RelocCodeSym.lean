/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.GenLsBlock

/-!
# Relocatable Per-Block Instruction Fetches for `E2E/Pqxdh/Reloc`

Per-block `CodeSym` / instruction-fetch definitions under `[LibsignalPlacement]` for Blocks `442`
(`drop_glue::<SessionStructure> [local#3]`), `445` (`drop_glue::<Chain> [local#2]`), `468`
(`Chain::clone [local#3]`), and `511` (`drop_glue::<SignalProtocolError> [local#2]`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches

-- Block `445`: `core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#2]`
gen_ls_blk 445

-- Block `442`: `core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]`
gen_ls_blk 442

-- Block `511`: `core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]`
gen_ls_blk 511

-- Block `468`: `<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]`
gen_ls_blk 468

end CryptoVerification
