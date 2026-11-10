/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.Placed.GenLsBlock

/-!
# Per-Block Fetch & Relocation Lemmas for `FromRecordChainClone`

Generates per-block `PlacedLib`, `WordTree` fetches, `ADRP` pair steps, `:lo12:` load/store
fetches, and symbol resolution lemmas for blocks `161` (`Chain::clone [local#2]`), `134`, and `157`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches

-- Block 161 (872B): `<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]` (`0x3846c`)
gen_ls_blk 161

-- Block 134 (24B): `core::ptr::drop_glue::<alloc::string::String> [local#4]` (`0x47f20`)
gen_ls_blk 134

end CryptoVerification
