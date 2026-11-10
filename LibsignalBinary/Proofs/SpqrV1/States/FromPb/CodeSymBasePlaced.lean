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
# `<spqr::v1::chunked::states::States>::from_pb` (Block `333`): Relocatable Block Base (`CodeSymBasePlaced`)

Emits `blkLib_333`, `blkPl_333`, `blkPC_333`, `lsProg_333`, `blkTree_333`, non-relaxable
relocation lemmas, and symbol-resolution lemmas for Block `333` (`2,911` insns, `11,644`B).
Per-instruction `gen_placed_fetches` are sharded across `CodeSymFetch0Placed..3Placed`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification

gen_ls_blk_base 333

end CryptoVerification
