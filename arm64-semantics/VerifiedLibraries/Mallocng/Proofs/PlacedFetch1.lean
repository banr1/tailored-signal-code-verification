/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedFetchBase

/-!
# Placed Fetch and Relocation Step Lemmas: Blocks 7 and 8

Generates placement-generic fetch and relocation step lemmas for `__malloc_alloc_meta` (`b07`)
and `alloc_slot` (`b08`).
-/

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection VerifiedLibraries.Mallocng

decl_core_block 7  190 b07 VerifiedLibraries.mallocng_blk07_malloc_alloc_meta
decl_core_block 8  590 b08 VerifiedLibraries.mallocng_blk08_alloc_slot

gen_placed_fetches blkPC0_b07 blkLib_b07 blkTree_b07 blkCodeEq_b07 blkSizeEq_b07
  via_placement blkPl_b07 blkPlaceable_b07 [0x0 → 0x2f4]

gen_placed_fetches blkPC0_b08 blkLib_b08 blkTree_b08 blkCodeEq_b08 blkSizeEq_b08
  via_placement blkPl_b08 blkPlaceable_b08 [0x0 → 0x934]

gen_blk_reloc_steps b07 7 190
gen_blk_reloc_steps b08 8 590

end VerifiedLibraries.Mallocng.Proofs
