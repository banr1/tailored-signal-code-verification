/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedFetchBase

/-!
# Placed Fetch and Relocation Step Shard 0

Instruction fetch and relocation step lemmas for mallocng blocks 2..6.
-/

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection VerifiedLibraries.Mallocng

decl_core_block 2  56  b02 VerifiedLibraries.mallocng_blk02_calloc
decl_core_block 3  1   b03 VerifiedLibraries.mallocng_blk03_free
decl_core_block 4  1   b04 VerifiedLibraries.mallocng_blk04_default_malloc
decl_core_block 5  300 b05 VerifiedLibraries.mallocng_blk05_nontrivial_free
decl_core_block 6  215 b06 VerifiedLibraries.mallocng_blk06_libc_free

gen_placed_fetches blkPC0_b02 blkLib_b02 blkTree_b02 blkCodeEq_b02 blkSizeEq_b02
  via_placement blkPl_b02 blkPlaceable_b02 [0x0 → 0xdc]

gen_placed_fetches blkPC0_b03 blkLib_b03 blkTree_b03 blkCodeEq_b03 blkSizeEq_b03
  via_placement blkPl_b03 blkPlaceable_b03 [0x0]

gen_placed_fetches blkPC0_b04 blkLib_b04 blkTree_b04 blkCodeEq_b04 blkSizeEq_b04
  via_placement blkPl_b04 blkPlaceable_b04 [0x0]

gen_placed_fetches blkPC0_b05 blkLib_b05 blkTree_b05 blkCodeEq_b05 blkSizeEq_b05
  via_placement blkPl_b05 blkPlaceable_b05 [0x0 → 0x4ac]

gen_placed_fetches blkPC0_b06 blkLib_b06 blkTree_b06 blkCodeEq_b06 blkSizeEq_b06
  via_placement blkPl_b06 blkPlaceable_b06 [0x0 → 0x358]

gen_blk_reloc_steps b02 2 56
gen_blk_reloc_steps b03 3 1
gen_blk_reloc_steps b04 4 1
gen_blk_reloc_steps b05 5 300
gen_blk_reloc_steps b06 6 215

end VerifiedLibraries.Mallocng.Proofs
