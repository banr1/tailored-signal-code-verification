/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedFetchBase

/-!
# Placed Fetch and Relocation Lemmas (Blocks 9-14)

Generated instruction-fetch and relocation-step lemmas for `mallocng` blocks 9-14
(`__libc_malloc_impl`, `__malloc_allzerop`, `posix_memalign`, `aligned_alloc`, `realloc`, and
`__libc_realloc`).
-/

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection VerifiedLibraries.Mallocng

decl_core_block 9  278 b09 VerifiedLibraries.mallocng_blk09_libc_malloc_impl
decl_core_block 10 91  b10 VerifiedLibraries.mallocng_blk10_malloc_allzerop
decl_core_block 11 22  b11 VerifiedLibraries.mallocng_blk11_posix_memalign
decl_core_block 12 188 b12 VerifiedLibraries.mallocng_blk12_aligned_alloc
decl_core_block 13 1   b13 VerifiedLibraries.mallocng_blk13_realloc
decl_core_block 14 252 b14 VerifiedLibraries.mallocng_blk14_libc_realloc

gen_placed_fetches blkPC0_b09 blkLib_b09 blkTree_b09 blkCodeEq_b09 blkSizeEq_b09
  via_placement blkPl_b09 blkPlaceable_b09 [0x0 → 0x454]

gen_placed_fetches blkPC0_b10 blkLib_b10 blkTree_b10 blkCodeEq_b10 blkSizeEq_b10
  via_placement blkPl_b10 blkPlaceable_b10 [0x0 → 0x168]

gen_placed_fetches blkPC0_b11 blkLib_b11 blkTree_b11 blkCodeEq_b11 blkSizeEq_b11
  via_placement blkPl_b11 blkPlaceable_b11 [0x0 → 0x54]

gen_placed_fetches blkPC0_b12 blkLib_b12 blkTree_b12 blkCodeEq_b12 blkSizeEq_b12
  via_placement blkPl_b12 blkPlaceable_b12 [0x0 → 0x2ec]

gen_placed_fetches blkPC0_b13 blkLib_b13 blkTree_b13 blkCodeEq_b13 blkSizeEq_b13
  via_placement blkPl_b13 blkPlaceable_b13 [0x0]

gen_placed_fetches blkPC0_b14 blkLib_b14 blkTree_b14 blkCodeEq_b14 blkSizeEq_b14
  via_placement blkPl_b14 blkPlaceable_b14 [0x0 → 0x3ec]

gen_blk_reloc_steps b09 9  278
gen_blk_reloc_steps b10 10 91
gen_blk_reloc_steps b11 11 22
gen_blk_reloc_steps b12 12 188
gen_blk_reloc_steps b13 13 1
gen_blk_reloc_steps b14 14 252

end VerifiedLibraries.Mallocng.Proofs
