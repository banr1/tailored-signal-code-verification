/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# Instruction Decodes for CLI SPQR V1 `RawVecInner` Helpers

Generates instruction decode theorems (`spqrAllocBinCli`) for `finish_grow [local#8]` and
`do_reserve_and_handle [local#7]` in `libsignalSessionCode_tree`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib.ProgramReflection

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

gen_decodes libsignalSessionCode_tree spqrAllocBinCli [(ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#8]" + 0) → (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#8]" + 168)]

gen_decodes libsignalSessionCode_tree spqrAllocBinCli [(ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]" + 0) → (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]" + 120)]

end CryptoVerification.SpqrV1.Alloc
