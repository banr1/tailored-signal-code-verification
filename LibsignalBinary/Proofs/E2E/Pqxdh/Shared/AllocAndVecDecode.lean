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
# Instruction Decode Lemmas for `AllocAndVec`

Kernel-checked (`rfl_kernel`) instruction decode lemmas on `libsignalSessionCode_tree` for
`<alloc::vec::Vec<u8>>::append_elements` (`0x1af54`, `0x7655c`) and
`<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]` (`0x764a0`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.Shared

open Arm64 CryptoVerification ProofLib.ProgramReflection

/-! ## `vecAppendElements` (`0x1af54`) -/

gen_decodes libsignalSessionCode_tree vecAppendElements [0x1af54 → 0x1afac]

/-! ## `tryAllocateIn2` (`0x764a0`) -/

gen_decodes libsignalSessionCode_tree tryAllocateIn2
  [(ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]" + 0) →
   (ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]" + 188)]

end CryptoVerification.E2E.Pqxdh.Shared
