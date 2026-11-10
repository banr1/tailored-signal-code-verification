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
# Per-Block Instruction Fetches for `grow_one` and `finish_grow` (Blocks 43 and 45)
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches

abbrev lsRustAllocSym : String := "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"
abbrev lsRustReallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc"
abbrev lsNoAllocShimSym : String := "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"
abbrev lsHandleErrorSym : String := "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

gen_ls_blk 45
gen_ls_blk 43

end CryptoVerification
