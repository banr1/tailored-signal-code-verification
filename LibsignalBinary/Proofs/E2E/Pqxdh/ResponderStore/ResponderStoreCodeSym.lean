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
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- shake: keep

/-!
# Relocatable Per-Block Fetches for `ResponderStore`

Generates per-block `PlacedLib`, `WordTree`, `gen_placed_fetches`, and symbol resolution lemmas for
the `ResponderStore` blocks under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches

gen_ls_blk 47
gen_ls_blk 50
gen_ls_blk 68
gen_ls_blk 51
gen_ls_blk 66
gen_ls_blk 67
gen_ls_blk 70
gen_ls_blk 83
gen_ls_blk 87
gen_ls_blk 107
gen_ls_blk 109
gen_ls_blk 112
gen_ls_blk 113
gen_ls_blk 203
gen_ls_blk 209

end CryptoVerification
