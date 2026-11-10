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
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.BytesCodeSym -- shake: keep

/-!
# Relocatable Per-Block Symbol Bindings for `TripleRatchet/Prost`

Per-block symbol bindings and instruction-fetch aliases for the Prost decoding and encoding
subroutines (blocks 1, 5, 7, 8, 10, 13, 76, 108, 250, 261, and 293).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

gen_ls_blk 1
gen_ls_blk 4
gen_ls_blk 7
gen_ls_blk 8
gen_ls_blk 10
gen_ls_blk 76
gen_ls_blk 108
gen_ls_blk 261
gen_ls_blk 293

end CryptoVerification
