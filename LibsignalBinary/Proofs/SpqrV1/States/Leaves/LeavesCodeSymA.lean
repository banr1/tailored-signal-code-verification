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
# SPQR V1 Leaf Transitions: Relocatable Block Programs (Blocks `335`–`349`, `354`–`355`, `370`, `382`)

Generates `[LibsignalPlacement]` `Program` reflections (`gen_ls_blk`) for the 13 leaf
state-machine blocks `335`, `336`, `337`, `338`, `343`, `344`, `345`, `346`, `349`, `354`, `355`,
`370`, and `382`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification

gen_ls_blk 335
gen_ls_blk 336
gen_ls_blk 337
gen_ls_blk 338
gen_ls_blk 343
gen_ls_blk 344
gen_ls_blk 345
gen_ls_blk 346
gen_ls_blk 349
gen_ls_blk 354
gen_ls_blk 355
gen_ls_blk 370
gen_ls_blk 382

end CryptoVerification
