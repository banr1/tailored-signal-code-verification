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
# Relocatable Per-Block Fetches for `TripleRatchet/Bytes`

Generated instruction-fetch definitions for blocks `224` (`bytes::bytes::static_drop`), `226`
(`bytes::bytes::static_clone`), `236` (`bytes::bytes::promotable_odd_drop`), `237`
(`bytes::bytes::promotable_even_drop`), and `250` (`<Bytes as From<Vec<u8>>>::from`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

gen_ls_blk 224
gen_ls_blk 226
gen_ls_blk 236
gen_ls_blk 237
gen_ls_blk 250

end CryptoVerification
