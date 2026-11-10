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
# Relocatable Per-Block Fetches for `TripleRatchet/InImageCallees`

Per-block `gen_block_Sym` instruction fetch lemmas for in-image `libsignal-core` and `uuid`
callees (`ServiceId::parse_from_service_id_string`, `PrivateKey::serialize`,
`PublicKey::try_from`, `<ProtocolAddress as Display>::fmt`, and `Uuid::try_parse`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

open Arm64 ProofLib

abbrev lsFmtWriteSym : String :=
  "_RNvNtCskxtBwYRO61I_4core3fmt5write"

gen_ls_blk 206
gen_ls_blk 208
gen_ls_blk 211
gen_ls_blk 215
gen_ls_blk 252
gen_ls_blk 254
gen_ls_blk 255

end CryptoVerification
