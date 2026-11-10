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
# Relocatable Per-Block Fetches for `SpqrV1/Top` Leaf and Mid Functions

Provides relocatable instruction fetches for `spqr::chain_from`, `spqr::init_inner`,
`spqr::encode_varint`, `spqr::initial_state`, `spqr::chain_from_version_negotiation`,
`Message::deserialize`, and `Message::serialize`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.SpqrV1.Top.Placed

open Arm64 Arm64.Obj ProofLib CryptoVerification

set_option maxHeartbeats 8000000 in
gen_ls_blk 323

set_option maxHeartbeats 8000000 in
gen_ls_blk 324

set_option maxHeartbeats 8000000 in
gen_ls_blk 326

set_option maxHeartbeats 8000000 in
gen_ls_blk 327

set_option maxHeartbeats 4000000 in
gen_ls_blk 328

set_option maxHeartbeats 8000000 in
gen_ls_blk 351

set_option maxHeartbeats 8000000 in
gen_ls_blk 352

end CryptoVerification.SpqrV1.Top.Placed
