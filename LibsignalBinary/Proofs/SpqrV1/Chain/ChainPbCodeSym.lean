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
# Relocatable Per-Block Fetches for `SpqrV1/Chain`

Per-block instruction fetch definitions for `Chain` and drop-glue code blocks:
- Block `287`: `core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]`
- Block `288`: `core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>`
- Block `364`: `<spqr::chain::Chain>::from_pb`
- Block `365`: `<spqr::chain::Chain>::into_pb`
- Block `366`: `<spqr::chain::Chain>::recv_key`
- Block `367`: `<spqr::chain::Chain>::send_key`
- Block `368`: `<spqr::chain::Chain>::add_epoch`
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

gen_ls_blk 287
gen_ls_blk 288
gen_ls_blk 364
gen_ls_blk 365
gen_ls_blk 366
gen_ls_blk 367
gen_ls_blk 368

end CryptoVerification
