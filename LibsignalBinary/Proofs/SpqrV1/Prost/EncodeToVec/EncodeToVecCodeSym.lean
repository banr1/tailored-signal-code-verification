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
# Relocatable Per-Block Fetches for `Prost/EncodeToVec`

Pre-extracted instruction-fetch tables for `encode::<PolynomialDecoder>` (Block `315`),
`encode::<PolynomialEncoder>` (Block `316`), and `PqRatchetState::encode_to_vec` (Block `426`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open CryptoVerification

set_option maxHeartbeats 8000000 in
gen_ls_blk 426

end CryptoVerification.SpqrV1.Prost.EncodeToVec
