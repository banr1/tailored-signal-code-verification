/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymBasePlaced

/-! # Block `332` (`States::recv`) Placed Fetch Shard 4 (`[13024 → 16276]`) -/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification

open ProofLib.GenPlacedFetches

gen_placed_fetches blkPC_332 blkLib_332 blkTree_332 blkCodeEq_332 blkTreeSize_332
  via_placement blkPl_332 blkPlaceable_332 [13024 → 16276]

end CryptoVerification
