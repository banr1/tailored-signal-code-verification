/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.AdvanceChainKey
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DeriveSeed
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.EvictOldestKey
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.InsertKey

/-!
# Store-Loop Iteration of `RatchetState::consume_message_key`

Assembles the four store-loop sub-segments (`DeriveSeed`, `InsertKey`, `EvictOldestKey`, and
`AdvanceChainKey`, `+0x334 → +0x334 / +0x4dc`) to establish `StoreLoopIterSpec` as well as placed
`StoreLoopIterPlacedSpec` and `StoreLoopPlacedSpec` on Block 24.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-- Single-iteration store-loop correctness (`StoreLoopIterSpec`). -/
theorem storeLoop_iter_ok (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) :
    StoreLoopIterSpec F A alloc img := by
  exact StoreLoop.storeLoop_iter_of_parts
    (StoreLoop.deriveSeed_ok F A alloc img)
    (StoreLoop.insertKey_ok F A alloc img)
    StoreLoop.evictOldestKey_ok
    (StoreLoop.advanceChainKey_ok F A alloc img)

/-- Placed single-iteration store-loop correctness (`StoreLoopIterPlacedSpec`). -/
theorem storeLoop_iter_placed_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    StoreLoopIterPlacedSpec F A H :=
  StoreLoop.storeLoop_iter_placed_of_parts
    (StoreLoop.deriveSeed_placed_ok F A H)
    (StoreLoop.insertKey_placed_ok F A H)
    StoreLoop.evictOldestKey_placed_ok
    (StoreLoop.advanceChainKey_placed_ok F A H)

/-- Placed full store-loop correctness (`StoreLoopPlacedSpec`). -/
theorem storeLoop_placed_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    StoreLoopPlacedSpec F A H :=
  storeLoop_placed_of_iter (storeLoop_iter_placed_ok F A H)

end CryptoVerification.LibsignalSession
