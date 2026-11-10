/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Common
import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Core

/-!
# Past-Counter Take Path of `RatchetState::consume_message_key`

Symbolic execution from `cmkTakePC` (`+0x05c`) to `ret` (`+0x798`) when `counter < ck.index`:
calls `find_receiver_chain_index`, searches `message_keys` for a matching counter (`+0x094 .. +0x0b0`),
and either removes and returns the stored key via `memmove` (`+0x5e4 .. +0x778`) or returns
`DuplicatedMessage(ck.index, counter)` (`+0x0b4 .. +0x16c`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-- Past-counter take-path correctness (`TakePathSpec`). -/
theorem takePath_ok (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) :
    TakePathSpec F A alloc img := by
  exact TakePath.takePath_ok_thm F A alloc img

/-- Placed past-counter take-path correctness (`TakePathPlacedSpec`). -/
theorem takePath_placed_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    TakePath.TakePathPlacedSpec F A H :=
  TakePath.takePath_placed_ok_thm F A H

end CryptoVerification.LibsignalSession
