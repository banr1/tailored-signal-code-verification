/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.TooFarPathProofs.Fetch
import LibsignalBinary.Proofs.ConsumeMessageKey.TooFarPathProofs.Core

/-!
# Too-Far Future-Counter Path of `RatchetState::consume_message_key`

Symbolic execution from `cmkTooFarPC` (`+0x170`) when `max_forward_jumps < counter - ck.index`:
allocates the 36-byte `"message from too far into the future"` error string (or panics on OOM at
`+0x9f4`), writes `InvalidMessage(msgType, msg)` into `ret`, and returns via `+0x77c`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-- Too-far future-counter path correctness (`TooFarPathSpec`). -/
theorem tooFarPath_ok (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) :
    TooFarPathSpec F A alloc img :=
  TooFarPath.tooFarPath_ok' F A alloc img

/-- Placed too-far future-counter path correctness (`TooFarPathPlacedSpec`). -/
theorem tooFarPath_placed_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    TooFarPathPlacedSpec F A H :=
  TooFarPath.tooFarPath_placed_ok' F A H

end CryptoVerification.LibsignalSession
