/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop

/-!
# Refinement of `RatchetState::find_receiver_chain_index`

Proves that `RatchetState::find_receiver_chain_index` (`0xea88`) with callees
`PublicKey::deserialize`, `<PublicKey as PartialEq>::eq`, and `<[u8] as ConstantTimeEq>::ct_eq`
satisfies `findIndexSpec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-- `RatchetState::find_receiver_chain_index` satisfies `FindIndexOk`. -/
theorem find_receiver_chain_index_ok (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) (A : RustAlloc)
    (himg : Obj.Loads libsignalSessionImage img) :
    FindIndexOk img F alloc A := by
  exact FindReceiverChainIndex.find_receiver_chain_index_bridge img F alloc A himg

theorem find_receiver_chain_index_placed_ok [LibsignalPlacement]
    {H : String → Option (State → State)} (A : RustAlloc)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_26).rebase (blkPl_26).base H) (blkPl_26).base
      (withLsCodeLoaded lsmpl (FindReceiverChainIndex.findPlacedSpec A)) :=
  FindReceiverChainIndex.find_receiver_chain_index_placed_ok A h_bb

end CryptoVerification.LibsignalSession
