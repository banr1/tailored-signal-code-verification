/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndex -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopSat -- proof-setup: allow-public-import

/-!
# `HookSat`-backed `black_box` Sibling of `ConsumeMessageKey/FindIndex`

Weakens `h_bb : H lsBlackBoxU8Sym = some blackBoxHook` to
`h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat` on `find_receiver_chain_index_placed_ok_sat`,
keeping a token-identical conclusion on `withLsCodeLoaded lsmpl (FindReceiverChainIndex.findPlacedSpec A)`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexSat

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement blkPC_26 blkPl_26 lsBlackBoxU8Sym lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSession.FindReceiverChainIndex (findPlacedSpec)
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat (blackBoxSpecSat)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopSat
  (find_receiver_chain_index_placed_ok_sat)

/-- `HookSat` `black_box` sibling of `CryptoVerification.LibsignalSession.find_receiver_chain_index_placed_ok`
(token-identical conclusion). -/
theorem find_receiver_chain_index_placed_ok_sat [LibsignalPlacement]
    {H : String → Option (State → State)} (A : RustAlloc)
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_26).rebase (blkPl_26).base H) (blkPl_26).base
      (withLsCodeLoaded lsmpl (findPlacedSpec A)) :=
  LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopSat.find_receiver_chain_index_placed_ok_sat
    A h_bb

end LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexSat
