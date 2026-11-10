/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare

/-!
# `HookSat` Sibling of `RecvCt2Chunk.CommonPlacedBudget` (`CommonPlacedBudgetSat`)

Replaces `[HkdfPlacedHooks F (Rust.withPanics ext)]` in
`CommonPlacedBudget.hkdfToSlice_placed_ok_of_hooks` (`:1072`) with
`[HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)]`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudgetSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement blkPC_379 blkPl_379 lsmpl)
open CryptoVerification.LibsignalSpqrV1 (spqrHkdfWith)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.ChainProofs (hkdfToSliceSpqrSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat (hkdf_to_slice_spqr_placed_ok_sat)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget (cryptoOfShaCompress)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)

theorem hkdfToSlice_placed_ok_of_hooks_sat [LibsignalPlacement] (F : ShaCompress)
    {ext : String → Option (State → State)} [HkdfPlacedHooksExactBudgetSat F (Rust.withPanics ext)] :
    subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F)))) :=
  hkdf_to_slice_spqr_placed_ok_sat (cryptoOfShaCompress F) (HkdfPlacedHooksExactBudgetSat.memset (F := F))

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudgetSat
