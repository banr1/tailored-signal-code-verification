/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdrBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampledPlaced

/-!
# Budget-Threaded Relocatable Callee Contracts for Inlined `.keysUnsampled` Arm (Block 124)

Defines `RustCliAllocBudget M` counterparts `AuthMacHdrPinnedPlacedOkX` (Block 342) and
`DoReserve2PlacedOkX` (Block 157) on `spqrSendPlacedProg`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement blkPC_157 blkPl_157 lsmpl)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Top.Send
  (subroutine_ok_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
  (doReserve1Raw32Spec do_reserve_2_raw32_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Auth.MacHdrBudget (authMacHdrPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced spqrSendPlacedProg)

export CryptoVerification.SpqrV1.Top.Send
  (subroutine_ok_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded)

variable [LibsignalPlacement]

/-- `<spqr::authenticator::Authenticator>::mac_hdr` (Block `342`) meets
    `withLsCodeRoLoaded lsmpl (authMacHdrPinnedSpec F M A lim)` on `spqrSendPlacedProg ext`. -/
def AuthMacHdrPinnedPlacedOkX (F : ShaCompress) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 342)
    (withLsCodeRoLoaded lsmpl (authMacHdrPinnedSpec F M A lim))

/-- `alloc::raw_vec::RawVecInner<A>::do_reserve_and_handle [local#2]` (Block `157`) meets
    `withLsCodeRoLoaded lsmpl (doReserve1Raw32Spec M A lim)` on `spqrSendPlacedProg ext`. -/
def DoReserve2PlacedOkX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 157)
    (withLsCodeRoLoaded lsmpl (doReserve1Raw32Spec M A lim))

theorem doReserve2_placed_ok_ext_x {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    DoReserve2PlacedOkX M A lim ext := by
  have hraw : subroutine_ok ((blkPC_157).rebase (blkPl_157).base (Rust.withPanics ext))
      (lsmpl.base 157) (withLsCodeRoLoaded lsmpl (doReserve1Raw32Spec M A lim)) :=
    subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (do_reserve_2_raw32_placed_ok (M := M) (A := A) (lim := lim) (H := Rust.withPanics ext)
        hA.handle_error hA.noAllocShim hA.alloc hA.realloc)
  exact CryptoVerification.SpqrV1.ls_subroutine_ok_of_blockProgram_cro
    (CryptoVerification.SpqrV1.ls_subroutine_ok_to_blockProgram hraw)

end LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
