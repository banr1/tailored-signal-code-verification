/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudget
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlacedBudget

/-!
# `HookSat` Sibling of `D3BadKemBobAuxPlacedBudget` (`D3BadKemBobAuxPlacedBudgetSat`)

Provides the 4 `[LibsignalFullPlacement]` Bad-KEM error-ownership corollaries of
`D3BadKemBobAuxPlacedBudget` re-typed over `PqxdhPlacedHookContractsSat`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetSat

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalFullPlacement LibsignalHooks
   blkPl_75 lsMemcpySym lsProg_75 lsmpl)
open CryptoVerification.E2E.Pqxdh.Initiator (Primitives StructuralPrims)
open CryptoVerification.E2E.Pqxdh.ResponderCore (PrimitivesMatchCrypto)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudget
  (ecPubKeyIsCanonical_placed_ok_cl)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget
  (hookSat_framelessMemcpy_of_allocMemcpyVm)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
  (PqxdhPlacedHookContractsSat)
open LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlacedBudget
  (vecAppendElements_fast_placed_ok_cl)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpySpec)

export LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget (
  AcceptBadKemEnv
  initializeBobSessionBadKemErrOwnedFrozenPlacedSpec
  initializeBobSession_badKem_errOwned_frozen_placed_ok_of_accept
  pqxdhAccept_badKem_err_owned_placed_ok_of_block
)

/-- Closed `[LibsignalFullPlacement]` budget-threaded owned-error rejecting contract for
`Pqxdh::accept` (Block `79`) on Bad-KEM lifted to any `callerProg` at `lsmpl.base 79`. -/
public theorem pqxdhAccept_badKem_err_owned_full_placed_ok_of_block_sat [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec
        A lim (AcceptBadKemEnv P)) :=
  pqxdhAccept_badKem_err_owned_placed_ok_of_block hWF
    (ecPubKeyIsCanonical_placed_ok_cl hWF hH.dalekMontToEd hH.dalekTorsionFree)
    (hH.calculateAgreement_ok hP)
    (vecAppendElements_fast_placed_ok_cl h_memcpy)
    hH.noAllocShim hH.alloc hH.dealloc h_memcpy

/-- `allocMemcpyVmSpec` convenience wrapper around
`pqxdhAccept_badKem_err_owned_full_placed_ok_of_block_sat`. -/
public theorem pqxdhAccept_badKem_err_owned_full_placed_ok_of_block_std_sat
    [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec
        A lim (AcceptBadKemEnv P)) :=
  pqxdhAccept_badKem_err_owned_full_placed_ok_of_block_sat hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)

/-- Closed `[LibsignalFullPlacement]` budget-threaded owned-error rejecting contract for
`initialize_bob_session` (Block `75`) on Bad-KEM. -/
public theorem initializeBobSession_badKem_errOwned_full_placed_ok_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A lim (AcceptBadKemEnv P)) :=
  initializeBobSession_badKem_errOwned_frozen_placed_ok_of_accept
    (pqxdhAccept_badKem_err_owned_full_placed_ok_of_block_sat hWF hP hH h_memcpy)

/-- `allocMemcpyVmSpec` convenience wrapper around
`initializeBobSession_badKem_errOwned_full_placed_ok_sat`. -/
public theorem initializeBobSession_badKem_errOwned_full_placed_ok_std_sat
    [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A lim (AcceptBadKemEnv P)) :=
  initializeBobSession_badKem_errOwned_full_placed_ok_sat hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetSat
