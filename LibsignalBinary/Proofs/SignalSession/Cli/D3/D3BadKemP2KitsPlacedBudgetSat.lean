/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetSat

/-!
# `HookSat` Sibling of `D3BadKemP2KitsPlacedBudget` (`D3BadKemP2KitsPlacedBudgetSat`)

Provides the 4 `[LibsignalFullPlacement]` cross-block / `4K` `initialize_bob_session`
(Block `75`) Bad-KEM contracts of `D3BadKemP2KitsPlacedBudget` Section 1 re-typed over
`PqxdhPlacedHookContractsSat`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudgetSat

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalFullPlacement LibsignalHooks lsMemcpySym lsmpl)
open CryptoVerification.E2E.Pqxdh.Initiator (Primitives StructuralPrims)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (PrimitivesMatchCrypto ls_subroutine_ok_withLsFrozen_of_block)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget
  (hookSat_framelessMemcpy_of_allocMemcpyVm)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
  (PqxdhPlacedHookContractsSat)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetSat
  (initializeBobSession_badKem_errOwned_full_placed_ok_sat)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpySpec)

export LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget (
  AcceptBadKemEnv
  initializeBobSessionBadKemErrOwned4KFrozenPlacedSpec
  initializeBobSessionBadKemErrOwnedFrozenPlacedSpec
  initializeBobSessionBadKemErrOwnedFrozenPlacedSpec_to_4K
)

/-- Closed `[LibsignalFullPlacement]` budget-threaded owned-error rejecting contract for
`initialize_bob_session` (Block `75`) on Bad-KEM lifted to any `callerProg` at `lsmpl.base 75`. -/
public theorem initializeBobSession_badKem_errOwned_full_placed_ok_of_block_sat
    [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 75)
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A lim (AcceptBadKemEnv P)) :=
  ls_subroutine_ok_withLsFrozen_of_block
    (initializeBobSession_badKem_errOwned_full_placed_ok_sat hWF hP hH h_memcpy)

/-- `allocMemcpyVmSpec` convenience wrapper around
`initializeBobSession_badKem_errOwned_full_placed_ok_of_block_sat`. -/
public theorem initializeBobSession_badKem_errOwned_full_placed_ok_of_block_std_sat
    [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok callerProg (lsmpl.base 75)
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A lim (AcceptBadKemEnv P)) :=
  initializeBobSession_badKem_errOwned_full_placed_ok_of_block_sat hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)

/-- Closed `[LibsignalFullPlacement]` `4K` (`768 + pqxdhEntryStackExt`) contract for
`initialize_bob_session` (Block `75`) on Bad-KEM lifted to any `callerProg` at `lsmpl.base 75`. -/
public theorem initializeBobSession_badKem_errOwned_4K_full_placed_ok_of_block_sat
    [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 75)
      (initializeBobSessionBadKemErrOwned4KFrozenPlacedSpec A lim (AcceptBadKemEnv P)) :=
  initializeBobSessionBadKemErrOwnedFrozenPlacedSpec_to_4K
    (initializeBobSession_badKem_errOwned_full_placed_ok_of_block_sat hWF hP hH h_memcpy)

/-- `allocMemcpyVmSpec` convenience wrapper around
`initializeBobSession_badKem_errOwned_4K_full_placed_ok_of_block_sat`. -/
public theorem initializeBobSession_badKem_errOwned_4K_full_placed_ok_of_block_std_sat
    [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok callerProg (lsmpl.base 75)
      (initializeBobSessionBadKemErrOwned4KFrozenPlacedSpec A lim (AcceptBadKemEnv P)) :=
  initializeBobSessionBadKemErrOwnedFrozenPlacedSpec_to_4K
    (initializeBobSession_badKem_errOwned_full_placed_ok_of_block_std_sat hWF hP hH h_memcpy)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudgetSat
