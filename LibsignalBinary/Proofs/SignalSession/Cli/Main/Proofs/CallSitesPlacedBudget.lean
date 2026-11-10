/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Call-Site Helpers for `main`

Block-`617` (`lsProg_617 H`) callee corollaries over `RustCliAllocBudget M` from
`AllocContractsXCliPlaced`, `AllocContractsFsPlaced`, and `MainCalleesBlk617`, re-exporting
allocator-polymorphic `SepWPp` combinators from `CallSitesPlaced.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName withStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession
  (lsFromUtf8Sym lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617 lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (fromUtf8AsciiSpec lsHandleErrorSymMain strlenSpec)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget

open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
  (addressSpec reserve16Spec)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
  (MainCalleesBlk617 tryAllocateInRustSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (session2MemcpyBudgetSpecX session2ShimBudgetSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustAllocSpecWithStack rustDeallocExternSpecWithStack)

/-! ## Block `617` Callee Corollaries (`withLsRoCl lsmpl`) -/

theorem main_panic_handle_error_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack) :
    ((blkPC_617).rebase (blkPl_617).base H).externAt? (lsρ lsHandleErrorSymMain) =
      some Rust.panicked :=
  hc.handleErrorPanic

theorem main_shim_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl session2ShimBudgetSpecX) :=
  AllocFsSitesPlacedBudget.AllocContractsXCliPlaced.shim2_rocl hC (prog := lsProg_617 H) (i := 617)

theorem main_alloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustAllocSpecWithStack M A lim false extHookStack)) :=
  AllocFsSitesPlacedBudget.AllocContractsXCliPlaced.alloc_rocl hC (prog := lsProg_617 H) (i := 617)

theorem main_dealloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack)) :=
  AllocFsSitesPlacedBudget.AllocContractsXCliPlaced.dealloc_rocl hC (prog := lsProg_617 H) (i := 617)

theorem main_memcpy_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl (sessionMemcpyBudgetSpec extHookStack)) :=
  AllocFsSitesPlacedBudget.AllocContractsXCliPlaced.session_memcpy_rocl hC
    (prog := lsProg_617 H) (i := 617) extHookStack (Nat.le_refl _) (by decide)

theorem main_shim_fs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsFsPlaced A lim H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl session2ShimBudgetSpecX.keepsFs) :=
  AllocFsSitesPlacedBudget.AllocContractsFsPlaced.shim2_rocl hC (prog := lsProg_617 H) (i := 617)

theorem main_alloc_fs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsFsPlaced A lim H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustAllocSpecWithStack M A lim false extHookStack).keepsFs) :=
  AllocFsSitesPlacedBudget.AllocContractsFsPlaced.alloc_rocl hC (prog := lsProg_617 H) (i := 617)

theorem main_dealloc_fs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsFsPlaced A lim H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs) :=
  AllocFsSitesPlacedBudget.AllocContractsFsPlaced.dealloc_rocl hC (prog := lsProg_617 H) (i := 617)

theorem main_memcpy_fs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsFsPlaced A lim H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl (sessionMemcpyBudgetSpec extHookStack).keepsFs) :=
  AllocFsSitesPlacedBudget.AllocContractsFsPlaced.session_memcpy_rocl hC
    (prog := lsProg_617 H) (i := 617) extHookStack (Nat.le_refl _) (by decide)

theorem main_memcpy2_fs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsFsPlaced A lim H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl session2MemcpyBudgetSpecX.keepsFs) :=
  AllocFsSitesPlacedBudget.AllocContractsFsPlaced.memcpy2_rocl hC (prog := lsProg_617 H) (i := 617)

theorem main_libc_memcpy_fs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsFsPlaced A lim H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl (withVmPreserved (libcMemcpySpec extHookStack)).keepsFs) :=
  AllocFsSitesPlacedBudget.AllocContractsFsPlaced.memcpy_rocl hC
    (prog := lsProg_617 H) (i := 617) extHookStack (Nat.le_refl _) (by decide)

theorem main_session_memcpy_ro_fs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsFsPlaced A lim H) (stk : Nat)
    (hstk : extHookStack ≤ stk) (h64 : stk ≤ 2 ^ 64) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl (withStack (withVmPreserved sessionMemcpyRegionROSpec) stk).keepsFs) :=
  AllocFsSitesPlacedBudget.AllocContractsFsPlaced.session_memcpy_region_ro_rocl hC
    (prog := lsProg_617 H) (i := 617) stk hstk h64

theorem main_strlen_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ "strlen")
      (withLsRoCl lsmpl (withVmPreserved (strlenSpec hookStack))) :=
  hc.strlen

theorem main_fromUtf8_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsFromUtf8Sym)
      (withLsRoCl lsmpl (withVmPreserved (fromUtf8AsciiSpec hookStack))) :=
  hc.fromUtf8

theorem main_address_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpec A lim uuidParse resStack)) :=
  hc.address

theorem main_reserve16_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 561)
      (withLsRoCl lsmpl (reserve16Spec A lim resStack)) :=
  hc.reserve16

theorem main_reserve1_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 561)
      (withLsRoCl lsmpl (doReserveSpecOf resStack A lim).keepsFs) :=
  hc.reserve1

theorem main_tryAllocateIn3_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 588)
      (withLsRoCl lsmpl (tryAllocateInRustSpecOf resStack A lim).keepsFs) :=
  hc.tryAllocateIn3

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget
