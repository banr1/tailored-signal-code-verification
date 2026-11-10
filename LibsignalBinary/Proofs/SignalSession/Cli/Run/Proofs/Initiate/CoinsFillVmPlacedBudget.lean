/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Cross-Block `withVmPreserved` Lifting for `coinsFillSpecPlacedW3`

Lifts `CoinsFillPlacedBudget.coinsFillSpecPlacedW3` to
`withLsCodeRoLoaded lsmpl (withVmPreserved (Initiate.coinsFillSpecPlacedW3 cStk))` on arbitrary
caller blocks `IsLsBlockProg callerProg i H` and on `initProgPlaced mmpl gh W`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillVmPlacedBudget

noncomputable section

open Arm64 Arm64.Process ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalSessionExterns
   ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (ls_subroutine_ok_rocl_of_plain subroutine_ok_rocl_of_plain
   subroutine_ok_withLsCodeRoLoaded_of_rocl withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack hookMemcpy_region_trace_ok hookMemset_region_trace_ok
   memcpyName memsetName withStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.MainHops (hookMemcpy_fs hookMemset_fs hookOk_withStack)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (cliCoinsFillStack cliCoinsFillStackPlaced initProgPlaced)
open CryptoVerification.SignalSession.Coins.Placed (blkPC_618 blkPl_618)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionMemsetRegionBudgetSpec)
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

private theorem hookMemcpy_vm (s : State) : VmPreserved s (hookMemcpy s) :=
  ⟨⟨rfl, rfl, rfl⟩, rfl,
    fun a => congrFun (LibsignalBinary.Heap.IfaceBudgetLemmas.perm_writeBytes_norm _ _ _) a,
    fun _ _ _ => rfl⟩

private theorem hookMemset_vm (s : State) : VmPreserved s (hookMemset s) :=
  ⟨⟨rfl, rfl, rfl⟩, rfl,
    fun a => congrFun (LibsignalBinary.Heap.IfaceBudgetLemmas.perm_writeBytes_norm _ _ _) a,
    fun _ _ _ => rfl⟩

/-- Weakens `CoinsFillPlacedBudget.coinsFillSpecPlacedW3` to `withVmPreserved (Initiate.coinsFillSpecPlacedW3 stk)`. -/
theorem coinsFill_vm_of_budget [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {stk : Nat}
    (h : subroutine_ok prog entry (CoinsFillPlacedBudget.coinsFillSpecPlacedW3 stk)) :
    subroutine_ok prog entry
      (withVmPreserved
        (CryptoVerification.SignalSession.Cli.RunProofs.Initiate.coinsFillSpecPlacedW3 stk)) := by
  refine subroutine_ok_mono h (fun _ _ _ hpre => hpre) (fun _ _ _ _ hq => ?_)
  dsimp only [CoinsFillPlacedBudget.coinsFillSpecPlacedW3,
    CryptoVerification.SignalSession.Cli.RunProofs.Initiate.coinsFillSpecPlacedW3,
    withLsCodeRoLoaded, withVmPreserved] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨hq.1.2.2, ⟨hq.1.1, hq.1.2.1⟩, hq.2⟩

/-- Cross-block `withVmPreserved (coinsFillSpecPlacedW3 cStk)` proof from `memcpy` and `memset` contracts at `cStk - 80`. -/
theorem signal_session_coins_fill_vm_placed_ok_of_mc_ms [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    {cStk : Nat} (hc1 : 80 ≤ cStk) (hc2 : cStk ≤ 2 ^ 63)
    (hmc : subroutine_ok ((blkPC_618).rebase (blkPl_618).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl (withStack sessionMemcpyRegionBudgetSpec (cStk - 80)).keepsFs))
    (hms : subroutine_ok ((blkPC_618).rebase (blkPl_618).base H) (lsρ memsetName)
      (withLsRoCl lsmpl (withStack sessionMemsetRegionBudgetSpec (cStk - 80)).keepsFs))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl
        (withVmPreserved
          (CryptoVerification.SignalSession.Cli.RunProofs.Initiate.coinsFillSpecPlacedW3 cStk))) := by
  have h618 : subroutine_ok ((blkPC_618).rebase (blkPl_618).base H) (lsmpl.base 618)
      (withVmPreserved
        (CryptoVerification.SignalSession.Cli.RunProofs.Initiate.coinsFillSpecPlacedW3 cStk)) :=
    coinsFill_vm_of_budget
      (CoinsFillPlacedBudget.signal_session_coins_fill_placed_ok_of_mc_ms hc1 hc2 hmc hms)
  exact subroutine_ok_withLsCodeRoLoaded_of_rocl
    (ls_subroutine_ok_rocl_of_plain (callerProg := callerProg) h618 hi)

/-- Cross-block `withVmPreserved (coinsFillSpecPlacedW3 cStk)` proof from `AllocContractsFsPlaced A lim H`. -/
theorem signal_session_coins_fill_vm_placed_ok_of_allocFs [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hFs : AllocContractsFsPlaced A lim H)
    {cStk : Nat} (hc1 : cliCoinsFillStackPlaced ≤ cStk) (hc2 : cStk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl
        (withVmPreserved
          (CryptoVerification.SignalSession.Cli.RunProofs.Initiate.coinsFillSpecPlacedW3 cStk))) := by
  have h618 : subroutine_ok ((blkPC_618).rebase (blkPl_618).base H) (lsmpl.base 618)
      (withVmPreserved
        (CryptoVerification.SignalSession.Cli.RunProofs.Initiate.coinsFillSpecPlacedW3 cStk)) :=
    coinsFill_vm_of_budget
      (CoinsFillPlacedBudget.signal_session_coins_fill_placed_ok hFs hc1 hc2)
  exact subroutine_ok_withLsCodeRoLoaded_of_rocl
    (ls_subroutine_ok_rocl_of_plain (callerProg := callerProg) h618 hi)

/-- Instantiates `withVmPreserved (coinsFillSpecPlacedW3 cStk)` on `initProgPlaced mmpl gh W` for `cliCoinsFillStack ≤ cStk ≤ 2 ^ 63`. -/
theorem signal_session_coins_fill_vm_placed_ok_at_init [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh) {cStk : Nat}
    (hc1 : cliCoinsFillStack ≤ cStk) (hc2 : cStk ≤ 2 ^ 63) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (withVmPreserved
          (CryptoVerification.SignalSession.Cli.RunProofs.Initiate.coinsFillSpecPlacedW3 cStk))) := by
  have hge : 80 ≤ cStk := by unfold cliCoinsFillStack extHookStack at hc1; omega
  obtain ⟨fmc, hfmc, _, _, _, hmcReg, _, _, hmcVm, hmcFs, _⟩ := hG.memcpy
  obtain ⟨fms, hfms, _, _, _, hmsReg, hmsVm, hmsFs, _⟩ := hG.memset
  have hmcSat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) memcpyName
      (withStack sessionMemcpyRegionBudgetSpec (cStk - 80)).keepsFs :=
    ⟨fmc,
      LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.cliGhostExterns_memcpy_some
        gh (cliExternsPlaced mmpl W) hfmc,
      (hookOk_withStack
        (hookOk_withVmPreserved hmcReg hmcVm : HookOk fmc sessionMemcpyRegionBudgetSpec)
        (cStk - 80)).keepsFs hmcFs⟩
  have hmsSat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) memsetName
      (withStack sessionMemsetRegionBudgetSpec (cStk - 80)).keepsFs :=
    ⟨fms,
      LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.cliGhostExterns_memset_some
        gh (cliExternsPlaced mmpl W) hfms,
      (hookOk_withStack
        (hookOk_withVmPreserved hmsReg hmsVm : HookOk fms sessionMemsetRegionBudgetSpec)
        (cStk - 80)).keepsFs hmsFs⟩
  exact signal_session_coins_fill_vm_placed_ok_of_mc_ms hge hc2
    (subroutine_ok_rocl_of_plain
      (ls_hook_ok_ultra_of_mem
        (prog := (blkPC_618).rebase (blkPl_618).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        hmcSat))
    (subroutine_ok_rocl_of_plain
      (ls_hook_ok_ultra_of_mem
        (prog := (blkPC_618).rebase (blkPl_618).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        hmsSat))

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillVmPlacedBudget
