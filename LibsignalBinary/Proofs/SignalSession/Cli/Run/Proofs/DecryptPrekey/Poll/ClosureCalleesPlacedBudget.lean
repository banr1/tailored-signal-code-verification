/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Pure and Crypto Callee Discharges

Discharges `ChainClone3OkPlaced`, `SenderChainClone3OkPlaced`, `dropSessionStructureLocal2Spec`,
and `FsAt` under `ClosureStagesStmtPlacedBudget.RunHooksPlaced A lim`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCalleesPlacedBudget

open Arm64 ProofLib
open CryptoVerification (IsLsBlockProg LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsAt FsFiles)
open CryptoVerification.LibsignalTripleRatchet (noAllocShimSpec)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots (cliGhostExterns_sat_of_cliExternsPlaced)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
  (ChainClone3OkPlaced SenderChainClone3OkPlaced chainClone3_placed_ok_of_hooks
   senderChainClone3_placed_ok_of_hooks)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
  (drop_session_structure4_placed_ok_at)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (cliExternsPlaced_sessionMemcpyRegion_budget_sat)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
  (dropSessionStructureLocal2Spec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. `ChainClone3`, `SenderChainClone3`, & `DropSessionStructure4` under `[LibsignalPlacement]` -/

private theorem noAllocShimBudget_eq_sessionShimBudget :
    withVmPreserved noAllocShimSpec = sessionShimBudgetSpec := rfl

private theorem framelessMemcpyBudget_eq_sessionMemcpyRegionBudget :
    withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec := rfl

theorem cliChainClone3_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    ChainClone3OkPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  chainClone3_placed_ok_of_hooks
    (noAllocShimBudget_eq_sessionShimBudget ▸ hh.codecHooks.shim)
    hh.codecHooks.alloc
    (framelessMemcpyBudget_eq_sessionMemcpyRegionBudget ▸ hh.codecHooks.memcpy)

theorem cliSenderChainClone3_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    SenderChainClone3OkPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  senderChainClone3_placed_ok_of_hooks
    (noAllocShimBudget_eq_sessionShimBudget ▸ hh.codecHooks.shim)
    hh.codecHooks.alloc
    (framelessMemcpyBudget_eq_sessionMemcpyRegionBudget ▸ hh.codecHooks.memcpy)

theorem cliDropSessionStructure4_placed_ok_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  drop_session_structure4_placed_ok_at hh.codecHooks.dealloc hi

theorem cliFsAt_of_files_eq_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {i : Nat}
    {ext : String → Option (State → State)} [IsLsBlockProg prog i ext]
    {envOk : FsFiles → Prop} {Q : Prop} {F0 : FsFiles} {s : State}
    (hh : RunHooksPlaced A lim ext)
    (hQ : Q) (henv : envOk F0) (hf : s.fs.files = F0) :
    FsAt envOk Q prog s :=
  .inr ⟨hQ, hh.fs prog i, hf ▸ henv⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCalleesPlacedBudget
