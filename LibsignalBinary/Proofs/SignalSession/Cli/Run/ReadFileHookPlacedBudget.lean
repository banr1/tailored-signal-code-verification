/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import Arm64.Trusted.Spec.Hoare

/-!
# Budget-Threaded `signal_session_io::read_file` Contracts (Placed)

Lifts budget-threaded `HookSat` for `lsReadFileSym`
(`readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv`) to `subroutine_ok` on any unmutated
caller block `i < 619` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHookPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks
   ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles subroutine_ok_withLsCodeRoLoaded_of_plain withLsCodeRoLoaded)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)

theorem cliReadFilePlaced_hookSat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (stk : Nat)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hRead : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv) :=
  hRead

/-- Lifts budget-threaded `HookSat` at `lsReadFileSym` on
`cliGhostExterns g (cliExternsPlaced mmpl W)` to `subroutine_ok`. -/
theorem cliReadFilePlaced_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (stk : Nat)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {prog : Program} {i : Nat}
    [IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hRead : subroutine_ok prog (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv)) :
    subroutine_ok prog (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv) :=
  hRead

theorem cliReadFilePlaced_rocl_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) (stk : Nat)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {prog : Program} {i : Nat}
    [IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hRead : subroutine_ok prog (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv)) :
    subroutine_ok prog (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain (cliReadFilePlaced_ok mmpl g W stk hRead)

/-- Generic `{H : LibsignalHooks}` lift of `HookSat H lsReadFileSym` to `subroutine_ok` on any
unmutated block `i < 619`. -/
theorem cliReadFilePlaced_ok_of_hookSat [LibsignalPlacement] {H : LibsignalHooks} (stk : Nat)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {prog : Program} {i : Nat} [IsLsBlockProg prog i H]
    (hReadHook : HookSat H lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv) :=
  ls_hook_ok_ultra_of_mem hReadHook (by decide) hi hunmut

theorem cliReadFilePlaced_rocl_ok_of_hookSat [LibsignalPlacement] {H : LibsignalHooks} (stk : Nat)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {prog : Program} {i : Nat} [IsLsBlockProg prog i H]
    (hReadHook : HookSat H lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain (cliReadFilePlaced_ok_of_hookSat stk hReadHook hi hunmut)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHookPlacedBudget
