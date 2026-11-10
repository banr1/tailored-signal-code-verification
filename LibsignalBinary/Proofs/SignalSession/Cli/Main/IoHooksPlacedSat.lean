/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooksPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudgetSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecsHook

/-!
# `HookSat`-Backed Block-`617` I/O Lookup & `MainIoPlacedSat` Bridges (`IoHooksPlacedSat`)

- **Role**: `Role::Proof` (outside the TCB). Untrusted groundwork for #1255 (HOOKS-PREP).
- **Overview**:
  Budget-threaded `HookSat` sibling of `IoHooksPlaced` (`:274–374`) on Block `617` (`lsProg_617 H`),
  deriving `subroutine_ok` for `writeFileSpecPlacedSat` / `writeStdoutSpecPlacedSat` and
  `MainIoPlacedSat` from `HookSat H lsWrite*Sym (write*SpecPlacedSat …)` instead of
  `H lsWrite*Sym = some write*Hook`, together with corollaries recovering them from the exact hooks
  via `IoHonestSpecsHook`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooksPlacedSat

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (subroutine_ok_rocl_of_plain withLsRoCl)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsReadFileSym lsReadStdinSym lsWriteFileSym lsWriteStdoutSym
   writeFileHook writeStdoutHook)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliExternsPlaced_writeFile cliExternsPlaced_writeStdout cliIo)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
  (writeFileSpecPlacedSat writeFileStackFloor writeStdoutSpecPlacedSat writeStdoutStackFloor)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecsHook
  (hookSat_writeFileSpecPlacedSat_of_hook hookSat_writeStdoutSpecPlacedSat_of_hook)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileLitSpecPlaced readStdinSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudgetSat (MainIoPlacedSat)

/-- `write_file` on Block `617` (`lsProg_617 H`) from `HookSat H lsWriteFileSym (writeFileSpecPlacedSat …)`. -/
theorem writeFile_rocl_ok_of_hookSat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {stk : Nat}
    (hSat : HookSat H lsWriteFileSym (writeFileSpecPlacedSat cliIo A lim stk)) :
    subroutine_ok (lsProg_617 H) (lsρ lsWriteFileSym)
      (withLsRoCl lsmpl (writeFileSpecPlacedSat cliIo A lim stk)) :=
  subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hSat (by decide)

/-- `write_stdout` on Block `617` (`lsProg_617 H`) from `HookSat H lsWriteStdoutSym (writeStdoutSpecPlacedSat …)`. -/
theorem writeStdout_rocl_ok_of_hookSat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {stk : Nat}
    (hSat : HookSat H lsWriteStdoutSym (writeStdoutSpecPlacedSat A lim stk)) :
    subroutine_ok (lsProg_617 H) (lsρ lsWriteStdoutSym)
      (withLsRoCl lsmpl (writeStdoutSpecPlacedSat A lim stk)) :=
  subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hSat (by decide)

/-- Exact-hook recovery corollary of `writeFile_rocl_ok_of_hookSat` (via `IoHonestSpecsHook`). -/
theorem writeFile_rocl_ok_of_lookup_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (stk : Nat)
    (hLookup : H lsWriteFileSym = some writeFileHook) :
    subroutine_ok (lsProg_617 H) (lsρ lsWriteFileSym)
      (withLsRoCl lsmpl (writeFileSpecPlacedSat cliIo A lim stk)) :=
  writeFile_rocl_ok_of_hookSat (hookSat_writeFileSpecPlacedSat_of_hook hLookup)

/-- Exact-hook recovery corollary of `writeStdout_rocl_ok_of_hookSat` (via `IoHonestSpecsHook`). -/
theorem writeStdout_rocl_ok_of_lookup_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (stk : Nat)
    (hLookup : H lsWriteStdoutSym = some writeStdoutHook) :
    subroutine_ok (lsProg_617 H) (lsρ lsWriteStdoutSym)
      (withLsRoCl lsmpl (writeStdoutSpecPlacedSat A lim stk)) :=
  writeStdout_rocl_ok_of_hookSat (hookSat_writeStdoutSpecPlacedSat_of_hook hLookup)

/-- Unconditional honest `write_file` on `lsProg_617 (cliExternsPlaced mmpl W)` (via T1). -/
theorem writeFile_rocl_ok_placed_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat) :
    subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ lsWriteFileSym)
      (withLsRoCl lsmpl (writeFileSpecPlacedSat cliIo A lim stk)) :=
  writeFile_rocl_ok_of_lookup_sat stk (cliExternsPlaced_writeFile mmpl W)

/-- Unconditional honest `write_stdout` on `lsProg_617 (cliExternsPlaced mmpl W)` (via T1). -/
theorem writeStdout_rocl_ok_placed_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat) :
    subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ lsWriteStdoutSym)
      (withLsRoCl lsmpl (writeStdoutSpecPlacedSat A lim stk)) :=
  writeStdout_rocl_ok_of_lookup_sat stk (cliExternsPlaced_writeStdout mmpl W)

/-- Budget-threaded `read_stdin` on Block `617` (`lsProg_617 H`) from `HookSat`. -/
theorem readStdin_rocl_ok_of_hookSat_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {stk : Nat}
    (hSat : HookSat H lsReadStdinSym (readStdinSpecPlaced cliIo A lim stk)) :
    subroutine_ok (lsProg_617 H) (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl (readStdinSpecPlaced cliIo A lim stk)) :=
  subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hSat (by decide)

/-- Budget-threaded `read_file` on Block `617` (`lsProg_617 H`) from `HookSat`. -/
theorem readFile_rocl_ok_of_hookSat_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {stk : Nat}
    (hSat : HookSat H lsReadFileSym (readFileLitSpecPlaced cliIo A lim stk)) :
    subroutine_ok (lsProg_617 H) (lsρ lsReadFileSym)
      (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo A lim stk)) :=
  subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hSat (by decide)

/-- `MainIoPlacedSat` over any extern map `H` from `HookSat` hypotheses on all four I/O symbols
    plus stack-floor bounds (discharged by `decide` at concrete `stk = extHookStack`). -/
theorem mainIo_of_lookup_placed_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (stk : Nat)
    (hReadStdin : HookSat H lsReadStdinSym (readStdinSpecPlaced cliIo A lim stk))
    (hReadFile : HookSat H lsReadFileSym (readFileLitSpecPlaced cliIo A lim stk))
    (hWriteFile : HookSat H lsWriteFileSym (writeFileSpecPlacedSat cliIo A lim stk))
    (hWriteStdout : HookSat H lsWriteStdoutSym (writeStdoutSpecPlacedSat A lim stk))
    (hwfStk : writeFileStackFloor ≤ stk := by decide)
    (hwsStk : writeStdoutStackFloor ≤ stk := by decide) :
    MainIoPlacedSat A lim H cliIo stk where
  readStdin := readStdin_rocl_ok_of_hookSat_sat hReadStdin
  readFile := readFile_rocl_ok_of_hookSat_sat hReadFile
  writeFile := writeFile_rocl_ok_of_hookSat hWriteFile
  writeStdout := writeStdout_rocl_ok_of_hookSat hWriteStdout
  hWriteFileStack := hwfStk
  hWriteStdoutStack := hwsStk

/-- Exact-hook recovery corollary of `mainIo_of_lookup_placed_sat` via `IoHonestSpecsHook`. -/
theorem mainIo_of_exact_lookup_placed_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (stk : Nat)
    (hReadStdin : HookSat H lsReadStdinSym (readStdinSpecPlaced cliIo A lim stk))
    (hReadFile : HookSat H lsReadFileSym (readFileLitSpecPlaced cliIo A lim stk))
    (hWriteFile : H lsWriteFileSym = some writeFileHook)
    (hWriteStdout : H lsWriteStdoutSym = some writeStdoutHook)
    (hwfStk : writeFileStackFloor ≤ stk := by decide)
    (hwsStk : writeStdoutStackFloor ≤ stk := by decide) :
    MainIoPlacedSat A lim H cliIo stk :=
  mainIo_of_lookup_placed_sat stk hReadStdin hReadFile
    (hookSat_writeFileSpecPlacedSat_of_hook hWriteFile)
    (hookSat_writeStdoutSpecPlacedSat_of_hook hWriteStdout)
    hwfStk hwsStk

/-- `MainIoPlacedSat` at `cliExternsPlaced mmpl W` from `readStdin`/`readFile` `subroutine_ok`
    hypotheses, discharging `writeFile`/`writeStdout` unconditionally via T1. -/
theorem mainIo_of_cliHooks_placed_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat)
    (hReadStdin : subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl (readStdinSpecPlaced cliIo A lim stk)))
    (hReadFile : subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ lsReadFileSym)
      (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo A lim stk)))
    (hwfStk : writeFileStackFloor ≤ stk := by decide)
    (hwsStk : writeStdoutStackFloor ≤ stk := by decide) :
    MainIoPlacedSat A lim (cliExternsPlaced mmpl W) cliIo stk where
  readStdin := hReadStdin
  readFile := hReadFile
  writeFile := writeFile_rocl_ok_placed_sat mmpl W stk
  writeStdout := writeStdout_rocl_ok_placed_sat mmpl W stk
  hWriteFileStack := hwfStk
  hWriteStdoutStack := hwsStk

end LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooksPlacedSat
