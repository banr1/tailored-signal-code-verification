/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooksPlacedSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecsHook

/-!
# `HookSat`-Backed `MainIoPlacedSat` on `cliGhostExterns` (`MainOkA1PlacedSat`)

- **Role**: `Role::Proof` (outside the TCB). Untrusted groundwork for #1255 (HOOKS-PREP).
- **Overview**:
  Budget-threaded `HookSat` sibling of `MainOkA1Placed.mainIo_of_cliGhostExterns_placed` and
  `MainOkA1Placed.mainIo_of_hookSat_placed` (`:104–133`), building `MainIoPlacedSat` on
  `cliGhostExterns g H0` from `HookSat H0 lsWrite*Sym (write*SpecPlacedSat …)` instead of
  `H0 lsWrite*Sym = some write*Hook`, plus exact-table recovery corollaries at
  `H0 := cliExternsPlaced mmpl W` via `IoHonestSpecsHook`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainOkA1PlacedSat

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsRoCl)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsMemcpySym lsMemsetSym lsReadFileSym lsReadStdinSym lsRustAllocSymCli
   lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli
   lsStringCloneSym lsWriteFileSym lsWriteStdoutSym)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliExternsPlaced_writeFile cliExternsPlaced_writeStdout cliIo)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns cliGhostExterns_other)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
  (writeFileSpecPlacedSat writeFileStackFloor writeStdoutSpecPlacedSat writeStdoutStackFloor)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecsHook
  (hookSat_writeFileSpecPlacedSat_of_hook hookSat_writeStdoutSpecPlacedSat_of_hook)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooksPlacedSat
  (mainIo_of_lookup_placed_sat writeFile_rocl_ok_of_hookSat writeStdout_rocl_ok_of_hookSat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileLitSpecPlaced readStdinSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudgetSat (MainIoPlacedSat)

private theorem hookSat_cliGhostExterns_other {α : Type} (g : CliGhostHooks)
    (H0 : LibsignalHooks) {sym : String} {spec : Spec α}
    (hsat : HookSat H0 sym spec)
    (h1 : sym ≠ lsRustAllocSymCli := by decide)
    (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide)
    (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide)
    (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ lsReadFileSym := by decide)
    (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ lsMemsetSym := by decide)
    (h10 : sym ≠ lsMemcpySym := by decide) :
    HookSat (cliGhostExterns g H0) sym spec := by
  rcases hsat with ⟨f, hf, hok⟩
  exact ⟨f, (cliGhostExterns_other g H0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).trans hf, hok⟩

/-- `MainIoPlacedSat` on `cliGhostExterns g H0` from `readStdin`/`readFile` `subroutine_ok`
    hypotheses and `HookSat H0 lsWrite*Sym (write*SpecPlacedSat …)` write hypotheses. -/
theorem mainIo_of_cliGhostExterns_placed_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H0 : LibsignalHooks} (g : CliGhostHooks) (stk : Nat)
    (hReadStdin : subroutine_ok (lsProg_617 (cliGhostExterns g H0))
      (lsρ lsReadStdinSym) (withLsRoCl lsmpl (readStdinSpecPlaced cliIo A lim stk)))
    (hReadFile : subroutine_ok (lsProg_617 (cliGhostExterns g H0))
      (lsρ lsReadFileSym) (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo A lim stk)))
    (hWriteFile : HookSat H0 lsWriteFileSym (writeFileSpecPlacedSat cliIo A lim stk))
    (hWriteStdout : HookSat H0 lsWriteStdoutSym (writeStdoutSpecPlacedSat A lim stk))
    (hwfStk : writeFileStackFloor ≤ stk := by decide)
    (hwsStk : writeStdoutStackFloor ≤ stk := by decide) :
    MainIoPlacedSat A lim (cliGhostExterns g H0) cliIo stk where
  readStdin := hReadStdin
  readFile := hReadFile
  writeFile := writeFile_rocl_ok_of_hookSat (hookSat_cliGhostExterns_other g H0 hWriteFile)
  writeStdout := writeStdout_rocl_ok_of_hookSat (hookSat_cliGhostExterns_other g H0 hWriteStdout)
  hWriteFileStack := hwfStk
  hWriteStdoutStack := hwsStk

/-- Exact-table recovery corollary of `mainIo_of_cliGhostExterns_placed_sat` on
    `cliExternsPlaced mmpl W` via `IoHonestSpecsHook`. -/
theorem mainIo_of_cliGhostExterns_placed_of_hooks_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (stk : Nat)
    (hReadStdin : subroutine_ok (lsProg_617 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadStdinSym) (withLsRoCl lsmpl (readStdinSpecPlaced cliIo A lim stk)))
    (hReadFile : subroutine_ok (lsProg_617 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo A lim stk)))
    (hwfStk : writeFileStackFloor ≤ stk := by decide)
    (hwsStk : writeStdoutStackFloor ≤ stk := by decide) :
    MainIoPlacedSat A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) cliIo stk :=
  mainIo_of_cliGhostExterns_placed_sat g stk hReadStdin hReadFile
    (hookSat_writeFileSpecPlacedSat_of_hook (cliExternsPlaced_writeFile mmpl W))
    (hookSat_writeStdoutSpecPlacedSat_of_hook (cliExternsPlaced_writeStdout mmpl W))
    hwfStk hwsStk

/-- `MainIoPlacedSat` on `cliGhostExterns g H0` from `HookSat` read and write hypotheses. -/
theorem mainIo_of_hookSat_placed_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H0 : LibsignalHooks} (g : CliGhostHooks) (stk : Nat)
    (hReadStdin : HookSat (cliGhostExterns g H0) lsReadStdinSym
      (readStdinSpecPlaced cliIo A lim stk))
    (hReadFile : HookSat (cliGhostExterns g H0) lsReadFileSym
      (readFileLitSpecPlaced cliIo A lim stk))
    (hWriteFile : HookSat H0 lsWriteFileSym (writeFileSpecPlacedSat cliIo A lim stk))
    (hWriteStdout : HookSat H0 lsWriteStdoutSym (writeStdoutSpecPlacedSat A lim stk))
    (hwfStk : writeFileStackFloor ≤ stk := by decide)
    (hwsStk : writeStdoutStackFloor ≤ stk := by decide) :
    MainIoPlacedSat A lim (cliGhostExterns g H0) cliIo stk :=
  mainIo_of_lookup_placed_sat stk hReadStdin hReadFile
    (hookSat_cliGhostExterns_other g H0 hWriteFile)
    (hookSat_cliGhostExterns_other g H0 hWriteStdout)
    hwfStk hwsStk

/-- Exact-table recovery corollary of `mainIo_of_hookSat_placed_sat` on
    `cliExternsPlaced mmpl W` via `IoHonestSpecsHook`. -/
theorem mainIo_of_hookSat_placed_of_hooks_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (stk : Nat)
    (hReadStdin : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadStdinSym
      (readStdinSpecPlaced cliIo A lim stk))
    (hReadFile : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileLitSpecPlaced cliIo A lim stk))
    (hwfStk : writeFileStackFloor ≤ stk := by decide)
    (hwsStk : writeStdoutStackFloor ≤ stk := by decide) :
    MainIoPlacedSat A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) cliIo stk :=
  mainIo_of_hookSat_placed_sat g stk hReadStdin hReadFile
    (hookSat_writeFileSpecPlacedSat_of_hook (cliExternsPlaced_writeFile mmpl W))
    (hookSat_writeStdoutSpecPlacedSat_of_hook (cliExternsPlaced_writeStdout mmpl W))
    hwfStk hwsStk

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainOkA1PlacedSat
