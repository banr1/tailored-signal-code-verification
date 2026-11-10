/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudgetSat -- proof-setup: allow-public-import

/-!
# Honest-Write-Spec Relocatable I/O `subroutine_ok` Projections (`IoSitesPlacedBudgetSat`)

- **Role**: `Role::Proof` (outside the TCB). Untrusted groundwork for #1255 (HOOKS-PREP).
- **Overview**:
  Honest-write-spec sibling of
  `LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.IoSitesPlacedBudget` on Block `617`
  (`(blkPC_617).rebase (blkPl_617).base H`), projecting the four `signal_session_io::*` contracts
  from `SpecsPlacedBudgetSat.MainIoPlacedSat`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.IoSitesPlacedBudgetSat

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsRoCl)
open CryptoVerification.SignalSession
  (lsReadFileSym lsReadStdinSym lsWriteFileSym lsWriteStdoutSym)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops (IoModel)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
  (writeFileSpecPlacedSat writeStdoutSpecPlacedSat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileLitSpecPlaced readStdinSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudgetSat (MainIoPlacedSat)

theorem main_readStdin_placed_ok_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    (hio : MainIoPlacedSat A lim H io hookStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl (readStdinSpecPlaced io A lim hookStack)) :=
  hio.readStdin

theorem main_readFile_placed_ok_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    (hio : MainIoPlacedSat A lim H io hookStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsReadFileSym)
      (withLsRoCl lsmpl (readFileLitSpecPlaced io A lim hookStack)) :=
  hio.readFile

theorem main_writeFile_placed_ok_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    (hio : MainIoPlacedSat A lim H io hookStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsWriteFileSym)
      (withLsRoCl lsmpl (writeFileSpecPlacedSat io A lim hookStack)) :=
  hio.writeFile

theorem main_writeStdout_placed_ok_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    (hio : MainIoPlacedSat A lim H io hookStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsWriteStdoutSym)
      (withLsRoCl lsmpl (writeStdoutSpecPlacedSat A lim hookStack)) :=
  hio.writeStdout

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.IoSitesPlacedBudgetSat
