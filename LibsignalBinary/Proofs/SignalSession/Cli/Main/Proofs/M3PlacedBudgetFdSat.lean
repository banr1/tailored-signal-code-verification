/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlacedSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFd -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Honest-Write-Spec `FdsGe3Closed`-Threaded `MainIoOfPlacedFdSat` (`M3PlacedBudgetFdSat`)

- **Role**: `Role::Proof` (outside the TCB). Untrusted groundwork for #1255 (HOOKS-PREP).
- **Overview**:
  Honest-write-spec twin of `M3PlacedBudgetFd.MainIoOfPlacedFd` and its write-only projection
  `MainIoOfPlacedFd.toWriteOnlyMainIo` (`:146–165`), keeping `readStdin` and `readFile` unchanged
  while replacing `writeFile` and `writeStdout` with `writeFileSpecPlacedSat` and
  `writeStdoutSpecPlacedSat` plus the stack-floor bounds `hWriteFileStack` and `hWriteStdoutStack`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFdSat

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsRoCl)
open CryptoVerification.SignalSession
  (lsReadFileSym lsReadStdinSym lsWriteFileSym lsWriteStdoutSym)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops (IoModel)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit (withLsRetAddr624AndFds)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (ReadStdinBoundedEnv readStdinSpecOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlacedSat (MainIoOfPlacedSat)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
  (writeFileSpecPlacedSat writeFileStackFloor writeStdoutSpecPlacedSat writeStdoutStackFloor)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFd (VacuousIoAllocEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (ReadFileRuleEnv readFileLitSpecPlaced)

/-- Honest-write-spec twin of `M3PlacedBudgetFd.MainIoOfPlacedFd` on Block `617` (`lsProg_617 H`). -/
structure MainIoOfPlacedFdSat [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat)
    (StdinEnv : List (BitVec 8) → List AllocEvent → Prop := ReadStdinBoundedEnv)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv io.rd) :
    Prop where
  readStdin : subroutine_ok (lsProg_617 H) (lsρ lsReadStdinSym)
    (withLsRoCl lsmpl (withFdsGe3Closed (readStdinSpecOfPlaced io A lim hookStack StdinEnv)))
  readFile : subroutine_ok (lsProg_617 H) (lsρ lsReadFileSym)
    (withLsRoCl lsmpl (withLsRetAddr624AndFds (readFileLitSpecPlaced io A lim hookStack ReadEnv)))
  writeFile : subroutine_ok (lsProg_617 H) (lsρ lsWriteFileSym)
    (withLsRoCl lsmpl (writeFileSpecPlacedSat io A lim hookStack))
  writeStdout : subroutine_ok (lsProg_617 H) (lsρ lsWriteStdoutSym)
    (withLsRoCl lsmpl (writeStdoutSpecPlacedSat A lim hookStack))
  hWriteFileStack : writeFileStackFloor ≤ hookStack
  hWriteStdoutStack : writeStdoutStackFloor ≤ hookStack

private theorem not_fitsEnv_vacuousIoAllocEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (h : FitsEnv M lim st VacuousIoAllocEnv) : False := by
  have hev := (h [.alloc (2 ^ 64)] rfl).1.1
  exact absurd hev (by decide)

/-- Project `MainIoOfPlacedFdSat` to a write-only `MainIoOfPlacedSat` at `VacuousIoAllocEnv` for
    hops `M5` and `M6` (which never invoke `readStdin` or `readFile`). -/
theorem MainIoOfPlacedFdSat.toWriteOnlyMainIoSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hio : MainIoOfPlacedFdSat A lim H io hookStack StdinEnv ReadEnv) :
    MainIoOfPlacedSat A lim H io hookStack
      (fun _ => VacuousIoAllocEnv) (fun _ _ => VacuousIoAllocEnv) where
  readStdin := by
    refine subroutine_ok_intro fun (x, st) s0 R _ _ hpre => False.elim ?_
    dsimp only [withLsRoCl, readStdinSpecOfPlaced] at hpre
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact not_fitsEnv_vacuousIoAllocEnv hpre.1.2.2.1
  readFile := by
    refine subroutine_ok_intro fun (x, st) s0 R _ _ hpre => False.elim ?_
    dsimp only [withLsRoCl, readFileLitSpecPlaced] at hpre
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact not_fitsEnv_vacuousIoAllocEnv hpre.1.2.2.2.2.2
  writeFile := hio.writeFile
  writeStdout := hio.writeStdout
  hWriteFileStack := hio.hWriteFileStack
  hWriteStdoutStack := hio.hWriteStdoutStack

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFdSat
