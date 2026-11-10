/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudgetSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed

/-!
# Honest-Write-Spec Bounded-Stdin Relocatable `MainIo` Contracts (`MainIoBoundedPlacedSat`)

- **Role**: `Role::Proof` (outside the TCB). Untrusted groundwork for #1255 (HOOKS-PREP).
- **Overview**:
  Honest-write-spec sibling of
  `LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced` (`MainIoOfPlacedSat`,
  `MainIoBoundedPlacedSat`, equivalences with `SpecsPlacedBudgetSat.MainIoPlacedSat`, Block-`617`
  call-site projections, and field-copy constructors replacing `readStdin`).
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlacedSat

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles subroutine_ok_rocl_of_plain withLsRoCl)
open CryptoVerification.SignalSession
  (lsReadFileSym lsReadStdinSym lsWriteFileSym lsWriteStdoutSym)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617 lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops (IoModel)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (ReadStdinEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (ReadStdinBoundedEnv readStdinSpecOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
  (writeFileSpecPlacedSat writeFileStackFloor writeStdoutSpecPlacedSat writeStdoutStackFloor)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (ReadFileRuleEnv readFileLitSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudgetSat (MainIoPlacedSat)

/-! ## 1. `MainIoOfPlacedSat`, `MainIoBoundedPlacedSat` & Equality with `MainIoPlacedSat` -/

/-- Envelope-parameterized honest-write-spec `MainIo` on Block `617` (`lsProg_617 H`). -/
structure MainIoOfPlacedSat [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat)
    (StdinEnv : List (BitVec 8) → List AllocEvent → Prop := ReadStdinBoundedEnv)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv io.rd) :
    Prop where
  readStdin : subroutine_ok (lsProg_617 H) (lsρ lsReadStdinSym)
    (withLsRoCl lsmpl (readStdinSpecOfPlaced io A lim hookStack StdinEnv))
  readFile : subroutine_ok (lsProg_617 H) (lsρ lsReadFileSym)
    (withLsRoCl lsmpl (readFileLitSpecPlaced io A lim hookStack ReadEnv))
  writeFile : subroutine_ok (lsProg_617 H) (lsρ lsWriteFileSym)
    (withLsRoCl lsmpl (writeFileSpecPlacedSat io A lim hookStack))
  writeStdout : subroutine_ok (lsProg_617 H) (lsρ lsWriteStdoutSym)
    (withLsRoCl lsmpl (writeStdoutSpecPlacedSat A lim hookStack))
  hWriteFileStack : writeFileStackFloor ≤ hookStack
  hWriteStdoutStack : writeStdoutStackFloor ≤ hookStack

/-- `StdinEnv`-parameterized honest-write-spec `MainIo` at `ReadEnv := ReadFileRuleEnv io.rd`. -/
abbrev MainIoBoundedPlacedSat [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat)
    (StdinEnv : List (BitVec 8) → List AllocEvent → Prop := ReadStdinBoundedEnv) : Prop :=
  MainIoOfPlacedSat A lim H io hookStack StdinEnv (ReadFileRuleEnv io.rd)

/-- Equivalence with `SpecsPlacedBudgetSat.MainIoPlacedSat` at `StdinEnv := ReadStdinEnv`. -/
theorem mainIoBoundedPlaced_iff_mainIoPlaced_sat [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat) :
    MainIoBoundedPlacedSat A lim H io hookStack ReadStdinEnv ↔
      MainIoPlacedSat A lim H io hookStack :=
  ⟨fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩,
   fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩⟩

/-- Propositional equality with `SpecsPlacedBudgetSat.MainIoPlacedSat` at `StdinEnv := ReadStdinEnv`. -/
theorem mainIoBoundedPlaced_eq_mainIoPlaced_sat [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat) :
    MainIoBoundedPlacedSat A lim H io hookStack ReadStdinEnv =
      MainIoPlacedSat A lim H io hookStack :=
  propext (mainIoBoundedPlaced_iff_mainIoPlaced_sat A lim H io hookStack)

theorem mainIoOfPlaced_eq_of_env_sat [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat)
    {StdinEnv₁ StdinEnv₂ : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv₁ ReadEnv₂ : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hstdin : ∀ bs evs, StdinEnv₁ bs evs ↔ StdinEnv₂ bs evs)
    (hread : ∀ fs p evs, ReadEnv₁ fs p evs ↔ ReadEnv₂ fs p evs) :
    MainIoOfPlacedSat A lim H io hookStack StdinEnv₁ ReadEnv₁ =
      MainIoOfPlacedSat A lim H io hookStack StdinEnv₂ ReadEnv₂ := by
  have hs : StdinEnv₁ = StdinEnv₂ := funext fun bs => funext fun evs => propext (hstdin bs evs)
  have hr : ReadEnv₁ = ReadEnv₂ :=
    funext fun fs => funext fun p => funext fun evs => propext (hread fs p evs)
  subst hs; subst hr; rfl

theorem mainIoOfPlaced_iff_of_env_sat [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat)
    {StdinEnv₁ StdinEnv₂ : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv₁ ReadEnv₂ : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hstdin : ∀ bs evs, StdinEnv₁ bs evs ↔ StdinEnv₂ bs evs)
    (hread : ∀ fs p evs, ReadEnv₁ fs p evs ↔ ReadEnv₂ fs p evs) :
    MainIoOfPlacedSat A lim H io hookStack StdinEnv₁ ReadEnv₁ ↔
      MainIoOfPlacedSat A lim H io hookStack StdinEnv₂ ReadEnv₂ := by
  rw [mainIoOfPlaced_eq_of_env_sat A lim H io hookStack hstdin hread]

theorem mainIoBoundedPlaced_eq_of_env_sat [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat)
    {StdinEnv₁ StdinEnv₂ : List (BitVec 8) → List AllocEvent → Prop}
    (hstdin : ∀ bs evs, StdinEnv₁ bs evs ↔ StdinEnv₂ bs evs) :
    MainIoBoundedPlacedSat A lim H io hookStack StdinEnv₁ =
      MainIoBoundedPlacedSat A lim H io hookStack StdinEnv₂ :=
  mainIoOfPlaced_eq_of_env_sat A lim H io hookStack hstdin (fun _ _ _ => Iff.rfl)

theorem mainIoBoundedPlaced_iff_of_env_sat [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat)
    {StdinEnv₁ StdinEnv₂ : List (BitVec 8) → List AllocEvent → Prop}
    (hstdin : ∀ bs evs, StdinEnv₁ bs evs ↔ StdinEnv₂ bs evs) :
    MainIoBoundedPlacedSat A lim H io hookStack StdinEnv₁ ↔
      MainIoBoundedPlacedSat A lim H io hookStack StdinEnv₂ := by
  rw [mainIoBoundedPlaced_eq_of_env_sat A lim H io hookStack hstdin]

/-! ## 2. Block-`617` Call-Site Projections (Matching `IoSitesPlacedBudgetSat`) -/

theorem main_readStdin_of_placed_ok_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hio : MainIoOfPlacedSat A lim H io hookStack StdinEnv ReadEnv) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl (readStdinSpecOfPlaced io A lim hookStack StdinEnv)) :=
  hio.readStdin

theorem main_readStdin_bounded_placed_ok_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hio : MainIoBoundedPlacedSat A lim H io hookStack StdinEnv) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl (readStdinSpecOfPlaced io A lim hookStack StdinEnv)) :=
  hio.readStdin

theorem main_readFile_of_placed_ok_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hio : MainIoOfPlacedSat A lim H io hookStack StdinEnv ReadEnv) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsReadFileSym)
      (withLsRoCl lsmpl (readFileLitSpecPlaced io A lim hookStack ReadEnv)) :=
  hio.readFile

theorem main_writeFile_of_placed_ok_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hio : MainIoOfPlacedSat A lim H io hookStack StdinEnv ReadEnv) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsWriteFileSym)
      (withLsRoCl lsmpl (writeFileSpecPlacedSat io A lim hookStack)) :=
  hio.writeFile

theorem main_writeStdout_of_placed_ok_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hio : MainIoOfPlacedSat A lim H io hookStack StdinEnv ReadEnv) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsWriteStdoutSym)
      (withLsRoCl lsmpl (writeStdoutSpecPlacedSat A lim hookStack)) :=
  hio.writeStdout

/-! ## 3. Field-Copy Constructors Replacing `readStdin` -/

/-- Replace only the `readStdin` field of `SpecsPlacedBudgetSat.MainIoPlacedSat` with a
    `subroutine_ok` witness at `StdinEnv`. -/
theorem mainIoBoundedPlaced_of_mainIoPlaced_and_readStdin_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hio : MainIoPlacedSat A lim H io hookStack)
    (hstdin : subroutine_ok (lsProg_617 H) (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl (readStdinSpecOfPlaced io A lim hookStack StdinEnv))) :
    MainIoBoundedPlacedSat A lim H io hookStack StdinEnv where
  readStdin := hstdin
  readFile := hio.readFile
  writeFile := hio.writeFile
  writeStdout := hio.writeStdout
  hWriteFileStack := hio.hWriteFileStack
  hWriteStdoutStack := hio.hWriteStdoutStack

/-- Replace only the `readStdin` field of `SpecsPlacedBudgetSat.MainIoPlacedSat` with a direct
    Block-`617` hook entry `H lsReadStdinSym = some f` satisfying
    `HookOk f (readStdinSpecOfPlaced … StdinEnv)`. -/
theorem mainIoBoundedPlaced_of_mainIoPlaced_and_hook_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {f : State → State}
    (hio : MainIoPlacedSat A lim H io hookStack)
    (hrow : H lsReadStdinSym = some f)
    (hhook : HookOk f (readStdinSpecOfPlaced io A lim hookStack StdinEnv)) :
    MainIoBoundedPlacedSat A lim H io hookStack StdinEnv :=
  mainIoBoundedPlaced_of_mainIoPlaced_and_readStdin_sat hio <|
    subroutine_ok_rocl_of_plain <|
      ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) ⟨f, hrow, hhook⟩ (by decide)

end LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlacedSat
