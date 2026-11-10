/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMainEntryFits

/-!
# Arbitrary-Domain D3 Block-`579 → 617 → Real Externs` Lift (`ElfSlicesPqOomH2KD3MainLiftGlue`)

**Checked by Lean.**

Lifts any Block-`579` `runSpecTightPlacedPreFd` contract and `MainEntryBudgetFitsCapOf` on
`domScopedRun Dom (runRel S)` across Block `579 → 617` (`cliGhostExterns ghFixed`) and across
`Block617TransferFixedHyp` to `cliExternsPlaced mmpl`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3MainLiftGlue

open Arm64 (GhostName Memory subroutine_ok)
open Arm64.Obj (MultiPlacement)
open CryptoVerification
  (LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliExternsPlaced cliProcessInputs libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.MainHops
  (LsCodeInv RunCall cliIo cliMainStk cliResStack cliWrOk mProgPlaced mainFrameSize)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_fromUtf8_eq cliGhostExterns_memrchr_eq)
open LibsignalBinary.Heap (AllocEvent)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3 (Block617TransferFixedHyp)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (b2MainSpecTightNeedLocksFineAt cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv
  (subroutine_ok_b2MainSpecTightNeedLocksFineAt_iff)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
  (MainEntryBudgetFitsCapOf cliGhostExterns_handleErrorMain cliGhostExterns_strlen domScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced (ReadStdinBoundedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
  (initFsState_cliProcessInputs_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFd (MainIoOfPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks allocContractsFsPlaced_of_hooks)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (runSpecTightPlacedPreFd)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMainEntryFits
  (b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed_preFd)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-- Lifts Block-`579` `runSpecTightPlacedPreFd` and `MainEntryBudgetFitsCapOf` on
`domScopedRun Dom (runRel S)` to ghost Block `617` (`cliGhostExterns ghFixed`). -/
theorem ghostMainSubroutineD3_of_domScopedRunTight_preFd
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_ghost : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk_ghost)
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnvOf : GhostName → BitVec 64 → RunCall → List AllocEvent → Prop}
    (Dom : Inputs → Prop) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ghFixed)
    (hioOf : ∀ (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlacedFd (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : ∀ (γ : GhostName) (tp : BitVec 64),
      MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
        uuidTryParse (RunEnvOf γ tp) (domScopedRun Dom (runRel S)))
    (hrun : ∀ (γ : GhostName) (tp : BitVec 64),
      @subroutine_ok _
        (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
        (mpl.base 579)
        (@runSpecTightPlacedPreFd (libsignalPlacementOf mpl hblk hext_nodup) _
          CodeOk_ghost
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (RunEnvOf γ tp) uuidTryParse (runRel S) cliWrOk cliResStack)) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W')) 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_ghost
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (domScopedRun Dom (runRel S)) cliProcessInputs) := by
  intro γ tp
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  have hM24 :=
    b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed_preFd
      (ext := fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W'))
      (W := W) (lim := cliBudgetLimits)
      hblk hext_nodup hCI Dom S
      hlibc initFsState_cliProcessInputs_eq
      (allocContractsFsPlaced_of_hooks mmpl ghFixed W (hG γ tp))
      (hioOf γ tp)
      (cliGhostExterns_strlen mmpl ghFixed W)
      (cliGhostExterns_fromUtf8_eq mmpl ghFixed W)
      (cliGhostExterns_memrchr_eq mmpl ghFixed W)
      (cliGhostExterns_handleErrorMain mmpl ghFixed W)
      hstk (hfitCap γ tp) (hrun γ tp)
  exact
    (subroutine_ok_b2MainSpecTightNeedLocksFineAt_iff mpl
      (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W')) 617 W (mpl.base 617)
      libcAddr CodeOk_ghost (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      cliBudgetLimits fineCostModel.init cliMainStk
      (LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.cliStaticsPlacedAt mpl)
      (domScopedRun Dom (runRel S)) cliProcessInputs).mp hM24

/-- Lifts Block-`579` `runSpecTightPlacedPreFd` and `MainEntryBudgetFitsCapOf` on
`domScopedRun Dom (runRel S)` across `579 → 617` and `Block617TransferFixedHyp` to
`cliExternsPlaced mmpl`. -/
theorem mainSubroutineD3F3_of_domScopedRunTight_preFd
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk_ghost)
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnvOf : GhostName → BitVec 64 → RunCall → List AllocEvent → Prop}
    (Dom : Inputs → Prop) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      CodeOk_ghost CodeOk_real libcAddr brkStart cliMainStk)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ghFixed)
    (hioOf : ∀ (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlacedFd (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : ∀ (γ : GhostName) (tp : BitVec 64),
      MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
        uuidTryParse (RunEnvOf γ tp) (domScopedRun Dom (runRel S)))
    (hrun : ∀ (γ : GhostName) (tp : BitVec 64),
      @subroutine_ok _
        (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
        (mpl.base 579)
        (@runSpecTightPlacedPreFd (libsignalPlacementOf mpl hblk hext_nodup) _
          CodeOk_ghost
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (RunEnvOf γ tp) uuidTryParse (runRel S) cliWrOk cliResStack)) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_real
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (domScopedRun Dom (runRel S)) cliProcessInputs) :=
  hTr W (domScopedRun Dom (runRel S))
    (ghostMainSubroutineD3_of_domScopedRunTight_preFd
      hblk hext_nodup ghFixed hCI Dom S hlibc hG hioOf hstk hfitCap hrun)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3MainLiftGlue
