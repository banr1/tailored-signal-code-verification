/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMainEntryFitsSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3MainLiftGlue -- proof-setup: allow-public-import

/-!
# `HookSat` Sibling of `ElfSlicesPqOomH2KD3MainLiftGlue` (`ElfSlicesPqOomH2KD3MainLiftGlueSat`)

**Checked by Lean.** Untrusted (`CliElfLib`, `Role::Proof`; `0` `sorry`, `std3` axioms).

Provides the general-`ext` `HookSat` Block-`579 → 617` F3 lift
`extMainSubroutineD3_of_domScopedRunTight_preFd_sat` (weakening `strlen` on `M1` to SWAR-padded
`strlenSpecROSat` and both `from_utf8` and `memrchr` to `HookSat` RW+RO contracts, re-anchoring to
`b2MainSpecTightNeedLocksFineAtPad`), plus `toSat` bridges for `cliGhostExterns`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3MainLiftGlueSat

open Arm64 (GhostName HookSat Memory State subroutine_ok)
open Arm64.Obj (MultiPlacement)
open CryptoVerification
  (LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliExternsPlaced cliProcessInputs libsignalSessionLib
   lsFromUtf8Sym lsMemrchrSym strlenHook)
open CryptoVerification.SignalSession.Cli (RunAnswer)
open CryptoVerification.SignalSession.Cli.MainHops
  (LsCodeInv RunCall cliIo cliMainStk cliResStack cliWrOk fromUtf8AsciiSpec
   lsHandleErrorSymMain mProgPlaced mainFrameSize memrchrSpec)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_fromUtf8_eq cliGhostExterns_memrchr_eq)
open LibsignalBinary.Heap (AllocEvent)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv
  (cliProgExtPlacedAt_eq cliStaticsPlacedAt_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad
  (b2MainSpecTightNeedLocksFineAtPad strlenSpecROSat)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
  (fromUtf8AsciiSpecRO memrchrSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesROSat
  (hookSat_fromUtf8ROVm_of_eq hookSat_memrchrROVm_ls_of_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
  (MainEntryBudgetFitsCapOf cliGhostExterns_handleErrorMain cliGhostExterns_strlen domScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInstSat
  (hookSat_fromUtf8Vm_of_eq hookSat_strlenRO_of_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced (ReadStdinBoundedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
  (initFsState_cliProcessInputs_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1PlacedBudgetSat
  (hookSat_memrchrVm_ls_of_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFd (MainIoOfPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks allocContractsFsPlaced_of_hooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (runSpecTightPlacedPreFd)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMainEntryFitsSat
  (b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed_preFd_sat)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-- SWAR-padded Variant-2 Block-`617` Fixed ghost-to-real transfer predicate
    (padded twin of `D3MainLiftGlueF3.Block617TransferFixedHyp`, swapping
    `b2MainSpecTightNeedLocksFineAt` for `b2MainSpecTightNeedLocksFineAtPad`). -/
def Block617TransferFixedPadHyp
    (mpl mmpl : MultiPlacement) (ghFixed : CliGhostHooks)
    (CodeOk_ghost CodeOk_real : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  ∀ (W : CliHooks) (Run : Inputs → RunAnswer → Prop),
    (∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W')) 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk_ghost
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)) →
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk_real
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)

/-- General-`ext` `HookSat` Block-`579 → 617` F3 lift over `MainIoOfPlacedFd` and
    `runSpecTightPlacedPreFd`, consuming SWAR-padded `strlenSpecROSat` on `M1` plus RW+RO `HookSat`
    contracts for both `from_utf8` and `memrchr`, re-anchoring to
    `b2MainSpecTightNeedLocksFineAtPad`. -/
theorem extMainSubroutineD3_of_domScopedRunTight_preFd_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnvOf : GhostName → BitVec 64 → RunCall → List AllocEvent → Prop}
    (Dom : Inputs → Prop) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (ext W))
    (hioOf : ∀ (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlacedFd (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (ext W) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hstrlenRO : HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : HookSat (ext W) lsMemrchrSym
      (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
        (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : HookSat (ext W) lsMemrchrSym
      (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
        (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : ∀ (γ : GhostName) (tp : BitVec 64),
      MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
        uuidTryParse (RunEnvOf γ tp) (domScopedRun Dom (runRel S)))
    (hrun : ∀ (γ : GhostName) (tp : BitVec 64),
      @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
        (mpl.base 579)
        (@runSpecTightPlacedPreFd (libsignalPlacementOf mpl hblk hext_nodup) _
          CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (RunEnvOf γ tp) uuidTryParse (runRel S) cliWrOk cliResStack)) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext 617 W) (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (domScopedRun Dom (runRel S)) cliProcessInputs) := by
  intro γ tp
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  have hM24 :=
    b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed_preFd_sat
      (ext := ext) (W := W) (lim := cliBudgetLimits)
      hblk hext_nodup hCI Dom S
      hlibc initFsState_cliProcessInputs_eq
      (hFs γ tp) (hioOf γ tp)
      hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO hpan
      hstk (hfitCap γ tp) (hrun γ tp)
  rw [← cliProgExtPlacedAt_eq, ← cliStaticsPlacedAt_eq]
  exact hM24

/-- `toSat` bridge for `ghostMainSubroutineD3_of_domScopedRunTight_preFd`
    (`ElfSlicesPqOomH2KD3MainLiftGlue.lean:78`) via
    `extMainSubroutineD3_of_domScopedRunTight_preFd_sat`, concluding
    `b2MainSpecTightNeedLocksFineAtPad`. -/
theorem ghostMainSubroutineD3_of_domScopedRunTight_preFd_via_sat
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
        (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk_ghost
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (domScopedRun Dom (runRel S)) cliProcessInputs) :=
  extMainSubroutineD3_of_domScopedRunTight_preFd_sat
    (ext := fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W'))
    hblk hext_nodup hCI Dom S hlibc
    (fun γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact allocContractsFsPlaced_of_hooks mmpl ghFixed W (hG γ tp))
    hioOf
    (cliGhostExterns_strlen mmpl ghFixed W)
    (hookSat_strlenRO_of_eq hookStack (cliGhostExterns_strlen mmpl ghFixed W))
    (hookSat_fromUtf8Vm_of_eq hookStack (cliGhostExterns_fromUtf8_eq mmpl ghFixed W))
    (hookSat_fromUtf8ROVm_of_eq hookStack (cliGhostExterns_fromUtf8_eq mmpl ghFixed W))
    (@hookSat_memrchrVm_ls_of_eq (libsignalPlacementOf mpl hblk hext_nodup) _
      (cliGhostExterns_memrchr_eq mmpl ghFixed W))
    (@hookSat_memrchrROVm_ls_of_eq (libsignalPlacementOf mpl hblk hext_nodup) _ extHookStack
      (cliGhostExterns_memrchr_eq mmpl ghFixed W))
    (cliGhostExterns_handleErrorMain mmpl ghFixed W)
    hstk hfitCap hrun

/-- `toSat` bridge for `mainSubroutineD3F3_of_domScopedRunTight_preFd`
    (`ElfSlicesPqOomH2KD3MainLiftGlue.lean:149`) via
    `ghostMainSubroutineD3_of_domScopedRunTight_preFd_via_sat`, under
    `Block617TransferFixedPadHyp`. -/
theorem mainSubroutineD3F3_of_domScopedRunTight_preFd_via_sat
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
    (hTr : Block617TransferFixedPadHyp mpl mmpl ghFixed
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
        (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk_real
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (domScopedRun Dom (runRel S)) cliProcessInputs) :=
  hTr W (domScopedRun Dom (runRel S))
    (ghostMainSubroutineD3_of_domScopedRunTight_preFd_via_sat
      hblk hext_nodup ghFixed hCI Dom S hlibc hG hioOf hstk hfitCap hrun)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3MainLiftGlueSat
