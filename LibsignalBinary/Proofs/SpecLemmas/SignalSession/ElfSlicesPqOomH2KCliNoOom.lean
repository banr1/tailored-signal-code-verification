/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.CliNoOomOfFitsEnv
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMainEntryFits

/-!
# Pre-`FdsGe3Closed` `cliBudgetLimits` `MainOkCliExt{Pq,Over}B2NeedLocksPlacedAt` Assemblers

**Checked by Lean.**

`MainIoOfPlacedFd` and `runSpecTightPlacedPreFd` counterparts of
`CliNoOomOfFitsEnv.mainOkCliExt{Pq,Over}B2NeedLocksPlacedAt_cliGhostExterns_cliBudgetLimits_of_kitEnvFits_and_runTightOf`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KCliNoOom

open Arm64 (GhostName Memory subroutine_ok)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (bytesOfString)
open CryptoVerification (libsignalMutatedBlocks libsignalSessionExterns)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs cliExternsPlaced cliProcessInputs libsignalSessionLib
   stdinCapBytes)
open CryptoVerification.SignalSession.Cli.MainHops
  (LsCodeInv RunCall cliIo cliMainStk cliResStack cliWrOk inputOf mProgPlaced mainFrameSize
   parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Heap (AllocEvent FitsEnv)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv RealCliMainBinaryEnvOf)
open LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal
  (mainEntryBudgetFitsCapOf_cliBudgetLimits_of_kitEnvFits)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter (BoundedReadFileEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (sessionCapBytes)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
  (MainOkCliExtOverB2NeedLocksPlacedAt MainOkCliExtPqB2NeedLocksPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced (ReadStdinBoundedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFd (MainIoOfPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (runSpecTightPlacedPreFd)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMainEntryFits
  (mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf_preFd
   mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf_preFd)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-- `cliBudgetLimits` specialization of
`mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf_preFd`. -/
theorem mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_cliBudgetLimits_of_kitEnvFits_and_runTightOf_preFd
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (E : UnreachedPqxdhPrimitives → CliHooks → RunCall → CliRunCalleeEnvs)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (ghOf W))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlacedFd (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hReadSub : ∀ (files : FsFiles) (path : List (BitVec 8)) (evs : List AllocEvent),
      ReadEnv files path evs → BoundedReadFileEnv evs)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hMain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
          (RealCliMainBinaryEnvOf (E X W) i))
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          CliRunBinaryEnv cliIo.rd (E X W g) sessionCapBytes g evs)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlacedPreFd (libsignalPlacementOf mpl hblk hext_nodup) _
            CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf_preFd
    hblk hext_nodup hCI ghOf RunEnv hlibc hG hioOf hstk
    (fun h547 X W γ tp =>
      mainEntryBudgetFitsCapOf_cliBudgetLimits_of_kitEnvFits
        hReadSub (hMain h547 X W) (hRunSub h547 X W γ tp))
    hrun

/-- `cliBudgetLimits` specialization of
`mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf_preFd`. -/
theorem mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_cliBudgetLimits_of_kitEnvFits_and_runTightOf_preFd
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (E : UnreachedPqxdhPrimitives → CliHooks → RunCall → CliRunCalleeEnvs)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (ghOf W))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlacedFd (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hReadSub : ∀ (files : FsFiles) (path : List (BitVec 8)) (evs : List AllocEvent),
      ReadEnv files path evs → BoundedReadFileEnv evs)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hMain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
          (RealCliMainBinaryEnvOf (E X W) i))
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          CliRunBinaryEnv cliIo.rd (E X W g) sessionCapBytes g evs)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlacedPreFd (libsignalPlacementOf mpl hblk hext_nodup) _
            CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf_preFd
    hblk hext_nodup hCI ghOf RunEnv hlibc hG hioOf hstk
    (fun h547 X W γ tp =>
      mainEntryBudgetFitsCapOf_cliBudgetLimits_of_kitEnvFits
        hReadSub (hMain h547 X W) (hRunSub h547 X W γ tp))
    hrun

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KCliNoOom
