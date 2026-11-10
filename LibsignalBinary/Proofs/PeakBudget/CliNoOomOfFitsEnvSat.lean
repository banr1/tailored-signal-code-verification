/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliNoOomOfFitsEnv -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlacedPadSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInstSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import ProofLib.SepLogic.WPp

/-!
# `HookSat` Sibling of `CliNoOomOfFitsEnv` (`CliNoOomOfFitsEnvSat`)

Replaces both exact-hook hypotheses
- `hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (utf8Err W))` (dropping `utf8Err`), and
- `hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook`
with `HookSat` RW (`withVmPreserved (fromUtf8AsciiSpec hookStack)`, `withVmPreserved (memrchrSpec extHookStack)`)
and RO (`withVmPreserved (fromUtf8AsciiSpecRO hookStack)`, `withVmPreserved (memrchrSpecRO extHookStack)`)
contracts across all 12 general-`ext` theorems of `CliNoOomOfFitsEnv`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.CliNoOomOfFitsEnvSat

open Arm64 (GhostName HookSat Memory State subroutine_ok)
open Arm64.Obj (Image MultiPlacement)
open Arm64.Process (ElfImage bytesOfString)
open CryptoVerification (libsignalMutatedBlocks libsignalSessionExterns)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhElfCorrectPlaced CliPqxdhInputs Inputs cliProcessInputs
   libsignalSessionLib lsFromUtf8Sym lsMemrchrSym stdinCapBytes strlenHook)
open CryptoVerification.SignalSession.Cli.MainHops
  (LsCodeInv RunCall cliIo cliMainStk cliResStack cliWrOk fromUtf8AsciiSpec
   inputOf lsHandleErrorSymMain mProgPlaced mainFrameSize memrchrSpec parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (runRel)
open CryptoVerification.SignalSession.Placed (cliProgPlacedSig)
open LibsignalBinary.Heap (AllocEvent BudgetLimits FitsEnv FreeOnlyEvs SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDefaultStaticBytes cliDefaultStaticCount cliOneGiB)
open LibsignalBinary.Proofs.PeakBudget.CliNoOomOfFitsEnv
  (CliReachesOOMExtPlacedAt not_cliReachesOOMExtPlacedAt_of_strict realCliRunBinaryEnvOf)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv RealCliMainBinaryEnvOf)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal (cliRealNinetyPctOneGiB)
open LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal
  (mainEntryBudgetFitsCap_of_fitsEnv
   mainEntryBudgetFitsCap_of_realMainEnvFits_1GiB
   mainEntryBudgetFitsCap_of_realMainEnvFits_90pct
   mainEntryBudgetFitsCap_of_realMainEnvFits_cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter (CliMainBoundedSetupEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (sessionCapBytes)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad (strlenSpecROSat)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (fromUtf8AsciiSpecRO memrchrSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness (cliProgExtPlacedSigAt)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
  (CliPqxdhExtElfCorrectStrictPlacedAt cliPqxdhElfCorrectPlaced_of_extProgEq
   cliPqxdhElfCorrectStrictPlaced_of_extProgEq)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlacedPadSat
  (CliElfExtB2NeedLocksPadAssumptions MainOkCliExtOverB2NeedLocksPadPlacedAt
   MainOkCliExtPqB2NeedLocksPadPlacedAt
   cliPqxdhExtOnInputsElfCorrectStrictPlacedAt_of_b2NeedLocksPadAssumptions)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.M2ExternNoAllocFail
  (ExternPreservesNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInstSat
  (mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap_sat
   mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoBoundedPlaced ReadStdinBoundedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
  (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.PlacedOomRecovery
  (CliPqxdhElfCorrectStrictPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced MainIoPlaced)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-- `HookSat` sibling of `mainOkCliExtPqB2NeedLocksPlacedAt_of_kitEnvFits_and_runTight`
    (`CliNoOomOfFitsEnv.lean:309`), dropping `utf8Err`. -/
theorem mainOkCliExtPqB2NeedLocksPlacedAt_of_kitEnvFits_and_runTight_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (E : UnreachedPqxdhPrimitives → CliHooks → RunCall → CliRunCalleeEnvs)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hstrlenRO : ∀ W : CliHooks, HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hEarly : ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel lim fineCostModel.init
        (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs))
    (hMain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel lim fineCostModel.init (RealCliMainBinaryEnvOf (E X W) i))
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
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPadPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap_sat
    hblk hext_nodup hCI RunEnv hlibc hFs hio hioBounded
    hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk
    (fun h547 X W γ tp =>
      mainEntryBudgetFitsCap_of_fitsEnv hEarly (hMain h547 X W) (hRunSub h547 X W γ tp))
    hrun

/-- `HookSat` sibling of `mainOkCliExtOverB2NeedLocksPlacedAt_of_kitEnvFits_and_runTight`
    (`CliNoOomOfFitsEnv.lean:373`), dropping `utf8Err`. -/
theorem mainOkCliExtOverB2NeedLocksPlacedAt_of_kitEnvFits_and_runTight_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (E : UnreachedPqxdhPrimitives → CliHooks → RunCall → CliRunCalleeEnvs)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hstrlenRO : ∀ W : CliHooks, HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hEarly : ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel lim fineCostModel.init
        (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs))
    (hMain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel lim fineCostModel.init (RealCliMainBinaryEnvOf (E X W) i))
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
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPadPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap_sat
    hblk hext_nodup hCI RunEnv hlibc hFs hio hioBounded
    hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk
    (fun h547 X W γ tp =>
      mainEntryBudgetFitsCap_of_fitsEnv hEarly (hMain h547 X W) (hRunSub h547 X W γ tp))
    hrun

/-- `HookSat` sibling of `mainOkCliExtPq_of_realMainEnvFits_90pct`
    (`CliNoOomOfFitsEnv.lean:968`), dropping `utf8Err`. -/
theorem mainOkCliExtPq_of_realMainEnvFits_90pct_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap)
    (img : Image)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hstrlenRO : ∀ W : CliHooks, HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPadPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap_sat
    hblk hext_nodup hCI (fun X W _ _ => realCliRunBinaryEnvOf hblk hext_nodup img X W)
    hlibc hFs hio hioBounded hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk
    (fun _ X W _ _ =>
      @mainEntryBudgetFitsCap_of_realMainEnvFits_90pct
        (libsignalPlacementOf mpl hblk hext_nodup) lim henf hsb hsc hcap90 img X W)
    hrun

/-- `HookSat` sibling of `mainOkCliExtOver_of_realMainEnvFits_90pct`
    (`CliNoOomOfFitsEnv.lean:1020`), dropping `utf8Err`. -/
theorem mainOkCliExtOver_of_realMainEnvFits_90pct_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap)
    (img : Image)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hstrlenRO : ∀ W : CliHooks, HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPadPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap_sat
    hblk hext_nodup hCI (fun X W _ _ => realCliRunBinaryEnvOf hblk hext_nodup img X W)
    hlibc hFs hio hioBounded hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk
    (fun _ X W _ _ =>
      @mainEntryBudgetFitsCap_of_realMainEnvFits_90pct
        (libsignalPlacementOf mpl hblk hext_nodup) lim henf hsb hsc hcap90 img X W)
    hrun

/-- `HookSat` sibling of `mainOkCliExtPq_of_realMainEnvFits_1GiB`
    (`CliNoOomOfFitsEnv.lean:1073`), dropping `utf8Err`. -/
theorem mainOkCliExtPq_of_realMainEnvFits_1GiB_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap1G : cliOneGiB ≤ lim.physCap)
    (img : Image)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hstrlenRO : ∀ W : CliHooks, HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPadPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap_sat
    hblk hext_nodup hCI (fun X W _ _ => realCliRunBinaryEnvOf hblk hext_nodup img X W)
    hlibc hFs hio hioBounded hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk
    (fun _ X W _ _ =>
      @mainEntryBudgetFitsCap_of_realMainEnvFits_1GiB
        (libsignalPlacementOf mpl hblk hext_nodup) lim henf hsb hsc hcap1G img X W)
    hrun

/-- `HookSat` sibling of `mainOkCliExtOver_of_realMainEnvFits_1GiB`
    (`CliNoOomOfFitsEnv.lean:1125`), dropping `utf8Err`. -/
theorem mainOkCliExtOver_of_realMainEnvFits_1GiB_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap1G : cliOneGiB ≤ lim.physCap)
    (img : Image)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hstrlenRO : ∀ W : CliHooks, HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPadPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap_sat
    hblk hext_nodup hCI (fun X W _ _ => realCliRunBinaryEnvOf hblk hext_nodup img X W)
    hlibc hFs hio hioBounded hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk
    (fun _ X W _ _ =>
      @mainEntryBudgetFitsCap_of_realMainEnvFits_1GiB
        (libsignalPlacementOf mpl hblk hext_nodup) lim henf hsb hsc hcap1G img X W)
    hrun

/-- `HookSat` sibling of `mainOkCliExtPq_of_realMainEnvFits`
    (`CliNoOomOfFitsEnv.lean:1178`), dropping `utf8Err`. -/
theorem mainOkCliExtPq_of_realMainEnvFits_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (img : Image)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hstrlenRO : ∀ W : CliHooks, HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPadPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap_sat
    hblk hext_nodup hCI (fun X W _ _ => realCliRunBinaryEnvOf hblk hext_nodup img X W)
    hlibc hFs hio hioBounded hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk
    (fun _ X W _ _ =>
      @mainEntryBudgetFitsCap_of_realMainEnvFits_cliBudgetLimits
        (libsignalPlacementOf mpl hblk hext_nodup) img X W)
    hrun

/-- `HookSat` sibling of `mainOkCliExtOver_of_realMainEnvFits`
    (`CliNoOomOfFitsEnv.lean:1227`), dropping `utf8Err`. -/
theorem mainOkCliExtOver_of_realMainEnvFits_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (img : Image)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hstrlenRO : ∀ W : CliHooks, HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPadPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap_sat
    hblk hext_nodup hCI (fun X W _ _ => realCliRunBinaryEnvOf hblk hext_nodup img X W)
    hlibc hFs hio hioBounded hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk
    (fun _ X W _ _ =>
      @mainEntryBudgetFitsCap_of_realMainEnvFits_cliBudgetLimits
        (libsignalPlacementOf mpl hblk hext_nodup) img X W)
    hrun

/-- `HookSat` sibling of `cliPqxdhExtElfCorrectStrictPlacedAt_of_realMainEnvFits`
    (`CliNoOomOfFitsEnv.lean:1464`), dropping `utf8Err` and concluding token-identical
    `CliPqxdhExtElfCorrectStrictPlacedAt` via `CliElfExtB2NeedLocksPadAssumptions`. -/
theorem cliPqxdhExtElfCorrectStrictPlacedAt_of_realMainEnvFits_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {exitStk : Nat} {libcAddr : BitVec 64} {hookStack : Nat} {elf : ElfImage}
    (img : Image)
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (ext W))
    (H : CliElfExtB2NeedLocksPadAssumptions mpl mmpl ext 617 cliProcessInputs
      exitStk libcAddr cliMainStk CodeOk cliBudgetLimits elf)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hstrlenRO : ∀ W : CliHooks, HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    CliPqxdhExtElfCorrectStrictPlacedAt mpl mmpl ext 617 elf :=
  cliPqxdhExtOnInputsElfCorrectStrictPlacedAt_of_b2NeedLocksPadAssumptions hext H
    (mainOkCliExtPq_of_realMainEnvFits_sat hblk hext_nodup hCI img hlibc hFs hio hioBounded
      hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk hrun)
    (mainOkCliExtOver_of_realMainEnvFits_sat hblk hext_nodup hCI img hlibc hFs hio hioBounded
      hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk hrun)

/-- `HookSat` sibling of `not_cliReachesOOMExtPlacedAt_of_realMainEnvFits`
    (`CliNoOomOfFitsEnv.lean:1513`), dropping `utf8Err` and concluding token-identical
    `¬ CliReachesOOMExtPlacedAt`. -/
theorem not_cliReachesOOMExtPlacedAt_of_realMainEnvFits_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {exitStk : Nat} {libcAddr : BitVec 64} {hookStack : Nat} {elf : ElfImage}
    (img : Image)
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (ext W))
    (H : CliElfExtB2NeedLocksPadAssumptions mpl mmpl ext 617 cliProcessInputs
      exitStk libcAddr cliMainStk CodeOk cliBudgetLimits elf)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hstrlenRO : ∀ W : CliHooks, HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (W : CliHooks) {i : Inputs} (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    ¬ CliReachesOOMExtPlacedAt mpl ext 617 elf W i :=
  not_cliReachesOOMExtPlacedAt_of_strict
    (cliPqxdhExtElfCorrectStrictPlacedAt_of_realMainEnvFits_sat hblk hext_nodup hCI img
      hext H hlibc hFs hio hioBounded hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO
      hpan hstk hrun)
    W hi

/-- `HookSat` sibling of `cliPqxdhElfCorrectStrictPlaced_of_realMainEnvFits`
    (`CliNoOomOfFitsEnv.lean:1610`), dropping `utf8Err` and concluding token-identical
    `CliPqxdhElfCorrectStrictPlaced`. -/
theorem cliPqxdhElfCorrectStrictPlaced_of_realMainEnvFits_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {exitStk : Nat} {libcAddr : BitVec 64} {hookStack : Nat} {elf : ElfImage}
    (img : Image)
    (hprog : ∀ W : CliHooks, cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext 617 W)
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (ext W))
    (H : CliElfExtB2NeedLocksPadAssumptions mpl mmpl ext 617 cliProcessInputs
      exitStk libcAddr cliMainStk CodeOk cliBudgetLimits elf)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hstrlenRO : ∀ W : CliHooks, HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    CliPqxdhElfCorrectStrictPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectStrictPlaced_of_extProgEq hprog
    (cliPqxdhExtElfCorrectStrictPlacedAt_of_realMainEnvFits_sat hblk hext_nodup hCI img
      hext H hlibc hFs hio hioBounded hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO
      hpan hstk hrun)

/-- `HookSat` sibling of `cliPqxdhElfCorrectPlaced_of_realMainEnvFits`
    (`CliNoOomOfFitsEnv.lean:1702`), dropping `utf8Err` and concluding token-identical
    `CliPqxdhElfCorrectPlaced`. -/
theorem cliPqxdhElfCorrectPlaced_of_realMainEnvFits_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {exitStk : Nat} {libcAddr : BitVec 64} {hookStack : Nat} {elf : ElfImage}
    (img : Image)
    (hprog : ∀ W : CliHooks, cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext 617 W)
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (ext W))
    (H : CliElfExtB2NeedLocksPadAssumptions mpl mmpl ext 617 cliProcessInputs
      exitStk libcAddr cliMainStk CodeOk cliBudgetLimits elf)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hstrlenRO : ∀ W : CliHooks, HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectPlaced_of_extProgEq hprog
    (cliPqxdhExtElfCorrectStrictPlacedAt_of_realMainEnvFits_sat hblk hext_nodup hCI img
      hext H hlibc hFs hio hioBounded hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO
      hpan hstk hrun)

end LibsignalBinary.Proofs.PeakBudget.CliNoOomOfFitsEnvSat
