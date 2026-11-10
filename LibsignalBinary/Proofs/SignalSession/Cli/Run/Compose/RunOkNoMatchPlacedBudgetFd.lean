/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `FdsGe3Closed`-Threaded D2(c) and Generic `RunSem` `signal_session::run` Composition

Composes `FdsGe3Closed`-threaded `signal_session::run` (Block `579`) and its Block-`617` transfer
(`mProgPlaced`) at `runSpecTightPlacedPreFd` and `runSpecPlacedPreFd` under `[LibsignalPlacement]`
and `[LibsignalFullPlacement]` (`LibsignalFrozen`), for arbitrary `S : RunSem`, `cliRunSem`, and
D2(c).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification
  (LibsignalFrozen LibsignalFullPlacement LibsignalHooks LibsignalPlacement blkPl_111 lsmpl lsρ)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliResStack cliRunBudgets cliRunNeeds cliWrOk mProgPlaced)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_553 blkPl_590 lsProg_589)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost InitGhost PksmGhost RunNeeds RunSem SlotAns runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs
  (DecPkOkD2c InitOk₀ cliDecryptPrekeyNeed cliInitiateNeed decPkDefD2c initDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton
  (CalleeSlot.OkPlaced pathNeed splitIdNeed splitSignedNeed)
open CryptoVerification.SignalSession.Cli.Slots (filesOk₀ scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetFd
  (dirGet_placed_caller_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (lsReadFile_subroutine_ok_of_hookSat withLsRetAddr624AndFds)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
  (runNeed_cli_le_resStack_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudgetFd
  (splitIdSpecPlacedOkFs splitId_placed_caller_ok_of_allocFs_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetFd
  (splitSignedSpecPlacedOkFs splitSigned_placed_caller_ok_of_allocFs_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
  (cliRunArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
  (pksmSlotSpecPlacedOkFs tryFromPlacedSpecOkFs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (cliRunSem runSlotEnvsOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudgetFd
  (RunArmEnvs RunArmsFrozenPlacedFd RunArmsPlacedFd RunEnv run_ok_frozen_placed_at_block_fd
   run_ok_placed_at_block_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd
  (runSpecPlacedPreFd runSpecTightPlacedPreFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (dropSpeSpecStkPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunHooksPlaced dropSpeX_placed_ok dropSpe_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (RunCalleesPlacedFd slotWithFdsGe3Closed slotWithPreFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (bundleReadSpecPlaced dirGetSpecPlaced pathSpecPlaced readFileSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpecX)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
  (cliRunArmEnvs cliRunCalleesEnvs)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (cliRunSem runSlotEnvsOf)

/-! ## Section 1: `CliRunHooksBundleFd` & Pre-`FdsGe3Closed` Slot Seam Predicates -/

/-- Bundle of `lsProg_579` hook obligations and `withLsRetAddr624AndFds` `HookSat` on
`lsReadFileSym` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
structure CliRunHooksBundleFd [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) : Prop where
  runHooks : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))
  readFileSat : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
    (withLsRetAddr624AndFds
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))

/-- Project `subroutine_ok` on Block `579` (`lsProg_579`) for `lsReadFileSym` from
`CliRunHooksBundleFd`. -/
theorem CliRunHooksBundleFd.readFile579 [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hHooks : CliRunHooksBundleFd mmpl g W A lim ReadEnv) :
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (withLsRetAddr624AndFds
        (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv)) :=
  lsReadFile_subroutine_ok_of_hookSat hHooks.readFileSat (by decide) (by decide)

/-- Pre-only `FdsGe3Closed` counterpart of `CliInitSlotOkPlacedAt` on `lsProg_579 H` calling
`lsmpl.base 521` (definitionally equal to `ElfSlicesPqOomH2KIfaces.CliInitSlotOkPlacedAtPreFd`). -/
def CliInitSlotOkPlacedAtPreFd [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Prop :=
  ∀ (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds),
    sEnvs.initiate = InitEnv →
    S.filesOk = filesOk₀ scopeIn (fun _ => True) →
    S.initiate = initDef X ⟨W.C, W.Q⟩ →
    S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
    needs.initiate = cliInitiateNeed cliRunBudgets →
    (slotWithPreFdsGe3Closed (slotsOfPlaced A lim sEnvs S needs).initiate).OkPlaced
      (lsProg_579 H) (lsmpl.base 521)

/-- `cliGhostExterns` wrapper for `CliInitSlotOkPlacedAtPreFd` (definitionally equal to
`ElfSlicesPqOomH2KIfaces.CliInitSlotOkPlacedPreFd`). -/
abbrev CliInitSlotOkPlacedPreFd [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Prop :=
  CliInitSlotOkPlacedAtPreFd (cliGhostExterns g (cliExternsPlaced mmpl W)) A lim InitEnv X W

/-- Pre-only `FdsGe3Closed` counterpart of `DecPkD2cSlotOkPlacedAt` on `lsProg_579 H` calling
`lsmpl.base 520` at `slotsOfPlaced`. -/
def DecPkD2cSlotOkPlacedAtPreFd [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (S : RunSem) (needs : RunNeeds) (sEnvs : RunSlotEnvs),
    sEnvs.decryptPrekey = DecPkEnv →
    S.filesOk = filesOk₀ scopeIn (fun _ => True) →
    S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn →
    S.decPkOk = DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn →
    needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets →
    (slotWithPreFdsGe3Closed (slotsOfPlaced A lim sEnvs S needs).decryptPrekey).OkPlaced
      (lsProg_579 H) (lsmpl.base 520)

/-- `cliGhostExterns` wrapper for `DecPkD2cSlotOkPlacedAtPreFd`. -/
def DecPkD2cSlotOkPlacedPreFd [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives),
    DecPkD2cSlotOkPlacedAtPreFd (cliGhostExterns g (cliExternsPlaced mmpl W)) X W A lim DecPkEnv

/-- Pre-only `FdsGe3Closed` counterpart of `DecPkD2cSlotOkFrozenPlacedAt` on `lsProg_579 H`
calling `lsmpl.base 520` (definitionally equal to
`ElfSlicesPqOomH2KIfaces.DecPkD2cSlotOkFrozenPlacedAtPreFd`). -/
def DecPkD2cSlotOkFrozenPlacedAtPreFd [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (S : RunSem) (needs : RunNeeds) (sEnvs : RunSlotEnvs),
    sEnvs.decryptPrekey = DecPkEnv →
    S.filesOk = filesOk₀ scopeIn (fun _ => True) →
    S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn →
    S.decPkOk = DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn →
    needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets →
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey).OkPlaced
      (lsProg_579 H) (lsmpl.base 520)

/-- `cliGhostExterns` wrapper for `DecPkD2cSlotOkFrozenPlacedAtPreFd` (definitionally equal to
`ElfSlicesPqOomH2KIfaces.DecPkD2cSlotOkFrozenPlacedPreFd`). -/
def DecPkD2cSlotOkFrozenPlacedPreFd [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives),
    DecPkD2cSlotOkFrozenPlacedAtPreFd
      (cliGhostExterns g (cliExternsPlaced mmpl W)) X W A lim DecPkEnv

/-- Ok-only `fs`-preserving counterpart of `PksmSlotOkPlaced` (Block `111`). -/
def PksmSlotOkPlacedFs [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop) : Prop :=
  ∀ (S : RunSem), S.pksmParse = pksmParse →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      blkPl_111.base (pksmSlotSpecPlacedOkFs M A lim PksmTryFromEnv S)

/-! ## Section 2: `LibsignalCodeRoLoaded` Public/Arm Callee Seam & Block-`617` Assembly -/

/-- `FdsGe3Closed`-threaded public/arm callee seam for `signal_session::run` (Blocks `589`, `563`,
`593`, `592`, `553`, and `RunSem`-dependent `RunArmsPlacedFd`) at
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
structure CliPubCalleesPlacedFd [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs) (aEnvs : RunSem → RunArmEnvs)
    (W : CliHooks) : Prop where
  dirGet : ∀ {stk : Nat}, cliRunBudgets.dirGetNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced cliIo.rd cliWrOk A lim cEnvs.dirGet stk))
  bundleRead : ∀ {stk : Nat}, cliRunBudgets.bundleReadNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 563)
      (withFdsGe3Closed (bundleReadSpecPlaced cliIo.rd cliWrOk A lim cEnvs.bundleRead stk))
  splitId : ∀ {stk : Nat}, splitIdNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 593)
      (splitIdSpecPlacedOkFs A lim cEnvs.splitId stk)
  splitSigned : ∀ {stk : Nat}, splitSignedNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 592)
      (splitSignedSpecPlacedOkFs A lim cEnvs.splitSigned stk)
  dropSpeX : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (blkPl_553).base (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim))
  dropSpe : ∀ (stk : Nat), 32 + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_553).base
      (dropSpeSpecStkPlaced A lim stk)
  arms : ∀ (S : RunSem) (decPkNeed : Nat),
    RunArmsPlacedFd (LibsignalCodeRoLoaded lsmpl) A lim cEnvs sEnvs (aEnvs S)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S (cliRunNeeds decPkNeed)
      cliResStack

private theorem cliGhostExterns_bcmp_keepsFs_sat (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W))
      CryptoVerification.SignalSession.Cli.cliBcmpName
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.SignalSession.Cli.cliBcmpSpec).keepsFs := by
  refine CryptoVerification.SignalSession.Cli.Slots.cliGhostExterns_sat_of_cliExternsPlaced
    mmpl g W ?_
  rcases LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliExternsPlaced_bcmp_budget_sat
    mmpl W with ⟨f, hf, hok⟩
  have hbcmp := CryptoVerification.SignalSession.Cli.RunGlue.cliExternsPlaced_bcmp mmpl W
  rw [hbcmp] at hf
  injection hf with hfg
  subst hfg
  exact ⟨_, hbcmp, hok.keepsFs fun _ => rfl⟩

/-- Discharges `dirGet`, `splitId`, `splitSigned`, `dropSpeX`, and `dropSpe` of
`CliPubCalleesPlacedFd` at `cliRunCalleesEnvs ReadEnv` from `CliRunHooksBundleFd` and `hPath589`,
leaving `bundleRead` and `arms`. -/
theorem cliPubCallees_of_arms_placed_fd [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {aEnvs : RunSem → RunArmEnvs}
    (W : CliHooks)
    (hHooks : CliRunHooksBundleFd mmpl g W A lim ReadEnv)
    (hPath589 : subroutine_ok
      (lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 596)
      (withFdsGe3Closed (pathSpecPlaced A lim PathEnv pathNeed)))
    (hBundleRead : ∀ {stk : Nat}, cliRunBudgets.bundleReadNeed ≤ stk →
      subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 563)
        (withFdsGe3Closed
          (bundleReadSpecPlaced cliIo.rd cliWrOk A lim (cliRunCalleesEnvs ReadEnv).bundleRead stk)))
    (harms : ∀ (S : RunSem) (decPkNeed : Nat),
      RunArmsPlacedFd (LibsignalCodeRoLoaded lsmpl) A lim (cliRunCalleesEnvs ReadEnv) sEnvs
        (aEnvs S) (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S
        (cliRunNeeds decPkNeed) cliResStack) :
    CliPubCalleesPlacedFd mmpl g A lim (cliRunCalleesEnvs ReadEnv) sEnvs aEnvs W :=
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  let hh := hHooks.runHooks
  { dirGet := fun {_stk} hstk =>
      dirGet_placed_caller_ok_of_deps_fd
        (callerProg := lsProg_579 H) (i := 579)
        (pathProg := lsProg_589 H) (jPath := 589)
        (fun _ hp => hp.2) hh.allocFs (cliGhostExterns_bcmp_keepsFs_sat mmpl g W)
        (by decide) (by decide)
        hPath589
        hHooks.readFileSat
        (hh.fs (lsProg_589 H) 589) hstk
        (fun _ _ _ _ h => h) (by decide)
    bundleRead := hBundleRead
    splitId := fun {_stk} hstk =>
      splitId_placed_caller_ok_of_allocFs_fd
        (callerProg := lsProg_579 H) (i := 579)
        hh.allocFs hstk (by decide)
    splitSigned := fun {_stk} hstk =>
      splitSigned_placed_caller_ok_of_allocFs_fd
        (callerProg := lsProg_579 H) (i := 579) (splitStk := splitIdNeed)
        hh.allocFs (by decide) hstk (by decide)
    dropSpeX := dropSpeX_placed_ok
      (callerProg := lsProg_579 H) (i := 579) hh (by decide)
    dropSpe := fun stk hstk hstk64 =>
      dropSpe_placed_ok
        (callerProg := lsProg_579 H) (i := 579)
        hh stk hstk hstk64 (by decide)
    arms := harms }

/-- Assemble `RunCalleesPlacedFd` at `slotsOfPlaced` from `CliRunHooksBundleFd`,
`CliPubCalleesPlacedFd`, and the 5 slot contracts. -/
theorem runCallees_cli_placed_fd [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {aEnvs : RunSem → RunArmEnvs}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8))}
    {decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop}
    {parseFn : List (BitVec 8) → Option PreKeySignalMessage}
    {decPkNeed : Nat}
    (hHooks : CliRunHooksBundleFd mmpl g W A lim cEnvs.readFile)
    (hpub : CliPubCalleesPlacedFd mmpl g A lim cEnvs sEnvs aEnvs W)
    (henc : (slotWithPreFdsGe3Closed
      (slotsOfPlaced A lim sEnvs (cliRunSem X W decPk decPkOk parseFn)
        (cliRunNeeds decPkNeed)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hdecSig : (slotWithPreFdsGe3Closed
      (slotsOfPlaced A lim sEnvs (cliRunSem X W decPk decPkOk parseFn)
        (cliRunNeeds decPkNeed)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hinit : CliInitSlotOkPlacedPreFd mmpl g A lim sEnvs.initiate X W)
    (hdecPk : (slotWithPreFdsGe3Closed
      (slotsOfPlaced A lim sEnvs (cliRunSem X W decPk decPkOk parseFn)
        (cliRunNeeds decPkNeed)).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 520))
    (hkem : (slotWithFdsGe3Closed
      (slotsOfPlaced A lim sEnvs (cliRunSem X W decPk decPkOk parseFn)
        (cliRunNeeds decPkNeed)).kemDeserialize).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_590).base) :
    RunCalleesPlacedFd A lim cEnvs (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets
      (slotsOfPlaced A lim sEnvs (cliRunSem X W decPk decPkOk parseFn)
        (cliRunNeeds decPkNeed)) :=
  { readFile := hHooks.readFile579
    dirGet := hpub.dirGet
    bundleRead := hpub.bundleRead
    splitId := hpub.splitId
    splitSigned := hpub.splitSigned
    dropSpeX := hpub.dropSpeX
    dropSpe := hpub.dropSpe
    encrypt := henc
    decryptSignal := hdecSig
    initiate := hinit (cliRunSem X W decPk decPkOk parseFn) sEnvs (cliRunNeeds decPkNeed)
      rfl rfl rfl rfl rfl
    decryptPrekey := hdecPk
    kemDeserialize := hkem }

/-- Block-`617` transfer of `signal_session::run` (Block `579`) meeting
`runSpecTightPlacedPreFd (LibsignalCodeRoLoaded lsmpl)`. -/
theorem hrun_cli_placed_fd [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {aEnvs : RunSem → RunArmEnvs}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8))}
    {decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop}
    {parseFn : List (BitVec 8) → Option PreKeySignalMessage}
    {decPkNeed : Nat}
    (_h547 : lsmpl.base 547 ≠ 0#64)
    (hHooks : CliRunHooksBundleFd mmpl g W A lim cEnvs.readFile)
    (hpub : CliPubCalleesPlacedFd mmpl g A lim cEnvs sEnvs aEnvs W)
    (henc : (slotWithPreFdsGe3Closed
      (slotsOfPlaced A lim sEnvs (cliRunSem X W decPk decPkOk parseFn)
        (cliRunNeeds decPkNeed)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hdecSig : (slotWithPreFdsGe3Closed
      (slotsOfPlaced A lim sEnvs (cliRunSem X W decPk decPkOk parseFn)
        (cliRunNeeds decPkNeed)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hinit : CliInitSlotOkPlacedPreFd mmpl g A lim sEnvs.initiate X W)
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk : (slotWithPreFdsGe3Closed
      (slotsOfPlaced A lim sEnvs (cliRunSem X W decPk decPkOk parseFn)
        (cliRunNeeds decPkNeed)).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 520))
    (hkem : (slotWithFdsGe3Closed
      (slotsOfPlaced A lim sEnvs (cliRunSem X W decPk decPkOk parseFn)
        (cliRunNeeds decPkNeed)).kemDeserialize).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_590).base)
    (htry : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 85) (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim)))
    (hpksm : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      blkPl_111.base
      (pksmSlotSpecPlacedOkFs M A lim
        (aEnvs (cliRunSem X W decPk decPkOk parseFn)).pksmTryFrom
        (cliRunSem X W decPk decPkOk parseFn))) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlacedPreFd (LibsignalCodeRoLoaded lsmpl) A lim
        (RunEnv (aEnvs (cliRunSem X W decPk decPkOk parseFn))) uuidTryParse
        (runRel (cliRunSem X W decPk decPkOk parseFn)) cliWrOk cliResStack) :=
  run_ok_placed_at_block_fd
    (callerProg := mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 617)
    (hpub.arms (cliRunSem X W decPk decPkOk parseFn) decPkNeed)
    hHooks.runHooks
    (runCallees_cli_placed_fd mmpl g X W hHooks hpub henc hdecSig hinit hdecPk hkem)
    htry
    hpksm
    (runNeed_cli_le_resStack_placed A lim sEnvs hdecPkNeed)
    (by decide)
    (by decide)

/-- D2(c) specialization of `hrun_cli_placed_fd` at `runSpecTightPlacedPreFd`. -/
theorem hrun_cli_d2c_tight_placed_fd [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {aEnvs : RunSem → RunArmEnvs}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hHooks : CliRunHooksBundleFd mmpl g W A lim cEnvs.readFile)
    (hpub : CliPubCalleesPlacedFd mmpl g A lim cEnvs sEnvs aEnvs W)
    (henc : (slotWithPreFdsGe3Closed
      (slotsOfPlaced A lim sEnvs
        (cliRunSem X W (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn) (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hdecSig : (slotWithPreFdsGe3Closed
      (slotsOfPlaced A lim sEnvs
        (cliRunSem X W (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn) (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hinit : CliInitSlotOkPlacedPreFd mmpl g A lim sEnvs.initiate X W)
    (hdecPk : DecPkD2cSlotOkPlacedPreFd mmpl g W A lim sEnvs.decryptPrekey)
    (hkem : (slotWithFdsGe3Closed
      (slotsOfPlaced A lim sEnvs
        (cliRunSem X W (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn) (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).kemDeserialize).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_590).base)
    (htry : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 85) (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim)))
    (hpksm : PksmSlotOkPlacedFs mmpl g W A lim
      (aEnvs (cliRunSem X W
        (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
        (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
        pksmParse)).pksmTryFrom) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlacedPreFd (LibsignalCodeRoLoaded lsmpl) A lim
        (RunEnv (aEnvs (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)))
        uuidTryParse
        (runRel (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse))
        cliWrOk cliResStack) :=
  hrun_cli_placed_fd mmpl g X W
    (decPk := decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
    (decPkOk := DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
    (parseFn := pksmParse)
    (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets)
    h547 hHooks hpub henc hdecSig hinit (by decide)
    (hdecPk X _ (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) sEnvs rfl rfl rfl rfl rfl)
    hkem htry (hpksm _ rfl)

/-- D2(c) specialization of `hrun_cli_placed_fd` at `runSpecPlacedPreFd` (definitionally equal to
`runSpecTightPlacedPreFd`). -/
theorem hrun_cli_d2c_placed_fd [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {aEnvs : RunSem → RunArmEnvs}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hHooks : CliRunHooksBundleFd mmpl g W A lim cEnvs.readFile)
    (hpub : CliPubCalleesPlacedFd mmpl g A lim cEnvs sEnvs aEnvs W)
    (henc : (slotWithPreFdsGe3Closed
      (slotsOfPlaced A lim sEnvs
        (cliRunSem X W (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn) (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hdecSig : (slotWithPreFdsGe3Closed
      (slotsOfPlaced A lim sEnvs
        (cliRunSem X W (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn) (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hinit : CliInitSlotOkPlacedPreFd mmpl g A lim sEnvs.initiate X W)
    (hdecPk : DecPkD2cSlotOkPlacedPreFd mmpl g W A lim sEnvs.decryptPrekey)
    (hkem : (slotWithFdsGe3Closed
      (slotsOfPlaced A lim sEnvs
        (cliRunSem X W (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn) (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).kemDeserialize).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_590).base)
    (htry : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 85) (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim)))
    (hpksm : PksmSlotOkPlacedFs mmpl g W A lim
      (aEnvs (cliRunSem X W
        (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
        (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
        pksmParse)).pksmTryFrom) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecPlacedPreFd (LibsignalCodeRoLoaded lsmpl) A lim
        (RunEnv (aEnvs (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)))
        uuidTryParse
        (runRel (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse))
        cliWrOk cliResStack) :=
  hrun_cli_d2c_tight_placed_fd mmpl g X W h547 hHooks hpub henc hdecSig hinit hdecPk hkem
    htry hpksm

/-! ## Section 3: `LibsignalFrozen` / `[LibsignalFullPlacement]` Composition -/

/-- `LibsignalFrozen` `FdsGe3Closed`-threaded public/arm callee seam for `signal_session::run`
(Blocks `589`, `563`, `593`, `592`, `553`, and `RunSem`-dependent `RunArmsFrozenPlacedFd`) at
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
structure CliPubCalleesFrozenPlacedFd [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs) (aEnvs : RunSem → RunArmEnvs)
    (W : CliHooks) : Prop where
  dirGet : ∀ {stk : Nat}, cliRunBudgets.dirGetNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced cliIo.rd cliWrOk A lim cEnvs.dirGet stk))
  bundleRead : ∀ {stk : Nat}, cliRunBudgets.bundleReadNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 563)
      (withFdsGe3Closed (bundleReadSpecPlaced cliIo.rd cliWrOk A lim cEnvs.bundleRead stk))
  splitId : ∀ {stk : Nat}, splitIdNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 593)
      (splitIdSpecPlacedOkFs A lim cEnvs.splitId stk)
  splitSigned : ∀ {stk : Nat}, splitSignedNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 592)
      (splitSignedSpecPlacedOkFs A lim cEnvs.splitSigned stk)
  dropSpeX : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (blkPl_553).base (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim))
  dropSpe : ∀ (stk : Nat), 32 + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_553).base
      (dropSpeSpecStkPlaced A lim stk)
  arms : ∀ (S : RunSem) (decPkNeed : Nat),
    RunArmsFrozenPlacedFd A lim cEnvs sEnvs (aEnvs S)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S (cliRunNeeds decPkNeed)
      cliResStack

/-- Discharges `dirGet`, `splitId`, `splitSigned`, `dropSpeX`, and `dropSpe` of
`CliPubCalleesFrozenPlacedFd` at `cliRunCalleesEnvs ReadEnv` from `CliRunHooksBundleFd` and
`hPath589`, leaving `bundleRead` and `arms`. -/
theorem cliPubCallees_of_arms_frozen_placed_fd [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {aEnvs : RunSem → RunArmEnvs}
    (W : CliHooks)
    (hHooks : CliRunHooksBundleFd mmpl g W A lim ReadEnv)
    (hPath589 : subroutine_ok
      (lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 596)
      (withFdsGe3Closed (pathSpecPlaced A lim PathEnv pathNeed)))
    (hBundleRead : ∀ {stk : Nat}, cliRunBudgets.bundleReadNeed ≤ stk →
      subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 563)
        (withFdsGe3Closed
          (bundleReadSpecPlaced cliIo.rd cliWrOk A lim (cliRunCalleesEnvs ReadEnv).bundleRead stk)))
    (harms : ∀ (S : RunSem) (decPkNeed : Nat),
      RunArmsFrozenPlacedFd A lim (cliRunCalleesEnvs ReadEnv) sEnvs (aEnvs S)
        (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S (cliRunNeeds decPkNeed)
        cliResStack) :
    CliPubCalleesFrozenPlacedFd mmpl g A lim (cliRunCalleesEnvs ReadEnv) sEnvs aEnvs W :=
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  let hh := hHooks.runHooks
  { dirGet := fun {_stk} hstk =>
      dirGet_placed_caller_ok_of_deps_fd
        (callerProg := lsProg_579 H) (i := 579)
        (pathProg := lsProg_589 H) (jPath := 589)
        (fun _ hp => hp.2) hh.allocFs (cliGhostExterns_bcmp_keepsFs_sat mmpl g W)
        (by decide) (by decide)
        hPath589
        hHooks.readFileSat
        (hh.fs (lsProg_589 H) 589) hstk
        (fun _ _ _ _ h => h) (by decide)
    bundleRead := hBundleRead
    splitId := fun {_stk} hstk =>
      splitId_placed_caller_ok_of_allocFs_fd
        (callerProg := lsProg_579 H) (i := 579)
        hh.allocFs hstk (by decide)
    splitSigned := fun {_stk} hstk =>
      splitSigned_placed_caller_ok_of_allocFs_fd
        (callerProg := lsProg_579 H) (i := 579) (splitStk := splitIdNeed)
        hh.allocFs (by decide) hstk (by decide)
    dropSpeX := dropSpeX_placed_ok
      (callerProg := lsProg_579 H) (i := 579) hh (by decide)
    dropSpe := fun stk hstk hstk64 =>
      dropSpe_placed_ok
        (callerProg := lsProg_579 H) (i := 579)
        hh stk hstk hstk64 (by decide)
    arms := harms }

/-- `[LibsignalFullPlacement]` `RunCalleesPlacedFd` assembly at `slotsOfSigPkFrozenPlaced` for
arbitrary `S : RunSem`. -/
theorem runCallees_cli_full_placed_fd [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {aEnvs : RunSem → RunArmEnvs}
    (W : CliHooks)
    (S : RunSem) {decPkNeed : Nat}
    (hHooks : CliRunHooksBundleFd mmpl g W A lim cEnvs.readFile)
    (hpub : CliPubCalleesFrozenPlacedFd mmpl g A lim cEnvs sEnvs aEnvs W)
    (henc : (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hdecSig : (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hinit : (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).initiate).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 521))
    (hdecPk : (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 520))
    (hkem : (slotWithFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).kemDeserialize).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_590).base) :
    RunCalleesPlacedFd A lim cEnvs (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets
      (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)) :=
  { readFile := hHooks.readFile579
    dirGet := hpub.dirGet
    bundleRead := hpub.bundleRead
    splitId := hpub.splitId
    splitSigned := hpub.splitSigned
    dropSpeX := hpub.dropSpeX
    dropSpe := hpub.dropSpe
    encrypt := henc
    decryptSignal := hdecSig
    initiate := hinit
    decryptPrekey := hdecPk
    kemDeserialize := hkem }

/-- `[LibsignalFullPlacement]` Block-`617` transfer of `signal_session::run` (Block `579`) meeting
`runSpecTightPlacedPreFd (LibsignalFrozen lsmpl)` for arbitrary `S : RunSem`. -/
theorem hrun_cli_sem_full_placed_fd [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {aEnvs : RunSem → RunArmEnvs}
    (W : CliHooks)
    (S : RunSem) {decPkNeed : Nat}
    (_h547 : lsmpl.base 547 ≠ 0#64)
    (hHooks : CliRunHooksBundleFd mmpl g W A lim cEnvs.readFile)
    (hpub : CliPubCalleesFrozenPlacedFd mmpl g A lim cEnvs sEnvs aEnvs W)
    (henc : (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hdecSig : (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hinit : (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).initiate).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 521))
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk : (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 520))
    (hkem : (slotWithFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).kemDeserialize).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_590).base)
    (htry : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 85) (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim)))
    (hpksm : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      blkPl_111.base (pksmSlotSpecPlacedOkFs M A lim (aEnvs S).pksmTryFrom S)) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlacedPreFd (LibsignalFrozen lsmpl) A lim
        (RunEnv (aEnvs S)) uuidTryParse (runRel S) cliWrOk cliResStack) :=
  run_ok_frozen_placed_at_block_fd
    (callerProg := mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 617)
    (hpub.arms S decPkNeed)
    hHooks.runHooks
    (runCallees_cli_full_placed_fd mmpl g W S hHooks hpub henc hdecSig hinit hdecPk hkem)
    htry
    hpksm
    (runNeed_cli_le_resStack_placed A lim sEnvs hdecPkNeed)
    (by decide)
    (by decide)

/-- `[LibsignalFullPlacement]` `cliRunSem` specialization of `hrun_cli_sem_full_placed_fd`. -/
theorem hrun_cli_full_placed_fd [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {aEnvs : RunSem → RunArmEnvs}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8))}
    {decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop}
    {parseFn : List (BitVec 8) → Option PreKeySignalMessage}
    {decPkNeed : Nat}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hHooks : CliRunHooksBundleFd mmpl g W A lim cEnvs.readFile)
    (hpub : CliPubCalleesFrozenPlacedFd mmpl g A lim cEnvs sEnvs aEnvs W)
    (henc : (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSem X W decPk decPkOk parseFn)
        (cliRunNeeds decPkNeed)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hdecSig : (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSem X W decPk decPkOk parseFn)
        (cliRunNeeds decPkNeed)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hinit : CliInitSlotOkPlacedPreFd mmpl g A lim sEnvs.initiate X W)
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk : (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSem X W decPk decPkOk parseFn)
        (cliRunNeeds decPkNeed)).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 520))
    (hkem : (slotWithFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSem X W decPk decPkOk parseFn)
        (cliRunNeeds decPkNeed)).kemDeserialize).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_590).base)
    (htry : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 85) (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim)))
    (hpksm : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      blkPl_111.base
      (pksmSlotSpecPlacedOkFs M A lim
        (aEnvs (cliRunSem X W decPk decPkOk parseFn)).pksmTryFrom
        (cliRunSem X W decPk decPkOk parseFn))) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlacedPreFd (LibsignalFrozen lsmpl) A lim
        (RunEnv (aEnvs (cliRunSem X W decPk decPkOk parseFn))) uuidTryParse
        (runRel (cliRunSem X W decPk decPkOk parseFn)) cliWrOk cliResStack) :=
  hrun_cli_sem_full_placed_fd mmpl g W (cliRunSem X W decPk decPkOk parseFn)
    h547 hHooks hpub henc hdecSig
    (hinit (cliRunSem X W decPk decPkOk parseFn) sEnvs (cliRunNeeds decPkNeed) rfl rfl rfl rfl rfl)
    hdecPkNeed hdecPk hkem htry hpksm

/-- `[LibsignalFullPlacement]` D2(c) `runSpecTightPlacedPreFd (LibsignalFrozen lsmpl)` assembly on
`mProgPlaced`. -/
theorem hrun_cli_d2c_tight_full_placed_fd [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {aEnvs : RunSem → RunArmEnvs}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hHooks : CliRunHooksBundleFd mmpl g W A lim cEnvs.readFile)
    (hpub : CliPubCalleesFrozenPlacedFd mmpl g A lim cEnvs sEnvs aEnvs W)
    (henc : (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs
        (cliRunSem X W (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn) (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hdecSig : (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs
        (cliRunSem X W (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn) (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hinit : CliInitSlotOkPlacedPreFd mmpl g A lim sEnvs.initiate X W)
    (hdecPk : DecPkD2cSlotOkFrozenPlacedPreFd mmpl g W A lim sEnvs.decryptPrekey)
    (hkem : (slotWithFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs
        (cliRunSem X W (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn) (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).kemDeserialize).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_590).base)
    (htry : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 85) (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim)))
    (hpksm : PksmSlotOkPlacedFs mmpl g W A lim
      (aEnvs (cliRunSem X W
        (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
        (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
        pksmParse)).pksmTryFrom) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlacedPreFd (LibsignalFrozen lsmpl) A lim
        (RunEnv (aEnvs (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)))
        uuidTryParse
        (runRel (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse))
        cliWrOk cliResStack) :=
  hrun_cli_full_placed_fd mmpl g X W
    (decPk := decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
    (decPkOk := DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
    (parseFn := pksmParse)
    (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets)
    h547 hHooks hpub henc hdecSig hinit (by decide)
    (hdecPk X _ (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) sEnvs rfl rfl rfl rfl rfl)
    hkem htry (hpksm _ rfl)

/-- `[LibsignalFullPlacement]` D2(c) `runSpecPlacedPreFd (LibsignalFrozen lsmpl)` assembly on
`mProgPlaced` (definitionally equal to `runSpecTightPlacedPreFd`). -/
theorem hrun_cli_d2c_full_placed_fd [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {aEnvs : RunSem → RunArmEnvs}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hHooks : CliRunHooksBundleFd mmpl g W A lim cEnvs.readFile)
    (hpub : CliPubCalleesFrozenPlacedFd mmpl g A lim cEnvs sEnvs aEnvs W)
    (henc : (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs
        (cliRunSem X W (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn) (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hdecSig : (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs
        (cliRunSem X W (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn) (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hinit : CliInitSlotOkPlacedPreFd mmpl g A lim sEnvs.initiate X W)
    (hdecPk : DecPkD2cSlotOkFrozenPlacedPreFd mmpl g W A lim sEnvs.decryptPrekey)
    (hkem : (slotWithFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs
        (cliRunSem X W (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn) (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).kemDeserialize).OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_590).base)
    (htry : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 85) (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim)))
    (hpksm : PksmSlotOkPlacedFs mmpl g W A lim
      (aEnvs (cliRunSem X W
        (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
        (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
        pksmParse)).pksmTryFrom) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecPlacedPreFd (LibsignalFrozen lsmpl) A lim
        (RunEnv (aEnvs (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)))
        uuidTryParse
        (runRel (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse))
        cliWrOk cliResStack) :=
  hrun_cli_d2c_tight_full_placed_fd mmpl g X W h547 hHooks hpub henc hdecSig hinit hdecPk hkem
    htry hpksm

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd
