/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import ProofLib.FsTrace
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.AgreesOutsideReadHooks
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
import ProofLib.Process.OracleEq
import ProofLib.SepLogic

/-!
# Return-Address-Narrowed Ghost Hooks and K-Twin Bundles (`ElfSlicesPqOomH2KHooks`)

**Checked by Lean.**

Defines return-address- and fd-narrowed ghost-hook specifications (`h2k_*SpecK`), K-twin hook
bundles, and the concrete ghost-hook family `h2k_ghFixedK`:
1. **Narrowed `spec` wrappers (`h2k_<hook>SpecK`)**: conjoin `keepSet (s.readReg64 .lr) = false`
   (and `FdsGe3Closed s.fs` on `lsReadFileSym`) onto `spec.pre`, leaving `post`, `onPanic`,
   `onExit`, and `onOom` unchanged (`hole2_keepSub` for the six allocator / I/O hooks,
   `hole2_keep` for `stringClone`).
2. **K-twin hook bundles**: `h2k_CliGhostAllocHooksK`, `h2k_CliGhostSpqrAllocHooksK`,
   `h2k_CodecHooksPlacedK`, `h2k_AllocContractsXCliPlacedK`, `h2k_AllocContractsFsPlacedK`,
   `h2k_RunHooksPlacedK`, `h2k_CliRunHooksBundleK`, and `h2k_MainIoOfPlacedK`.
3. **Ghost-hook tuple (`h2k_ghFixedK`) and guard extraction**: raises `.Exception` iff the
   narrowed `ActiveF3CallPre` fails, yielding `h2k_keepLr_false_of_noException`,
   `h2k_keepSubLr_false_of_noException`, and `h2k_fds_of_noException` on every non-`.Exception`
   transition.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks

open Arm64 (FsTraced GhostName HookFsTraced HookOk HookSat Memory Program Reg SepProp Spec State
  SubroutineOutcome subroutine_ok)
open Arm64.Obj (MultiPlacement)
open ProofLib (hookNoop libcMemcpySpec libcMemmoveSpec libcMemsetSpec memcpyRegionSpec
  memsetRegionSpec)
open VerifiedLibraries (mallocngLib)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsHandleErrorSym
  lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsRustReallocSym lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles TraceFsSound withLsCodeRoLoaded
  withLsRoCl)
open CryptoVerification.LibsignalSessionRepr (VecGhost)
open CryptoVerification.LibsignalTripleRatchet (extHookStack framelessMemcpySpec lsMemcpySym
  memcpyName memmoveName memsetName noAllocShimSpec sessionMemcpyRegionSpec sessionMemcpySpec
  sessionMemsetRegionSpec sessionMemsetSpec withStack)
open CryptoVerification.LibsignalTripleRatchet.Prost (lsHandleAllocErrorSym)
open CryptoVerification.SignalSession (CliHooks cliElfBytes cliElfImage cliExternsPlaced
  libsignalSessionLib lsFormatInnerSym lsFromUtf8Sym lsMemrchrSym lsReadFileSym lsReadStdinSym
  lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
  lsRustReallocSymCli lsStringCloneSym lsWriteFileSym lsWriteStdoutSym)
open CryptoVerification.SignalSession.Cli (ReadFileGhost ReadRule cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops (IoModel ReadFileLitGhost ReadStdinGhost cliIo
  cliRunBudgets cliWrOk fromUtf8AsciiSpec hookOk_withStack memrchrSpec)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks CliGhostHooksFs IsFsC
  cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (CliPanicHooksPlaced)
open CryptoVerification.SignalSession.CliExt (ReadFileCall)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Heap.Fine (f3RdlAddrs f3RdlAzAddr fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec stringCloneNoOomSpec)
open LibsignalBinary.Heap.SpecBudget (formatInnerBudgetSpec rustAllocZeroedBudgetSpec
  withVmPreserved)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (keepFsTrace keepFsTrace_fsT)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (ExternNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook (ActiveF3ReadFileRun
  F3ReadFileFixedCallGuard f3ReadFileFallback readFileAnySpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed
  ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced (
  ActiveReadStdinLinkedRun keepFilesTrace keepFilesTrace_fsT)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (ActiveF3CallPre
  f3AllocFallback f3DeallocFallback f3LinkedCallHook f3LinkedCallHook_fs f3LinkedCallHook_fsT
  f3ReadStdinFallback f3ReallocFallback f3StringCloneFallback)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookExactMemcpy)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness (
  f3EmptyMemcpyGhostHookNarrow f3EmptyMemcpyGhostHookNarrow_exact f3EmptyMemcpyGhostHookNarrow_fsT
  f3EmptyMemcpyGhostHookNarrow_noAllocFailed f3EmptyMemcpyGhostHookNarrow_r1_allocWitness
  f3EmptyMemsetGhostHookNarrow f3EmptyMemsetGhostHookNarrow_eq_narrow
  f3EmptyMemsetGhostHookNarrow_fsT f3EmptyMemsetGhostHookNarrow_noAllocFailed
  f3EmptyMemsetGhostHookNarrow_r1_allocWitness)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced (ReadStdinBoundedEnv
  readStdinSpecOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv
  readFileLitSpecPlaced readFileSpecPlaced writeFileSpecPlaced writeStdoutSpecPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst (
  hole2_ActiveStrCloneRun hole2_emptyProg hole2_hblk hole2_hext_nodup hole2_hookStack hole2_keep
  hole2_keepSub hole2_targets)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec
  sessionMemcpyRegionBudgetSpec sessionMemmoveBudgetSpec sessionMemsetBudgetSpec
  sessionMemsetRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocSpecWithStack
  rustDeallocExternSpecWithStack rustReallocExternSpecWithStack)

/-! ## Narrowed `Spec` Combinators and `h2k_<hook>SpecK` Wrappers -/

/-- Narrow `spec.pre` by conjoining `⌜keepSet (s.readReg64 .lr) = false⌝` while keeping `post`,
    `onPanic`, `onExit`, and `onOom` definitionally unchanged. -/
def h2k_withKeepLrFalse {α : Type} (keepSet : BitVec 64 → Bool) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜keepSet (s.readReg64 .lr) = false⌝ ∗ spec.pre x s }

/-- Narrow `spec.pre` by conjoining `⌜keepSet (s.readReg64 .lr) = false ∧ FdsGe3Closed s.fs⌝`
while keeping `post`, `onPanic`, `onExit`, and `onOom` definitionally unchanged. -/
def h2k_withKeepLrAndFds {α : Type} (keepSet : BitVec 64 → Bool) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s => ⌜keepSet (s.readReg64 .lr) = false ∧ FdsGe3Closed s.fs⌝ ∗ spec.pre x s }

/-- Narrowed `alloc` spec (`hole2_keepSub`, `rustCliAllocBudgetSpec M A lim false`). -/
def h2k_allocSpecK [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Nat × Nat × M.σ) :=
  h2k_withKeepLrFalse hole2_keepSub (rustCliAllocBudgetSpec M A lim false)

/-- Narrowed `dealloc` spec (`hole2_keepSub`, `rustCliDeallocBudgetSpec M A lim`). -/
def h2k_deallocSpecK [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (BitVec 64 × Nat × Nat × M.σ) :=
  h2k_withKeepLrFalse hole2_keepSub (rustCliDeallocBudgetSpec M A lim)

/-- Narrowed `realloc` spec (`hole2_keepSub`, `rustCliReallocBudgetSpec M A lim`). -/
def h2k_reallocSpecK [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ) :=
  h2k_withKeepLrFalse hole2_keepSub (rustCliReallocBudgetSpec M A lim)

/-- Narrowed `allocZeroed` spec (`hole2_keepSub`, `rustAllocZeroedBudgetSpec M A lim`). -/
def h2k_allocZeroedSpecK [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Nat × Nat × M.σ) :=
  h2k_withKeepLrFalse hole2_keepSub (rustAllocZeroedBudgetSpec M A lim)

/-- Narrowed `stringClone` `NoOom` spec (`hole2_keep`, `stringCloneNoOomSpec M A lim`). -/
def h2k_stringCloneSpecK [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (BitVec 64 × BitVec 64 × VecGhost × M.σ) :=
  h2k_withKeepLrFalse hole2_keep (stringCloneNoOomSpec M A lim)

/-- Narrowed `stringClone` budget spec (`hole2_keep`, `stringCloneBudgetSpec`). -/
def h2k_stringCloneBudgetSpecK [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × BitVec 64 × VecGhost × M.σ) :=
  h2k_withKeepLrFalse hole2_keep (stringCloneBudgetSpec M A lim)

/-- Narrowed `readFile` spec (`hole2_keepSub` + `FdsGe3Closed s.fs`). -/
def h2k_readFileSpecK {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv rd) :
    Spec (ReadFileGhost × M.σ) :=
  h2k_withKeepLrAndFds hole2_keepSub (readFileSpecPlaced rd pathOk A lim stk ReadEnv)

/-- Block-`617` literal-path (`ro = true`, `hole2_keepSub` + `FdsGe3Closed s.fs`) companion of
    `h2k_readFileSpecK` for `h2k_MainIoOfPlacedK.readFile`. -/
def h2k_readFileLitSpecK {M : AllocCostModel} (io : IoModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv io.rd) :
    Spec (ReadFileLitGhost × M.σ) :=
  h2k_withKeepLrAndFds hole2_keepSub (readFileLitSpecPlaced io A lim stk ReadEnv)

/-- Unified `ro : Bool` (`hole2_keepSub` + `FdsGe3Closed s.fs`) companion of `h2k_readFileSpecK`
    used in the outer `ActiveF3CallPre` guard of `h2k_readFileFixedGhostHookFineK`. -/
def h2k_readFileAnySpecK {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) :
    Spec (ReadFileCall × M.σ) :=
  h2k_withKeepLrAndFds hole2_keepSub (readFileAnySpecPlaced A lim stk ReadEnv)

/-- Narrowed `readStdin` spec (`hole2_keepSub`, `readStdinSpecOfPlaced io A lim stk StdinEnv`). -/
def h2k_readStdinSpecK [LibsignalPlacement] {M : AllocCostModel} (io : IoModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (StdinEnv : List (BitVec 8) → List AllocEvent → Prop := ReadStdinBoundedEnv) :
    Spec (ReadStdinGhost × M.σ) :=
  h2k_withKeepLrFalse hole2_keepSub (readStdinSpecOfPlaced io A lim stk StdinEnv)

/-- `WithStack` extern wrapper (`hole2_keepSub`) mirroring `Hooks2Budget.rustAllocSpecWithStack`. -/
def h2k_rustAllocSpecWithStackK [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (zeroed : Bool) (stk : Nat) : Spec (Nat × Nat × M.σ) :=
  h2k_withKeepLrFalse hole2_keepSub (rustAllocSpecWithStack M A lim zeroed stk)

/-- `WithStack` extern wrapper (`hole2_keepSub`) mirroring `Hooks2Budget.rustDeallocExternSpecWithStack`. -/
def h2k_rustDeallocExternSpecWithStackK [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (BitVec 64 × Nat × Nat × M.σ) :=
  h2k_withKeepLrFalse hole2_keepSub (rustDeallocExternSpecWithStack M A lim stk)

/-- `WithStack` extern wrapper (`hole2_keepSub`) mirroring `Hooks2Budget.rustReallocExternSpecWithStack`. -/
def h2k_rustReallocExternSpecWithStackK [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ) :=
  h2k_withKeepLrFalse hole2_keepSub (rustReallocExternSpecWithStack M A lim stk)

/-! ## K-Twin Hook Bundles -/

/-- K-twin of `CliGhostAllocHooks` at `h2k_{alloc,dealloc,realloc}SpecK`. -/
structure h2k_CliGhostAllocHooksK [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (g : CliGhostHooks) : Prop where
  alloc : HookOk g.alloc (h2k_allocSpecK M A lim)
  dealloc : HookOk g.dealloc (h2k_deallocSpecK M A lim)
  realloc : HookOk g.realloc (h2k_reallocSpecK M A lim)
  alloc_fs : ∀ s : State, (g.alloc s).fs = s.fs
  dealloc_fs : ∀ s : State, (g.dealloc s).fs = s.fs
  realloc_fs : ∀ s : State, (g.realloc s).fs = s.fs
  alloc_fsT : HookFsTraced IsFsC g.alloc
  dealloc_fsT : HookFsTraced IsFsC g.dealloc
  realloc_fsT : HookFsTraced IsFsC g.realloc
  shim_eq : g.shim = hookNoop := by rfl
  memset : ∃ f, g.memset = some f ∧
    (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
    (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
    HookOk f memsetRegionSpec ∧
    HookOk f sessionMemsetRegionSpec ∧
    (∀ s : State, VmPreserved s (f s)) ∧
    (∀ s : State, (f s).fs = s.fs) ∧
    HookFsTraced IsFsC f
  memcpy : ∃ f, g.memcpy = some f ∧
    (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
    (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
    HookOk f memcpyRegionSpec ∧
    HookOk f sessionMemcpyRegionSpec ∧
    HookOk f framelessMemcpySpec ∧
    HookOk f sessionMemcpyRegionROSpec ∧
    (∀ s : State, VmPreserved s (f s)) ∧
    (∀ s : State, (f s).fs = s.fs) ∧
    HookFsTraced IsFsC f
  memcpy_exact : ∀ f, g.memcpy = some f → HookExactMemcpy f
  memset_acp : ∀ f, g.memset = some f → ∀ s : State, (f s).sigActions = s.sigActions ∧ (f s).oracle = s.oracle

/-- K-twin of `CliGhostSpqrAllocHooks` extending `h2k_CliGhostAllocHooksK` with
`h2k_allocZeroedSpecK`. -/
structure h2k_CliGhostSpqrAllocHooksK [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (g : CliGhostHooks) : Prop extends h2k_CliGhostAllocHooksK M A lim g where
  allocZeroed : HookOk g.allocZeroed (h2k_allocZeroedSpecK M A lim)
  allocZeroed_fs : ∀ s : State, (g.allocZeroed s).fs = s.fs
  allocZeroed_fsT : HookFsTraced IsFsC g.allocZeroed

/-- K-twin of `CodecHooksPlaced` at `h2k_{alloc,realloc,dealloc}SpecK`. -/
structure h2k_CodecHooksPlacedK [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  shim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)
  alloc : HookSat H lsRustAllocSym (h2k_allocSpecK M A lim)
  realloc : HookSat H lsRustReallocSym (h2k_reallocSpecK M A lim)
  dealloc : HookSat H lsRustDeallocSym (h2k_deallocSpecK M A lim)
  memcpy : HookSat H lsMemcpySym (withVmPreserved framelessMemcpySpec)
  panic_alloc : H lsHandleAllocErrorSym = some Arm64.Rust.panicked
  panic_raw : H lsHandleErrorSym = some Arm64.Rust.panicked

/-- K-twin of `AllocContractsXCliPlaced` narrowing the three ghost allocator contracts with
`hole2_keepSub`. -/
structure h2k_AllocContractsXCliPlacedK [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  alloc : subroutine_ok (lsProg_617 H) (lsρ lsRustAllocSymCli)
    (withLsCodeRoLoaded lsmpl (h2k_rustAllocSpecWithStackK M A lim false extHookStack))
  dealloc : subroutine_ok (lsProg_617 H) (lsρ lsRustDeallocSymCli)
    (withLsCodeRoLoaded lsmpl (h2k_rustDeallocExternSpecWithStackK M A lim extHookStack))
  realloc : subroutine_ok (lsProg_617 H) (lsρ lsRustReallocSymCli)
    (withLsCodeRoLoaded lsmpl (h2k_rustReallocExternSpecWithStackK M A lim extHookStack))
  shim : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsCodeRoLoaded lsmpl (withStack sessionShimBudgetSpec stk))
  memcpy : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (libcMemcpySpec stk)))
  session_memcpy : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (sessionMemcpyBudgetSpec stk))
  memcpy_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (withStack (withVmPreserved memcpyRegionSpec) stk))
  session_memcpy_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionBudgetSpec stk))
  memmove : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memmoveName)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (libcMemmoveSpec stk)))
  session_memmove : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memmoveName)
      (withLsCodeRoLoaded lsmpl (sessionMemmoveBudgetSpec stk))
  memset : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (libcMemsetSpec stk)))
  session_memset : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (withLsCodeRoLoaded lsmpl (sessionMemsetBudgetSpec stk))
  memset_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (withLsCodeRoLoaded lsmpl (withStack (withVmPreserved memsetRegionSpec) stk))
  session_memset_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (withLsCodeRoLoaded lsmpl (withStack sessionMemsetRegionBudgetSpec stk))

/-- K-twin of `AllocContractsFsPlaced` narrowing the three ghost allocator `.keepsFs`
contracts with `hole2_keepSub`. -/
structure h2k_AllocContractsFsPlacedK [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  alloc : subroutine_ok (lsProg_617 H) (lsρ lsRustAllocSymCli)
    (withLsCodeRoLoaded lsmpl (h2k_rustAllocSpecWithStackK M A lim false extHookStack).keepsFs)
  dealloc : subroutine_ok (lsProg_617 H) (lsρ lsRustDeallocSymCli)
    (withLsCodeRoLoaded lsmpl (h2k_rustDeallocExternSpecWithStackK M A lim extHookStack).keepsFs)
  realloc : subroutine_ok (lsProg_617 H) (lsρ lsRustReallocSymCli)
    (withLsCodeRoLoaded lsmpl (h2k_rustReallocExternSpecWithStackK M A lim extHookStack).keepsFs)
  shim : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsCodeRoLoaded lsmpl (withStack sessionShimBudgetSpec stk).keepsFs)
  memcpy : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (libcMemcpySpec stk)).keepsFs)
  session_memcpy : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (sessionMemcpyBudgetSpec stk).keepsFs)
  memcpy_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (withStack (withVmPreserved memcpyRegionSpec) stk).keepsFs)
  session_memcpy_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionBudgetSpec stk).keepsFs)
  memmove : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memmoveName)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (libcMemmoveSpec stk)).keepsFs)
  session_memmove : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memmoveName)
      (withLsCodeRoLoaded lsmpl (sessionMemmoveBudgetSpec stk).keepsFs)
  memset : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (libcMemsetSpec stk)).keepsFs)
  session_memset : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (withLsCodeRoLoaded lsmpl (sessionMemsetBudgetSpec stk).keepsFs)
  memset_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (withLsCodeRoLoaded lsmpl (withStack (withVmPreserved memsetRegionSpec) stk).keepsFs)
  session_memset_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memsetName)
      (withLsCodeRoLoaded lsmpl (withStack sessionMemsetRegionBudgetSpec stk).keepsFs)
  session_memcpy_region_ro : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_617 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (withStack (withVmPreserved sessionMemcpyRegionROSpec) stk).keepsFs)

/-- K-twin of `RunHooksPlaced` at the narrowed ghost-hook specs. -/
structure h2k_RunHooksPlacedK [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : LibsignalHooks) : Prop where
  alloc : h2k_AllocContractsXCliPlacedK A lim ext
  allocFs : h2k_AllocContractsFsPlacedK A lim ext
  panics : CliPanicHooksPlaced ext
  memcpyRO : HookSat ext lsMemcpySym (withVmPreserved sessionMemcpyRegionROSpec)
  bcmp : HookSat ext "bcmp" (withVmPreserved cliBcmpSpec)
  fs : ∀ (prog : Program) (i : Nat), [IsLsBlockProg prog i ext] → TraceFsSound prog
  utf8 : ∀ stk : Nat, HookSat ext lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec stk))
  memrchr : ∀ stk : Nat, HookSat ext lsMemrchrSym (withVmPreserved (memrchrSpec stk))
  codecHooks : h2k_CodecHooksPlacedK M A lim ext
  allocZeroed : HookSat ext lsRustAllocZeroedSymCli (h2k_allocZeroedSpecK M A lim)
  stringClone : HookSat ext lsStringCloneSym (h2k_stringCloneBudgetSpecK M A lim)
  formatInner : HookSat ext lsFormatInnerSym (formatInnerBudgetSpec M A lim)

/-- K-twin of `CliRunHooksBundle` combining `h2k_RunHooksPlacedK` with `lsReadFileSym`
`subroutine_ok` at `h2k_readFileSpecK`. -/
structure h2k_CliRunHooksBundleK [LibsignalPlacement] (mmpl : MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) : Prop where
  runHooks : h2k_RunHooksPlacedK A lim (cliGhostExterns g (cliExternsPlaced mmpl W))
  readFile579 : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (lsρ lsReadFileSym)
    (h2k_readFileSpecK cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv)

/-- K-twin of `MainIoOfPlaced` narrowing `lsReadStdinSym` and `lsReadFileSym` with
`hole2_keepSub` while leaving `writeFile` and `writeStdout` unchanged. -/
structure h2k_MainIoOfPlacedK [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat)
    (StdinEnv : List (BitVec 8) → List AllocEvent → Prop := ReadStdinBoundedEnv)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv io.rd) :
    Prop where
  readStdin : subroutine_ok (lsProg_617 H) (lsρ lsReadStdinSym)
    (withLsRoCl lsmpl (h2k_readStdinSpecK io A lim hookStack StdinEnv))
  readFile : subroutine_ok (lsProg_617 H) (lsρ lsReadFileSym)
    (withLsRoCl lsmpl (h2k_readFileLitSpecK io A lim hookStack ReadEnv))
  writeFile : subroutine_ok (lsProg_617 H) (lsρ lsWriteFileSym)
    (withLsRoCl lsmpl (writeFileSpecPlaced io A lim hookStack))
  writeStdout : subroutine_ok (lsProg_617 H) (lsρ lsWriteStdoutSym)
    (withLsRoCl lsmpl (writeStdoutSpecPlaced A lim hookStack))

/-! ## Ghost-Hook Family (`h2k_ghFixedK`) -/

/-- K-narrowed `alloc` ghost hook: direct instantiation of parametric `f3LinkedCallHook` at
    `h2k_allocSpecK` (`hole2_keepSub`). -/
noncomputable def h2k_allocGhostHookFineK [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) : State → State :=
  f3LinkedCallHook keep P_real P_sub entryTarget
    (fun γ tp => h2k_allocSpecK fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)
    (f3AllocFallback mmpl false)

/-- K-narrowed `dealloc` ghost hook: direct instantiation of parametric `f3LinkedCallHook` at
    `h2k_deallocSpecK` (`hole2_keepSub`). -/
noncomputable def h2k_deallocGhostHookFineK [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) : State → State :=
  f3LinkedCallHook keep P_real P_sub entryTarget
    (fun γ tp => h2k_deallocSpecK fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)
    (f3DeallocFallback mmpl)

/-- K-narrowed `realloc` ghost hook: direct instantiation of parametric `f3LinkedCallHook` at
    `h2k_reallocSpecK` (`hole2_keepSub`). -/
noncomputable def h2k_reallocGhostHookFineK [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) : State → State :=
  f3LinkedCallHook keep P_real P_sub entryTarget
    (fun γ tp => h2k_reallocSpecK fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)
    (f3ReallocFallback mmpl)

/-- K-narrowed `allocZeroed` ghost hook: direct instantiation of parametric `f3LinkedCallHook` at
    `h2k_allocZeroedSpecK` (`hole2_keepSub`). -/
noncomputable def h2k_allocZeroedGhostHookFineK [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) : State → State :=
  f3LinkedCallHook keep P_real P_sub entryTarget
    (fun γ tp => h2k_allocZeroedSpecK fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)
    (f3AllocFallback mmpl true)

open Classical in
/-- K-twin of `hole2_strCloneGhostHook` guarding `ActiveF3CallPre` with `h2k_stringCloneSpecK`
(`hole2_keep`). -/
noncomputable def h2k_strCloneGhostHookK [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (s0 : State) : State :=
  if _ : ActiveF3CallPre
      (fun γ tp => h2k_stringCloneSpecK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) s0 then
    if hReal : hole2_ActiveStrCloneRun mpl s0 then
      Classical.choose hReal.2.2.2.2
    else
      keepFsTrace (f3StringCloneFallback mmpl) s0
  else
    { s0 with status := .Exception "ghost-hook precondition violated" }

theorem h2k_strCloneGhostHookK_fsT [LibsignalPlacement] (mpl mmpl : MultiPlacement) :
    HookFsTraced IsFsC (h2k_strCloneGhostHookK mpl mmpl) := by
  classical
  intro s0
  unfold h2k_strCloneGhostHookK
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2.2).2.2.2.1
    · exact keepFsTrace_fsT _ s0
  · exact FsTraced.of_eq rfl rfl

open Classical in
/-- K-twin of `f3ReadFileFixedGhostHookFine` guarding `ActiveF3CallPre` with
`h2k_readFileAnySpecK` (`hole2_keepSub` and `FdsGe3Closed`). -/
noncomputable def h2k_readFileFixedGhostHookFineK
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) (s0 : State) : State :=
  if _ : ActiveF3CallPre
      (fun γ tp => h2k_readFileAnySpecK
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk
        (ReadFileRuleEnvFixed cliIo.rd)) s0 then
    if hReal : ActiveF3ReadFileRun keep P_real P_sub entry_io F3ReadFileFixedCallGuard s0 then
      Classical.choose hReal.2.2.2.2
    else
      keepFsTrace (f3ReadFileFallback mmpl) s0
  else
    { s0 with status := .Exception "read_file ghost-hook precondition violated" }

theorem h2k_readFileFixedGhostHookFineK_fsT
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) :
    HookFsTraced IsFsC
      (h2k_readFileFixedGhostHookFineK keep P_real P_sub entry_io mmpl brkStart lim stk) := by
  classical
  intro s0
  unfold h2k_readFileFixedGhostHookFineK
  split
  · split
    · rename_i hReal
      have hspec := Classical.choose_spec hReal.2.2.2.2
      exact FsTraced.of_eq hspec.2.2.2.1 (congrArg Arm64.FsState.files hspec.2.2.1)
    · exact FsTraced.of_eq rfl rfl
  · exact FsTraced.of_eq rfl rfl

noncomputable def h2k_readFileFixedGhostHookFineSubK
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) :
    { f : State → State // HookFsTraced IsFsC f } :=
  ⟨h2k_readFileFixedGhostHookFineK keep P_real P_sub entry_io mmpl brkStart lim stk,
   h2k_readFileFixedGhostHookFineK_fsT keep P_real P_sub entry_io mmpl brkStart lim stk⟩

open Classical in
/-- K-twin of `f3ReadStdinGhostHookFine` guarding `ActiveF3CallPre` with `h2k_readStdinSpecK`
(`hole2_keepSub`). -/
noncomputable def h2k_readStdinGhostHookFineK [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) (s0 : State) : State :=
  if _ : ActiveF3CallPre
      (fun γ tp => h2k_readStdinSpecK cliIo
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk ReadStdinBoundedEnv) s0 then
    if hReal : ActiveReadStdinLinkedRun keep P_real P_sub entry_io s0 then
      Classical.choose hReal.2.2.2
    else
      keepFilesTrace (f3ReadStdinFallback mmpl) s0
  else
    { s0 with status := .Exception "read_stdin ghost-hook precondition violated" }

theorem h2k_readStdinGhostHookFineK_fsT [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) :
    HookFsTraced IsFsC
      (h2k_readStdinGhostHookFineK keep P_real P_sub entry_io mmpl brkStart lim stk) := by
  classical
  intro s0
  unfold h2k_readStdinGhostHookFineK
  split
  · split
    · rename_i hReal
      have hspec := Classical.choose_spec hReal.2.2.2
      exact FsTraced.of_eq hspec.2.2.2.1 hspec.2.2.1
    · exact keepFilesTrace_fsT (f3ReadStdinFallback mmpl) s0
  · exact FsTraced.of_eq rfl rfl

noncomputable def h2k_readStdinGhostHookFineSubK [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) :
    { f : State → State // HookFsTraced IsFsC f } :=
  ⟨h2k_readStdinGhostHookFineK keep P_real P_sub entry_io mmpl brkStart lim stk,
   h2k_readStdinGhostHookFineK_fsT keep P_real P_sub entry_io mmpl brkStart lim stk⟩

/-- K ghost-hook tuple instantiating `hole2_ghFixed` at the seven `h2k_*SpecK` specs. -/
noncomputable def h2k_ghFixedK [LibsignalPlacement] (mpl mmpl : MultiPlacement) : CliGhostHooks where
  alloc := h2k_allocGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
    (hole2_targets mpl).alloc mmpl cliElfImage.brkStart cliBudgetLimits
  dealloc := h2k_deallocGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
    (hole2_targets mpl).dealloc mmpl cliElfImage.brkStart cliBudgetLimits
  realloc := h2k_reallocGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
    (hole2_targets mpl).realloc mmpl cliElfImage.brkStart cliBudgetLimits
  allocZeroed := h2k_allocZeroedGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
    (hole2_targets mpl).allocZeroed mmpl cliElfImage.brkStart cliBudgetLimits
  shim := hookNoop
  stringClone := some (h2k_strCloneGhostHookK mpl mmpl)
  readFile := some (h2k_readFileFixedGhostHookFineSubK hole2_keepSub hole2_emptyProg f3TrialRxProg
    (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack)
  readStdin := some (h2k_readStdinGhostHookFineSubK hole2_keepSub hole2_emptyProg f3TrialRxProg
    (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack)
  memset := some (f3EmptyMemsetGhostHookNarrow mmpl)
  memcpy := some (f3EmptyMemcpyGhostHookNarrow mmpl)

/-- Per-symbol `keepSet` selector (`hole2_keep` on `lsStringCloneSym`, `hole2_keepSub` on the
six allocator / I/O hooks). -/
def h2k_keepSetForSym (sym : String) : BitVec 64 → Bool :=
  if sym == lsStringCloneSym then hole2_keep else hole2_keepSub

/-! ## Hook Closure Lemmas and Non-`.Exception` Guard Extraction -/

/-- Spec-free `CliGhostHooksFs` companion for `h2k_ghFixedK`. -/
theorem h2k_hole2_hFsK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    CliGhostHooksFs (h2k_ghFixedK mpl mmpl) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have _ := hLs
  have _ := hMm
  refine
    { alloc_fsT := f3LinkedCallHook_fsT _ _ _ _ _ _
      dealloc_fsT := f3LinkedCallHook_fsT _ _ _ _ _ _
      realloc_fsT := f3LinkedCallHook_fsT _ _ _ _ _ _
      allocZeroed_fsT := f3LinkedCallHook_fsT _ _ _ _ _ _
      shim_fsT := CryptoVerification.SignalSession.Cli.RunGlue.hookNoop_fsT
      stringClone_fsT := ?_
      memset_fsT := ?_
      memcpy_fsT := ?_ }
  · intro f hf
    dsimp only [h2k_ghFixedK] at hf
    injection hf with hfeq
    subst hfeq
    exact h2k_strCloneGhostHookK_fsT mpl mmpl
  · intro f hf
    dsimp only [h2k_ghFixedK] at hf
    injection hf with hfeq
    subst hfeq
    exact f3EmptyMemsetGhostHookNarrow_fsT mmpl
  · intro f hf
    dsimp only [h2k_ghFixedK] at hf
    injection hf with hfeq
    subst hfeq
    exact f3EmptyMemcpyGhostHookNarrow_fsT mmpl

private theorem h2k_hookMemcpy_trace (s : State) :
    (ProofLib.hookMemcpy s).trace = s.trace := by
  unfold ProofLib.hookMemcpy ProofLib.retHook
  dsimp (config := { zeta := true, zetaHave := true }) only [State.setMem, State.setPC]

private theorem h2k_emptyProg_externAt (pc : BitVec 64) :
    hole2_emptyProg.externAt? pc = none := rfl

private theorem h2k_emptyProg_steps_noAllocFailed {s0 sf : State} {entry : BitVec 64}
    (h : Arm64.Steps hole2_emptyProg (s0.setPC entry) sf) :
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.TraceDeltaNoAllocFailed
      s0 sf :=
  LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_trans
    (s1 := s0.setPC entry)
    (LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl)
    (LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.steps_traceDeltaNoAllocFailed
      LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.execSyscall_noAllocFailed
      (fun pc _ he => nomatch (h2k_emptyProg_externAt pc).symm.trans he)
      h)

private theorem h2k_linkedCallHook_noAllocFailed {α : Type}
    (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α)
    (fallback : State → State) :
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.HookNoAllocFailed
      (f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg entryTarget specOf fallback) := by
  classical
  intro s0
  unfold f3LinkedCallHook
  split
  · split
    · rename_i hReal
      exact h2k_emptyProg_steps_noAllocFailed (Classical.choose_spec hReal.2.2.2).1.toSteps
    · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl
  · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl

private theorem h2k_strCloneProg_externs_noAllocFailed (mpl : MultiPlacement) :
    ExternNoAllocFailed
      (LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.hole2_strCloneProg
        mpl).externs := by
  intro sym f hf
  dsimp only [LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.hole2_strCloneProg] at hf
  split at hf
  · injection hf with hfeq
    subst hfeq
    exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.hookNoAllocFailed_of_trace_eq
      _ h2k_hookMemcpy_trace
  · split at hf
    · injection hf with hfeq
      subst hfeq
      exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.hookNoAllocFailed_of_trace_eq
        _ (fun _ => rfl)
    · cases hf

private theorem h2k_strCloneGhostHookK_noAllocFailed [LibsignalPlacement] (mpl mmpl : MultiPlacement) :
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.HookNoAllocFailed
      (h2k_strCloneGhostHookK mpl mmpl) := by
  classical
  intro s0
  unfold h2k_strCloneGhostHookK
  split
  · split
    · rename_i hReal
      exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_trans
        (s1 := s0.setPC (mpl.base 623))
        (LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl)
        (LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.steps_traceDeltaNoAllocFailed
          LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.execSyscall_noAllocFailed
          (LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.externAt_noAllocFailed_of_externs
            LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.externNoAllocFailed_none
            (h2k_strCloneProg_externs_noAllocFailed mpl))
          (Classical.choose_spec hReal.2.2.2.2).1.toSteps)
    · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl
  · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl

private theorem h2k_readFileFixedGhostHookFineK_noAllocFailed
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.HookNoAllocFailed
      (h2k_readFileFixedGhostHookFineK keep P_real P_sub entry_io mmpl brkStart lim stk) := by
  classical
  intro s0
  unfold h2k_readFileFixedGhostHookFineK
  split
  · split
    · rename_i hReal
      exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq
        (Classical.choose_spec hReal.2.2.2.2).2.2.2.1
    · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl
  · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl

private theorem h2k_readStdinGhostHookFineK_noAllocFailed [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.HookNoAllocFailed
      (h2k_readStdinGhostHookFineK keep P_real P_sub entry_io mmpl brkStart lim stk) := by
  classical
  intro s0
  unfold h2k_readStdinGhostHookFineK
  split
  · split
    · rename_i hReal
      exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq
        (Classical.choose_spec hReal.2.2.2).2.2.2.1
    · unfold keepFilesTrace
      dsimp only
      split
      · rename_i hkeep
        exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq
          hkeep.2
      · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl
  · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl

/-- Spec-free `ExternNoAllocFailed` companion for `h2k_ghFixedK`. -/
theorem h2k_hole2_hghNoAllocK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ExternNoAllocFailed (cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none)) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have _ := hLs
  have _ := hMm
  intro name f h
  unfold cliGhostExterns at h
  dsimp only [h2k_ghFixedK, h2k_allocGhostHookFineK, h2k_deallocGhostHookFineK,
    h2k_reallocGhostHookFineK, h2k_allocZeroedGhostHookFineK,
    h2k_readFileFixedGhostHookFineSubK, h2k_readStdinGhostHookFineSubK] at h
  split at h
  · injection h with hfeq; subst hfeq; exact h2k_linkedCallHook_noAllocFailed _ _ _
  · split at h
    · injection h with hfeq; subst hfeq; exact h2k_linkedCallHook_noAllocFailed _ _ _
    · split at h
      · injection h with hfeq; subst hfeq; exact h2k_linkedCallHook_noAllocFailed _ _ _
      · split at h
        · injection h with hfeq; subst hfeq; exact h2k_linkedCallHook_noAllocFailed _ _ _
        · split at h
          · injection h with hfeq; subst hfeq
            exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.hookNoAllocFailed_of_trace_eq
              _ (fun _ => rfl)
          · split at h
            · injection h with hfeq; subst hfeq
              exact h2k_strCloneGhostHookK_noAllocFailed mpl mmpl
            · split at h
              · injection h with hfeq; subst hfeq
                exact h2k_readFileFixedGhostHookFineK_noAllocFailed _ _ _ _ _ _ _ _
              · split at h
                · injection h with hfeq; subst hfeq
                  exact h2k_readStdinGhostHookFineK_noAllocFailed _ _ _ _ _ _ _ _
                · split at h
                  · injection h with hfeq; subst hfeq
                    exact f3EmptyMemsetGhostHookNarrow_noAllocFailed mmpl
                  · split at h
                    · injection h with hfeq; subst hfeq
                      exact f3EmptyMemcpyGhostHookNarrow_noAllocFailed mmpl
                    · cases h

private theorem h2k_hookOk_of_eq_on_pre {α : Type} {P : State → Prop}
    {f_K f_orig : State → State} {spec : Spec α}
    (hEq : ∀ x R s0, s0.status = .Running → s0.spAligned = true →
      P s0 → (s0.mem ⊨ spec.pre x s0 ∗ R) → f_K s0 = f_orig s0)
    (hOrig : HookOk f_orig spec) :
    HookOk f_K { spec with pre := fun x s => ⌜P s⌝ ∗ spec.pre x s } := by
  intro x R s0 hrun hpre hsp
  dsimp only at hpre
  rw [ProofLib.sepConj_assoc, ProofLib.satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hP, hpre_orig⟩
  rw [hEq x R s0 hrun hsp hP hpre_orig]
  exact hOrig x R s0 hrun hpre_orig hsp

private theorem h2k_f3LinkedCallHook_eq_of_sat {α : Type}
    {keep keepSet : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State} {γ : GhostName} {tp : BitVec 64}
    {x : α} {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hlr : keepSet (s0.readReg64 .lr) = false)
    (hpre_orig : s0.mem ⊨ (specOf γ tp).pre x s0 ∗ R) :
    f3LinkedCallHook keep P_real P_sub entryTarget
      (fun γ' tp' => h2k_withKeepLrFalse keepSet (specOf γ' tp')) fallback s0 =
    f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback s0 := by
  classical
  have hActK : ActiveF3CallPre (fun γ' tp' => h2k_withKeepLrFalse keepSet (specOf γ' tp')) s0 := by
    refine ⟨hrun, hsp, γ, tp, x, R, ?_⟩
    dsimp only [h2k_withKeepLrFalse]
    rw [ProofLib.sepConj_assoc, ProofLib.satisfies_pure_sepConj]
    exact ⟨hlr, hpre_orig⟩
  have hAct : ActiveF3CallPre specOf s0 := ⟨hrun, hsp, γ, tp, x, R, hpre_orig⟩
  unfold f3LinkedCallHook
  rw [dite_eq_left_of_eq_true (eq_true hActK), dite_eq_left_of_eq_true (eq_true hAct)]

private theorem h2k_hookOk_linkedCallHook_of_orig {α : Type}
    {keep keepSet : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State} {γ : GhostName} {tp : BitVec 64}
    (hOrig : HookOk (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback) (specOf γ tp)) :
    HookOk
      (f3LinkedCallHook keep P_real P_sub entryTarget
        (fun γ' tp' => h2k_withKeepLrFalse keepSet (specOf γ' tp')) fallback)
      (h2k_withKeepLrFalse keepSet (specOf γ tp)) :=
  h2k_hookOk_of_eq_on_pre (fun _ _ _ => h2k_f3LinkedCallHook_eq_of_sat) hOrig

private theorem h2k_f3EmptyMemsetGhostHookNarrow_acp (mmpl : MultiPlacement) (s : State) :
    (f3EmptyMemsetGhostHookNarrow mmpl s).sigActions = s.sigActions ∧
      (f3EmptyMemsetGhostHookNarrow mmpl s).oracle = s.oracle := by
  classical
  rw [f3EmptyMemsetGhostHookNarrow_eq_narrow]
  refine ⟨?_, ?_⟩
  · exact (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost.memsetGhostHook_oomPoolPreserved
      rfl rfl (fun _ _ => rfl)
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.mallocngBlockProg21_externAt_none
        mmpl Arm64.Syscall.standard)
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode.mallocngBlockProg21_hasWords
        mmpl Arm64.Syscall.standard) s).1.2.2
  · unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowMemOpsR1.narrowMemsetGhostHook
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost.memsetGhostHook
      LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.linkedCallHook
    split
    · split
      · rename_i hReal
        have hOra := Arm64.Steps.oracle_eq_of_standard
          (prog := Program.ofSvc Arm64.Syscall.standard) rfl (fun _ => rfl)
          (Classical.choose_spec hReal.2.2.2).1.toSteps
        exact hOra.trans (by cases s; rfl)
      · rw [LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost.keepFsTrace_hookMemset_eq]
        cases s; rfl
    · rfl

/-- `h2k_CliGhostSpqrAllocHooksK` for `h2k_ghFixedK`. -/
theorem h2k_hole2_hGSpqrK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (γ : GhostName) (tp : BitVec 64),
      h2k_CliGhostSpqrAllocHooksK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (h2k_ghFixedK mpl mmpl) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro γ tp
  have hOrig := LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.hole2_hGSpqr
    mpl mmpl hLs hMm γ tp
  exact
    { alloc := h2k_hookOk_linkedCallHook_of_orig hOrig.alloc
      dealloc := h2k_hookOk_linkedCallHook_of_orig hOrig.dealloc
      realloc := h2k_hookOk_linkedCallHook_of_orig hOrig.realloc
      alloc_fs := f3LinkedCallHook_fs _ _ _ _ _ _
      dealloc_fs := f3LinkedCallHook_fs _ _ _ _ _ _
      realloc_fs := f3LinkedCallHook_fs _ _ _ _ _ _
      alloc_fsT := f3LinkedCallHook_fsT _ _ _ _ _ _
      dealloc_fsT := f3LinkedCallHook_fsT _ _ _ _ _ _
      realloc_fsT := f3LinkedCallHook_fsT _ _ _ _ _ _
      shim_eq := rfl
      memset := f3EmptyMemsetGhostHookNarrow_r1_allocWitness mmpl rfl
      memcpy := f3EmptyMemcpyGhostHookNarrow_r1_allocWitness mmpl rfl
      memcpy_exact := fun f hf => by
        dsimp only [h2k_ghFixedK] at hf
        injection hf with hfeq
        subst hfeq
        exact f3EmptyMemcpyGhostHookNarrow_exact mmpl
      memset_acp := fun f hf s => by
        dsimp only [h2k_ghFixedK] at hf
        injection hf with hfeq
        subst hfeq
        exact h2k_f3EmptyMemsetGhostHookNarrow_acp mmpl s
      allocZeroed := h2k_hookOk_linkedCallHook_of_orig hOrig.allocZeroed
      allocZeroed_fs := f3LinkedCallHook_fs _ _ _ _ _ _
      allocZeroed_fsT := f3LinkedCallHook_fsT _ _ _ _ _ _ }

theorem h2k_hole2_hGK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (γ : GhostName) (tp : BitVec 64),
      h2k_CliGhostAllocHooksK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (h2k_ghFixedK mpl mmpl) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  fun γ tp => (h2k_hole2_hGSpqrK mpl mmpl hLs hMm γ tp).toh2k_CliGhostAllocHooksK

private theorem h2k_readFileFixedGhostHookFineK_eq_of_any
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {mmpl : MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    {γ : GhostName} {tp : BitVec 64} {y : ReadFileCall × fineCostModel.σ}
    {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hlr : hole2_keepSub (s0.readReg64 .lr) = false) (hfds : FdsGe3Closed s0.fs)
    (hpreAny : s0.mem ⊨ (readFileAnySpecPlaced
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk
      (ReadFileRuleEnvFixed cliIo.rd)).pre y s0 ∗ R) :
    h2k_readFileFixedGhostHookFineK keep P_real P_sub entry_io mmpl brkStart lim stk s0 =
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileFixedGhostHookFine
      keep P_real P_sub entry_io mmpl brkStart lim stk s0 := by
  classical
  have hActK : ActiveF3CallPre
      (fun γ' tp' => h2k_readFileAnySpecK
        (fineHookRustCliAllocBudget γ' mmpl tp' brkStart) lim stk
        (ReadFileRuleEnvFixed cliIo.rd)) s0 := by
    refine ⟨hrun, hsp, γ, tp, y, R, ?_⟩
    dsimp only [h2k_readFileAnySpecK, h2k_withKeepLrAndFds]
    rw [ProofLib.sepConj_assoc, ProofLib.satisfies_pure_sepConj]
    exact ⟨⟨hlr, hfds⟩, hpreAny⟩
  have hAct : LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.ActiveF3ReadFilePre
      (fun γ' tp' => fineHookRustCliAllocBudget γ' mmpl tp' brkStart) lim stk
      (ReadFileRuleEnvFixed cliIo.rd) s0 :=
    ⟨hrun, hsp, γ, tp, y, R, hpreAny⟩
  unfold h2k_readFileFixedGhostHookFineK
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileFixedGhostHookFine
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileFixedGhostHook
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileLinkedHook
  rw [dite_eq_left_of_eq_true (eq_true hActK), dite_eq_left_of_eq_true (eq_true hAct)]

/-- `HookSat` on `lsReadFileSym` for `h2k_ghFixedK` at `h2k_readFileSpecK`. -/
theorem h2k_hole2_hReadSatK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)) lsReadFileSym
        (h2k_readFileSpecK cliIo.rd cliWrOk
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have _ := hLs
  intro W γ tp
  have hPl : mallocngLib.Placeable mmpl :=
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.hole2_hPl_mng mmpl hMm
  have hKeep : ∀ a : BitVec 64,
      (mallocngLib.findCodeBlock mmpl a).isSome = true → hole2_keepSub a = true :=
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.hole2_keepMallocng mmpl hMm
  have hOrigHs :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileFixedGhostHookFine_ok_placed
      (keep := hole2_keepSub) (P_real := hole2_emptyProg) (P_sub := f3TrialRxProg)
      (entry_io := (hole2_targets mpl).readFile) (mmpl := mmpl) (brkStart := cliElfImage.brkStart)
      (lim := cliBudgetLimits) (stk := hole2_hookStack)
      rfl LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_svc
      (fun _ _ => rfl)
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext
      hPl hKeep (Nat.le_refl _)
      (LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.hole2_readFileCond_ok mmpl hMm)
      γ tp
  have hOrigRun :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.AgreesOutsideReadHooks.hookOk_readFileSpecPlaced_mono_stk
      (stk0 := hole2_hookStack) (stk := cliRunBudgets.readFile) (by decide) (by decide) hOrigHs
  have hOkK : HookOk
      (h2k_readFileFixedGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack)
      (h2k_readFileSpecK cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)) := by
    apply h2k_hookOk_of_eq_on_pre _ hOrigRun
    rintro ⟨x, st⟩ R s0 hrun hsp ⟨hlr, hfds⟩ hpreRun
    let F_stk : SepProp :=
      Arm64.memRegion (s0.sp - BitVec.ofNat 64 cliRunBudgets.readFile)
        (cliRunBudgets.readFile - hole2_hookStack)
    have hsplit : ProofLib.stackAt s0.sp cliRunBudgets.readFile =
        F_stk ∗ ProofLib.stackAt s0.sp hole2_hookStack := by
      have h0 := ProofLib.stackAt_split_bottom s0.sp hole2_hookStack
        (cliRunBudgets.readFile - hole2_hookStack) (by decide)
      have heq : hole2_hookStack + (cliRunBudgets.readFile - hole2_hookStack) =
          cliRunBudgets.readFile := by decide
      rwa [heq] at h0
    have hpre0 : s0.mem ⊨ (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)).pre (x, st) s0 ∗ (F_stk ∗ R) := by
      dsimp only [readFileSpecPlaced] at hpreRun ⊢
      rw [hsplit] at hpreRun
      exact ProofLib.Satisfies.mono (ProofLib.Entails.of_eq (by sep_ac_rfl)) hpreRun
    let y : ReadFileCall × fineCostModel.σ := (⟨x.pathA, false, x.path, x.ret⟩, st)
    have hpreAny : s0.mem ⊨ (readFileAnySpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)).pre y s0 ∗ (F_stk ∗ R) := by
      dsimp only [readFileAnySpecPlaced, y, CryptoVerification.SignalSession.CliExt.bytesAt]
      dsimp only [readFileSpecPlaced] at hpre0
      rw [ProofLib.sepConj_assoc, ProofLib.sepConj_assoc, ProofLib.sepConj_assoc,
        ProofLib.sepConj_assoc, ProofLib.satisfies_pure_sepConj] at hpre0 ⊢
      exact ⟨⟨hpre0.1.1, hpre0.1.2.1, hpre0.1.2.2.1, hpre0.1.2.2.2.1,
        hpre0.1.2.2.2.2.1.1, hpre0.1.2.2.2.2.2⟩, hpre0.2⟩
    exact h2k_readFileFixedGhostHookFineK_eq_of_any hrun hsp hlr hfds hpreAny
  exact ⟨_, CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_readFile_some
    (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W) rfl, hOkK⟩

private theorem h2k_hole2_hioOfK_at [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    h2k_MainIoOfPlacedK
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)) cliIo hole2_hookStack
      ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd) := by
  let P_sub := f3TrialRxProg
  let H := cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)
  have hsvc_real : hole2_emptyProg.svc = Arm64.Syscall.standard := rfl
  have hsvc_sub : P_sub.svc = Arm64.Syscall.standard :=
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_svc
  have hreal_no : ∀ pc, hole2_keepSub pc = true → hole2_emptyProg.externAt? pc = none :=
    fun _ _ => rfl
  have hsub_no : ∀ pc, P_sub.externAt? pc = none :=
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext
  have hPl : mallocngLib.Placeable mmpl :=
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.hole2_hPl_mng mmpl hMm
  have hKeep : ∀ a : BitVec 64,
      (mallocngLib.findCodeBlock mmpl a).isSome = true → hole2_keepSub a = true :=
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.hole2_keepMallocng mmpl hMm
  have hstk : extHookStack ≤ hole2_hookStack := Nat.le_refl _
  have hStdinOrig :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3ReadStdinGhostHookFine_ok_bounded
      (keep := hole2_keepSub) (P_real := hole2_emptyProg) (P_sub := P_sub)
      (entry_io := (hole2_targets mpl).readStdin) (mmpl := mmpl) (brkStart := cliElfImage.brkStart)
      (lim := cliBudgetLimits) (stk := hole2_hookStack)
      hsvc_real hsvc_sub hreal_no hsub_no hPl hKeep hstk
      (LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.hole2_readStdinCond_ok mmpl hMm)
      γ tp
  have hStdinOkK : HookOk
      (h2k_readStdinGhostHookFineK hole2_keepSub hole2_emptyProg P_sub
        (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack)
      (h2k_readStdinSpecK cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        hole2_hookStack ReadStdinBoundedEnv) := by
    apply h2k_hookOk_of_eq_on_pre _ hStdinOrig
    rintro ⟨x, st⟩ R s0 hrun hsp hlr hpreOrig
    classical
    have hActK : ActiveF3CallPre
        (fun γ' tp' => h2k_readStdinSpecK cliIo
          (fineHookRustCliAllocBudget γ' mmpl tp' cliElfImage.brkStart) cliBudgetLimits
          hole2_hookStack ReadStdinBoundedEnv) s0 := by
      refine ⟨hrun, hsp, γ, tp, (x, st), R, ?_⟩
      dsimp only [h2k_readStdinSpecK, h2k_withKeepLrFalse]
      rw [ProofLib.sepConj_assoc, ProofLib.satisfies_pure_sepConj]
      exact ⟨hlr, hpreOrig⟩
    have hAct : LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.ActiveF3ReadStdinPre
        (fun γ' tp' => fineHookRustCliAllocBudget γ' mmpl tp' cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack s0 :=
      ⟨hrun, hsp, γ, tp, (x, st), R, hpreOrig⟩
    unfold h2k_readStdinGhostHookFineK
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3ReadStdinGhostHookFine
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3ReadStdinGhostHook
    rw [dite_eq_left_of_eq_true (eq_true hActK), dite_eq_left_of_eq_true (eq_true hAct)]
  have hLitOrig :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileFixedGhostHookFine_ok_lit
      (keep := hole2_keepSub) (P_real := hole2_emptyProg) (P_sub := P_sub)
      (entry_io := (hole2_targets mpl).readFile) (mmpl := mmpl) (brkStart := cliElfImage.brkStart)
      (lim := cliBudgetLimits) (stk := hole2_hookStack)
      hsvc_real hsvc_sub hreal_no hsub_no hPl hKeep hstk
      (LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.hole2_readFileCond_ok mmpl hMm)
      γ tp
  have hLitOkK : HookOk
      (h2k_readFileFixedGhostHookFineK hole2_keepSub hole2_emptyProg P_sub
        (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack)
      (h2k_readFileLitSpecK cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)) := by
    apply h2k_hookOk_of_eq_on_pre _ hLitOrig
    rintro ⟨x, st⟩ R s0 hrun hsp ⟨hlr, hfds⟩ hpreOrig
    let y : ReadFileCall × fineCostModel.σ := (⟨x.pathA, true, x.path, x.ret⟩, st)
    have hpreAny : s0.mem ⊨ (readFileAnySpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)).pre y s0 ∗ R := by
      simpa only [readFileAnySpecPlaced, readFileLitSpecPlaced, y,
        CryptoVerification.SignalSession.CliExt.bytesAt, ↓reduceIte] using hpreOrig
    exact h2k_readFileFixedGhostHookFineK_eq_of_any hrun hsp hlr hfds hpreAny
  exact
    { readStdin :=
        CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_rocl_of_plain <|
          CryptoVerification.ls_hook_ok_ultra_of_mem
            (prog := lsProg_617 H) (i := 617)
            ⟨_, CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_readStdin_some
              (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W) rfl, hStdinOkK⟩
            (by decide)
      readFile :=
        CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_rocl_of_plain <|
          CryptoVerification.ls_hook_ok_ultra_of_mem
            (prog := lsProg_617 H) (i := 617)
            ⟨_, CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_readFile_some
              (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W) rfl, hLitOkK⟩
            (by decide)
      writeFile :=
        CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_rocl_of_plain <|
          CryptoVerification.ls_hook_ok_ultra_of_mem
            (prog := lsProg_617 H) (i := 617)
            ⟨CryptoVerification.SignalSession.writeFileHook,
             (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_other
              (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              (CryptoVerification.SignalSession.Cli.MainHops.cliExternsPlaced_writeFile mmpl W),
             LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced.writeFileHook_ok_placed
              _ cliBudgetLimits hole2_hookStack⟩
            (by decide)
      writeStdout :=
        CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_rocl_of_plain <|
          CryptoVerification.ls_hook_ok_ultra_of_mem
            (prog := lsProg_617 H) (i := 617)
            ⟨CryptoVerification.SignalSession.writeStdoutHook,
             (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_other
              (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              (CryptoVerification.SignalSession.Cli.MainHops.cliExternsPlaced_writeStdout mmpl W),
             LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced.writeStdoutHook_ok_placed
              _ cliBudgetLimits hole2_hookStack⟩
            (by decide) }

/-- `h2k_MainIoOfPlacedK` for `h2k_ghFixedK` at `h2k_readStdinSpecK` and `h2k_readFileLitSpecK`. -/
theorem h2k_hole2_hioOfK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @h2k_MainIoOfPlacedK (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)) _
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)) cliIo hole2_hookStack
        ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  fun W γ tp =>
    @h2k_hole2_hioOfK_at (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
      mpl mmpl hMm W γ tp

private def h2k_dummyNzVec32 : List.Vector (BitVec 8) 32 :=
  ⟨1#8 :: List.replicate 31 0#8, rfl⟩

private def h2k_dummyC0 : CryptoGames.LibsignalSession.Crypto where
  F st _ := st
  E _ b := b
  D _ b := b
  X _ _ := h2k_dummyNzVec32
  pubKey _ := h2k_dummyNzVec32

private def h2k_dummyK0 : CryptoVerification.LibsignalSpqrV1.MlKem where
  keyPair _ := List.Vector.replicate 2400 0#8
  encaps1 _ _ :=
    some (List.Vector.replicate 960 0#8,
          List.Vector.replicate 2080 0#8,
          List.Vector.replicate 32 0#8)
  encaps2 _ _ := List.Vector.replicate 128 0#8
  decaps _ _ _ := List.Vector.replicate 32 0#8
  validPk _ _ := true

private def h2k_dummyQ0 : CryptoVerification.E2E.PqxdhPrims where
  F512 st _ := st
  montToEd _ _ := some (List.Vector.replicate 160 0#8)
  compress _ := List.Vector.replicate 32 0#8
  edNeg p := p
  isTorsionFree _ := true
  dsmb _ A _ := A
  scalarMod s := s
  scalarWide w := CryptoVerification.E2E.fitVec 32 w.toList
  encaps _ _ := (List.Vector.replicate 1568 0#8, List.Vector.replicate 32 0#8)
  decaps _ _ := List.Vector.replicate 32 0#8
  K := h2k_dummyK0

private def h2k_dummyCliHooks : CliHooks where
  C := h2k_dummyC0
  Q := h2k_dummyQ0
  bcmp a b := if a = b then 0#64 else 1#64
  bcmp_ok a b _ := by
    by_cases h : a = b
    · simp [h]
    · simp only [h, ↓reduceIte, iff_false]
      decide
  utf8Err _ := (0#64, 0#16)

private theorem h2k_strClone_sat_of_bundle [LibsignalPlacement]
    {mmpl : MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hb : LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget.CliRunHooksBundle
      mmpl g W A lim ReadEnv) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneBudgetSpec M A lim) :=
  hb.runHooks.stringClone

/-- `HookOk` of `h2k_strCloneGhostHookK` at `h2k_stringCloneBudgetSpecK` (`hole2_keep`). -/
theorem h2k_segc_strCloneGhostHook_okK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookOk (h2k_strCloneGhostHookK mpl mmpl)
      (h2k_stringCloneBudgetSpecK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hSatOrig :=
    @h2k_strClone_sat_of_bundle
      (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
      _ _ _ _ _ _ _
      (LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.hole2_hHooksBundle
        mpl mmpl hLs hMm h2k_dummyCliHooks γ tp)
  rcases hSatOrig with ⟨f, hf, hOrig⟩
  have hsome := CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_stringClone_some
    (LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.hole2_ghFixed mpl mmpl)
    (cliExternsPlaced mmpl h2k_dummyCliHooks) rfl
  rw [hsome] at hf
  injection hf with hfeq
  subst hfeq
  apply h2k_hookOk_of_eq_on_pre _ hOrig
  rintro ⟨p, ret, g, st⟩ R s0 hrun hsp hlr hpreOrig
  classical
  dsimp only [stringCloneBudgetSpec] at hpreOrig
  rw [ProofLib.sepConj_assoc, ProofLib.satisfies_pure_sepConj] at hpreOrig
  rcases hpreOrig with ⟨⟨hx0, hx8, hEnv, hLr⟩, hrest⟩
  have hFit := LibsignalBinary.Heap.RustStdAllocBudgetBridge.fitsEvents_stringClone_of_fitsEnv
    fineCostModel cliBudgetLimits st g hEnv
  have hpreN : s0.mem ⊨
      (stringCloneNoOomSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits).pre
        (p, ret, g, st) s0 ∗ R := by
    dsimp only [stringCloneNoOomSpec]
    rw [ProofLib.sepConj_assoc, ProofLib.satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8, hFit, hLr⟩, hrest⟩
  have hActK : ActiveF3CallPre
      (fun γ' tp' => h2k_stringCloneSpecK fineCostModel
        (fineHookRustCliAllocBudget γ' mmpl tp' cliElfImage.brkStart) cliBudgetLimits) s0 := by
    refine ⟨hrun, hsp, γ, tp, (p, ret, g, st), R, ?_⟩
    dsimp only [h2k_stringCloneSpecK, h2k_withKeepLrFalse]
    rw [ProofLib.sepConj_assoc, ProofLib.satisfies_pure_sepConj]
    exact ⟨hlr, hpreN⟩
  have hAct : ActiveF3CallPre
      (fun γ' tp' => stringCloneNoOomSpec fineCostModel
        (fineHookRustCliAllocBudget γ' mmpl tp' cliElfImage.brkStart) cliBudgetLimits) s0 :=
    ⟨hrun, hsp, γ, tp, (p, ret, g, st), R, hpreN⟩
  unfold h2k_strCloneGhostHookK
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.hole2_strCloneGhostHook
  rw [dite_eq_left_of_eq_true (eq_true hActK), dite_eq_left_of_eq_true (eq_true hAct)]

private theorem h2k_hookNoop_vm (s : State) : LibsignalBinary.Heap.VmPreserved s (hookNoop s) :=
  LibsignalBinary.Heap.VmPreserved.refl s

private theorem h2k_writeBytes_perm_eq (m : Memory) (p : BitVec 64) (bs : List (BitVec 8))
    (a : BitVec 64) : (m.writeBytes p bs).perm a = m.perm a :=
  congrFun (LibsignalBinary.Heap.IfaceBudgetLemmas.perm_writeBytes_norm m p bs) a

private theorem h2k_hookMemcpy_vm (s : State) :
    LibsignalBinary.Heap.VmPreserved s (ProofLib.hookMemcpy s) :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, h2k_writeBytes_perm_eq _ _ _, fun _ _ _ => rfl⟩

private theorem h2k_hookMemmove_vm (s : State) :
    LibsignalBinary.Heap.VmPreserved s (ProofLib.hookMemmove s) :=
  h2k_hookMemcpy_vm s

private theorem h2k_hook_placed_rocl_ok [LibsignalPlacement] {α : Type} {H : LibsignalHooks}
    {sym : String} {spec : Spec α}
    (hsat : HookSat H sym spec)
    (hmem : sym ∈ CryptoVerification.libsignalSessionExterns := by decide) :
    subroutine_ok (lsProg_617 H) (lsρ sym) (withLsCodeRoLoaded lsmpl spec) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
    (CryptoVerification.ls_hook_ok_ultra_of_mem hsat hmem)

private theorem h2k_cli_row_ghost_rocl_ok [LibsignalPlacement] {α : Type}
    (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {sym : String} {f : State → State} {spec : Spec α}
    (hrow : (sym, f) ∈ CryptoVerification.SignalSession.cliHookTablePlaced mmpl W)
    (hh : HookOk f spec)
    (hmem : sym ∈ CryptoVerification.libsignalSessionExterns)
    (h1 : sym ≠ lsRustAllocSymCli := by decide)
    (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide)
    (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide)
    (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ lsReadFileSym := by decide)
    (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ CryptoVerification.SignalSession.lsMemsetSym := by decide)
    (h10 : sym ≠ CryptoVerification.SignalSession.lsMemcpySym := by decide) :
    subroutine_ok (lsProg_617 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ sym)
      (withLsCodeRoLoaded lsmpl spec) :=
  h2k_hook_placed_rocl_ok
    (CryptoVerification.SignalSession.Cli.Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      ⟨f, CryptoVerification.SignalSession.Cli.RunGlue.cliExternsPlaced_row mmpl W hrow, hh⟩
      h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    hmem

set_option maxRecDepth 200000 in
private theorem h2k_memcpy_mem : memcpyName ∈ CryptoVerification.libsignalSessionExterns := by
  decide

set_option maxRecDepth 200000 in
private theorem h2k_memmove_mem : memmoveName ∈ CryptoVerification.libsignalSessionExterns := by
  decide

set_option maxRecDepth 200000 in
private theorem h2k_memset_mem : memsetName ∈ CryptoVerification.libsignalSessionExterns := by
  decide

private theorem h2k_memmove_ghost_rocl_ok [LibsignalPlacement] {α : Type}
    (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {f : State → State} {spec : Spec α}
    (hrow : (memmoveName, f) ∈ CryptoVerification.SignalSession.cliHookTablePlaced mmpl W)
    (hh : HookOk f spec) :
    subroutine_ok (lsProg_617 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ memmoveName)
      (withLsCodeRoLoaded lsmpl spec) :=
  h2k_cli_row_ghost_rocl_ok mmpl g W hrow hh h2k_memmove_mem

private theorem h2k_stackAt_split_ext (sp : BitVec 64) :
    ProofLib.stackAt sp extHookStack =
      Arm64.memRegion (sp - BitVec.ofNat 64 extHookStack)
        (extHookStack - CryptoVerification.RustHeap.allocHookStack) ∗
      ProofLib.stackAt sp CryptoVerification.RustHeap.allocHookStack := by
  have h0 := ProofLib.stackAt_split_bottom sp CryptoVerification.RustHeap.allocHookStack
    (extHookStack - CryptoVerification.RustHeap.allocHookStack) (by decide)
  have heq : CryptoVerification.RustHeap.allocHookStack +
      (extHookStack - CryptoVerification.RustHeap.allocHookStack) = extHookStack := by decide
  rwa [heq] at h0

private theorem h2k_pure_sepConj_imp {P Q : Prop} {R : SepProp} (h : P → Q) :
    ⌜P⌝ ∗ R ⊢ ⌜Q⌝ ∗ R :=
  ProofLib.Entails.pure_left fun hp => ProofLib.Entails.pure_right (h hp) (ProofLib.Entails.refl R)

private theorem h2k_allocWithStack_okK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookOk (h2k_ghFixedK mpl mmpl).alloc
      (h2k_rustAllocSpecWithStackK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits false extHookStack) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hOrigG := LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.hole2_hGSpqr
    mpl mmpl hLs hMm γ tp
  have hOrigWS :=
    LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget.hookOk_rustAllocWithStack
      (stk := extHookStack) hOrigG.alloc
  apply h2k_hookOk_of_eq_on_pre _ hOrigWS
  rintro ⟨size, align, st⟩ R s0 hrun hsp hlr hpreWS
  let F_stk : SepProp :=
    Arm64.memRegion (s0.sp - BitVec.ofNat 64 extHookStack)
      (extHookStack - CryptoVerification.RustHeap.allocHookStack)
  have hpre0 : s0.mem ⊨
      (rustCliAllocBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits false).pre
        (size, align, st) s0 ∗ (F_stk ∗ R) := by
    dsimp only [rustAllocSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocBudgetSpecWithStack,
      rustCliAllocBudgetSpec] at hpreWS ⊢
    rw [h2k_stackAt_split_ext s0.sp] at hpreWS
    exact ProofLib.Satisfies.mono (ProofLib.Entails.of_eq (by dsimp only [F_stk]; sep_ac_rfl)) hpreWS
  exact h2k_f3LinkedCallHook_eq_of_sat hrun hsp hlr hpre0

private theorem h2k_deallocExternWithStack_okK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookOk (h2k_ghFixedK mpl mmpl).dealloc
      (h2k_rustDeallocExternSpecWithStackK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits extHookStack) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hOrigG := LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.hole2_hGSpqr
    mpl mmpl hLs hMm γ tp
  have hOrigWS :=
    LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget.hookOk_rustDeallocExternWithStack
      (stk := extHookStack) hOrigG.dealloc
  apply h2k_hookOk_of_eq_on_pre _ hOrigWS
  rintro ⟨p, size, align, st⟩ R s0 hrun hsp hlr hpreExt
  let F_stk : SepProp :=
    Arm64.memRegion (s0.sp - BitVec.ofNat 64 extHookStack)
      (extHookStack - CryptoVerification.RustHeap.allocHookStack)
  have hpreWS : s0.mem ⊨
      (LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetSpecWithStack fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits extHookStack).pre (p, size, align, st) s0 ∗ R := by
    refine ProofLib.Satisfies.mono (ProofLib.sepConj_mono_left ?_) hpreExt
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetSpecWithStack]
    exact h2k_pure_sepConj_imp (fun ⟨h0, h1, h2, _, hlr624⟩ => ⟨h0, h1, h2, hlr624⟩)
  have hpre0 : s0.mem ⊨
      (rustCliDeallocBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits).pre
        (p, size, align, st) s0 ∗ (F_stk ∗ R) := by
    dsimp only [LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetSpecWithStack,
      rustCliDeallocBudgetSpec] at hpreWS ⊢
    rw [h2k_stackAt_split_ext s0.sp] at hpreWS
    exact ProofLib.Satisfies.mono (ProofLib.Entails.of_eq (by dsimp only [F_stk]; sep_ac_rfl)) hpreWS
  exact h2k_f3LinkedCallHook_eq_of_sat hrun hsp hlr hpre0

private theorem h2k_reallocExternWithStack_okK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookOk (h2k_ghFixedK mpl mmpl).realloc
      (h2k_rustReallocExternSpecWithStackK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits extHookStack) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hOrigG := LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.hole2_hGSpqr
    mpl mmpl hLs hMm γ tp
  have hOrigWS :=
    LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget.hookOk_rustReallocExternWithStack
      (stk := extHookStack) hOrigG.realloc
  apply h2k_hookOk_of_eq_on_pre _ hOrigWS
  rintro ⟨p, old, align, new, bs, st⟩ R s0 hrun hsp hlr hpreExt
  let F_stk : SepProp :=
    Arm64.memRegion (s0.sp - BitVec.ofNat 64 extHookStack)
      (extHookStack - CryptoVerification.RustHeap.allocHookStack)
  have hpreWS : s0.mem ⊨
      (LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocBudgetSpecWithStack fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits extHookStack).pre (p, old, align, new, bs, st) s0 ∗ R := by
    refine ProofLib.Satisfies.mono (ProofLib.sepConj_mono_left ?_) hpreExt
    dsimp only [rustReallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocBudgetSpecWithStack]
    exact h2k_pure_sepConj_imp
      (fun ⟨h0, h1, h2, h3, _hold, hnew, hblo, hbln, hlr624⟩ =>
        ⟨h0, h1, h2, h3, hnew, hblo, hbln, hlr624⟩)
  have hpre0 : s0.mem ⊨
      (rustCliReallocBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits).pre
        (p, old, align, new, bs, st) s0 ∗ (F_stk ∗ R) := by
    dsimp only [LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocBudgetSpecWithStack,
      rustCliReallocBudgetSpec] at hpreWS ⊢
    rw [h2k_stackAt_split_ext s0.sp] at hpreWS
    exact ProofLib.Satisfies.mono (ProofLib.Entails.of_eq (by dsimp only [F_stk]; sep_ac_rfl)) hpreWS
  exact h2k_f3LinkedCallHook_eq_of_sat hrun hsp hlr hpre0

private theorem h2k_hole2_hHooksBundleK_at [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2k_CliRunHooksBundleK mmpl (h2k_ghFixedK mpl mmpl) W
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  let g := h2k_ghFixedK mpl mmpl
  have hGSpqr := h2k_hole2_hGSpqrK mpl mmpl hLs hMm γ tp
  obtain ⟨fMs, hfMs, hMsLibc, hMsSess, hMsReg, hMsSessReg, hMsVm, hMsFs, _⟩ := hGSpqr.memset
  obtain ⟨fMc, hfMc, hMcLibc, hMcSess, hMcReg, hMcSessReg, hMcFrame, hMcRO, hMcVm, hMcFs, _⟩ := hGSpqr.memcpy
  have hMsEq := CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_memset_some
    g (cliExternsPlaced mmpl W) hfMs
  have hMcEq := CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_memcpy_some
    g (cliExternsPlaced mmpl W) hfMc
  have hBase :=
    LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.cliExternsPlaced_baseHelperRows
      mmpl W
  have hAllocX : h2k_AllocContractsXCliPlacedK
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    { alloc := h2k_hook_placed_rocl_ok
        ⟨g.alloc, CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_alloc g _,
          h2k_allocWithStack_okK mpl mmpl hLs hMm γ tp⟩
      dealloc := h2k_hook_placed_rocl_ok
        ⟨g.dealloc, CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_dealloc g _,
          h2k_deallocExternWithStack_okK mpl mmpl hLs hMm γ tp⟩
      realloc := h2k_hook_placed_rocl_ok
        ⟨g.realloc, CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_realloc g _,
          h2k_reallocExternWithStack_okK mpl mmpl hLs hMm γ tp⟩
      shim := fun stk _ _ => h2k_hook_placed_rocl_ok
        ⟨hookNoop,
          (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_shim g _).trans
            (congrArg some hGSpqr.shim_eq),
          hookOk_withStack (hookOk_withVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionShim_hookOk
            h2k_hookNoop_vm) stk⟩
      memcpy := fun stk _ _ => h2k_hook_placed_rocl_ok
        ⟨fMc, hMcEq, hookOk_withVmPreserved (hMcLibc stk) hMcVm⟩ h2k_memcpy_mem
      session_memcpy := fun stk _ _ => h2k_hook_placed_rocl_ok
        ⟨fMc, hMcEq, hookOk_withVmPreserved (hMcSess stk) hMcVm⟩ h2k_memcpy_mem
      memcpy_region := fun stk _ _ => h2k_hook_placed_rocl_ok
        ⟨fMc, hMcEq, hookOk_withStack (hookOk_withVmPreserved hMcReg hMcVm) stk⟩ h2k_memcpy_mem
      session_memcpy_region := fun stk _ _ => h2k_hook_placed_rocl_ok
        ⟨fMc, hMcEq, hookOk_withStack (hookOk_withVmPreserved hMcSessReg hMcVm) stk⟩ h2k_memcpy_mem
      memmove := fun stk _ _ => h2k_memmove_ghost_rocl_ok mmpl g W
        (CryptoVerification.SignalSession.Cli.Slots.memmove_row_placed mmpl W)
        (hookOk_withVmPreserved (ProofLib.hookMemmove_ok stk) h2k_hookMemmove_vm)
      session_memmove := fun stk _ _ => h2k_memmove_ghost_rocl_ok mmpl g W
        (CryptoVerification.SignalSession.Cli.Slots.memmove_row_placed mmpl W)
        (hookOk_withVmPreserved (CryptoVerification.LibsignalTripleRatchet.hookMemmove_trace_ok stk)
          h2k_hookMemmove_vm)
      memset := fun stk hle _ => h2k_hook_placed_rocl_ok
        ⟨fMs, hMsEq,
          hookOk_withVmPreserved
            (hMsLibc stk (CryptoVerification.SignalSession.Cli.MainHops.pos_of_extHookStack_le hle))
            hMsVm⟩ h2k_memset_mem
      session_memset := fun stk hle _ => h2k_hook_placed_rocl_ok
        ⟨fMs, hMsEq,
          hookOk_withVmPreserved
            (hMsSess stk (CryptoVerification.SignalSession.Cli.MainHops.pos_of_extHookStack_le hle))
            hMsVm⟩ h2k_memset_mem
      memset_region := fun stk _ _ => h2k_hook_placed_rocl_ok
        ⟨fMs, hMsEq, hookOk_withStack (hookOk_withVmPreserved hMsReg hMsVm) stk⟩ h2k_memset_mem
      session_memset_region := fun stk _ _ => h2k_hook_placed_rocl_ok
        ⟨fMs, hMsEq, hookOk_withStack (hookOk_withVmPreserved hMsSessReg hMsVm) stk⟩ h2k_memset_mem }
  have hAllocFs : h2k_AllocContractsFsPlacedK
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    { alloc := h2k_hook_placed_rocl_ok
        ⟨g.alloc, CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_alloc g _,
          (h2k_allocWithStack_okK mpl mmpl hLs hMm γ tp).keepsFs hGSpqr.alloc_fs⟩
      dealloc := h2k_hook_placed_rocl_ok
        ⟨g.dealloc, CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_dealloc g _,
          (h2k_deallocExternWithStack_okK mpl mmpl hLs hMm γ tp).keepsFs hGSpqr.dealloc_fs⟩
      realloc := h2k_hook_placed_rocl_ok
        ⟨g.realloc, CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_realloc g _,
          (h2k_reallocExternWithStack_okK mpl mmpl hLs hMm γ tp).keepsFs hGSpqr.realloc_fs⟩
      shim := fun stk _ _ => h2k_hook_placed_rocl_ok
        ⟨hookNoop,
          (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_shim g _).trans
            (congrArg some hGSpqr.shim_eq),
          (hookOk_withStack (hookOk_withVmPreserved
            CryptoVerification.LibsignalTripleRatchet.sessionShim_hookOk h2k_hookNoop_vm)
            stk).keepsFs CryptoVerification.SignalSession.Cli.MainHops.hookNoop_fs⟩
      memcpy := fun stk _ _ => h2k_hook_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withVmPreserved (hMcLibc stk) hMcVm).keepsFs hMcFs⟩ h2k_memcpy_mem
      session_memcpy := fun stk _ _ => h2k_hook_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withVmPreserved (hMcSess stk) hMcVm).keepsFs hMcFs⟩ h2k_memcpy_mem
      memcpy_region := fun stk _ _ => h2k_hook_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withStack (hookOk_withVmPreserved hMcReg hMcVm) stk).keepsFs hMcFs⟩
        h2k_memcpy_mem
      session_memcpy_region := fun stk _ _ => h2k_hook_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withStack (hookOk_withVmPreserved hMcSessReg hMcVm) stk).keepsFs hMcFs⟩
        h2k_memcpy_mem
      memmove := fun stk _ _ => h2k_memmove_ghost_rocl_ok mmpl g W
        (CryptoVerification.SignalSession.Cli.Slots.memmove_row_placed mmpl W) <|
        (hookOk_withVmPreserved (ProofLib.hookMemmove_ok stk) h2k_hookMemmove_vm).keepsFs
          CryptoVerification.SignalSession.Cli.MainHops.hookMemmove_fs
      session_memmove := fun stk _ _ => h2k_memmove_ghost_rocl_ok mmpl g W
        (CryptoVerification.SignalSession.Cli.Slots.memmove_row_placed mmpl W) <|
        (hookOk_withVmPreserved (CryptoVerification.LibsignalTripleRatchet.hookMemmove_trace_ok stk)
          h2k_hookMemmove_vm).keepsFs CryptoVerification.SignalSession.Cli.MainHops.hookMemmove_fs
      memset := fun stk hle _ => h2k_hook_placed_rocl_ok
        ⟨fMs, hMsEq,
          (hookOk_withVmPreserved
            (hMsLibc stk (CryptoVerification.SignalSession.Cli.MainHops.pos_of_extHookStack_le hle))
            hMsVm).keepsFs hMsFs⟩ h2k_memset_mem
      session_memset := fun stk hle _ => h2k_hook_placed_rocl_ok
        ⟨fMs, hMsEq,
          (hookOk_withVmPreserved
            (hMsSess stk (CryptoVerification.SignalSession.Cli.MainHops.pos_of_extHookStack_le hle))
            hMsVm).keepsFs hMsFs⟩ h2k_memset_mem
      memset_region := fun stk _ _ => h2k_hook_placed_rocl_ok
        ⟨fMs, hMsEq, (hookOk_withStack (hookOk_withVmPreserved hMsReg hMsVm) stk).keepsFs hMsFs⟩
        h2k_memset_mem
      session_memset_region := fun stk _ _ => h2k_hook_placed_rocl_ok
        ⟨fMs, hMsEq,
          (hookOk_withStack (hookOk_withVmPreserved hMsSessReg hMsVm) stk).keepsFs hMsFs⟩
        h2k_memset_mem
      session_memcpy_region_ro := fun stk _ _ => h2k_hook_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withStack (hookOk_withVmPreserved hMcRO hMcVm) stk).keepsFs hMcFs⟩
        h2k_memcpy_mem }
  have hCodec : h2k_CodecHooksPlacedK fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    { shim :=
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliExternsPlaced_noAllocShim_budget_sat
          mmpl g W hGSpqr.shim_eq
      alloc := ⟨g.alloc, CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_alloc g _,
        hGSpqr.alloc⟩
      realloc := ⟨g.realloc, CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_realloc g _,
        hGSpqr.realloc⟩
      dealloc := ⟨g.dealloc, CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_dealloc g _,
        hGSpqr.dealloc⟩
      memcpy := ⟨fMc, hMcEq, hookOk_withVmPreserved hMcFrame hMcVm⟩
      panic_alloc :=
        CryptoVerification.SignalSession.Cli.Slots.cliGhostExterns_panic_handle_alloc_error mmpl g W
      panic_raw :=
        CryptoVerification.SignalSession.Cli.Slots.cliGhostExterns_panic_handle_error mmpl g W }
  exact
    { runHooks :=
        { alloc := hAllocX
          allocFs := hAllocFs
          panics :=
            LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.cliGhostExterns_panics
              g hBase.panics
          memcpyRO := ⟨fMc, hMcEq, hookOk_withVmPreserved hMcRO hMcVm⟩
          bcmp :=
            CryptoVerification.SignalSession.Cli.Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
              (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliExternsPlaced_bcmp_budget_sat
                mmpl W)
          fs := fun _ _ _ =>
            CryptoVerification.SignalSession.Cli.RunGlue.traceFsSound_lsProg_cli_ghost
              mmpl g W (h2k_hole2_hFsK mpl mmpl hLs hMm)
          utf8 := fun stk =>
            CryptoVerification.SignalSession.Cli.Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
              (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliExternsPlaced_fromUtf8_budget_sat
                mmpl W stk)
          memrchr := fun stk =>
            CryptoVerification.SignalSession.Cli.Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
              (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliExternsPlaced_memrchr_budget_sat
                mmpl W stk)
          codecHooks := hCodec
          allocZeroed := ⟨g.allocZeroed,
            CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_allocZeroed g _,
            hGSpqr.allocZeroed⟩
          stringClone := ⟨h2k_strCloneGhostHookK mpl mmpl,
            CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_stringClone_some g _ rfl,
            h2k_segc_strCloneGhostHook_okK mpl mmpl hLs hMm γ tp⟩
          formatInner :=
            LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk.cliFormatInner_budget_sat mmpl g W }
      readFile579 :=
        CryptoVerification.ls_hook_ok_ultra_of_mem
          (prog := lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 579)
          (h2k_hole2_hReadSatK mpl mmpl hLs hMm W γ tp) (by decide) }

/-- `h2k_CliRunHooksBundleK` for `h2k_ghFixedK`. -/
theorem h2k_hole2_hHooksBundleK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @h2k_CliRunHooksBundleK
        (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
        mmpl (h2k_ghFixedK mpl mmpl) W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  fun W γ tp =>
    @h2k_hole2_hHooksBundleK_at (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
      mpl mmpl hLs hMm W γ tp

private theorem h2k_activeCallPre_of_dite_noException {P : Prop} [Decidable P]
    {t : P → State} {msg0 : String} {a : State}
    (hnoex : ∀ msg, (if h : P then t h else { a with status := .Exception msg0 }).status ≠
      .Exception msg) :
    P := by
  by_contra hnot
  rw [dite_eq_right_of_eq_false (eq_false hnot)] at hnoex
  exact hnoex msg0 rfl

private theorem h2k_pure_of_activeCallPre {α : Type} {P : State → Prop}
    {specOf : GhostName → BitVec 64 → Spec α} {a : State}
    (hAct : ActiveF3CallPre
      (fun γ tp => { specOf γ tp with pre := fun x s => ⌜P s⌝ ∗ (specOf γ tp).pre x s }) a) :
    P a := by
  rcases hAct with ⟨_, _, γ, tp, x, R, hsat⟩
  dsimp only at hsat
  rw [ProofLib.sepConj_assoc, ProofLib.satisfies_pure_sepConj] at hsat
  exact hsat.1

private theorem h2k_keepSub_false_of_keep_false {x : BitVec 64} (h : hole2_keep x = false) :
    hole2_keepSub x = false := by
  unfold hole2_keep hole2_keepSub at *
  rw [decide_eq_false_iff_not] at h ⊢
  exact fun hsub => h (Or.inr hsub)

/-- Non-`.Exception` `lr`-guard extraction: for any of the seven replayed ghost hooks `f` in
`h2k_ghFixedK`, `(f a).status ≠ .Exception` implies `h2k_keepSetForSym sym (a.readReg64 .lr) = false`. -/
theorem h2k_keepLr_false_of_noException [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    {sym : String} {f : State → State} {a : State}
    (hext : cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f)
    (hnoShim : sym ≠ lsRustNoAllocShimSymCli)
    (hnoex : ∀ msg, (f a).status ≠ .Exception msg)
    (hnoMs : sym ≠ CryptoVerification.SignalSession.lsMemsetSym := by decide)
    (hnoMc : sym ≠ CryptoVerification.SignalSession.lsMemcpySym := by decide) :
    h2k_keepSetForSym sym (a.readReg64 .lr) = false := by
  classical
  unfold cliGhostExterns at hext
  dsimp only [h2k_ghFixedK, h2k_readFileFixedGhostHookFineSubK,
    h2k_readStdinGhostHookFineSubK] at hext
  split at hext
  · rename_i hc
    have hsym := beq_iff_eq.mp hc
    subst hsym
    injection hext with hfeq; subst hfeq
    have hne : (lsRustAllocSymCli == lsStringCloneSym) = false := by decide
    simp only [h2k_keepSetForSym, hne, Bool.false_eq_true, ↓reduceIte]
    unfold h2k_allocGhostHookFineK f3LinkedCallHook at hnoex
    have hAct := h2k_activeCallPre_of_dite_noException hnoex
    dsimp only [h2k_allocSpecK, h2k_withKeepLrFalse] at hAct
    exact h2k_pure_of_activeCallPre hAct
  · split at hext
    · rename_i _ hc
      have hsym := beq_iff_eq.mp hc
      subst hsym
      injection hext with hfeq; subst hfeq
      have hne : (lsRustDeallocSymCli == lsStringCloneSym) = false := by decide
      simp only [h2k_keepSetForSym, hne, Bool.false_eq_true, ↓reduceIte]
      unfold h2k_deallocGhostHookFineK f3LinkedCallHook at hnoex
      have hAct := h2k_activeCallPre_of_dite_noException hnoex
      dsimp only [h2k_deallocSpecK, h2k_withKeepLrFalse] at hAct
      exact h2k_pure_of_activeCallPre hAct
    · split at hext
      · rename_i _ _ hc
        have hsym := beq_iff_eq.mp hc
        subst hsym
        injection hext with hfeq; subst hfeq
        have hne : (lsRustReallocSymCli == lsStringCloneSym) = false := by decide
        simp only [h2k_keepSetForSym, hne, Bool.false_eq_true, ↓reduceIte]
        unfold h2k_reallocGhostHookFineK f3LinkedCallHook at hnoex
        have hAct := h2k_activeCallPre_of_dite_noException hnoex
        dsimp only [h2k_reallocSpecK, h2k_withKeepLrFalse] at hAct
        exact h2k_pure_of_activeCallPre hAct
      · split at hext
        · rename_i _ _ _ hc
          have hsym := beq_iff_eq.mp hc
          subst hsym
          injection hext with hfeq; subst hfeq
          have hne : (lsRustAllocZeroedSymCli == lsStringCloneSym) = false := by decide
          simp only [h2k_keepSetForSym, hne, Bool.false_eq_true, ↓reduceIte]
          unfold h2k_allocZeroedGhostHookFineK f3LinkedCallHook at hnoex
          have hAct := h2k_activeCallPre_of_dite_noException hnoex
          dsimp only [h2k_allocZeroedSpecK, h2k_withKeepLrFalse] at hAct
          exact h2k_pure_of_activeCallPre hAct
        · split at hext
          · rename_i _ _ _ _ hc
            exact False.elim (hnoShim (beq_iff_eq.mp hc))
          · split at hext
            · rename_i _ _ _ _ _ hc
              have hsym := beq_iff_eq.mp hc
              subst hsym
              injection hext with hfeq; subst hfeq
              have heq : (lsStringCloneSym == lsStringCloneSym) = true := by decide
              simp only [h2k_keepSetForSym, heq, ↓reduceIte]
              unfold h2k_strCloneGhostHookK at hnoex
              have hAct := h2k_activeCallPre_of_dite_noException hnoex
              dsimp only [h2k_stringCloneSpecK, h2k_withKeepLrFalse] at hAct
              exact h2k_pure_of_activeCallPre hAct
            · split at hext
              · rename_i _ _ _ _ _ _ hc
                have hsym := beq_iff_eq.mp hc
                subst hsym
                injection hext with hfeq; subst hfeq
                have hne : (lsReadFileSym == lsStringCloneSym) = false := by decide
                simp only [h2k_keepSetForSym, hne, Bool.false_eq_true, ↓reduceIte]
                unfold h2k_readFileFixedGhostHookFineK at hnoex
                have hAct := h2k_activeCallPre_of_dite_noException hnoex
                dsimp only [h2k_readFileAnySpecK, h2k_withKeepLrAndFds] at hAct
                exact (h2k_pure_of_activeCallPre hAct).1
              · split at hext
                · rename_i _ _ _ _ _ _ _ hc
                  have hsym := beq_iff_eq.mp hc
                  subst hsym
                  injection hext with hfeq; subst hfeq
                  have hne : (lsReadStdinSym == lsStringCloneSym) = false := by decide
                  simp only [h2k_keepSetForSym, hne, Bool.false_eq_true, ↓reduceIte]
                  unfold h2k_readStdinGhostHookFineK at hnoex
                  have hAct := h2k_activeCallPre_of_dite_noException hnoex
                  dsimp only [h2k_readStdinSpecK, h2k_withKeepLrFalse] at hAct
                  exact h2k_pure_of_activeCallPre hAct
                · split at hext
                  · rename_i _ _ _ _ _ _ _ _ hc
                    exact False.elim (hnoMs (beq_iff_eq.mp hc))
                  · split at hext
                    · rename_i _ _ _ _ _ _ _ _ _ hc
                      exact False.elim (hnoMc (beq_iff_eq.mp hc))
                    · cases hext

/-- Corollary of `h2k_keepLr_false_of_noException`: since `hole2_keepSub ⊆ hole2_keep`, every
    non-`.Exception` call to any of the 7 replayed ghost hooks in `h2k_ghFixedK` satisfies
    `hole2_keepSub (a.readReg64 .lr) = false`. -/
theorem h2k_keepSubLr_false_of_noException [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    {sym : String} {f : State → State} {a : State}
    (hext : cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f)
    (hnoShim : sym ≠ lsRustNoAllocShimSymCli)
    (hnoex : ∀ msg, (f a).status ≠ .Exception msg)
    (hnoMs : sym ≠ CryptoVerification.SignalSession.lsMemsetSym := by decide)
    (hnoMc : sym ≠ CryptoVerification.SignalSession.lsMemcpySym := by decide) :
    hole2_keepSub (a.readReg64 .lr) = false := by
  have h := h2k_keepLr_false_of_noException mpl mmpl hext hnoShim hnoex hnoMs hnoMc
  unfold h2k_keepSetForSym at h
  split at h
  · exact h2k_keepSub_false_of_keep_false h
  · exact h

/-- Non-`.Exception` `FdsGe3Closed` extraction: for any non-`.Exception` call to the
`lsReadFileSym` ghost hook in `h2k_ghFixedK`, `FdsGe3Closed a.fs` holds. -/
theorem h2k_fds_of_noException [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    {baseExt : LibsignalHooks} {f : State → State} {a : State}
    (hext : cliGhostExterns (h2k_ghFixedK mpl mmpl) baseExt lsReadFileSym = some f)
    (hnoex : ∀ msg, (f a).status ≠ .Exception msg) :
    FdsGe3Closed a.fs := by
  classical
  have hsome : cliGhostExterns (h2k_ghFixedK mpl mmpl) baseExt lsReadFileSym =
      some (h2k_readFileFixedGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack) :=
    CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_readFile_some
      (h2k_ghFixedK mpl mmpl) baseExt rfl
  rw [hsome] at hext
  injection hext with hfeq
  subst hfeq
  unfold h2k_readFileFixedGhostHookFineK at hnoex
  have hAct := h2k_activeCallPre_of_dite_noException hnoex
  dsimp only [h2k_readFileAnySpecK, h2k_withKeepLrAndFds] at hAct
  exact (h2k_pure_of_activeCallPre hAct).2

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
