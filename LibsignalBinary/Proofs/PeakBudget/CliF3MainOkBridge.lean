/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import ProofLib
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.IfaceBudgetBaseBridges
public import LibsignalBinary.Proofs.PeakBudget.CliKitEnvFits
public import LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit
public import LibsignalBinary.Proofs.PeakBudget.CliNoOomOfFitsEnv
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4A.T2Strict2Bridge
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore

/-!
# Whole-program `FitsEnv` to `MainOk`, strict placed ELF correctness, and `¬ CliReachesOOMPlaced`

Chains `ReadFileRuleEnvFixed cliIo.rd ⊆ BoundedReadFileEnv`, ghost-externs `MainOk` under
`cliBudgetLimits` and `f3CliGhostHooksFixed`, internal Block-`617` ghost-to-real transfer to
`MainOkCliF3{Pq,Over}B2NeedLocksPlacedAt`, and placed ELF correctness / OOM-freedom
(`cliPqxdh{Elf,Binary}Correct{StrictPlaced2,Placed}_of_f3Fixed`, `hAlloc_of_f3Fixed`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.CliF3MainOkBridge

open Arm64 (GhostName HookFsTraced HookOk Memory Program State Steps subroutine_ok)
open Arm64.Obj (Image MultiPlacement)
open Arm64.Process (ElfImage bytesOfString initFsState)
open ProofLib
  (hookNoop libcMemcpySpec libcMemsetSpec memcpyRegionSpec memsetRegionSpec
   stripExecOutside)
open CryptoVerification (LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns)
open CryptoVerification.E2E
  (UnreachedPqxdhPrimitives aesDecHookMallocng aesEncHookMallocng libcruxHmacHookMallocng)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack framelessMemcpySpec sessionMemcpyRegionSpec sessionMemcpySpec
   sessionMemsetRegionSpec sessionMemsetSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhBinaryCorrectPlaced CliPqxdhElfCorrectPlaced
   CliPqxdhInputs CliReachesOOMPlaced Inputs
   cliExternsPlaced cliProcessInputs libsignalSessionLib
   lsMemcpySym lsMemsetSym lsReadFileSym lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli
   lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym
   stdinCapBytes)
open CryptoVerification.SignalSession.Cli.MainHops
  (LsCodeInv RunCall cliIo cliMainStk cliResStack cliRunBudgets cliWrOk inputOf mProgPlaced
   mainFrameSize parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC cliGhostExterns)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open LibsignalBinary.Heap
  (AllocEvent FitsEnv FreeOnlyEvs VmPreserved
   rustCliAllocBudgetSpecBase rustCliDeallocBudgetSpecBase rustCliReallocBudgetSpecBase
   rustDeallocEvents
   subroutine_ok_rustCliAllocBudget_of_base subroutine_ok_rustCliDeallocBudget_of_base
   subroutine_ok_rustCliReallocBudget_of_base)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetCondSpec)
open LibsignalBinary.Heap.SpecBudget (cliIoCapsEvents cliIoReadScheduleCaps)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliKitEnvFits
  (realCliMainBinaryKitEnvOfFixed_fitsEnv_cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit (specCliIoReadSchedule_events_eq)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
  (BoundedReadFileEnv boundedReadFileEnv_of_readFileRuleEnv_cliIo)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (CanonicalOrFallbackPksmEnv)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (binaryKitRunSlotEnvsFixed mkBinaryKitRealCalleeEnvsFixed
   realCliDecPkBinaryWideSlotEnvFixed realCliInitBinarySlotEnvFixed
   realCliMainBinaryKitEnvOfFixed realCliRunBinaryKitEnvOfFixed
   runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed_canonOrFallback
   runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed_canonSlice)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit (PksmCanonSliceEnv)
open LibsignalBinary.Proofs.PeakBudget.CliNoOomOfFitsEnv
  (mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_cliBudgetLimits_of_kitEnvFits_and_runTightOf
   mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_cliBudgetLimits_of_kitEnvFits_and_runTightOf)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen StubReachesTarget)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
  (MainOkCliExtOverB2NeedLocksPlacedAt MainOkCliExtPqB2NeedLocksPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed ReadFileRuleEnvFixed fdsGe3Closed_initFsState)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (f3ReadFileFixedGhostHookFine readFileAnyBudgetCondSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
  (readStdinBudgetCondSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (F3GhostEntryTargets cliGhostAllocHooks_f3CliGhostHooksFixed
   f3AllocGhostHookFine_steps_of_call
   f3AllocZeroedGhostHookFine_steps_of_call
   f3CliGhostHooksFixed
   f3DeallocGhostHookFine_steps_of_call
   f3ReadFileFixedGhostHookFine_steps_of_call
   f3ReadStdinGhostHookFine f3ReadStdinGhostHookFine_steps_of_call
   f3ReallocGhostHookFine_steps_of_call
   f3StringCloneGhostHookFine_steps_of_call
   mainIoOfPlaced_f3CliGhostHooksFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (Block617TransferFixedHyp GhostSymActive block617TransferFixed_of_replaysOn
   blockProgram_cliGhostExterns_externAt?_cases
   cliExternsPlaced_nonMallocng_preserves_fdsGe3Closed cliExternsPlaced_preserves_execFrozen
   mainOkCliF3Over_of_block617TransferFixed mainOkCliF3Pq_of_block617TransferFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
  (CliPqxdhBinaryCorrectStrictPlaced2 CliPqxdhElfCorrectStrictPlaced2)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (CliElfF3B2NeedLocksAssumptions
   MainOkCliF3OverB2NeedLocksPlacedAt MainOkCliF3PqB2NeedLocksPlacedAt
   cliPqxdhBinaryCorrectPlaced_of_f3B2NeedLocks'
   cliPqxdhBinaryCorrectStrictPlaced2_of_f3B2NeedLocks'
   cliPqxdhElfCorrectPlaced_of_f3B2NeedLocks'
   cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocks')
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv
  (mainOkCliExtOverB2NeedLocksPlacedAt_iff mainOkCliExtPqB2NeedLocksPlacedAt_iff)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4A.T2Strict2Bridge
  (hAlloc_of_cliPqxdhElfCorrectStrictPlaced2 not_cliReachesOOMPlaced_of_strict2)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookExactMemcpy)

/-! ## `ReadFileRuleEnvFixed cliIo.rd` ⊆ `BoundedReadFileEnv` -/

/-- Both arms of `ReadFileRuleEnvFixed cliIo.rd` satisfy `BoundedReadFileEnv`:
    the normal `ReadFileRuleEnv` arm via `boundedReadFileEnv_of_readFileRuleEnv_cliIo` and
    the 2 MiB over-cap read-and-free arm via `specCliIoReadSchedule_events_eq 9 2097152` +
    `FreeOnlyEvs.singleton 1 2097152`. -/
theorem boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo
    (files : FsFiles) (path : List (BitVec 8)) {evs : List AllocEvent}
    (h : ReadFileRuleEnvFixed cliIo.rd files path evs) :
    BoundedReadFileEnv evs := by
  rcases h with hPlain | ⟨_, _, hEvs⟩
  · exact boundedReadFileEnv_of_readFileRuleEnv_cliIo files path hPlain
  · rw [hEvs]
    change BoundedReadFileEnv
      (cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 2097152) ++ rustDeallocEvents 2097152 1)
    rw [specCliIoReadSchedule_events_eq 9 2097152]
    exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, ⟨2097152, rfl⟩, FreeOnlyEvs.singleton 1 2097152⟩))

/-! ## Ghost-hook and subroutine replay bundle (`F3FixedHookHyp`) -/

/-- Ghost-hook, subroutine-correctness, and Block-`617` replay hypotheses for `f3CliGhostHooksFixed` (including `fMemset` and `fMemcpy`). -/
structure F3FixedHookHyp
    (mpl mmpl : MultiPlacement)
    (CodeOk_ghost CodeOk_real : Memory → Prop)
    (libcAddr brkStart : BitVec 64)
    (keep : BitVec 64 → Bool)
    (InvMem : Memory → Prop)
    (P_real P_sub : Program)
    (T : F3GhostEntryTargets)
    (hookStack : Nat)
    (fMemset fMemcpy : Option (State → State)) : Prop where
  hPl_ls : libsignalSessionLib.Placeable mpl
  hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
    (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i)
  hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup
  hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk_ghost
  hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc
  hHookStack : extHookStack ≤ hookStack
  hMainStk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk
  hsvc_real : P_real.svc = Arm64.Syscall.standard
  hsvc_sub : P_sub.svc = Arm64.Syscall.standard
  hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none
  hsub_no : ∀ pc, P_sub.externAt? pc = none
  hPl_mng : mallocngLib.Placeable mmpl
  hKeepMallocng : ∀ a : BitVec 64,
    (mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true
  hAlloc : ∀ γ tp, subroutine_ok P_sub T.alloc
    (rustCliAllocBudgetSpecBase fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits false)
  hDealloc : ∀ γ tp, subroutine_ok P_sub T.dealloc
    (rustCliDeallocBudgetSpecBase fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits)
  hRealloc : ∀ γ tp, subroutine_ok P_sub T.realloc
    (rustCliReallocBudgetSpecBase fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits)
  hAllocZeroed : ∀ γ tp, subroutine_ok P_sub T.allocZeroed
    (rustCliAllocBudgetSpecBase fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits true)
  hStrClone : ∀ γ tp, subroutine_ok P_sub T.stringClone
    (stringCloneBudgetCondSpec fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits)
  hReadFileCond : ∀ γ tp, subroutine_ok P_sub T.readFile
    (readFileAnyBudgetCondSpec
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits extHookStack)
  hReadStdinCond : ∀ γ tp, subroutine_ok P_sub T.readStdin
    (readStdinBudgetCondSpec
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits extHookStack)
  hMemset : ∃ f, fMemset = some f ∧
    (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
    (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
    HookOk f memsetRegionSpec ∧
    HookOk f sessionMemsetRegionSpec ∧
    (∀ s : State, VmPreserved s (f s)) ∧
    (∀ s : State, (f s).fs = s.fs) ∧
    HookFsTraced IsFsC f
  hMemcpy : ∃ f, fMemcpy = some f ∧
    (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
    (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
    HookOk f memcpyRegionSpec ∧
    HookOk f sessionMemcpyRegionSpec ∧
    HookOk f framelessMemcpySpec ∧
    HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec ∧
    (∀ s : State, VmPreserved s (f s)) ∧
    (∀ s : State, (f s).fs = s.fs) ∧
    HookFsTraced IsFsC f
  hMemcpyExact : ∀ f, fMemcpy = some f → HookExactMemcpy f
  hMemsetAcp : ∀ f, fMemset = some f →
    ∀ s : State, (f s).sigActions = s.sigActions ∧ (f s).oracle = s.oracle
  hStubAlloc : StubReachesTarget P_real (libsignalSessionLib.resolve mpl lsRustAllocSymCli) T.alloc
  hStubDealloc : StubReachesTarget P_real (libsignalSessionLib.resolve mpl lsRustDeallocSymCli) T.dealloc
  hStubRealloc : StubReachesTarget P_real (libsignalSessionLib.resolve mpl lsRustReallocSymCli) T.realloc
  hStubAllocZeroed : StubReachesTarget P_real (libsignalSessionLib.resolve mpl lsRustAllocZeroedSymCli) T.allocZeroed
  hStubStrClone : StubReachesTarget P_real (libsignalSessionLib.resolve mpl lsStringCloneSym) T.stringClone
  hStubReadFile : StubReachesTarget P_real (libsignalSessionLib.resolve mpl lsReadFileSym) T.readFile
  hStubReadStdin : StubReachesTarget P_real (libsignalSessionLib.resolve mpl lsReadStdinSym) T.readStdin
  hShim : ∀ u : State,
    u.pc = libsignalSessionLib.resolve mpl lsRustNoAllocShimSymCli →
    u.status = .Running →
    ExecFrozen u.mem →
    InvMem u.mem →
    Steps P_real u (hookNoop u)
  hCode : ∀ m : Memory, CodeOk_real m → CodeOk_ghost m
  hGhostCL : ∀ (W : CliHooks) (m : Memory), CodeOk_ghost m →
    (cliProgExtPlacedAt mpl
      (fun W' => cliGhostExterns
        (@f3CliGhostHooksFixed (libsignalPlacementOf mpl hblk hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
        (cliExternsPlaced mmpl W')) 617 W).CodeLoaded m
  hFr0 : ∀ m : Memory, CodeOk_real m → ExecFrozen m
  hInv0 : ∀ m : Memory, CodeOk_real m → InvMem m
  hInvStable : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m'
  hInvCodeSub : ∀ m : Memory, ExecFrozen m → InvMem m → P_sub.CodeLoaded (stripExecOutside keep m)
  hRealNone : ∀ (W : CliHooks) (sym : String) (f : State → State),
    GhostSymActive
      (@f3CliGhostHooksFixed (libsignalPlacementOf mpl hblk hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy) sym f →
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
      (libsignalSessionLib.resolve mpl sym) = none
  hStepsReal : ∀ (W : CliHooks) (u v : State),
    Steps P_real u v → Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v
  hReplayMemset : ∀ (W : CliHooks) (i : Inputs) (s0 sf u : State) (f : State → State),
    let P_ghost := cliProgExtPlacedAt mpl
      (fun W' => cliGhostExterns
        (@f3CliGhostHooksFixed (libsignalPlacementOf mpl hblk hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
        (cliExternsPlaced mmpl W')) 617 W
    let P_real_W := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
    fMemset = some f →
    CodeOk_real s0.mem →
    s0.pc = mpl.base 617 →
    s0.fs = initFsState (cliProcessInputs i) →
    s0.trace = [] →
    Steps P_ghost s0 u →
    Steps P_ghost (f u) sf →
    (∀ msg, sf.status ≠ .Exception msg) →
    sf.status ≠ .Halted →
    u.pc = libsignalSessionLib.resolve mpl lsMemsetSym →
    u.status = .Running →
    (∀ msg, (f u).status ≠ .Exception msg) →
    u.mem.KeepsFrozen (f u).mem →
    ExecFrozen u.mem →
    keep (u.readReg64 .lr) = false →
    InvMem u.mem →
    FdsGe3Closed u.fs →
    Steps P_real_W u (f u) ∧ ExecFrozen (f u).mem ∧ FdsGe3Closed (f u).fs
  hReplayMemcpy : ∀ (W : CliHooks) (i : Inputs) (s0 sf u : State) (f : State → State),
    let P_ghost := cliProgExtPlacedAt mpl
      (fun W' => cliGhostExterns
        (@f3CliGhostHooksFixed (libsignalPlacementOf mpl hblk hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
        (cliExternsPlaced mmpl W')) 617 W
    let P_real_W := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
    fMemcpy = some f →
    CodeOk_real s0.mem →
    s0.pc = mpl.base 617 →
    s0.fs = initFsState (cliProcessInputs i) →
    s0.trace = [] →
    Steps P_ghost s0 u →
    Steps P_ghost (f u) sf →
    (∀ msg, sf.status ≠ .Exception msg) →
    sf.status ≠ .Halted →
    u.pc = libsignalSessionLib.resolve mpl lsMemcpySym →
    u.status = .Running →
    (∀ msg, (f u).status ≠ .Exception msg) →
    u.mem.KeepsFrozen (f u).mem →
    ExecFrozen u.mem →
    keep (u.readReg64 .lr) = false →
    InvMem u.mem →
    FdsGe3Closed u.fs →
    Steps P_real_W u (f u) ∧ ExecFrozen (f u).mem ∧ FdsGe3Closed (f u).fs
  hMallocngFds : ∀ (W : CliHooks) (i : Inputs) (s0 sf u : State) (f : State → State),
    let P_ghost := cliProgExtPlacedAt mpl
      (fun W' => cliGhostExterns
        (@f3CliGhostHooksFixed (libsignalPlacementOf mpl hblk hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
        (cliExternsPlaced mmpl W')) 617 W
    CodeOk_real s0.mem →
    s0.pc = mpl.base 617 →
    s0.fs = initFsState (cliProcessInputs i) →
    s0.trace = [] →
    Steps P_ghost s0 u →
    Steps P_ghost (f u) sf →
    (∀ msg, sf.status ≠ .Exception msg) →
    sf.status ≠ .Halted →
    u.status = .Running →
    (f = aesEncHookMallocng mmpl W.C.E ∨
     f = aesDecHookMallocng mmpl W.C.D ∨
     f = libcruxHmacHookMallocng mmpl W.C.F) →
    ExecFrozen u.mem →
    InvMem u.mem →
    FdsGe3Closed u.fs →
    FdsGe3Closed (f u).fs
  hSvcFds : ∀ (W : CliHooks) (i : Inputs) (s0 sf u : State),
    let P_ghost := cliProgExtPlacedAt mpl
      (fun W' => cliGhostExterns
        (@f3CliGhostHooksFixed (libsignalPlacementOf mpl hblk hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
        (cliExternsPlaced mmpl W')) 617 W
    CodeOk_real s0.mem →
    s0.pc = mpl.base 617 →
    s0.fs = initFsState (cliProcessInputs i) →
    s0.trace = [] →
    Steps P_ghost s0 u →
    Steps P_ghost (Arm64.Syscall.standard u) sf →
    (∀ msg, sf.status ≠ .Exception msg) →
    sf.status ≠ .Halted →
    u.status = .Running →
    P_ghost.externAt? u.pc = none →
    P_ghost.fetchMem u.mem u.pc = some (.system false 0#16) →
    ExecFrozen u.mem →
    InvMem u.mem →
    FdsGe3Closed u.fs →
    FdsGe3Closed (Arm64.Syscall.standard u).fs
  hLrCalls : ∀ (W : CliHooks) (i : Inputs) (s0 sf u : State),
    let P_ghost := cliProgExtPlacedAt mpl
      (fun W' => cliGhostExterns
        (@f3CliGhostHooksFixed (libsignalPlacementOf mpl hblk hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
        (cliExternsPlaced mmpl W')) 617 W
    let P_real_W := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
    CodeOk_real s0.mem →
    s0.pc = mpl.base 617 →
    s0.fs = initFsState (cliProcessInputs i) →
    s0.trace = [] →
    Steps P_ghost s0 u →
    Steps P_ghost u sf →
    (∀ msg, sf.status ≠ .Exception msg) →
    sf.status ≠ .Halted →
    u.status = .Running →
    P_ghost.externAt? u.pc ≠ P_real_W.externAt? u.pc →
    keep (u.readReg64 .lr) = false

/-! ## Ghost-externs `MainOkCliExt{Pq,Over}B2NeedLocksPlacedAt` -/

/-- Whole-program ghost-externs `MainOkCliExtPqB2NeedLocksPlacedAt` under `cliBudgetLimits`,
    `f3CliGhostHooksFixed`, `ReadFileRuleEnvFixed cliIo.rd`, and
    `mkBinaryKitRealCalleeEnvsFixed img (cliRunSemD2c_placed X W) X W`. -/
theorem mainOkCliExtPqB2NeedLocksPlacedAt_f3Fixed
    {mpl mmpl : MultiPlacement}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hKitFits : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
          (@realCliMainBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W i))
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns
        (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
        (cliExternsPlaced mmpl W))
      617 cliProcessInputs CodeOk_ghost libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_cliBudgetLimits_of_kitEnvFits_and_runTightOf
    HF.hblk HF.hext_nodup HF.hCI
    (fun _ => @f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
    (fun X W => @mkBinaryKitRealCalleeEnvsFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
      img (cliRunSemD2c_placed X W) X W)
    RunEnv HF.hlibc
    (fun _ γ tp =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl HF.hblk HF.hext_nodup
      cliGhostAllocHooks_f3CliGhostHooksFixed
        HF.hsvc_real HF.hsvc_sub HF.hreal_no HF.hsub_no HF.hPl_mng HF.hKeepMallocng
        γ tp
        (subroutine_ok_rustCliAllocBudget_of_base (HF.hAlloc γ tp))
        (subroutine_ok_rustCliDeallocBudget_of_base (HF.hDealloc γ tp))
        (subroutine_ok_rustCliReallocBudget_of_base (HF.hRealloc γ tp))
        HF.hMemset HF.hMemcpy HF.hMemcpyExact HF.hMemsetAcp)
    (fun W γ tp => @mainIoOfPlaced_f3CliGhostHooksFixed
      (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
      keep P_real P_sub T mmpl W brkStart cliBudgetLimits hookStack fMemset fMemcpy
      HF.hsvc_real HF.hsvc_sub HF.hreal_no HF.hsub_no HF.hPl_mng HF.hKeepMallocng
      HF.hHookStack HF.hReadFileCond HF.hReadStdinCond γ tp)
    (fun files path _ h => boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo files path h)
    HF.hMainStk
    hKitFits
    hRunSub
    hrun

/-- Overcap-arm ghost-externs `MainOkCliExtOverB2NeedLocksPlacedAt` under `cliBudgetLimits`,
    `f3CliGhostHooksFixed`, `ReadFileRuleEnvFixed cliIo.rd`, and
    `mkBinaryKitRealCalleeEnvsFixed img (cliRunSemD2c_placed X W) X W`. -/
theorem mainOkCliExtOverB2NeedLocksPlacedAt_f3Fixed
    {mpl mmpl : MultiPlacement}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hKitFits : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
          (@realCliMainBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W i))
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns
        (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
        (cliExternsPlaced mmpl W))
      617 cliProcessInputs CodeOk_ghost libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_cliBudgetLimits_of_kitEnvFits_and_runTightOf
    HF.hblk HF.hext_nodup HF.hCI
    (fun _ => @f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
    (fun X W => @mkBinaryKitRealCalleeEnvsFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
      img (cliRunSemD2c_placed X W) X W)
    RunEnv HF.hlibc
    (fun _ γ tp =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl HF.hblk HF.hext_nodup
      cliGhostAllocHooks_f3CliGhostHooksFixed
        HF.hsvc_real HF.hsvc_sub HF.hreal_no HF.hsub_no HF.hPl_mng HF.hKeepMallocng
        γ tp
        (subroutine_ok_rustCliAllocBudget_of_base (HF.hAlloc γ tp))
        (subroutine_ok_rustCliDeallocBudget_of_base (HF.hDealloc γ tp))
        (subroutine_ok_rustCliReallocBudget_of_base (HF.hRealloc γ tp))
        HF.hMemset HF.hMemcpy HF.hMemcpyExact HF.hMemsetAcp)
    (fun W γ tp => @mainIoOfPlaced_f3CliGhostHooksFixed
      (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
      keep P_real P_sub T mmpl W brkStart cliBudgetLimits hookStack fMemset fMemcpy
      HF.hsvc_real HF.hsvc_sub HF.hreal_no HF.hsub_no HF.hPl_mng HF.hKeepMallocng
      HF.hHookStack HF.hReadFileCond HF.hReadStdinCond γ tp)
    (fun files path _ h => boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo files path h)
    HF.hMainStk
    hKitFits
    hRunSub
    hrun

/-! ## Block-`617` ghost-to-real transfer and real-externs `MainOkCliF3{Pq,Over}` -/

private theorem findSome?_const_none {α β : Type} (xs : List α) (p : α → Bool) :
    (xs.findSome? fun x => if p x then (none : Option β) else none) = none := by
  induction xs with
  | nil => rfl
  | cons _ tl ih =>
    simp only [List.findSome?_cons, ite_self] at ih ⊢
    exact ih

private theorem findSome?_table_exists (tbl : List (String × Nat))
    {ext : String → Option (State → State)} (off : Nat) {f : State → State}
    (h : (tbl.findSome? fun (n, o) => if o == off then ext n else none) = some f) :
    ∃ sym : String, ext sym = some f := by
  induction tbl with
  | nil => simp at h
  | cons hd tl ih =>
    rcases hd with ⟨n, o⟩
    simp only [List.findSome?_cons] at h
    cases hoo : (o == off) with
    | false =>
      simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h
      exact ih h
    | true =>
      simp only [hoo, ↓reduceIte] at h
      cases he : ext n with
      | none => rw [he] at h; exact ih h
      | some g =>
        rw [he] at h
        injection h with hgf
        subst hgf
        exact ⟨n, he⟩

private theorem blockProgram_externAt?_some_exists
    {lib : Arm64.Obj.MultiPlacedLib} {mpl : MultiPlacement} {idx : Nat}
    {ext : String → Option (State → State)} {pc : BitVec 64} {f : State → State}
    (h : (lib.blockProgram mpl idx ext).externAt? pc = some f) :
    ∃ sym : String, ext sym = some f := by
  unfold Arm64.Obj.MultiPlacedLib.blockProgram Arm64.Obj.PlacedLib.program
    Program.externAt? Program.hookAtOff? at h
  dsimp only at h
  rw [findSome?_const_none, Option.or_none] at h
  exact findSome?_table_exists _ _ h

/-- Internal Block-`617` ghost-to-real transfer for `f3CliGhostHooksFixed` via
`Ghost617Transfer.block617TransferFixed_of_replaysOn`, the `f3*GhostHookFine_steps_of_call` replay lemmas, `hookNoop`, and `HF.hReplay{Memset,Memcpy}`. -/
private theorem block617TransferFixed_f3CliGhostHooksFixed
    {mpl mmpl : MultiPlacement}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy) :
    Block617TransferFixedHyp mpl mmpl
      (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
      CodeOk_ghost CodeOk_real libcAddr brkStart cliMainStk := by
  let : LibsignalPlacement := libsignalPlacementOf mpl HF.hblk HF.hext_nodup
  let ghFixed := @f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
    keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy
  refine block617TransferFixed_of_replaysOn keep InvMem FdsGe3Closed
    HF.hCode HF.hGhostCL HF.hFr0 HF.hInv0 HF.hInvStable
    (fun i => fdsGe3Closed_initFsState (cliProcessInputs i)) ?_
  intro W i s0 sf
  dsimp only
  intro hReal0 hpc0 hfs0 htr0 hsteps hnoex_sf hnhalt_sf
  refine ⟨?_, ?_, ?_⟩
  · intro pc f heg
    have h617 : 617 < libsignalSessionLib.blocks.length := by decide
    rcases blockProgram_cliGhostExterns_externAt?_cases h617 HF.hPl_ls ghFixed
        (cliExternsPlaced mmpl W) heg with
      her | ⟨sym, hAct, hpc_eq⟩
    · obtain ⟨sym, hsym⟩ := blockProgram_externAt?_some_exists her
      refine Or.inl ⟨her, fun u hpre hpost _ hrun _ hkf hfr ⟨hinv, hfs⟩ => ?_⟩
      refine ⟨cliExternsPlaced_preserves_execFrozen mmpl W hsym u hfr,
        HF.hInvStable u.mem _ hinv hkf, ?_⟩
      rcases cliExternsPlaced_nonMallocng_preserves_fdsGe3Closed mmpl W hsym with hpres | hmal
      · exact hpres u hfs
      · exact HF.hMallocngFds W i s0 sf u f hReal0 hpc0 hfs0 htr0 hpre hpost
          hnoex_sf hnhalt_sf hrun hmal hfr hinv hfs
    · refine Or.inr ⟨hpc_eq ▸ HF.hRealNone W sym f hAct,
        fun u hpre hpost hpc_u hrun hnoex hkf hfr hlr ⟨hinv, hfs⟩ => ?_⟩
      have hpc : u.pc = libsignalSessionLib.resolve mpl sym := hpc_u.trans hpc_eq
      have hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem) :=
        HF.hInvCodeSub u.mem hfr hinv
      suffices Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
          ExecFrozen (f u).mem ∧ FdsGe3Closed (f u).fs by
        exact ⟨this.1, this.2.1, HF.hInvStable u.mem _ hinv hkf, this.2.2⟩
      rcases hAct with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, hsc⟩ | ⟨rfl, h, hrf⟩ | ⟨rfl, h, hrs⟩ | ⟨rfl, hms⟩ | ⟨rfl, hmc⟩
      · dsimp only [ghFixed, f3CliGhostHooksFixed] at hnoex ⊢
        obtain ⟨hst, hfr', hfs_eq⟩ := f3AllocGhostHookFine_steps_of_call
          HF.hsvc_real HF.hsvc_sub HF.hreal_no HF.hsub_no HF.hStubAlloc HF.hKeepMallocng
          (fun γ tp => subroutine_ok_rustCliAllocBudget_of_base (HF.hAlloc γ tp))
          hpc hrun hnoex hfr hlr hCodeSub
        exact ⟨HF.hStepsReal W u _ hst, hfr', hfs_eq ▸ hfs⟩
      · dsimp only [ghFixed, f3CliGhostHooksFixed] at hnoex ⊢
        obtain ⟨hst, hfr', hfs_eq⟩ := f3DeallocGhostHookFine_steps_of_call
          HF.hsvc_real HF.hsvc_sub HF.hreal_no HF.hsub_no HF.hStubDealloc HF.hKeepMallocng
          (fun γ tp => subroutine_ok_rustCliDeallocBudget_of_base (HF.hDealloc γ tp))
          hpc hrun hnoex hfr hlr hCodeSub
        exact ⟨HF.hStepsReal W u _ hst, hfr', hfs_eq ▸ hfs⟩
      · dsimp only [ghFixed, f3CliGhostHooksFixed] at hnoex ⊢
        obtain ⟨hst, hfr', hfs_eq⟩ := f3ReallocGhostHookFine_steps_of_call
          HF.hsvc_real HF.hsvc_sub HF.hreal_no HF.hsub_no HF.hStubRealloc HF.hKeepMallocng
          (fun γ tp => subroutine_ok_rustCliReallocBudget_of_base (HF.hRealloc γ tp))
          hpc hrun hnoex hfr hlr hCodeSub
        exact ⟨HF.hStepsReal W u _ hst, hfr', hfs_eq ▸ hfs⟩
      · dsimp only [ghFixed, f3CliGhostHooksFixed] at hnoex ⊢
        obtain ⟨hst, hfr', hfs_eq⟩ := f3AllocZeroedGhostHookFine_steps_of_call
          HF.hsvc_real HF.hsvc_sub HF.hreal_no HF.hsub_no HF.hStubAllocZeroed HF.hKeepMallocng
          (fun γ tp => subroutine_ok_rustCliAllocBudget_of_base (HF.hAllocZeroed γ tp))
          hpc hrun hnoex hfr hlr hCodeSub
        exact ⟨HF.hStepsReal W u _ hst, hfr', hfs_eq ▸ hfs⟩
      · dsimp only [ghFixed, f3CliGhostHooksFixed]
        exact ⟨HF.hStepsReal W u _ (HF.hShim u hpc hrun hfr hinv), hfr, hfs⟩
      · dsimp only [ghFixed, f3CliGhostHooksFixed] at hsc
        injection hsc with hfeq
        subst hfeq
        obtain ⟨hst, hfr', hfs_eq⟩ := f3StringCloneGhostHookFine_steps_of_call
          HF.hsvc_real HF.hsvc_sub HF.hreal_no HF.hsub_no HF.hStubStrClone HF.hKeepMallocng
          HF.hStrClone hpc hrun hnoex hfr hlr hCodeSub
        exact ⟨HF.hStepsReal W u _ hst, hfr', hfs_eq ▸ hfs⟩
      · dsimp only [ghFixed, f3CliGhostHooksFixed] at hrf
        injection hrf with hsubeq
        have hfeq : f = f3ReadFileFixedGhostHookFine keep P_real P_sub T.readFile mmpl brkStart
            cliBudgetLimits hookStack := (congrArg Subtype.val hsubeq).symm
        subst hfeq
        obtain ⟨hst, hfr', hfs_eq⟩ := f3ReadFileFixedGhostHookFine_steps_of_call
          HF.hsvc_real HF.hsvc_sub HF.hreal_no HF.hsub_no HF.hStubReadFile HF.hKeepMallocng
          HF.hHookStack HF.hReadFileCond hpc hrun hnoex hfr hlr hfs hCodeSub
        exact ⟨HF.hStepsReal W u _ hst, hfr', hfs_eq ▸ hfs⟩
      · dsimp only [ghFixed, f3CliGhostHooksFixed] at hrs
        injection hrs with hsubeq
        have hfeq : f = f3ReadStdinGhostHookFine keep P_real P_sub T.readStdin mmpl brkStart
            cliBudgetLimits hookStack := (congrArg Subtype.val hsubeq).symm
        subst hfeq
        obtain ⟨hst, hfr', _, _, hfs_pres⟩ := f3ReadStdinGhostHookFine_steps_of_call
          HF.hsvc_real HF.hsvc_sub HF.hreal_no HF.hsub_no HF.hStubReadStdin HF.hKeepMallocng
          HF.hHookStack HF.hReadStdinCond hpc hrun hnoex hfr hlr hCodeSub
        exact ⟨HF.hStepsReal W u _ hst, hfr', hfs_pres hfs⟩
      · dsimp only [ghFixed, f3CliGhostHooksFixed] at hms
        exact HF.hReplayMemset W i s0 sf u f hms hReal0 hpc0 hfs0 htr0 hpre hpost
          hnoex_sf hnhalt_sf hpc hrun hnoex hkf hfr hlr hinv hfs
      · dsimp only [ghFixed, f3CliGhostHooksFixed] at hmc
        exact HF.hReplayMemcpy W i s0 sf u f hmc hReal0 hpc0 hfs0 htr0 hpre hpost
          hnoex_sf hnhalt_sf hpc hrun hnoex hkf hfr hlr hinv hfs
  · intro z hpre hrest hrun heg hfm hfr hinv hfs
    exact HF.hSvcFds W i s0 sf z hReal0 hpc0 hfs0 htr0 hpre hrest hnoex_sf hnhalt_sf
      hrun heg hfm hfr hinv hfs
  · intro z hpre hrest hrun hne
    exact HF.hLrCalls W i s0 sf z hReal0 hpc0 hfs0 htr0 hpre hrest hnoex_sf hnhalt_sf hrun hne

/-- Real-externs `MainOkCliF3PqB2NeedLocksPlacedAt` from `F3FixedHookHyp`, `hKitFits`, `hRunSub`,
    and `hrun` (with `Block617TransferFixedHyp` closed internally). -/
theorem mainOkCliF3Pq_of_f3Fixed
    {mpl mmpl : MultiPlacement}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hKitFits : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
          (@realCliMainBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W i))
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  mainOkCliF3Pq_of_block617TransferFixed
    (block617TransferFixed_f3CliGhostHooksFixed HF)
    ((mainOkCliExtPqB2NeedLocksPlacedAt_iff mpl mmpl
      (fun W => cliGhostExterns
        (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
        (cliExternsPlaced mmpl W))
      617 cliProcessInputs CodeOk_ghost libcAddr brkStart cliMainStk cliBudgetLimits).mp
      (mainOkCliExtPqB2NeedLocksPlacedAt_f3Fixed HF img RunEnv hKitFits hRunSub hrun))

/-- Real-externs `MainOkCliF3OverB2NeedLocksPlacedAt` from `F3FixedHookHyp`, `hKitFits`, `hRunSub`,
    and `hrun` (with `Block617TransferFixedHyp` closed internally). -/
theorem mainOkCliF3Over_of_f3Fixed
    {mpl mmpl : MultiPlacement}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hKitFits : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
          (@realCliMainBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W i))
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  mainOkCliF3Over_of_block617TransferFixed
    (block617TransferFixed_f3CliGhostHooksFixed HF)
    ((mainOkCliExtOverB2NeedLocksPlacedAt_iff mpl mmpl
      (fun W => cliGhostExterns
        (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
        (cliExternsPlaced mmpl W))
      617 cliProcessInputs CodeOk_ghost libcAddr brkStart cliMainStk cliBudgetLimits).mp
      (mainOkCliExtOverB2NeedLocksPlacedAt_f3Fixed HF img RunEnv hKitFits hRunSub hrun))

/-! ## Placed ELF correctness and `¬ CliReachesOOMPlaced` dischargers -/

/-- Strict placed ELF correctness (`CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf`) from `F3FixedHookHyp`, `hKitFits`, `hRunSub`, and `hrun`. -/
theorem cliPqxdhElfCorrectStrictPlaced2_of_f3Fixed
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {elf : ElfImage}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr cliMainStk CodeOk_real elf)
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr elf.brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (RunEnvPq RunEnvOver : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hKitFits : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
          (@realCliMainBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W i))
    (hRunSubPq : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnvPq X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hRunSubOver : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnvOver X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hrunPq : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (RunEnvPq X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (hrunOver : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (RunEnvOver X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf :=
  cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocks' H
    (mainOkCliF3Pq_of_f3Fixed HF img RunEnvPq hKitFits hRunSubPq hrunPq)
    (mainOkCliF3Over_of_f3Fixed HF img RunEnvOver hKitFits hRunSubOver hrunOver)

/-- Placed ELF correctness (`CliPqxdhElfCorrectPlaced mpl mmpl elf`) from `F3FixedHookHyp`, `hKitFits`, `hRunSub`, and `hrun`. -/
theorem cliPqxdhElfCorrectPlaced_of_f3Fixed
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {elf : ElfImage}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr cliMainStk CodeOk_real elf)
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr elf.brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (RunEnvPq RunEnvOver : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hKitFits : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
          (@realCliMainBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W i))
    (hRunSubPq : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnvPq X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hRunSubOver : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnvOver X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hrunPq : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (RunEnvPq X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (hrunOver : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (RunEnvOver X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectPlaced_of_f3B2NeedLocks' H
    (mainOkCliF3Pq_of_f3Fixed HF img RunEnvPq hKitFits hRunSubPq hrunPq)
    (mainOkCliF3Over_of_f3Fixed HF img RunEnvOver hKitFits hRunSubOver hrunOver)

/-- Discharges the OOM-freedom premise (`DEV-CLI12`) of `StatementPqElf.CliPqxdhElfSecurePlaced`:
`∀ i, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i` from
`FitsEnv fineCostModel cliBudgetLimits` and F3 ghost-to-real transfer. -/
theorem hAlloc_of_f3Fixed
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {elf : ElfImage}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr cliMainStk CodeOk_real elf)
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr elf.brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (RunEnvPq RunEnvOver : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hKitFits : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
          (@realCliMainBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W i))
    (hRunSubPq : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnvPq X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hRunSubOver : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnvOver X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hrunPq : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (RunEnvPq X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (hrunOver : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (RunEnvOver X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (W : CliHooks) :
    ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i :=
  hAlloc_of_cliPqxdhElfCorrectStrictPlaced2
    (cliPqxdhElfCorrectStrictPlaced2_of_f3Fixed H HF img RunEnvPq RunEnvOver
      hKitFits hRunSubPq hRunSubOver hrunPq hrunOver)
    W

/-- Pointwise `¬ CliReachesOOMPlaced mpl mmpl elf W i` companion to `hAlloc_of_f3Fixed`. -/
theorem not_cliReachesOOMPlaced_of_f3Fixed
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {elf : ElfImage}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr cliMainStk CodeOk_real elf)
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr elf.brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (RunEnvPq RunEnvOver : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hKitFits : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
          (@realCliMainBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W i))
    (hRunSubPq : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnvPq X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hRunSubOver : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnvOver X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hrunPq : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (RunEnvPq X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (hrunOver : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (RunEnvOver X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (W : CliHooks) (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    ¬ CliReachesOOMPlaced mpl mmpl elf W i :=
  not_cliReachesOOMPlaced_of_strict2
    (cliPqxdhElfCorrectStrictPlaced2_of_f3Fixed H HF img RunEnvPq RunEnvOver
      hKitFits hRunSubPq hRunSubOver hrunPq hrunOver)
    W i hi

/-- Binary-level `CliPqxdhBinaryCorrectStrictPlaced2 bytes` composer across all `LinkedAt` placements. -/
theorem cliPqxdhBinaryCorrectStrictPlaced2_of_f3Fixed
    {bytes : List (BitVec 8)} {elf : ElfImage}
    (hparse : ElfImage.parse bytes = .ok elf)
    (hAssump : ∀ mpl mmpl : MultiPlacement,
      libsignalSessionLib.LinkedAt bytes mpl →
      mallocngLib.LinkedAt bytes mmpl →
      ∃ (exitStk : Nat) (libcAddr : BitVec 64)
        (CodeOk_ghost CodeOk_real : Memory → Prop)
        (keep : BitVec 64 → Bool) (InvMem : Memory → Prop)
        (P_real P_sub : Program) (T : F3GhostEntryTargets) (hookStack : Nat)
        (fMemset fMemcpy : Option (State → State)),
        CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr cliMainStk CodeOk_real elf ∧
        MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk_real libcAddr elf.brkStart cliMainStk ∧
        MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk_real libcAddr elf.brkStart cliMainStk ∧
        F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr elf.brkStart
          keep InvMem P_real P_sub T hookStack fMemset fMemcpy) :
    CliPqxdhBinaryCorrectStrictPlaced2 bytes := by
  refine cliPqxdhBinaryCorrectStrictPlaced2_of_f3B2NeedLocks' hparse ?_
  intro mpl mmpl hls hmng
  obtain ⟨exitStk, libcAddr, _, CodeOk_real, _, _, _, _, _, _, _, _, H, hmain, hover, _⟩ :=
    hAssump mpl mmpl hls hmng
  exact ⟨exitStk, libcAddr, cliMainStk, CodeOk_real, H, hmain, hover⟩

/-- Binary-level `CliPqxdhBinaryCorrectPlaced bytes` composer across all `LinkedAt` placements. -/
theorem cliPqxdhBinaryCorrectPlaced_of_f3Fixed
    {bytes : List (BitVec 8)} {elf : ElfImage}
    (hparse : ElfImage.parse bytes = .ok elf)
    (hAssump : ∀ mpl mmpl : MultiPlacement,
      libsignalSessionLib.LinkedAt bytes mpl →
      mallocngLib.LinkedAt bytes mmpl →
      ∃ (exitStk : Nat) (libcAddr : BitVec 64)
        (CodeOk_ghost CodeOk_real : Memory → Prop)
        (keep : BitVec 64 → Bool) (InvMem : Memory → Prop)
        (P_real P_sub : Program) (T : F3GhostEntryTargets) (hookStack : Nat)
        (fMemset fMemcpy : Option (State → State)),
        CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr cliMainStk CodeOk_real elf ∧
        MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk_real libcAddr elf.brkStart cliMainStk ∧
        MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk_real libcAddr elf.brkStart cliMainStk ∧
        F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr elf.brkStart
          keep InvMem P_real P_sub T hookStack fMemset fMemcpy) :
    CliPqxdhBinaryCorrectPlaced bytes := by
  refine cliPqxdhBinaryCorrectPlaced_of_f3B2NeedLocks' hparse ?_
  intro mpl mmpl hls hmng
  obtain ⟨exitStk, libcAddr, _, CodeOk_real, _, _, _, _, _, _, _, _, H, hmain, hover, _⟩ :=
    hAssump mpl mmpl hls hmng
  exact ⟨exitStk, libcAddr, cliMainStk, CodeOk_real, H, hmain, hover⟩

/-! ## `CliKitEnvFits`-discharged `MainOk`, placed ELF, and `¬ CliReachesOOMPlaced` theorems -/

/-- Canonical-slice `RunEnv` predicate specialized to `ReadFileRuleEnvFixed cliIo.rd`,
    `realCliInitBinarySlotEnvFixed W`, `realCliDecPkBinaryWideSlotEnvFixed X W`,
    `PksmCanonSliceEnv x.bytes`, and `cliRunSemD2c_placed X W`. -/
abbrev canonSliceRunEnvFixed
    (mpl mmpl : MultiPlacement) (brkStart : BitVec 64)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    RunCall → List AllocEvent → Prop :=
  letI : CryptoVerification.LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget.RunEnv
    (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (binaryKitRunSlotEnvsFixed W (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
        (realCliInitBinarySlotEnvFixed W) (realCliDecPkBinaryWideSlotEnvFixed X W))
      (fun x => PksmCanonSliceEnv x.bytes)
      (cliRunSemD2c_placed X W))

/-- `CanonicalOrFallbackPksmEnv FallbackEnv` companion `RunEnv` predicate. -/
abbrev canonOrFallbackRunEnvFixed
    (FallbackEnv : PksmGhost → List AllocEvent → Prop)
    (mpl mmpl : MultiPlacement) (brkStart : BitVec 64)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    RunCall → List AllocEvent → Prop :=
  letI : CryptoVerification.LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget.RunEnv
    (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (binaryKitRunSlotEnvsFixed W (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
        (realCliInitBinarySlotEnvFixed W) (realCliDecPkBinaryWideSlotEnvFixed X W))
      (CanonicalOrFallbackPksmEnv FallbackEnv)
      (cliRunSemD2c_placed X W))

/-- Ghost-externs `MainOkCliExtPqB2NeedLocksPlacedAt` with `hKitFits` discharged via
    `CliKitEnvFits.realCliMainBinaryKitEnvOfFixed_fitsEnv_cliBudgetLimits`. -/
theorem mainOkCliExtPqB2NeedLocksPlacedAt_of_cliKitEnvFits
    {mpl mmpl : MultiPlacement}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns
        (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
        (cliExternsPlaced mmpl W))
      617 cliProcessInputs CodeOk_ghost libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtPqB2NeedLocksPlacedAt_f3Fixed HF img RunEnv
    (fun _ X W i hi =>
      @realCliMainBinaryKitEnvOfFixed_fitsEnv_cliBudgetLimits
        (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
        img (cliRunSemD2c_placed X W) X W i hi)
    hRunSub hrun

/-- Ghost-externs `MainOkCliExtOverB2NeedLocksPlacedAt` with `hKitFits` discharged via
    `CliKitEnvFits.realCliMainBinaryKitEnvOfFixed_fitsEnv_cliBudgetLimits`. -/
theorem mainOkCliExtOverB2NeedLocksPlacedAt_of_cliKitEnvFits
    {mpl mmpl : MultiPlacement}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns
        (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
        (cliExternsPlaced mmpl W))
      617 cliProcessInputs CodeOk_ghost libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtOverB2NeedLocksPlacedAt_f3Fixed HF img RunEnv
    (fun _ X W i hi =>
      @realCliMainBinaryKitEnvOfFixed_fitsEnv_cliBudgetLimits
        (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
        img (cliRunSemD2c_placed X W) X W i hi)
    hRunSub hrun

/-- Real-externs `MainOkCliF3PqB2NeedLocksPlacedAt` with `hKitFits` discharged via
    `CliKitEnvFits.realCliMainBinaryKitEnvOfFixed_fitsEnv_cliBudgetLimits` and
    `Block617TransferFixedHyp` closed internally. -/
theorem mainOkCliF3Pq_of_cliKitEnvFits
    {mpl mmpl : MultiPlacement}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  mainOkCliF3Pq_of_f3Fixed HF img RunEnv
    (fun _ X W i hi =>
      @realCliMainBinaryKitEnvOfFixed_fitsEnv_cliBudgetLimits
        (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
        img (cliRunSemD2c_placed X W) X W i hi)
    hRunSub hrun

/-- Real-externs `MainOkCliF3OverB2NeedLocksPlacedAt` with `hKitFits` discharged via
    `CliKitEnvFits.realCliMainBinaryKitEnvOfFixed_fitsEnv_cliBudgetLimits` and
    `Block617TransferFixedHyp` closed internally. -/
theorem mainOkCliF3Over_of_cliKitEnvFits
    {mpl mmpl : MultiPlacement}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  mainOkCliF3Over_of_f3Fixed HF img RunEnv
    (fun _ X W i hi =>
      @realCliMainBinaryKitEnvOfFixed_fitsEnv_cliBudgetLimits
        (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
        img (cliRunSemD2c_placed X W) X W i hi)
    hRunSub hrun

/-- `canonSliceRunEnvFixed` specialization of `mainOkCliF3Pq_of_cliKitEnvFits` discharging both
    `hKitFits` and `hRunSub` automatically (taking only `HF`, `img`, and `hrun`). -/
theorem mainOkCliF3Pq_of_cliKitEnvFits_canonSlice
    {mpl mmpl : MultiPlacement}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (canonSliceRunEnvFixed mpl mmpl brkStart HF.hblk HF.hext_nodup X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  mainOkCliF3Pq_of_cliKitEnvFits HF img
    (canonSliceRunEnvFixed mpl mmpl brkStart HF.hblk HF.hext_nodup)
    (fun _ X W γ tp g hi hparse hin _ evs hevs =>
      @runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed_canonSlice
        (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _
        img (cliRunSemD2c_placed X W) X W
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
        g hi hparse hin rfl rfl evs hevs)
    hrun

/-- `canonSliceRunEnvFixed` specialization of `mainOkCliF3Over_of_cliKitEnvFits` discharging both
    `hKitFits` and `hRunSub` automatically (taking only `HF`, `img`, and `hrun`). -/
theorem mainOkCliF3Over_of_cliKitEnvFits_canonSlice
    {mpl mmpl : MultiPlacement}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (canonSliceRunEnvFixed mpl mmpl brkStart HF.hblk HF.hext_nodup X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  mainOkCliF3Over_of_cliKitEnvFits HF img
    (canonSliceRunEnvFixed mpl mmpl brkStart HF.hblk HF.hext_nodup)
    (fun _ X W γ tp g hi hparse hin _ evs hevs =>
      @runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed_canonSlice
        (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _
        img (cliRunSemD2c_placed X W) X W
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
        g hi hparse hin rfl rfl evs hevs)
    hrun

/-- `canonOrFallbackRunEnvFixed` specialization of `mainOkCliF3Pq_of_cliKitEnvFits`. -/
theorem mainOkCliF3Pq_of_cliKitEnvFits_canonOrFallback
    {mpl mmpl : MultiPlacement}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (FallbackEnv : PksmGhost → List AllocEvent → Prop)
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (canonOrFallbackRunEnvFixed FallbackEnv mpl mmpl brkStart HF.hblk HF.hext_nodup X W γ tp)
            uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  mainOkCliF3Pq_of_cliKitEnvFits HF img
    (canonOrFallbackRunEnvFixed FallbackEnv mpl mmpl brkStart HF.hblk HF.hext_nodup)
    (fun _ X W γ tp g hi hparse hin _ evs hevs =>
      @runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed_canonOrFallback
        (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ FallbackEnv
        img (cliRunSemD2c_placed X W) X W
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
        g hi hparse hin rfl rfl evs hevs)
    hrun

/-- `canonOrFallbackRunEnvFixed` specialization of `mainOkCliF3Over_of_cliKitEnvFits`. -/
theorem mainOkCliF3Over_of_cliKitEnvFits_canonOrFallback
    {mpl mmpl : MultiPlacement}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (FallbackEnv : PksmGhost → List AllocEvent → Prop)
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (canonOrFallbackRunEnvFixed FallbackEnv mpl mmpl brkStart HF.hblk HF.hext_nodup X W γ tp)
            uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  mainOkCliF3Over_of_cliKitEnvFits HF img
    (canonOrFallbackRunEnvFixed FallbackEnv mpl mmpl brkStart HF.hblk HF.hext_nodup)
    (fun _ X W γ tp g hi hparse hin _ evs hevs =>
      @runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed_canonOrFallback
        (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ FallbackEnv
        img (cliRunSemD2c_placed X W) X W
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
        g hi hparse hin rfl rfl evs hevs)
    hrun

/-- Strict placed ELF correctness (`CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf`) with `hKitFits`
    discharged via `CliKitEnvFits.realCliMainBinaryKitEnvOfFixed_fitsEnv_cliBudgetLimits`. -/
theorem cliPqxdhElfCorrectStrictPlaced2_of_cliKitEnvFits
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {elf : ElfImage}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr cliMainStk CodeOk_real elf)
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr elf.brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (RunEnvPq RunEnvOver : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hRunSubPq : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnvPq X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hRunSubOver : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnvOver X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hrunPq : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (RunEnvPq X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (hrunOver : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (RunEnvOver X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf :=
  cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocks' H
    (mainOkCliF3Pq_of_cliKitEnvFits HF img RunEnvPq hRunSubPq hrunPq)
    (mainOkCliF3Over_of_cliKitEnvFits HF img RunEnvOver hRunSubOver hrunOver)

/-- `canonSliceRunEnvFixed` specialization of `cliPqxdhElfCorrectStrictPlaced2_of_cliKitEnvFits`
    taking a single Block-`579` `hrun` hypothesis for both arms. -/
theorem cliPqxdhElfCorrectStrictPlaced2_of_cliKitEnvFits_canonSlice
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {elf : ElfImage}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr cliMainStk CodeOk_real elf)
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr elf.brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (canonSliceRunEnvFixed mpl mmpl elf.brkStart HF.hblk HF.hext_nodup X W γ tp)
            uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf :=
  cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocks' H
    (mainOkCliF3Pq_of_cliKitEnvFits_canonSlice HF img hrun)
    (mainOkCliF3Over_of_cliKitEnvFits_canonSlice HF img hrun)

/-- Placed ELF correctness (`CliPqxdhElfCorrectPlaced mpl mmpl elf`) with `hKitFits` discharged via `CliKitEnvFits`. -/
theorem cliPqxdhElfCorrectPlaced_of_cliKitEnvFits
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {elf : ElfImage}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr cliMainStk CodeOk_real elf)
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr elf.brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (RunEnvPq RunEnvOver : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hRunSubPq : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnvPq X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hRunSubOver : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnvOver X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hrunPq : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (RunEnvPq X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (hrunOver : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (RunEnvOver X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectPlaced_of_f3B2NeedLocks' H
    (mainOkCliF3Pq_of_cliKitEnvFits HF img RunEnvPq hRunSubPq hrunPq)
    (mainOkCliF3Over_of_cliKitEnvFits HF img RunEnvOver hRunSubOver hrunOver)

theorem cliPqxdhElfCorrectPlaced_of_cliKitEnvFits_canonSlice
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {elf : ElfImage}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr cliMainStk CodeOk_real elf)
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr elf.brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (canonSliceRunEnvFixed mpl mmpl elf.brkStart HF.hblk HF.hext_nodup X W γ tp)
            uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectPlaced_of_f3B2NeedLocks' H
    (mainOkCliF3Pq_of_cliKitEnvFits_canonSlice HF img hrun)
    (mainOkCliF3Over_of_cliKitEnvFits_canonSlice HF img hrun)

/-- `CliKitEnvFits`-discharged OOM-freedom theorem (`DEV-CLI12`, `StatementPqElf.CliPqxdhElfSecurePlaced`):
proves `∀ i, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i` with `hKitFits`
and `Block617TransferFixedHyp` discharged internally. -/
theorem hAlloc_of_cliKitEnvFits
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {elf : ElfImage}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr cliMainStk CodeOk_real elf)
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr elf.brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (RunEnvPq RunEnvOver : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hRunSubPq : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnvPq X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hRunSubOver : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnvOver X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hrunPq : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (RunEnvPq X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (hrunOver : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (RunEnvOver X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (W : CliHooks) :
    ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i :=
  hAlloc_of_cliPqxdhElfCorrectStrictPlaced2
    (cliPqxdhElfCorrectStrictPlaced2_of_cliKitEnvFits H HF img RunEnvPq RunEnvOver
      hRunSubPq hRunSubOver hrunPq hrunOver)
    W

/-- `canonSliceRunEnvFixed` specialization of `hAlloc_of_cliKitEnvFits` taking only `H`, `HF`,
    `img`, and `hrun`. -/
theorem hAlloc_of_cliKitEnvFits_canonSlice
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {elf : ElfImage}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr cliMainStk CodeOk_real elf)
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr elf.brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (canonSliceRunEnvFixed mpl mmpl elf.brkStart HF.hblk HF.hext_nodup X W γ tp)
            uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (W : CliHooks) :
    ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i :=
  hAlloc_of_cliPqxdhElfCorrectStrictPlaced2
    (cliPqxdhElfCorrectStrictPlaced2_of_cliKitEnvFits_canonSlice H HF img hrun)
    W

theorem not_cliReachesOOMPlaced_of_cliKitEnvFits
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {elf : ElfImage}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr cliMainStk CodeOk_real elf)
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr elf.brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (RunEnvPq RunEnvOver : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hRunSubPq : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnvPq X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hRunSubOver : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnvOver X W γ tp g evs →
          @realCliRunBinaryKitEnvOfFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            img (cliRunSemD2c_placed X W) X W g evs)
    (hrunPq : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (RunEnvPq X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (hrunOver : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (RunEnvOver X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (W : CliHooks) (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    ¬ CliReachesOOMPlaced mpl mmpl elf W i :=
  not_cliReachesOOMPlaced_of_strict2
    (cliPqxdhElfCorrectStrictPlaced2_of_cliKitEnvFits H HF img RunEnvPq RunEnvOver
      hRunSubPq hRunSubOver hrunPq hrunOver)
    W i hi

theorem not_cliReachesOOMPlaced_of_cliKitEnvFits_canonSlice
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {elf : ElfImage}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop}
    {P_real P_sub : Program} {T : F3GhostEntryTargets} {hookStack : Nat}
    {fMemset fMemcpy : Option (State → State)}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr cliMainStk CodeOk_real elf)
    (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr elf.brkStart
      keep InvMem P_real P_sub T hookStack fMemset fMemcpy)
    (img : Image)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (cliGhostExterns
              (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits hookStack fMemset fMemcpy)
              (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
            (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (canonSliceRunEnvFixed mpl mmpl elf.brkStart HF.hblk HF.hext_nodup X W γ tp)
            uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (W : CliHooks) (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    ¬ CliReachesOOMPlaced mpl mmpl elf W i :=
  not_cliReachesOOMPlaced_of_strict2
    (cliPqxdhElfCorrectStrictPlaced2_of_cliKitEnvFits_canonSlice H HF img hrun)
    W i hi

/-- Binary-level `CliPqxdhBinaryCorrectStrictPlaced2 bytes` composer with `hKitFits` discharged via `CliKitEnvFits`. -/
theorem cliPqxdhBinaryCorrectStrictPlaced2_of_cliKitEnvFits_canonSlice
    {bytes : List (BitVec 8)} {elf : ElfImage}
    (img : Image)
    (hparse : ElfImage.parse bytes = .ok elf)
    (hAssump : ∀ mpl mmpl : MultiPlacement,
      libsignalSessionLib.LinkedAt bytes mpl →
      mallocngLib.LinkedAt bytes mmpl →
      ∃ (exitStk : Nat) (libcAddr : BitVec 64)
        (CodeOk_ghost CodeOk_real : Memory → Prop)
        (keep : BitVec 64 → Bool) (InvMem : Memory → Prop)
        (P_real P_sub : Program) (T : F3GhostEntryTargets) (hookStack : Nat)
        (fMemset fMemcpy : Option (State → State))
        (_H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr cliMainStk CodeOk_real elf)
        (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr elf.brkStart
          keep InvMem P_real P_sub T hookStack fMemset fMemcpy),
        mpl.base 547 ≠ 0#64 →
          ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
            @subroutine_ok _
              (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
                (cliGhostExterns
                  (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits
                    hookStack fMemset fMemcpy)
                  (cliExternsPlaced mmpl W)))
              (mpl.base 579)
              (@runSpecTightPlaced
                (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
                (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
                (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
                (canonSliceRunEnvFixed mpl mmpl elf.brkStart HF.hblk HF.hext_nodup X W γ tp)
                uuidTryParse
                (runRel (cliRunSemD2c_placed X W))
                cliWrOk cliResStack)) :
    CliPqxdhBinaryCorrectStrictPlaced2 bytes := by
  refine cliPqxdhBinaryCorrectStrictPlaced2_of_f3B2NeedLocks' hparse ?_
  intro mpl mmpl hls hmng
  obtain ⟨exitStk, libcAddr, _, CodeOk_real, _, _, _, _, _, _, _, _, H, HF, hrun⟩ :=
    hAssump mpl mmpl hls hmng
  exact ⟨exitStk, libcAddr, cliMainStk, CodeOk_real, H,
    mainOkCliF3Pq_of_cliKitEnvFits_canonSlice HF img hrun,
    mainOkCliF3Over_of_cliKitEnvFits_canonSlice HF img hrun⟩

/-- Binary-level `CliPqxdhBinaryCorrectPlaced bytes` composer with `hKitFits` discharged via `CliKitEnvFits`. -/
theorem cliPqxdhBinaryCorrectPlaced_of_cliKitEnvFits_canonSlice
    {bytes : List (BitVec 8)} {elf : ElfImage}
    (img : Image)
    (hparse : ElfImage.parse bytes = .ok elf)
    (hAssump : ∀ mpl mmpl : MultiPlacement,
      libsignalSessionLib.LinkedAt bytes mpl →
      mallocngLib.LinkedAt bytes mmpl →
      ∃ (exitStk : Nat) (libcAddr : BitVec 64)
        (CodeOk_ghost CodeOk_real : Memory → Prop)
        (keep : BitVec 64 → Bool) (InvMem : Memory → Prop)
        (P_real P_sub : Program) (T : F3GhostEntryTargets) (hookStack : Nat)
        (fMemset fMemcpy : Option (State → State))
        (_H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr cliMainStk CodeOk_real elf)
        (HF : F3FixedHookHyp mpl mmpl CodeOk_ghost CodeOk_real libcAddr elf.brkStart
          keep InvMem P_real P_sub T hookStack fMemset fMemcpy),
        mpl.base 547 ≠ 0#64 →
          ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
            @subroutine_ok _
              (@mProgPlaced (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
                (cliGhostExterns
                  (@f3CliGhostHooksFixed (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) keep P_real P_sub T mmpl elf.brkStart cliBudgetLimits
                    hookStack fMemset fMemcpy)
                  (cliExternsPlaced mmpl W)))
              (mpl.base 579)
              (@runSpecTightPlaced
                (libsignalPlacementOf mpl HF.hblk HF.hext_nodup)
                (libsignalPlacementOf mpl HF.hblk HF.hext_nodup) _ CodeOk_ghost
                (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
                (canonSliceRunEnvFixed mpl mmpl elf.brkStart HF.hblk HF.hext_nodup X W γ tp)
                uuidTryParse
                (runRel (cliRunSemD2c_placed X W))
                cliWrOk cliResStack)) :
    CliPqxdhBinaryCorrectPlaced bytes := by
  refine cliPqxdhBinaryCorrectPlaced_of_f3B2NeedLocks' hparse ?_
  intro mpl mmpl hls hmng
  obtain ⟨exitStk, libcAddr, _, CodeOk_real, _, _, _, _, _, _, _, _, H, HF, hrun⟩ :=
    hAssump mpl mmpl hls hmng
  exact ⟨exitStk, libcAddr, cliMainStk, CodeOk_real, H,
    mainOkCliF3Pq_of_cliKitEnvFits_canonSlice HF img hrun,
    mainOkCliF3Over_of_cliKitEnvFits_canonSlice HF img hrun⟩

end LibsignalBinary.Proofs.PeakBudget.CliF3MainOkBridge
