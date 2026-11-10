/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliElf
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2ExecFrozenWire
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Branch2
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemcpy
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KNarrowR1
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2StepsLiftR2
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfStockStubResolve

/-!
# K-Pinned Ghost-to-Real Transfer and 6-Arm `MainOk` Assembly

**Checked by Lean.**

Assembles Route-2 `Block617TransferFixedHyp`, the 11-field witness carrier `h2asm_F3CliElfGhostWitnessK`,
and all six `MainOk` arms into `CliPqBinaryV2OomF3BytesPlaced cliElfBytes` at the K-pinned ghost
hook bundle `h2k_ghFixedK mpl mmpl`:
- Discharges `lsRustNoAllocShimSymCli` via `h2b2_shim_branch2`, excludes `lsStringCloneSym` from
  Block-`617` externs, and factors the remaining six hooks (`alloc`, `dealloc`, `realloc`,
  `allocZeroed`, `readFile`, `readStdin`) through `h2asm_Branch2HookReplaysK`.
- Instantiates `Block617TransferFixedHyp` via `keep := fun _ => false` and `PredFs := fun _ => True`
  using `ElfSlicesPqOomH2KHooks` and `hole_gap3_f3CodeOk_to_libsignalFrozen`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm

open Arm64 (GhostName HookSat Memory Program SepProp Spec State Steps SubroutineOutcome subroutine_ok)
open Arm64.Obj (MultiPlacement)
open ProofLib (stripExecOutside)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement mallocngBlockProg)
open CryptoGames.LibsignalSession (GhostState)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification
  (LibsignalFrozen LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns)
open CryptoVerification.E2E
  (PEParams PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives wirePrekey)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession
  (CliHooks Inputs OutcomeMatchesModelExceptPath PqParty PqSessionMatches PqxdhPartyInSpecDomain
   cliElfBytes cliElfImage cliElf_parse cliExternsPlaced cliProcessInputs libsignalSessionLib
   lsMemcpySym lsMemsetSym lsReadFileSym lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli
   lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym observe
   partyAddress pqRecvInputs pqRecvPrekeyModel pqxdhExpectedOutcome sessionFile)
open CryptoVerification.SignalSession.Cli (CommitOk MainResult RunAnswer)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliMainStk cliResStack cliRunBudgets cliWrOk mainFrameSize)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooksFs cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ActiveRealRun ExecFrozen SpecPreservesFsTrace SpecStripSInvariant)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (D3NoMatchSessionFile)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
  (MainInitSemF3G MainOkOverD3F3G MainOkPathBD3F3G MainOkUntypedD3F3G MainOkValidMatchD3F3G)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (cliRunSemPathB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (pqD3ScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (cliRunSemD3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (ExternNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (MainOkCliExtPqB2NeedLocksPlacedAt b2MainSpecTightNeedLocksFineAt cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
  (F3MemsetMemcpyEntryLrFalse MainOkCliF3PqB2NeedLocksPlacedAtG
   mainOkCliF3PqG_of_block617TransferFixedG)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (ActiveF3CallPre f3LinkedCallHook)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (GhostSymActive)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
  (Block617TransferFixedHypG)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode
  (mallocngBlockProg20_externAt_none mallocngBlockProg20_hasWords masterMemcpySpec
   subroutine_ok_masterMemcpy_of_hasWords)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost
  (keepCoversBlk20_keepMemcpyBlk20 keepMemcpyBlk20 masterMemcpy_outcome_setPC
   masterMemcpy_pre_setPC specPreservesFsTrace_masterMemcpy specStripSInvariant_masterMemcpy)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn
  (codeLoaded_stripExecOutside_blk20 mallocngBlockProg20_svc_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode
  (mallocngBlockProg21_externAt_none mallocngBlockProg21_hasWords masterMemsetSpec
   subroutine_ok_masterMemset_of_hasWords)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost
  (keepCoversBlk21_keepMemsetBlk21 keepMemsetBlk21 masterMemset_outcome_setPC
   masterMemset_pre_setPC specPreservesFsTrace_masterMemset specStripSInvariant_masterMemset)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
  (activeF3CallPre_const_iff emptyStdProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays
  (codeLoaded_stripExecOutside_blk21 mallocngBlockProg21_svc_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
  (f3EmptyMemcpyGhostHookNarrow f3EmptyMemsetGhostHookNarrow)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced (ReadStdinBoundedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
  (InitRunSemOk initD3ScopedRun)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv F3CodeOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Branch2
  (h2b2_realW_externAt_none_of_ghostSymActive h2b2_shim_branch2 h2b2_stub_alloc
   h2b2_stub_allocZeroed h2b2_stub_dealloc h2b2_stub_readFile h2b2_stub_readStdin
   h2b2_stub_realloc)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2ExecFrozenWire
  (h2ef_block617TransferFixedG_of_steps_to_stepsAll_codeOnly
   h2ef_block617TransferFixedG_replaysOn_false_codeOnly)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_StepsVisitedIn h2fsgen_real_subroutine_run_visitedIn_of_stripS h2fsgen_stepsUntil_det)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
  (h2k_CliGhostAllocHooksK h2k_CliGhostSpqrAllocHooksK h2k_CliRunHooksBundleK h2k_MainIoOfPlacedK
   h2k_fds_of_noException h2k_ghFixedK h2k_hole2_hFsK h2k_hole2_hGSpqrK h2k_hole2_hHooksBundleK
   h2k_hole2_hReadSatK h2k_hole2_hghNoAllocK h2k_hole2_hioOfK
   h2k_keepSubLr_false_of_noException h2k_readFileFixedGhostHookFineSubK h2k_readFileSpecK
   h2k_readStdinGhostHookFineSubK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemcpy
  (h2k_ghFixedK_blk20TrapHook h2k_keepSub_covers_blk20)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset
  (h2k_ghFixedK_blk21TrapHook h2k_keepSub_covers_blk21)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KNarrowR1
  (h2k_ghFixedK_blk20_ext_trap h2k_ghFixedK_blk21_ext_trap)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2StepsLiftR2
  (h2sl_steps_realW_of_visitedIn_keepSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
  (CliPqBinaryV2OomF3BytesPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG
  (cliElf_f3B2NeedLocksAssumptionsG cliPqBinaryV2OomF3BytesPlaced_cliElf_of_mainG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_emptyProg hole2_hMainStk hole2_hPl_mng hole2_hblk hole2_hext_nodup hole2_hookStack
   hole2_keepSub hole2_targets hole_gap3_f3CodeOk_to_libsignalFrozen)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfStockStubResolve
  (h2b2_stockResolve_memcpy_eq_base h2b2_stockResolve_memset_eq_base)

/-! ## Per-Hook Replay Bundles and 8-Way `GhostSymActive` Dispatcher -/

/-- Concrete `State → State` function for `lsReadFileSym` in `h2k_ghFixedK mpl mmpl`. -/
noncomputable abbrev h2asm_readFileHookK (mpl mmpl : MultiPlacement) : State → State :=
  (h2k_readFileFixedGhostHookFineSubK hole2_keepSub hole2_emptyProg f3TrialRxProg
    (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack).1

/-- Concrete `State → State` function for `lsReadStdinSym` in `h2k_ghFixedK mpl mmpl`. -/
noncomputable abbrev h2asm_readStdinHookK [LibsignalPlacement] (mpl mmpl : MultiPlacement) : State → State :=
  (h2k_readStdinGhostHookFineSubK hole2_keepSub hole2_emptyProg f3TrialRxProg
    (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack).1

/-- 6-field per-hook replay bundle at `h2k_ghFixedK mpl mmpl` (`alloc`, `dealloc`, `realloc`,
`allocZeroed`, `readFile`, `readStdin`). -/
structure h2asm_Branch2HookReplaysK [LibsignalPlacement] (mpl mmpl : MultiPlacement) : Prop where
  alloc :
    ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsRustAllocSymCli →
      u.status = .Running →
      (∀ msg, ((h2k_ghFixedK mpl mmpl).alloc u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen ((h2k_ghFixedK mpl mmpl).alloc u).mem →
      ExecFrozen u.mem →
      hole2_keepSub (u.readReg64 .lr) = false →
      F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        ((h2k_ghFixedK mpl mmpl).alloc u)
  dealloc :
    ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsRustDeallocSymCli →
      u.status = .Running →
      (∀ msg, ((h2k_ghFixedK mpl mmpl).dealloc u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen ((h2k_ghFixedK mpl mmpl).dealloc u).mem →
      ExecFrozen u.mem →
      hole2_keepSub (u.readReg64 .lr) = false →
      F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        ((h2k_ghFixedK mpl mmpl).dealloc u)
  realloc :
    ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsRustReallocSymCli →
      u.status = .Running →
      (∀ msg, ((h2k_ghFixedK mpl mmpl).realloc u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen ((h2k_ghFixedK mpl mmpl).realloc u).mem →
      ExecFrozen u.mem →
      hole2_keepSub (u.readReg64 .lr) = false →
      F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        ((h2k_ghFixedK mpl mmpl).realloc u)
  allocZeroed :
    ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsRustAllocZeroedSymCli →
      u.status = .Running →
      (∀ msg, ((h2k_ghFixedK mpl mmpl).allocZeroed u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen ((h2k_ghFixedK mpl mmpl).allocZeroed u).mem →
      ExecFrozen u.mem →
      hole2_keepSub (u.readReg64 .lr) = false →
      F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        ((h2k_ghFixedK mpl mmpl).allocZeroed u)
  readFile :
    ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsReadFileSym →
      u.status = .Running →
      (∀ msg, (h2asm_readFileHookK mpl mmpl u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (h2asm_readFileHookK mpl mmpl u).mem →
      ExecFrozen u.mem →
      hole2_keepSub (u.readReg64 .lr) = false →
      F3CodeInv mpl mmpl u.mem →
      FdsGe3Closed u.fs →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        (h2asm_readFileHookK mpl mmpl u)
  readStdin :
    ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsReadStdinSym →
      u.status = .Running →
      (∀ msg, (h2asm_readStdinHookK mpl mmpl u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (h2asm_readStdinHookK mpl mmpl u).mem →
      ExecFrozen u.mem →
      hole2_keepSub (u.readReg64 .lr) = false →
      F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        (h2asm_readStdinHookK mpl mmpl u)

/-- Post-stub target-entry replay bundle starting at `u.setPC (hole2_targets mpl).<hook>`. -/
structure h2asm_Branch2TargetReplaysK [LibsignalPlacement] (mpl mmpl : MultiPlacement) : Prop where
  alloc :
    ∀ (W : CliHooks) (u : State),
      u.status = .Running →
      (∀ msg, ((h2k_ghFixedK mpl mmpl).alloc u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen ((h2k_ghFixedK mpl mmpl).alloc u).mem →
      ExecFrozen u.mem →
      hole2_keepSub (u.readReg64 .lr) = false →
      F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC (hole2_targets mpl).alloc) ((h2k_ghFixedK mpl mmpl).alloc u)
  dealloc :
    ∀ (W : CliHooks) (u : State),
      u.status = .Running →
      (∀ msg, ((h2k_ghFixedK mpl mmpl).dealloc u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen ((h2k_ghFixedK mpl mmpl).dealloc u).mem →
      ExecFrozen u.mem →
      hole2_keepSub (u.readReg64 .lr) = false →
      F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC (hole2_targets mpl).dealloc) ((h2k_ghFixedK mpl mmpl).dealloc u)
  realloc :
    ∀ (W : CliHooks) (u : State),
      u.status = .Running →
      (∀ msg, ((h2k_ghFixedK mpl mmpl).realloc u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen ((h2k_ghFixedK mpl mmpl).realloc u).mem →
      ExecFrozen u.mem →
      hole2_keepSub (u.readReg64 .lr) = false →
      F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC (hole2_targets mpl).realloc) ((h2k_ghFixedK mpl mmpl).realloc u)
  allocZeroed :
    ∀ (W : CliHooks) (u : State),
      u.status = .Running →
      (∀ msg, ((h2k_ghFixedK mpl mmpl).allocZeroed u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen ((h2k_ghFixedK mpl mmpl).allocZeroed u).mem →
      ExecFrozen u.mem →
      hole2_keepSub (u.readReg64 .lr) = false →
      F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC (hole2_targets mpl).allocZeroed) ((h2k_ghFixedK mpl mmpl).allocZeroed u)
  readFile :
    ∀ (W : CliHooks) (u : State),
      u.status = .Running →
      (∀ msg, (h2asm_readFileHookK mpl mmpl u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (h2asm_readFileHookK mpl mmpl u).mem →
      ExecFrozen u.mem →
      hole2_keepSub (u.readReg64 .lr) = false →
      F3CodeInv mpl mmpl u.mem →
      FdsGe3Closed u.fs →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC (hole2_targets mpl).readFile) (h2asm_readFileHookK mpl mmpl u)
  readStdin :
    ∀ (W : CliHooks) (u : State),
      u.status = .Running →
      (∀ msg, (h2asm_readStdinHookK mpl mmpl u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (h2asm_readStdinHookK mpl mmpl u).mem →
      ExecFrozen u.mem →
      hole2_keepSub (u.readReg64 .lr) = false →
      F3CodeInv mpl mmpl u.mem →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC (hole2_targets mpl).readStdin) (h2asm_readStdinHookK mpl mmpl u)

/-- Prepends `h2b2_stub_*` (`StubReachesTargetOn`) steps to lift `h2asm_Branch2TargetReplaysK`
to `h2asm_Branch2HookReplaysK`. -/
theorem h2asm_branch2HookReplays_of_targetReplays
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hTgt :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2TargetReplaysK mpl mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2asm_Branch2HookReplaysK mpl mmpl :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  { alloc := fun W u hpc hrun hnoex hkf hfr hlr hinv =>
      (h2b2_stub_alloc hLs W u hpc hrun hfr hinv).trans
        (hTgt.alloc W u hrun hnoex hkf hfr hlr hinv)
    dealloc := fun W u hpc hrun hnoex hkf hfr hlr hinv =>
      (h2b2_stub_dealloc hLs W u hpc hrun hfr hinv).trans
        (hTgt.dealloc W u hrun hnoex hkf hfr hlr hinv)
    realloc := fun W u hpc hrun hnoex hkf hfr hlr hinv =>
      (h2b2_stub_realloc hLs W u hpc hrun hfr hinv).trans
        (hTgt.realloc W u hrun hnoex hkf hfr hlr hinv)
    allocZeroed := fun W u hpc hrun hnoex hkf hfr hlr hinv =>
      (h2b2_stub_allocZeroed hLs W u hpc hrun hfr hinv).trans
        (hTgt.allocZeroed W u hrun hnoex hkf hfr hlr hinv)
    readFile := fun W u hpc hrun hnoex hkf hfr hlr hinv hfds =>
      (h2b2_stub_readFile hLs W u hpc hrun hfr hinv).trans
        (hTgt.readFile W u hrun hnoex hkf hfr hlr hinv hfds)
    readStdin := fun W u hpc hrun hnoex hkf hfr hlr hinv =>
      (h2b2_stub_readStdin hLs W u hpc hrun hfr hinv).trans
        (hTgt.readStdin W u hrun hnoex hkf hfr hlr hinv) }

private theorem h2asm_stepsVisitedIn_mono {D1 D2 : BitVec 64 → Bool} {P1 : Program} {s sf : State}
    (h : ∀ pc, D1 pc = true → D2 pc = true)
    (hvis : h2fsgen_StepsVisitedIn D1 P1 s sf) :
    h2fsgen_StepsVisitedIn D2 P1 s sf := by
  induction hvis with
  | refl u => exact .refl u
  | step hd h1 _ ih => exact .step (h _ hd) h1 ih

private theorem h2asm_f3LinkedCallHook_empty_visitedIn {α : Type}
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    {spec : Spec α} {fallback : State → State}
    (hsvc_sub : P_sub.svc = Arm64.Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hOk : subroutine_ok P_sub entryTarget spec) (hInvS : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3LinkedCallHook keep emptyStdProg P_sub entryTarget (fun _ _ => spec) fallback u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := f3LinkedCallHook keep emptyStdProg P_sub entryTarget (fun _ _ => spec) fallback u
    h2fsgen_StepsVisitedIn keep hole2_emptyProg (u.setPC entryTarget) sf_g ∧
      ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs := by
  classical
  have hActPre : ActiveF3CallPre (fun _ _ => spec) u := by
    by_contra hnAct
    apply hnoex "ghost-hook precondition violated"
    unfold f3LinkedCallHook; simp [hnAct]
  obtain ⟨_, hsp, x, R, hpre⟩ := (activeF3CallPre_const_iff spec u).mp hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS (P1 := emptyStdProg) rfl hsvc_sub
      (fun _ _ => rfl) hsub_no hOk hInvS hFsT hPrePC hOutPC hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep emptyStdProg P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have heq : f3LinkedCallHook keep emptyStdProg P_sub entryTarget (fun _ _ => spec) fallback u =
      sf := by
    unfold f3LinkedCallHook; simp only [hActPre, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
  dsimp only; rw [heq]; exact ⟨hvis, hfr_sf, hfs⟩

/-- Stock `ld.lld` Block-`617` replay for `f3EmptyMemsetGhostHookNarrow mmpl` at `lsMemsetSym`
    (`resolve mpl "memset" = mmpl.base 21` via `ElfStockStubResolve.h2b2_stockResolve_memset_eq_base`). -/
theorem h2asm_memsetNarrow_replay617
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) (u : State)
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMemsetSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyMemsetGhostHookNarrow mmpl u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hlr_false : keepMemsetBlk21 mmpl (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
      (f3EmptyMemsetGhostHookNarrow mmpl u) := by
  have h21 : (21 : Nat) < mallocngLib.blocks.length := by decide
  have hpc21 : u.pc = mmpl.base 21 := hpc.trans (h2b2_stockResolve_memset_eq_base hLs hMm)
  have hsetpc : u.setPC (mmpl.base 21) = u := by
    cases u; dsimp [State.setPC] at hpc21 ⊢; subst hpc21; rfl
  have hcl21 : (mallocngBlockProg mmpl 21 Arm64.Syscall.standard).CodeLoaded u.mem :=
    hInv.mngBlockCodeLoaded 21 h21 (fun _ => none) (fun _ => none) Arm64.Syscall.standard
  obtain ⟨hvis, _, _⟩ :=
    h2asm_f3LinkedCallHook_empty_visitedIn
      (mallocngBlockProg21_svc_eq mmpl)
      (mallocngBlockProg21_externAt_none mmpl Arm64.Syscall.standard)
      (subroutine_ok_masterMemset_of_hasWords
        (mallocngBlockProg21_externAt_none mmpl Arm64.Syscall.standard)
        (mallocngBlockProg21_hasWords mmpl Arm64.Syscall.standard))
      (specStripSInvariant_masterMemset (keepMemsetBlk21 mmpl))
      specPreservesFsTrace_masterMemset masterMemset_pre_setPC masterMemset_outcome_setPC
      hrun hnoex hfr hlr_false
      (codeLoaded_stripExecOutside_blk21 (keepCoversBlk21_keepMemsetBlk21 mmpl) hcl21)
  have hBody :=
    h2sl_steps_realW_of_visitedIn_keepSub hLs mmpl W
      (h2asm_stepsVisitedIn_mono (h2k_keepSub_covers_blk21 hMm) hvis)
  rwa [hsetpc] at hBody

/-- Stock `ld.lld` Block-`617` replay for `f3EmptyMemcpyGhostHookNarrow mmpl` at `lsMemcpySym`
    (`resolve mpl "memcpy" = mmpl.base 20` via `ElfStockStubResolve.h2b2_stockResolve_memcpy_eq_base`). -/
theorem h2asm_memcpyNarrow_replay617
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) (u : State)
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMemcpySym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyMemcpyGhostHookNarrow mmpl u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hlr_false : keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
      (f3EmptyMemcpyGhostHookNarrow mmpl u) := by
  have h20 : (20 : Nat) < mallocngLib.blocks.length := by decide
  have hpc20 : u.pc = mmpl.base 20 := hpc.trans (h2b2_stockResolve_memcpy_eq_base hLs hMm)
  have hsetpc : u.setPC (mmpl.base 20) = u := by
    cases u; dsimp [State.setPC] at hpc20 ⊢; subst hpc20; rfl
  have hcl20 : (mallocngBlockProg mmpl 20 Arm64.Syscall.standard).CodeLoaded u.mem :=
    hInv.mngBlockCodeLoaded 20 h20 (fun _ => none) (fun _ => none) Arm64.Syscall.standard
  obtain ⟨hvis, _, _⟩ :=
    h2asm_f3LinkedCallHook_empty_visitedIn
      (mallocngBlockProg20_svc_eq mmpl)
      (mallocngBlockProg20_externAt_none mmpl Arm64.Syscall.standard)
      (subroutine_ok_masterMemcpy_of_hasWords
        (mallocngBlockProg20_externAt_none mmpl Arm64.Syscall.standard)
        (mallocngBlockProg20_hasWords mmpl Arm64.Syscall.standard))
      (specStripSInvariant_masterMemcpy (keepMemcpyBlk20 mmpl))
      specPreservesFsTrace_masterMemcpy masterMemcpy_pre_setPC masterMemcpy_outcome_setPC
      hrun hnoex hfr hlr_false
      (codeLoaded_stripExecOutside_blk20 (keepCoversBlk20_keepMemcpyBlk20 mmpl) hcl20)
  have hBody :=
    h2sl_steps_realW_of_visitedIn_keepSub hLs mmpl W
      (h2asm_stepsVisitedIn_mono (h2k_keepSub_covers_blk20 hMm) hvis)
  rwa [hsetpc] at hBody

/-- 10-way `GhostSymActive (h2k_ghFixedK mpl mmpl)` replay dispatcher closing
`lsRustNoAllocShimSymCli` via `h2b2_shim_branch2`, `lsStringCloneSym` via `hne_sc`, `lsMemsetSym`
via `h2asm_memsetNarrow_replay617`, `lsMemcpySym` via `h2asm_memcpyNarrow_replay617`, and the
remaining six hooks via `hBranch2`. -/
theorem h2asm_ghostReplay_of_branch2K
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      sym ≠ lsStringCloneSym →
      GhostSymActive (h2k_ghFixedK mpl mmpl) sym f →
      ∀ u : State,
        u.pc = libsignalSessionLib.resolve mpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        (sym ≠ lsRustNoAllocShimSymCli → sym ≠ lsMemsetSym → sym ≠ lsMemcpySym →
          hole2_keepSub (u.readReg64 .lr) = false) →
        (sym = lsMemsetSym → keepMemsetBlk21 mmpl (u.readReg64 .lr) = false) →
        (sym = lsMemcpySym → keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false) →
        F3CodeInv mpl mmpl u.mem →
        (sym = lsReadFileSym → FdsGe3Closed u.fs) →
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro W sym f _hsym_ext hne_sc hAct u hpc hrun hnoex hkf hfr hlr_sub hlr_ms hlr_mc hinv hread_fds
  rcases hAct with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, _hsc⟩ | ⟨rfl, _, hrf⟩ | ⟨rfl, _, hrs⟩ | ⟨rfl, hms⟩ | ⟨rfl, hmc⟩
  · exact hBranch2.alloc W u hpc hrun hnoex hkf hfr (hlr_sub (by decide) (by decide) (by decide)) hinv
  · exact hBranch2.dealloc W u hpc hrun hnoex hkf hfr (hlr_sub (by decide) (by decide) (by decide)) hinv
  · exact hBranch2.realloc W u hpc hrun hnoex hkf hfr (hlr_sub (by decide) (by decide) (by decide)) hinv
  · exact hBranch2.allocZeroed W u hpc hrun hnoex hkf hfr (hlr_sub (by decide) (by decide) (by decide)) hinv
  · exact (h2b2_shim_branch2 hLs W u hpc hrun hfr hinv).1
  · exact False.elim (hne_sc rfl)
  · dsimp only [h2k_ghFixedK] at hrf
    injection hrf with hsubeq
    have hfeq : f = h2asm_readFileHookK mpl mmpl := (congrArg Subtype.val hsubeq).symm
    subst hfeq
    exact hBranch2.readFile W u hpc hrun hnoex hkf hfr
      (hlr_sub (by decide) (by decide) (by decide)) hinv (hread_fds rfl)
  · dsimp only [h2k_ghFixedK] at hrs
    injection hrs with hsubeq
    have hfeq : f = h2asm_readStdinHookK mpl mmpl := (congrArg Subtype.val hsubeq).symm
    subst hfeq
    exact hBranch2.readStdin W u hpc hrun hnoex hkf hfr
      (hlr_sub (by decide) (by decide) (by decide)) hinv
  · dsimp only [h2k_ghFixedK] at hms
    injection hms with hfeq
    subst hfeq
    exact h2asm_memsetNarrow_replay617 hLs hMm W u hpc hrun hnoex hfr (hlr_ms rfl) hinv
  · dsimp only [h2k_ghFixedK] at hmc
    injection hmc with hfeq
    subst hfeq
    exact h2asm_memcpyNarrow_replay617 hLs hMm W u hpc hrun hnoex hfr (hlr_mc rfl) hinv

/-! ## `Block617TransferFixedHypG` at `h2k_ghFixedK` -/

/-- Proves `Block617TransferFixedHypG` at `h2k_ghFixedK mpl mmpl` (`C3e-10G`) from `hF3Frozen` and
`hBranch2` via `h2ef_block617TransferFixedG_replaysOn_false_codeOnly`, `h2k_ghFixedK_blk{21,20}TrapHook` (`C3e-5/6`), and `h2k_ghFixedK_blk{21,20}_ext_trap` (`R2-T1`). -/
theorem h2asm_hole2_hTrFrozenKG_of_f3Frozen
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hF3Frozen : ∀ m : Memory, F3CodeOk mpl mmpl m → LibsignalFrozen mpl m)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    Block617TransferFixedHypG mpl mmpl
      (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      (cliExternsPlaced mmpl) (F3MemsetMemcpyEntryLrFalse mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  exact h2ef_block617TransferFixedG_replaysOn_false_codeOnly mpl mmpl hF3Frozen
    (fun W _sym _f hsym_ext hAct =>
      h2b2_realW_externAt_none_of_ghostSymActive hLs (h2k_ghFixedK mpl mmpl) W hsym_ext hAct)
    (h2asm_ghostReplay_of_branch2K hLs hMm hBranch2)
    (@h2k_keepSubLr_false_of_noException _ mpl mmpl)
    (@h2k_fds_of_noException _ mpl mmpl)
    (fun hext hnoShim => h2k_ghFixedK_blk21TrapHook mpl hMm hext hnoShim)
    (fun hext hnoShim => h2k_ghFixedK_blk20TrapHook mpl hMm hext hnoShim)
    (h2k_ghFixedK_blk21_ext_trap hLs hMm)
    (h2k_ghFixedK_blk20_ext_trap hLs hMm)

/-- Proves `Block617TransferFixedHypG` at `h2k_ghFixedK mpl mmpl` from `hBranch2`, discharging
`hF3Frozen` via `hole_gap3_f3CodeOk_to_libsignalFrozen`. -/
theorem h2asm_hole2_hTrFrozenKG
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    Block617TransferFixedHypG mpl mmpl
      (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      (cliExternsPlaced mmpl) (F3MemsetMemcpyEntryLrFalse mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2asm_hole2_hTrFrozenKG_of_f3Frozen mpl mmpl hLs hMm
    (fun _m hCO => hole_gap3_f3CodeOk_to_libsignalFrozen hLs hCO)
    hBranch2

/-- Plain-`Steps` route to `Block617TransferFixedHypG` at `h2k_ghFixedK` via
`h2ef_block617TransferFixedG_of_steps_to_stepsAll_codeOnly`. -/
theorem h2asm_hole2_hTrFrozenKG_steps
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    Block617TransferFixedHypG mpl mmpl
      (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      (cliExternsPlaced mmpl) (F3MemsetMemcpyEntryLrFalse mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  exact h2ef_block617TransferFixedG_of_steps_to_stepsAll_codeOnly mpl mmpl
    (fun _m hCO => hole_gap3_f3CodeOk_to_libsignalFrozen hLs hCO)
    (fun W _sym _f hsym_ext hAct =>
      h2b2_realW_externAt_none_of_ghostSymActive hLs (h2k_ghFixedK mpl mmpl) W hsym_ext hAct)
    (h2asm_ghostReplay_of_branch2K hLs hMm hBranch2)
    (@h2k_keepSubLr_false_of_noException _ mpl mmpl)
    (@h2k_fds_of_noException _ mpl mmpl)
    (fun hext hnoShim => h2k_ghFixedK_blk21TrapHook mpl hMm hext hnoShim)
    (fun hext hnoShim => h2k_ghFixedK_blk20TrapHook mpl hMm hext hnoShim)
    (h2k_ghFixedK_blk21_ext_trap hLs hMm)
    (h2k_ghFixedK_blk20_ext_trap hLs hMm)

/-! ## K-Pinned Witness Carrier and 6-Arm `MainOk*G` Assembly -/

/-- K-pinned Hole-2 witness carrier at `ghFixed := h2k_ghFixedK mpl mmpl`. -/
structure h2asm_F3CliElfGhostWitnessK (mpl mmpl : MultiPlacement) where
  hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
    (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i)
  hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup
  hPl_mng : mallocngLib.Placeable mmpl
  hMainStk : mainFrameSize + max (max extHookStack hole2_hookStack) cliResStack ≤ cliMainStk
  hTrFrozen :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    Block617TransferFixedHypG mpl mmpl
      (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      (cliExternsPlaced mmpl) (F3MemsetMemcpyEntryLrFalse mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk
  hGSpqr :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    ∀ (γ : GhostName) (tp : BitVec 64),
      h2k_CliGhostSpqrAllocHooksK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (h2k_ghFixedK mpl mmpl)
  hFs :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    CliGhostHooksFs (h2k_ghFixedK mpl mmpl)
  hReadSat :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)) lsReadFileSym
        (h2k_readFileSpecK cliIo.rd cliWrOk
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))
  hghNoAlloc :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    ExternNoAllocFailed (cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none))
  hioOf :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @h2k_MainIoOfPlacedK (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)) cliIo hole2_hookStack
        ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd)
  hHooksBundle :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @h2k_CliRunHooksBundleK (libsignalPlacementOf mpl hblk hext_nodup) mmpl
        (h2k_ghFixedK mpl mmpl) W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd)

theorem h2asm_F3CliElfGhostWitnessK.hG {mpl mmpl : MultiPlacement}
    (w : h2asm_F3CliElfGhostWitnessK mpl mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
    ∀ (γ : GhostName) (tp : BitVec 64),
      h2k_CliGhostAllocHooksK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (h2k_ghFixedK mpl mmpl) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  fun γ tp => (w.hGSpqr γ tp).toh2k_CliGhostAllocHooksK

/-- Constructs `h2asm_F3CliElfGhostWitnessK mpl mmpl` from `hBranch2` and
`ElfSlicesPqOomH2KHooks`. -/
theorem h2asm_mkGhostWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    h2asm_F3CliElfGhostWitnessK mpl mmpl where
  hblk := hole2_hblk mpl hLs
  hext_nodup := hole2_hext_nodup mpl hLs
  hPl_mng := hole2_hPl_mng mmpl hMm
  hMainStk := hole2_hMainStk
  hTrFrozen := h2asm_hole2_hTrFrozenKG mpl mmpl hLs hMm hBranch2
  hGSpqr := h2k_hole2_hGSpqrK mpl mmpl hLs hMm
  hFs := h2k_hole2_hFsK mpl mmpl hLs hMm
  hReadSat := h2k_hole2_hReadSatK mpl mmpl hLs hMm
  hghNoAlloc := h2k_hole2_hghNoAllocK mpl mmpl hLs hMm
  hioOf := h2k_hole2_hioOfK mpl mmpl hLs hMm
  hHooksBundle := h2k_hole2_hHooksBundleK mpl mmpl hLs hMm

/-- Ghost Block-`617` counterpart of `MainOkOverD3F3` instantiated strictly at
    `cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)` and `LibsignalFrozen mpl`. -/
def h2asm_GhostMainOkOverK [LibsignalPlacement] (mpl mmpl : MultiPlacement) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok
          (cliProgExtPlacedAt mpl
            (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
          (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
            cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
            Run cliProcessInputs)) ∧
      (∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
          (rc : BitVec 256),
          body.length < 2 ^ 32 →
          pksmParse body = some pm →
          pkToE? pm = some m →
          m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          let inp := pqRecvInputs WP st (wirePrekey :: body) rc
          ∃ a, Run inp a ∧
            (OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
               (pqRecvPrekeyModel X WP { st with session := none } m rc)
               (observe inp.files a) ∧
             D3NoMatchSessionFile X WP st x g m rc (observe inp.files a)) ∧
            CommitOk inp (MainResult.ofAnswer a)) ∧
      (∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256),
          m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
          ∃ a, Run inp a ∧
            (OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
               (pqRecvPrekeyModel X WP { st with session := none } m rc)
               (observe inp.files a) ∧
             D3NoMatchSessionFile X WP st x g m rc (observe inp.files a)) ∧
            CommitOk inp (MainResult.ofAnswer a))

/-- Ghost Block-`617` counterpart of `MainOkUntypedD3F3` instantiated strictly at
    `cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)` and `LibsignalFrozen mpl`. -/
def h2asm_GhostMainOkUntypedK [LibsignalPlacement] (mpl mmpl : MultiPlacement) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ W : CliHooks,
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) cliProcessInputs)

/-- Ghost Block-`617` counterpart of `MainOkPathBD3F3` instantiated strictly at
    `cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)` and `LibsignalFrozen mpl`. -/
def h2asm_GhostMainOkPathBK [LibsignalPlacement] (mpl mmpl : MultiPlacement) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) cliProcessInputs)

/-- Ghost Block-`617` counterpart of `MainOkValidMatchD3F3` instantiated strictly at
    `cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)` and `LibsignalFrozen mpl`. -/
def h2asm_GhostMainOkValidMatchK [LibsignalPlacement] (mpl mmpl : MultiPlacement) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok
          (cliProgExtPlacedAt mpl
            (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
          (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
            cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
            Run cliProcessInputs)) ∧
      ∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
          (rc : BitVec 256),
          body.length < 2 ^ 32 →
          pksmParse body = some pm →
          pkToE? pm = some m →
          m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          let inp := pqRecvInputs WP st (wirePrekey :: body) rc
          ∃ a, Run inp a ∧
            observe inp.files a = pqxdhExpectedOutcome WP inp (pqRecvPrekeyModel X WP st m rc) ∧
            CommitOk inp (MainResult.ofAnswer a)

/-- Ghost Block-`617` counterpart of `MainInitSemF3` instantiated strictly at
    `cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)` and `LibsignalFrozen mpl`. -/
def h2asm_GhostMainInitSemK [LibsignalPlacement] (mpl mmpl : MultiPlacement) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    ∃ S : RunSem,
      InitRunSemOk S X ⟨W.C, W.Q⟩ ∧
      ∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok
          (cliProgExtPlacedAt mpl
            (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
          (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
            cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
            (initD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)) cliProcessInputs)

/-- Arm 1/6 (`hmain`): `MainOkCliF3PqB2NeedLocksPlacedAtG` via `h2asm_hole2_hTrFrozenKG`. -/
theorem h2asm_hmain_cliElfKG
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hGhostMain :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl
        (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
        617 cliProcessInputs (LibsignalFrozen mpl)
        (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk cliBudgetLimits) :
    MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  mainOkCliF3PqG_of_block617TransferFixedG
    (h2asm_hole2_hTrFrozenKG mpl mmpl hLs hMm hBranch2) hGhostMain

/-- Arm 2/6 (`hoverD3`): `MainOkOverD3F3G` via `h2asm_hole2_hTrFrozenKG`. -/
theorem h2asm_hoverD3_cliElfKG
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hGhostOver :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_GhostMainOkOverK mpl mmpl) :
    MainOkOverD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hTr := h2asm_hole2_hTrFrozenKG mpl mmpl hLs hMm hBranch2
  intro h547 X W
  obtain ⟨Run, hOk, hPost⟩ := hGhostOver h547 X W
  exact ⟨Run, hTr W Run hOk, hPost⟩

/-- Arm 3/6 (`huntyped`): `MainOkUntypedD3F3G` via `h2asm_hole2_hTrFrozenKG`. -/
theorem h2asm_huntyped_cliElfKG
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hGhostUntyped :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_GhostMainOkUntypedK mpl mmpl) :
    MainOkUntypedD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hTr := h2asm_hole2_hTrFrozenKG mpl mmpl hLs hMm hBranch2
  intro h547 W
  exact hTr W (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) (hGhostUntyped h547 W)

/-- Arm 4/6 (`hpathB`): `MainOkPathBD3F3G` via `h2asm_hole2_hTrFrozenKG`. -/
theorem h2asm_hpathB_cliElfKG
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hGhostPathB :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_GhostMainOkPathBK mpl mmpl) :
    MainOkPathBD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hTr := h2asm_hole2_hTrFrozenKG mpl mmpl hLs hMm hBranch2
  intro h547 X W
  exact hTr W (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) (hGhostPathB h547 X W)

/-- Arm 5/6 (`hvalidMatch`): `MainOkValidMatchD3F3G` via `h2asm_hole2_hTrFrozenKG`. -/
theorem h2asm_hvalidMatch_cliElfKG
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hGhostValidMatch :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_GhostMainOkValidMatchK mpl mmpl) :
    MainOkValidMatchD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hTr := h2asm_hole2_hTrFrozenKG mpl mmpl hLs hMm hBranch2
  intro h547 X W
  obtain ⟨Run, hOk, hPost⟩ := hGhostValidMatch h547 X W
  exact ⟨Run, hTr W Run hOk, hPost⟩

/-- Arm 6/6 (`hinitSem`): `MainInitSemF3G` via `h2asm_hole2_hTrFrozenKG`. -/
theorem h2asm_hinitSem_cliElfKG
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hGhostInit :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_GhostMainInitSemK mpl mmpl) :
    MainInitSemF3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hTr := h2asm_hole2_hTrFrozenKG mpl mmpl hLs hMm hBranch2
  intro h547 X W
  obtain ⟨S, hSem, hOk⟩ := hGhostInit h547 X W
  exact ⟨S, hSem, hTr W (initD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)) hOk⟩

/-- Bundle of the 6 ghost Block-`617` `MainOk` obligations at `ghFixed := h2k_ghFixedK mpl mmpl`. -/
structure h2asm_GhostMainArmsK [LibsignalPlacement] (mpl mmpl : MultiPlacement) : Prop where
  hmain : MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl
    (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
    617 cliProcessInputs (LibsignalFrozen mpl)
    (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk cliBudgetLimits
  hoverD3 : h2asm_GhostMainOkOverK mpl mmpl
  huntyped : h2asm_GhostMainOkUntypedK mpl mmpl
  hpathB : h2asm_GhostMainOkPathBK mpl mmpl
  hvalidMatch : h2asm_GhostMainOkValidMatchK mpl mmpl
  hinitSem : h2asm_GhostMainInitSemK mpl mmpl

/-- Assembles `CliPqBinaryV2OomF3BytesPlaced cliElfBytes` across `cliElf_parse`,
`cliElf_f3B2NeedLocksAssumptionsG`, and all six `MainOk*G` arms at `h2k_ghFixedK mpl mmpl`. -/
theorem h2asm_cliPqBinaryV2OomF3BytesPlaced_cliElfK
    (hBranch2 : ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl),
      mallocngLib.LinkedAt cliElfBytes mmpl →
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hGhostArms : ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl),
      mallocngLib.LinkedAt cliElfBytes mmpl →
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_GhostMainArmsK mpl mmpl) :
    CliPqBinaryV2OomF3BytesPlaced cliElfBytes :=
  cliPqBinaryV2OomF3BytesPlaced_cliElf_of_mainG
    cliElf_parse
    (fun _mpl _mmpl hLs hMm => cliElf_f3B2NeedLocksAssumptionsG hLs hMm)
    (fun mpl mmpl hLs hMm =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_hmain_cliElfKG mpl mmpl hLs hMm
        (hBranch2 mpl mmpl hLs hMm)
        (hGhostArms mpl mmpl hLs hMm).hmain)
    (fun mpl mmpl hLs hMm =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_hoverD3_cliElfKG mpl mmpl hLs hMm
        (hBranch2 mpl mmpl hLs hMm)
        (hGhostArms mpl mmpl hLs hMm).hoverD3)
    (fun mpl mmpl hLs hMm =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_huntyped_cliElfKG mpl mmpl hLs hMm
        (hBranch2 mpl mmpl hLs hMm)
        (hGhostArms mpl mmpl hLs hMm).huntyped)
    (fun mpl mmpl hLs hMm =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_hpathB_cliElfKG mpl mmpl hLs hMm
        (hBranch2 mpl mmpl hLs hMm)
        (hGhostArms mpl mmpl hLs hMm).hpathB)
    (fun mpl mmpl hLs hMm =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_hvalidMatch_cliElfKG mpl mmpl hLs hMm
        (hBranch2 mpl mmpl hLs hMm)
        (hGhostArms mpl mmpl hLs hMm).hvalidMatch)
    (fun mpl mmpl hLs hMm =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_hinitSem_cliElfKG mpl mmpl hLs hMm
        (hBranch2 mpl mmpl hLs hMm)
        (hGhostArms mpl mmpl hLs hMm).hinitSem)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
