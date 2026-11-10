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
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost
import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopAlloc
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopDealloc
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReads
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemcpy
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KNarrowR1
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG

/-!
# K-Pinned `Block617TransferFixedHyp` and `MainOk` Assembly (`ElfSlicesPqOomH2KAssembly`)

**Checked by Lean.**

Discharges all six Block-`617` hook replay obligations (`alloc`, `allocZeroed`, `dealloc`,
`realloc`, `readFile`, `readStdin`) from `ElfSlicesPqOomH2FirstStopAlloc`,
`ElfSlicesPqOomH2FirstStopDealloc`, `ElfSlicesPqOomH2FirstStopRealloc`, and
`ElfSlicesPqOomH2FirstStopReads`, closing `Block617TransferFixedHyp`, the K-pinned witness
carriers, and `CliPqBinaryV2OomF3BytesPlaced cliElfBytes` modulo `h2ka_MainGhostArmsK`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KAssembly

open Arm64 (GhostName HookSat Memory State Steps subroutine_ok)
open Arm64.Obj (MultiPlacement)
open ProofLib (stripExecOutside)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (LibsignalFrozen LibsignalPlacement)
open CryptoVerification.E2E
  (PEParams PreKeyMessageFields UnreachedPqxdhPrimitives wirePrekey)
open CryptoVerification.SignalSession
  (CliHooks Inputs PqParty PqSessionMatches PqxdhPartyInSpecDomain
   cliElfBytes cliElfImage cliElf_parse cliExternsPlaced cliProcessInputs libsignalSessionLib
   lsMemcpySym lsMemsetSym lsReadFileSym lsStringCloneSym observe pqRecvInputs pqRecvPrekeyModel
   pqxdhExpectedOutcome)
open CryptoVerification.SignalSession.Cli (CommitOk MainResult RunAnswer)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliMainStk cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks CliGhostHooksFs cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
  (MainInitSemF3G MainOkOverD3F3G MainOkPathBD3F3G MainOkUntypedD3F3G MainOkValidMatchD3F3G)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (cliRunSemPathB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (pqD3ScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (cliRunSemD3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (ExternNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (ActiveF3ReadFileRun F3ReadFileFixedCallGuard readFileAnySpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
  (ActiveReadStdinLinkedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (MainOkCliExtPqB2NeedLocksPlacedAt b2MainSpecTightNeedLocksFineAt cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
  (F3MemsetMemcpyEntryLrFalse MainOkCliF3PqB2NeedLocksPlacedAtG
   mainOkCliF3PqG_of_block617TransferFixedG)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (ActiveF3CallPre)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (GhostSymActive)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
  (Block617TransferFixedHypG)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (keepMemcpyBlk20)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (keepMemsetBlk21)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (ReadStdinBoundedEnv readStdinSpecOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
  (InitRunSemOk initD3ScopedRun)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv F3CodeOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
  (h2asm_Branch2HookReplaysK h2asm_F3CliElfGhostWitnessK h2asm_GhostMainArmsK
   h2asm_GhostMainOkOverK h2asm_cliPqBinaryV2OomF3BytesPlaced_cliElfK
   h2asm_hole2_hTrFrozenKG h2asm_memcpyNarrow_replay617 h2asm_memsetNarrow_replay617
   h2asm_mkGhostWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Branch2
  (h2b2_AllFirstStopHyps h2b2_branch2_alloc_explicitLr_perPc
   h2b2_branch2_allocZeroed_explicitLr_perPc h2b2_branch2_dealloc_explicitLr_perPc
   h2b2_branch2_readFile_explicitLr_perPc h2b2_branch2_readStdin_explicitLr_perPc
   h2b2_branch2_realloc_explicitLr_perPc h2b2_realW_externAt_none_of_ghostSymActive
   h2b2_shim_branch2)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2ExecFrozenWire
  (h2ef_block617TransferFixedG_of_steps_to_stepsAll_codeOnly
   h2ef_block617TransferFixedG_replaysOn_false_codeOnly
   h2ef_h2k_ghFixedK_preserves_execFrozen h2ef_pGhost617K_codeLoaded_of_libsignalFrozen)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopAlloc
  (h2fsalloc_alloc_activeRealRun_keepSub h2fsalloc_allocZeroed_activeRealRun_keepSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopDealloc
  (h2fsdealloc_activeRealRun_keepSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReads
  (h2fsreads_readFile_activeRealRun_keepSub h2fsreads_readStdin_activeRealRun_keepSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
  (h2k_CliGhostAllocHooksK h2k_CliGhostSpqrAllocHooksK h2k_CliRunHooksBundleK
   h2k_MainIoOfPlacedK h2k_fds_of_noException h2k_ghFixedK h2k_hole2_hFsK h2k_hole2_hGK
   h2k_hole2_hGSpqrK h2k_hole2_hHooksBundleK h2k_hole2_hReadSatK h2k_hole2_hghNoAllocK
   h2k_hole2_hioOfK h2k_keepSubLr_false_of_noException h2k_readFileFixedGhostHookFineSubK
   h2k_readFileSpecK h2k_readStdinGhostHookFineSubK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemcpy
  (h2k_ghFixedK_blk20TrapHook)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset
  (h2k_ghFixedK_blk21TrapHook)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KNarrowR1
  (h2k_ghFixedK_blk20_ext_trap h2k_ghFixedK_blk21_ext_trap)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
  (CliPqBinaryV2OomF3BytesPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG
  (cliElf_f3B2NeedLocksAssumptionsG cliPqBinaryV2OomF3BytesPlaced_cliElf_of_mainG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_emptyProg hole2_hblk hole2_hext_nodup hole2_hookStack hole2_keepSub hole2_targets
   hole_gap3_f3CodeOk_to_libsignalFrozen)

/-! ## `FirstStopReads` Replay Input Signatures -/

/-- `readFile` first-stop lemma signature (`mallocngLib.LinkedAt cliElfBytes mmpl → h2b2_R_ReadFile mmpl`). -/
abbrev h2ka_ReadFileFirstStopLemma (mmpl : MultiPlacement) : Prop :=
  mallocngLib.LinkedAt cliElfBytes mmpl →
  ∀ {s0 : State},
    ActiveF3CallPre
      (fun γ tp => readFileAnySpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)) s0 →
    ExecFrozen s0.mem →
    hole2_keepSub (s0.readReg64 .lr) = false →
    f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem) →
    FdsGe3Closed s0.fs →
    ActiveF3ReadFileRun hole2_keepSub hole2_emptyProg f3TrialRxProg
      (hole2_targets mmpl).readFile F3ReadFileFixedCallGuard s0

/-- `readStdin` first-stop lemma signature (`mallocngLib.LinkedAt cliElfBytes mmpl → h2b2_R_ReadStdin mmpl`). -/
abbrev h2ka_ReadStdinFirstStopLemma [LibsignalPlacement] (mmpl : MultiPlacement) : Prop :=
  mallocngLib.LinkedAt cliElfBytes mmpl →
  ∀ {s0 : State},
    ActiveF3CallPre
      (fun γ tp => readStdinSpecOfPlaced cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack ReadStdinBoundedEnv) s0 →
    ExecFrozen s0.mem →
    hole2_keepSub (s0.readReg64 .lr) = false →
    f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem) →
    ActiveReadStdinLinkedRun hole2_keepSub hole2_emptyProg f3TrialRxProg
      (hole2_targets mmpl).readStdin s0

/-- Paired `readFile` and `readStdin` first-stop replay hypotheses. -/
structure h2ka_ReadsFirstStopHyps [LibsignalPlacement] (mmpl : MultiPlacement) : Prop where
  readFile : h2ka_ReadFileFirstStopLemma mmpl
  readStdin : h2ka_ReadStdinFirstStopLemma mmpl

theorem h2ka_readsFirstStopHyps [LibsignalPlacement] (mmpl : MultiPlacement) :
    h2ka_ReadsFirstStopHyps mmpl :=
  ⟨h2fsreads_readFile_activeRealRun_keepSub mmpl,
   h2fsreads_readStdin_activeRealRun_keepSub mmpl⟩

/-! ## 6-Field First-Stop Bundle, `h2asm_Branch2HookReplaysK`, and `Block617TransferFixedHyp` -/

/-- Instantiates `h2b2_AllFirstStopHyps` from `ElfSlicesPqOomH2FirstStopAlloc`,
`ElfSlicesPqOomH2FirstStopDealloc`, `ElfSlicesPqOomH2FirstStopRealloc`, and
`ElfSlicesPqOomH2FirstStopReads`. -/
theorem h2ka_allFirstStopHyps [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    h2b2_AllFirstStopHyps mpl mmpl :=
  h2b2_AllFirstStopHyps.of_five hMm
    (h2fsalloc_alloc_activeRealRun_keepSub mmpl hMm)
    (h2fsalloc_allocZeroed_activeRealRun_keepSub mmpl hMm)
    (h2fsdealloc_activeRealRun_keepSub mmpl hMm)
    (h2fsreads_readFile_activeRealRun_keepSub mmpl hMm)
    (h2fsreads_readStdin_activeRealRun_keepSub mmpl hMm)

/-- Constructs `h2asm_Branch2HookReplaysK mpl mmpl` under `[LibsignalPlacement]`. -/
theorem h2ka_branch2HookReplaysK_placed [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    h2asm_Branch2HookReplaysK mpl mmpl where
  alloc W _u hpc hrun hnoex _hkf hfr hlr hinv :=
    (h2b2_branch2_alloc_explicitLr_perPc hLs hMm W hpc hrun hnoex hfr hlr hinv).1
  dealloc W _u hpc hrun hnoex _hkf hfr hlr hinv :=
    (h2b2_branch2_dealloc_explicitLr_perPc hLs hMm W hpc hrun hnoex hfr hlr hinv).1
  realloc W _u hpc hrun hnoex _hkf hfr hlr hinv :=
    (h2b2_branch2_realloc_explicitLr_perPc hLs hMm W hpc hrun hnoex hfr hlr hinv).1
  allocZeroed W _u hpc hrun hnoex _hkf hfr hlr hinv :=
    (h2b2_branch2_allocZeroed_explicitLr_perPc hLs hMm W hpc hrun hnoex hfr hlr hinv).1
  readFile W _u hpc hrun hnoex _hkf hfr hlr hinv hfds :=
    (h2b2_branch2_readFile_explicitLr_perPc hLs hMm W hpc hrun hnoex hfr hlr hfds hinv).1
  readStdin W _u hpc hrun hnoex _hkf hfr hlr hinv :=
    (h2b2_branch2_readStdin_explicitLr_perPc hLs hMm W hpc hrun hnoex hfr hlr hinv).1

/-- Discharges `h2asm_Branch2HookReplaysK mpl mmpl` on `cliElfBytes`. -/
theorem h2ka_branch2HookReplaysK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2asm_Branch2HookReplaysK mpl mmpl :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2ka_branch2HookReplaysK_placed mpl mmpl hLs hMm

/-- Proves `Block617TransferFixedHypG` at `ghFixed := h2k_ghFixedK mpl mmpl` via
`h2asm_hole2_hTrFrozenKG` and `h2ka_branch2HookReplaysK`. -/
theorem h2ka_hole2_hTrFrozenKG
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    Block617TransferFixedHypG mpl mmpl
      (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      (cliExternsPlaced mmpl) (F3MemsetMemcpyEntryLrFalse mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  h2asm_hole2_hTrFrozenKG mpl mmpl hLs hMm
    (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)

/-- 10-way `GhostSymActive (h2k_ghFixedK mpl mmpl)` Block-`617` replay dispatcher. -/
theorem h2ka_ghostReplay617K [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) (sym : String) (f : State → State)
    (_hmem : sym ∈ (libsignalSessionLib.blockLib 617).text.externs)
    (hne_sc : sym ≠ lsStringCloneSym)
    (hAct : GhostSymActive (h2k_ghFixedK mpl mmpl) sym f)
    (u : State)
    (hpc : u.pc = libsignalSessionLib.resolve mpl sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f u).status ≠ .Exception msg)
    (_hkf : u.mem.KeepsFrozen (f u).mem)
    (hfr : ExecFrozen u.mem)
    (hlr : sym ≠ CryptoVerification.SignalSession.lsRustNoAllocShimSymCli →
      sym ≠ lsMemsetSym → sym ≠ lsMemcpySym →
      hole2_keepSub (u.readReg64 .lr) = false)
    (hlr_ms : sym = lsMemsetSym → keepMemsetBlk21 mmpl (u.readReg64 .lr) = false)
    (hlr_mc : sym = lsMemcpySym → keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false)
    (hinv : F3CodeInv mpl mmpl u.mem)
    (hread_fds : sym = lsReadFileSym → FdsGe3Closed u.fs) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) := by
  rcases hAct with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, _⟩ | ⟨rfl, _hfsT, hrf⟩ | ⟨rfl, _hfsT, hrs⟩ | ⟨rfl, hms⟩ | ⟨rfl, hmc⟩
  · exact (h2b2_branch2_alloc_explicitLr_perPc hLs hMm
      W hpc hrun hnoex hfr (hlr (by decide) (by decide) (by decide)) hinv).1
  · exact (h2b2_branch2_dealloc_explicitLr_perPc hLs hMm
      W hpc hrun hnoex hfr (hlr (by decide) (by decide) (by decide)) hinv).1
  · exact (h2b2_branch2_realloc_explicitLr_perPc hLs hMm
      W hpc hrun hnoex hfr (hlr (by decide) (by decide) (by decide)) hinv).1
  · exact (h2b2_branch2_allocZeroed_explicitLr_perPc hLs hMm
      W hpc hrun hnoex hfr (hlr (by decide) (by decide) (by decide)) hinv).1
  · exact (h2b2_shim_branch2 hLs W u hpc hrun hfr hinv).1
  · exact False.elim (hne_sc rfl)
  · dsimp only [h2k_ghFixedK] at hrf
    injection hrf with hsubeq
    have hv := (congrArg Subtype.val hsubeq).symm
    dsimp only [h2k_readFileFixedGhostHookFineSubK] at hv
    subst hv
    exact (h2b2_branch2_readFile_explicitLr_perPc hLs hMm
      W hpc hrun hnoex hfr (hlr (by decide) (by decide) (by decide)) (hread_fds rfl) hinv).1
  · dsimp only [h2k_ghFixedK] at hrs
    injection hrs with hsubeq
    have hv := (congrArg Subtype.val hsubeq).symm
    dsimp only [h2k_readStdinGhostHookFineSubK] at hv
    subst hv
    exact (h2b2_branch2_readStdin_explicitLr_perPc hLs hMm
      W hpc hrun hnoex hfr (hlr (by decide) (by decide) (by decide)) hinv).1
  · dsimp only [h2k_ghFixedK] at hms
    injection hms with hfeq
    subst hfeq
    exact h2asm_memsetNarrow_replay617 hLs hMm W u hpc hrun hnoex hfr (hlr_ms rfl) hinv
  · dsimp only [h2k_ghFixedK] at hmc
    injection hmc with hfeq
    subst hfeq
    exact h2asm_memcpyNarrow_replay617 hLs hMm W u hpc hrun hnoex hfr (hlr_mc rfl) hinv

/-- `Block617TransferFixedHypG` at `h2k_ghFixedK` via
`h2ef_block617TransferFixedG_replaysOn_false_codeOnly`. -/
theorem h2ka_hole2_hTrFrozenKG_via_replaysOn [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    Block617TransferFixedHypG mpl mmpl
      (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      (cliExternsPlaced mmpl) (F3MemsetMemcpyEntryLrFalse mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  h2ef_block617TransferFixedG_replaysOn_false_codeOnly mpl mmpl
    (fun _m hCO => hole_gap3_f3CodeOk_to_libsignalFrozen hLs hCO)
    (fun W _sym _f hmem hAct =>
      h2b2_realW_externAt_none_of_ghostSymActive hLs (h2k_ghFixedK mpl mmpl) W hmem hAct)
    (h2ka_ghostReplay617K mpl mmpl hLs hMm)
    (@h2k_keepSubLr_false_of_noException _ mpl mmpl)
    (@h2k_fds_of_noException _ mpl mmpl)
    (fun hext hnoShim => h2k_ghFixedK_blk21TrapHook mpl hMm hext hnoShim)
    (fun hext hnoShim => h2k_ghFixedK_blk20TrapHook mpl hMm hext hnoShim)
    (h2k_ghFixedK_blk21_ext_trap hLs hMm)
    (h2k_ghFixedK_blk20_ext_trap hLs hMm)

/-- `Block617TransferFixedHypG` at `h2k_ghFixedK` via
`h2ef_block617TransferFixedG_of_steps_to_stepsAll_codeOnly`. -/
theorem h2ka_hole2_hTrFrozenKG_via_execfzSec5 [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    Block617TransferFixedHypG mpl mmpl
      (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      (cliExternsPlaced mmpl) (F3MemsetMemcpyEntryLrFalse mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  h2ef_block617TransferFixedG_of_steps_to_stepsAll_codeOnly mpl mmpl
    (fun _m hCO => hole_gap3_f3CodeOk_to_libsignalFrozen hLs hCO)
    (fun W _sym _f hmem hAct =>
      h2b2_realW_externAt_none_of_ghostSymActive hLs (h2k_ghFixedK mpl mmpl) W hmem hAct)
    (h2ka_ghostReplay617K mpl mmpl hLs hMm)
    (@h2k_keepSubLr_false_of_noException _ mpl mmpl)
    (@h2k_fds_of_noException _ mpl mmpl)
    (fun hext hnoShim => h2k_ghFixedK_blk21TrapHook mpl hMm hext hnoShim)
    (fun hext hnoShim => h2k_ghFixedK_blk20TrapHook mpl hMm hext hnoShim)
    (h2k_ghFixedK_blk21_ext_trap hLs hMm)
    (h2k_ghFixedK_blk20_ext_trap hLs hMm)

/-- `ExecFrozen` preservation across active hooks of `h2k_ghFixedK`. -/
theorem h2ka_ghFixedK_preserves_execFrozen [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) {sym : String} {f : State → State}
    (hAct : GhostSymActive (h2k_ghFixedK mpl mmpl) sym f) :
    ∀ u : State, ExecFrozen u.mem → ExecFrozen (f u).mem :=
  h2ef_h2k_ghFixedK_preserves_execFrozen mpl mmpl hAct

theorem h2ka_pGhost617K_codeLoaded_of_libsignalFrozen [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (W : CliHooks) (m : Memory)
    (hFrz : LibsignalFrozen mpl m) :
    (cliProgExtPlacedAt mpl
      (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
      617 W).CodeLoaded m :=
  h2ef_pGhost617K_codeLoaded_of_libsignalFrozen mpl mmpl W m hFrz

/-! ## K-Pinned Hole-2 Witness Carriers -/

/-- K-pinned Hole-2 witness bundle at `ghFixed := h2k_ghFixedK mpl mmpl`, packaging
`Block617TransferFixedHypG` and all narrowed hook witnesses. -/
structure h2ka_F3CliElfGhostWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) where
  ghFixed : CliGhostHooks
  ghFixed_eq :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ghFixed = h2k_ghFixedK mpl mmpl
  hTrFrozen : Block617TransferFixedHypG mpl mmpl
    (fun W => cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
    (cliExternsPlaced mmpl) (F3MemsetMemcpyEntryLrFalse mmpl)
    (LibsignalFrozen mpl) (F3CodeOk mpl mmpl)
    (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk
  hFs : CliGhostHooksFs ghFixed
  hghNoAlloc : ExternNoAllocFailed (cliGhostExterns ghFixed (fun _ => none))
  hGSpqr :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (γ : GhostName) (tp : BitVec 64),
      h2k_CliGhostSpqrAllocHooksK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed
  hG :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (γ : GhostName) (tp : BitVec 64),
      h2k_CliGhostAllocHooksK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed
  hReadSat : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (h2k_readFileSpecK cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))
  hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    @h2k_MainIoOfPlacedK (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)) _
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hole2_hookStack
      ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd)
  hHooksBundle : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    @h2k_CliRunHooksBundleK
      (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
      mmpl ghFixed W fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd)

noncomputable def h2ka_f3CliElfGhostWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    h2ka_F3CliElfGhostWitnessK mpl mmpl hLs :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  { ghFixed := h2k_ghFixedK mpl mmpl
    ghFixed_eq := rfl
    hTrFrozen := h2ka_hole2_hTrFrozenKG mpl mmpl hLs hMm
    hFs := h2k_hole2_hFsK mpl mmpl hLs hMm
    hghNoAlloc := h2k_hole2_hghNoAllocK mpl mmpl hLs hMm
    hGSpqr := h2k_hole2_hGSpqrK mpl mmpl hLs hMm
    hG := h2k_hole2_hGK mpl mmpl hLs hMm
    hReadSat := h2k_hole2_hReadSatK mpl mmpl hLs hMm
    hioOf := h2k_hole2_hioOfK mpl mmpl hLs hMm
    hHooksBundle := h2k_hole2_hHooksBundleK mpl mmpl hLs hMm }

theorem h2ka_nonempty_f3CliElfGhostWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    Nonempty (h2ka_F3CliElfGhostWitnessK mpl mmpl hLs) :=
  ⟨h2ka_f3CliElfGhostWitnessK mpl mmpl hLs hMm⟩

theorem h2ka_f3CliElfGhostWitnessK_h2asm
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    h2asm_F3CliElfGhostWitnessK mpl mmpl :=
  h2asm_mkGhostWitnessK mpl mmpl hLs hMm
    (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)

theorem h2ka_nonempty_h2asm_f3CliElfGhostWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    Nonempty (h2asm_F3CliElfGhostWitnessK mpl mmpl) :=
  ⟨h2ka_f3CliElfGhostWitnessK_h2asm mpl mmpl hLs hMm⟩

/-! ## `MainOk`, D3 Arms, and `CliPqBinaryV2OomF3BytesPlaced` at `h2k_ghFixedK` -/

/-- Block-`617` ghost-side `MainOk` and 5 D3 arm obligations pinned at
`ghFixed := h2k_ghFixedK mpl mmpl` and `CodeOk_ghost := LibsignalFrozen mpl`. -/
structure h2ka_MainGhostArmsK [LibsignalPlacement] (mpl mmpl : MultiPlacement) : Prop where
  mainPq : MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl
    (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
    617 cliProcessInputs (LibsignalFrozen mpl)
    (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk cliBudgetLimits
  overD3 : h2asm_GhostMainOkOverK mpl mmpl
  untypedD3 : mpl.base 547 ≠ 0#64 →
    ∀ W : CliHooks, ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc
          (LibsignalFrozen mpl)
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) cliProcessInputs)
  pathBD3 : mpl.base 547 ≠ 0#64 →
    ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks), ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc
          (LibsignalFrozen mpl)
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) cliProcessInputs)
  validMatchD3 : mpl.base 547 ≠ 0#64 →
    ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
      let WP : PEParams := ⟨W.C, W.Q⟩
      ∃ Run : Inputs → RunAnswer → Prop,
        (∀ (γ : GhostName) (tp : BitVec 64),
          subroutine_ok
            (cliProgExtPlacedAt mpl
              (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
            (mpl.base 617)
            (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc
              (LibsignalFrozen mpl)
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
  initSem : mpl.base 547 ≠ 0#64 →
    ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
      ∃ S : RunSem,
        InitRunSemOk S X ⟨W.C, W.Q⟩ ∧
        ∀ (γ : GhostName) (tp : BitVec 64),
          subroutine_ok
            (cliProgExtPlacedAt mpl
              (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
            (mpl.base 617)
            (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc
              (LibsignalFrozen mpl)
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
              cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
              (initD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)) cliProcessInputs)

/-- `MainOkCliF3PqB2NeedLocksPlacedAtG` via `h2ka_hole2_hTrFrozenKG`. -/
theorem h2ka_hmain_cliElfG
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hGhostPq :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl
        (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
        617 cliProcessInputs (LibsignalFrozen mpl)
        (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk cliBudgetLimits) :
    MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  mainOkCliF3PqG_of_block617TransferFixedG
    (h2ka_hole2_hTrFrozenKG mpl mmpl hLs hMm) hGhostPq

/-- `MainOkOverD3F3G` via `h2ka_hole2_hTrFrozenKG`. -/
theorem h2ka_hoverD3_cliElfG
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hGhostOver :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_GhostMainOkOverK mpl mmpl) :
    MainOkOverD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hTr := h2ka_hole2_hTrFrozenKG mpl mmpl hLs hMm
  intro h547 X W
  obtain ⟨Run, hOk, hPost⟩ := hGhostOver h547 X W
  exact ⟨Run, hTr W Run hOk, hPost⟩

/-- `MainOkUntypedD3F3G` via `h2ka_hole2_hTrFrozenKG`. -/
theorem h2ka_huntyped_cliElfG
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hGhostUntyped :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      mpl.base 547 ≠ 0#64 →
      ∀ W : CliHooks, ∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok
          (cliProgExtPlacedAt mpl
            (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
          (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc
            (LibsignalFrozen mpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
            cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
            (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) cliProcessInputs)) :
    MainOkUntypedD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  fun h547 W => h2ka_hole2_hTrFrozenKG mpl mmpl hLs hMm W _ (hGhostUntyped h547 W)

/-- `MainOkPathBD3F3G` via `h2ka_hole2_hTrFrozenKG`. -/
theorem h2ka_hpathB_cliElfG
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hGhostPathB :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks), ∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok
          (cliProgExtPlacedAt mpl
            (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
          (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc
            (LibsignalFrozen mpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
            cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
            (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) cliProcessInputs)) :
    MainOkPathBD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  fun h547 X W => h2ka_hole2_hTrFrozenKG mpl mmpl hLs hMm W _ (hGhostPathB h547 X W)

/-- `MainOkValidMatchD3F3G` via `h2ka_hole2_hTrFrozenKG`. -/
theorem h2ka_hvalidMatch_cliElfG
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hGhostValidMatch :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
        let WP : PEParams := ⟨W.C, W.Q⟩
        ∃ Run : Inputs → RunAnswer → Prop,
          (∀ (γ : GhostName) (tp : BitVec 64),
            subroutine_ok
              (cliProgExtPlacedAt mpl
                (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
              (mpl.base 617)
              (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc
                (LibsignalFrozen mpl)
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
                CommitOk inp (MainResult.ofAnswer a)) :
    MainOkValidMatchD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro h547 X W
  obtain ⟨Run, hmainW, hclauses⟩ := hGhostValidMatch h547 X W
  exact ⟨Run, h2ka_hole2_hTrFrozenKG mpl mmpl hLs hMm W Run hmainW, hclauses⟩

/-- `MainInitSemF3G` via `h2ka_hole2_hTrFrozenKG`. -/
theorem h2ka_hinitSem_cliElfG
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hGhostInit :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
        ∃ S : RunSem,
          InitRunSemOk S X ⟨W.C, W.Q⟩ ∧
          ∀ (γ : GhostName) (tp : BitVec 64),
            subroutine_ok
              (cliProgExtPlacedAt mpl
                (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
              (mpl.base 617)
              (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc
                (LibsignalFrozen mpl)
                (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
                cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
                (initD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)) cliProcessInputs)) :
    MainInitSemF3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro h547 X W
  obtain ⟨S, hSemOk, hmainW⟩ := hGhostInit h547 X W
  exact ⟨S, hSemOk, h2ka_hole2_hTrFrozenKG mpl mmpl hLs hMm W _ hmainW⟩

/-- Assembles `CliPqBinaryV2OomF3BytesPlaced cliElfBytes` from `h2ka_MainGhostArmsK`. -/
theorem h2ka_cliPqBinaryV2OomF3BytesPlaced_cliElf
    (hGhostArms : ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl),
      mallocngLib.LinkedAt cliElfBytes mmpl →
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2ka_MainGhostArmsK mpl mmpl) :
    CliPqBinaryV2OomF3BytesPlaced cliElfBytes :=
  cliPqBinaryV2OomF3BytesPlaced_cliElf_of_mainG
    cliElf_parse
    (fun _mpl _mmpl hLs hMm => cliElf_f3B2NeedLocksAssumptionsG hLs hMm)
    (fun mpl mmpl hLs hMm =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2ka_hmain_cliElfG mpl mmpl hLs hMm (hGhostArms mpl mmpl hLs hMm).mainPq)
    (fun mpl mmpl hLs hMm =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2ka_hoverD3_cliElfG mpl mmpl hLs hMm (hGhostArms mpl mmpl hLs hMm).overD3)
    (fun mpl mmpl hLs hMm =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2ka_huntyped_cliElfG mpl mmpl hLs hMm (hGhostArms mpl mmpl hLs hMm).untypedD3)
    (fun mpl mmpl hLs hMm =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2ka_hpathB_cliElfG mpl mmpl hLs hMm (hGhostArms mpl mmpl hLs hMm).pathBD3)
    (fun mpl mmpl hLs hMm =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2ka_hvalidMatch_cliElfG mpl mmpl hLs hMm (hGhostArms mpl mmpl hLs hMm).validMatchD3)
    (fun mpl mmpl hLs hMm =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2ka_hinitSem_cliElfG mpl mmpl hLs hMm (hGhostArms mpl mmpl hLs hMm).initSem)

/-- Assembles `CliPqBinaryV2OomF3BytesPlaced cliElfBytes` from `h2asm_GhostMainArmsK` and
`h2ka_branch2HookReplaysK`. -/
theorem h2ka_cliPqBinaryV2OomF3BytesPlaced_cliElf_of_h2asm
    (hGhostArms : ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl),
      mallocngLib.LinkedAt cliElfBytes mmpl →
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_GhostMainArmsK mpl mmpl) :
    CliPqBinaryV2OomF3BytesPlaced cliElfBytes :=
  h2asm_cliPqBinaryV2OomF3BytesPlaced_cliElfK h2ka_branch2HookReplaysK hGhostArms

theorem h2ka_cliPqBinaryV2OomF3BytesPlaced_cliElf_of_ghostArms
    (hGhostArms : ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl),
      mallocngLib.LinkedAt cliElfBytes mmpl →
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_GhostMainArmsK mpl mmpl) :
    CliPqBinaryV2OomF3BytesPlaced cliElfBytes :=
  h2ka_cliPqBinaryV2OomF3BytesPlaced_cliElf_of_h2asm hGhostArms

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KAssembly
