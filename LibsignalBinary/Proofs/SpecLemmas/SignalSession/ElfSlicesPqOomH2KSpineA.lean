/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapFixed
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFd
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KCliNoOom
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3MainLiftGlue
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.PeakBudget.CliF3MainOkBridge
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2LsRetAddrKeep
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinKit
import ProofLib.SepLogic

/-!
# Spine-A (`main`, Block `617`) Closers at `h2k_ghFixedK` (`ElfSlicesPqOomH2KSpineA`)

**Checked by Lean.**

Closes the Spine-A (`main`, Block `617`) obligations from the Spine-B (`run` at Block `579`,
`runSpecTightPlacedPreFd`) interfaces in `ElfSlicesPqOomH2KIfaces`:
1. Proves `FdsGe3Closed` preservation across `h2k_readFileFixedGhostHookFineK` and
   `h2k_readStdinGhostHookFineK`, and closes `MainIoOfPlacedFd` at `h2k_ghFixedK mpl mmpl`
   (`h2k_hole2_hioOfFd`).
2. Proves self-contained `MainEntryBudgetFitsCapOf` for `initD3ScopedRun` (`h2k_fitCap_initD3`).
3. Provides witness-parametric (`w : F3CliElfGhostWitnessK mpl mmpl`) and concrete `cliElfBytes`
   closers for `hmain`, `hinitSem`, `huntyped`, and generic D3 `RunSem` slices.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineA

open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open CryptoGames (Party)
open CryptoVerification
  (LibsignalFrozen LibsignalHooks LibsignalPlacement libsignalMutatedBlocks
   libsignalSessionExterns ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives partyAddressName)
open CryptoVerification.LibsignalPublicApi.StoreKit (subroutine_ok_rocl_of_plain withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (pniPrefix serviceIdParse uuidTryParse)
open CryptoVerification.SignalSession
  (Address CliHooks Cmd Inputs bundleDir cliElfBytes cliElfImage cliExternsPlaced
   cliProcessInputs libsignalSessionLib lsReadFileSym lsReadStdinSym partyAddress)
open CryptoVerification.SignalSession.Cli
  (IdGhost StoresGhost addressText decimalText pathOf utf8)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV RunCall addrParse cliIo cliMainStk cliResStack cliRunBudgets cliRunBudgets_placed
   cliRunNeeds cliWrOk coinsOf instLsCodeInvFrozen mProgPlaced namedWrites namedWrites_ascii
   parseArgs pathStr)
open CryptoVerification.SignalSession.Cli.RunCompose
  (PksmGhost RunSem addrValOf finish readBundleV runAns runFiles runRel)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns cliGhostExterns_readFile_some cliGhostExterns_readStdin_some)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed initDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.CliExt (ReadFileCall)
open LibsignalBinary.Heap (AllocEvent BudgetLimits)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliF3MainOkBridge
  (boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapFixed
  (mainEntryBudgetFitsCapOf_initD3ScopedRun_fixed)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (binaryKitRunSlotEnvsFixed realCliDecPkBinaryWideSlotEnvFixed realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom (cliDecPkCanonSlotEnvExact')
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
  (DecPkD3UntypedEnvOf PqxdhAcceptBadKemErrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
  (MainInitSemF3G MainOkUntypedD3F3G)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
  (CliPqOrD3RecvInputs pqD3ScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (cliRunSemD3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (ActiveF3ReadFilePre f3ReadFileFixedGhostHook f3ReadFileFixedGhostHookFine
   f3ReadFileFixedGhostHookFine_ok_lit f3ReadFileLinkedHook readFileAnySpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (hookSat_withLsRetAddr624AndFds_of_withFds_keepLrAndFds lsReadFile_rocl_of_hookSat
   withLsRetAddr624AndFds)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed ReadFileRuleEnvFixed hookOk_withFdsGe3Closed hookOk_withFdsGe3Closed_of_fs_eq
   withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced (keepFilesTrace)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (MainOkCliExtPqB2NeedLocksPlacedAt b2MainSpecTightNeedLocksFineAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
  (F3MemsetMemcpyEntryLrFalse MainOkCliF3PqB2NeedLocksPlacedAtG
   mainOkCliF3PqG_of_block617TransferFixedG)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (ActiveF3CallPre f3ReadStdinFallback_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv
  (mainOkCliExtPqB2NeedLocksPlacedAt_iff)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG (withEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
  (MainEntryBudgetFitsCapOf domScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (ReadStdinBoundedEnv readStdinSpecOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFd (MainIoOfPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
  (CliInitD3Inputs initD3ScopedRun initRunSemOk_of_filesOk₀)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
  (RunArmAtMeEnv RunArmEnvs RunCoreEnv RunDispatchEnv RunEnv RunInit2ChainEnv RunInit3Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileLitSpecPlaced readFileSpecPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3TrialRxProg f3TrialRxProg_no_ext f3TrialRxProg_svc)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
  (h2asm_Branch2HookReplaysK h2asm_GhostMainInitSemK h2asm_GhostMainOkUntypedK
   h2asm_hmain_cliElfKG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
  (h2kb_alloc_pre_keepSub_false h2kb_dealloc_pre_keepSub_false h2kb_hole2_hG
   h2kb_hole2_hioOf_writeFile h2kb_hole2_hioOf_writeStdout h2kb_hookOk_of_withKeepLrFalse
   h2kb_readStdin_okK h2kb_readStdin_pre_keepSub_false h2kb_realloc_pre_keepSub_false)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KCliNoOom
  (mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_cliBudgetLimits_of_kitEnvFits_and_runTightOf_preFd)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3MainLiftGlue
  (ghostMainSubroutineD3_of_domScopedRunTight_preFd)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
  (h2k_ghFixedK h2k_hole2_hReadSatK h2k_readFileAnySpecK h2k_readFileFixedGhostHookFineK
   h2k_readFileLitSpecK h2k_readFileSpecK h2k_readStdinGhostHookFineK h2k_withKeepLrAndFds)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (h2ki_SpineBCanonSliceAt h2ki_SpineBCanonSliceK h2ki_SpineBRunTightOfSemAt
   h2ki_SpineBRunTightOfSemK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
  (F3CliElfGhostWitnessK GhostMainInitSemOfWitnessK GhostMainOkUntypedOfWitnessK
   mkF3CliElfGhostWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2LsRetAddrKeep
  (h2lr_lsRetAddr624_keepSub_false)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
  (fits2_mkBinaryKitRealCalleeEnvsDecPk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_emptyProg hole2_hMainStk hole2_hPl_mng hole2_hblk hole2_hext_nodup hole2_hookStack
   hole2_keepMallocng hole2_keepSub hole2_readFileCond_ok hole2_targets hole_g5a_untyped_fitsCap)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinCanonPrime
  (canonOrFallbackRunEnvExact')
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinKit
  (hole_hmain_runEnvExact'_sub_binaryKit_closed
   realCliMainBinaryKitEnvOfExact'_fitsEnv_cliBudgetLimits_closed)

/-! ## Plain Allocator Bridges and K-Hook `FdsGe3Closed` Preservation -/

/-- Lift `w.hGSpqrK` (`h2k_CliGhostSpqrAllocHooksK`) to plain `CliGhostSpqrAllocHooks` via
`LsRetAddr624 lr → hole2_keepSub lr = false` (`h2lr_lsRetAddr624_keepSub_false`). -/
theorem F3CliElfGhostWitnessK.hGSpqr {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
    ∀ (γ : GhostName) (tp : BitVec 64),
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits w.ghFixed := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  intro γ tp
  have hGK := w.hGSpqrK γ tp
  exact
    { alloc := h2kb_hookOk_of_withKeepLrFalse hGK.alloc (h2kb_alloc_pre_keepSub_false hLs)
      dealloc := h2kb_hookOk_of_withKeepLrFalse hGK.dealloc (h2kb_dealloc_pre_keepSub_false hLs)
      realloc := h2kb_hookOk_of_withKeepLrFalse hGK.realloc (h2kb_realloc_pre_keepSub_false hLs)
      allocZeroed :=
        h2kb_hookOk_of_withKeepLrFalse hGK.allocZeroed
          (h2kb_alloc_pre_keepSub_false (zeroed := true) hLs)
      alloc_fs := hGK.alloc_fs
      dealloc_fs := hGK.dealloc_fs
      realloc_fs := hGK.realloc_fs
      allocZeroed_fs := hGK.allocZeroed_fs
      alloc_fsT := hGK.alloc_fsT
      dealloc_fsT := hGK.dealloc_fsT
      realloc_fsT := hGK.realloc_fsT
      allocZeroed_fsT := hGK.allocZeroed_fsT
      shim_eq := hGK.shim_eq
      memset := hGK.memset
      memcpy := hGK.memcpy
      memcpy_exact := hGK.memcpy_exact
      memset_acp := hGK.memset_acp }

/-- Lift `w.hGK` (`h2k_CliGhostAllocHooksK`) to plain `CliGhostAllocHooks` via
`LsRetAddr624 lr → hole2_keepSub lr = false`. -/
theorem F3CliElfGhostWitnessK.hG {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
    ∀ (γ : GhostName) (tp : BitVec 64),
      CliGhostAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits w.ghFixed :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  fun γ tp => (F3CliElfGhostWitnessK.hGSpqr w hLs γ tp).toCliGhostAllocHooks

/-- `h2k_readFileFixedGhostHookFineK` preserves `State.fs` identically on all branches (`Active`
linked run, `keepFsTrace` fallback, and `.Exception` guard). -/
theorem h2k_readFileFixedGhostHookFineK_fs
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) (s0 : State) :
    (h2k_readFileFixedGhostHookFineK keep P_real P_sub entry_io mmpl brkStart lim stk s0).fs =
      s0.fs := by
  classical
  unfold h2k_readFileFixedGhostHookFineK
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2.2).2.2.1
    · rfl
  · rfl

/-- `h2k_readStdinGhostHookFineK` preserves `FdsGe3Closed` (`fds ≥ 3 = none`) on all branches,
even though fd `0` offset advances on the active `read_stdin` syscall run. -/
theorem fdsGe3Closed_h2k_readStdinGhostHookFineK [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) {s0 : State}
    (hfds : FdsGe3Closed s0.fs) :
    FdsGe3Closed
      (h2k_readStdinGhostHookFineK keep P_real P_sub entry_io mmpl brkStart lim stk s0).fs := by
  classical
  unfold h2k_readStdinGhostHookFineK
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2).2.2.2.2.1 hfds
    · unfold keepFilesTrace
      dsimp only
      split
      · rw [f3ReadStdinFallback_fs]
        exact hfds
      · exact hfds
  · exact hfds

/-! ## `MainIoOfPlacedFd` at `h2k_ghFixedK` and `F3WitnessMainIoFd` -/

private theorem h2k_spineA_hookOk_of_eq_on_pre {α : Type} {P : State → Prop}
    {f_K f_orig : State → State} {spec : Spec α}
    (hEq : ∀ x R s0, s0.status = .Running → s0.spAligned = true →
      P s0 → (s0.mem ⊨ spec.pre x s0 ∗ R) → f_K s0 = f_orig s0)
    (hOrig : HookOk f_orig spec) :
    HookOk f_K { spec with pre := fun x s => ⌜P s⌝ ∗ spec.pre x s } := by
  intro x R s0 hrun hpre hsp
  dsimp only at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hP, hpre_orig⟩
  rw [hEq x R s0 hrun hsp hP hpre_orig]
  exact hOrig x R s0 hrun hpre_orig hsp

private theorem h2k_spineA_readFileFixedGhostHookFineK_eq_of_any
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
    f3ReadFileFixedGhostHookFine keep P_real P_sub entry_io mmpl brkStart lim stk s0 := by
  classical
  have hActK : ActiveF3CallPre
      (fun γ' tp' => h2k_readFileAnySpecK
        (fineHookRustCliAllocBudget γ' mmpl tp' brkStart) lim stk
        (ReadFileRuleEnvFixed cliIo.rd)) s0 := by
    refine ⟨hrun, hsp, γ, tp, y, R, ?_⟩
    dsimp only [h2k_readFileAnySpecK, h2k_withKeepLrAndFds]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hlr, hfds⟩, hpreAny⟩
  have hAct : ActiveF3ReadFilePre
      (fun γ' tp' => fineHookRustCliAllocBudget γ' mmpl tp' brkStart) lim stk
      (ReadFileRuleEnvFixed cliIo.rd) s0 :=
    ⟨hrun, hsp, γ, tp, y, R, hpreAny⟩
  unfold h2k_readFileFixedGhostHookFineK f3ReadFileFixedGhostHookFine
    f3ReadFileFixedGhostHook f3ReadFileLinkedHook
  rw [dite_eq_left_of_eq_true (eq_true hActK), dite_eq_left_of_eq_true (eq_true hAct)]

/-- `HookSat` on `lsReadFileSym` at `h2k_ghFixedK` for `withLsRetAddr624AndFds (readFileLitSpecPlaced …)`
(Block-`617` `M3` `read_file("coins")` contract). -/
theorem h2k_hole2_readFileLit_hookSat_lsRetAddr624AndFds
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat
      (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      lsReadFileSym
      (withLsRetAddr624AndFds
        (readFileLitSpecPlaced cliIo
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd))) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  let P_sub := f3TrialRxProg
  let H := cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)
  have hLitOrig :=
    f3ReadFileFixedGhostHookFine_ok_lit
      (keep := hole2_keepSub) (P_real := hole2_emptyProg) (P_sub := P_sub)
      (entry_io := (hole2_targets mpl).readFile) (mmpl := mmpl) (brkStart := cliElfImage.brkStart)
      (lim := cliBudgetLimits) (stk := hole2_hookStack)
      rfl f3TrialRxProg_svc (fun _ _ => rfl) f3TrialRxProg_no_ext
      (hole2_hPl_mng mmpl hMm) (hole2_keepMallocng mmpl hMm) (Nat.le_refl _)
      (hole2_readFileCond_ok mmpl hMm) γ tp
  have hLitOkK : HookOk
      (h2k_readFileFixedGhostHookFineK hole2_keepSub hole2_emptyProg P_sub
        (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack)
      (h2k_readFileLitSpecK cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)) := by
    apply h2k_spineA_hookOk_of_eq_on_pre _ hLitOrig
    rintro ⟨x, st⟩ R s0 hrun hsp ⟨hlr, hfds⟩ hpreOrig
    let y : ReadFileCall × fineCostModel.σ := (⟨x.pathA, true, x.path, x.ret⟩, st)
    have hpreAny : s0.mem ⊨ (readFileAnySpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)).pre y s0 ∗ R := by
      simpa only [readFileAnySpecPlaced, readFileLitSpecPlaced, y,
        CryptoVerification.SignalSession.CliExt.bytesAt, ↓reduceIte]
        using hpreOrig
    exact h2k_spineA_readFileFixedGhostHookFineK_eq_of_any hrun hsp hlr hfds hpreAny
  have hFdsK : HookSat H lsReadFileSym
      (withFdsGe3Closed
        (h2k_readFileLitSpecK cliIo
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd))) :=
    ⟨_, cliGhostExterns_readFile_some (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W) rfl,
     hookOk_withFdsGe3Closed_of_fs_eq
       (h2k_readFileFixedGhostHookFineK_fs hole2_keepSub hole2_emptyProg P_sub
         (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack)
       hLitOkK⟩
  exact hookSat_withLsRetAddr624AndFds_of_withFds_keepLrAndFds
    (fun _ hlr => h2lr_lsRetAddr624_keepSub_false hLs hlr) hFdsK

/-- `HookSat` on `lsReadFileSym` at `h2k_ghFixedK` for `withLsRetAddr624AndFds (readFileSpecPlaced …)`
at `cliRunBudgets.readFile` (shared Block-`579` / Spine-B / Spine-C `read_file` contract). -/
theorem h2k_hole2_readFile_hookSat_lsRetAddr624AndFds
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat
      (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      lsReadFileSym
      (withLsRetAddr624AndFds
        (readFileSpecPlaced cliIo.rd cliWrOk
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  let H := cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)
  rcases h2k_hole2_hReadSatK mpl mmpl hLs hMm W γ tp with ⟨fn, hfn, hOkK⟩
  have hfn' := cliGhostExterns_readFile_some (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W) rfl
  have hfnEq : fn = h2k_readFileFixedGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
      (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack :=
    Option.some.inj (hfn.symm.trans hfn')
  subst hfnEq
  have hFdsK : HookSat H lsReadFileSym
      (withFdsGe3Closed
        (h2k_readFileSpecK cliIo.rd cliWrOk
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))) :=
    ⟨_, hfn,
     hookOk_withFdsGe3Closed_of_fs_eq
       (h2k_readFileFixedGhostHookFineK_fs hole2_keepSub hole2_emptyProg f3TrialRxProg
         (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack)
       hOkK⟩
  exact hookSat_withLsRetAddr624AndFds_of_withFds_keepLrAndFds
    (fun _ hlr => h2lr_lsRetAddr624_keepSub_false hLs hlr) hFdsK

/-- Closes `MainIoOfPlacedFd` (`readStdin`, `readFile`, `writeFile`, `writeStdout`) on
`lsProg_617` at `ghFixed := h2k_ghFixedK mpl mmpl`. -/
theorem h2k_hole2_hioOfFd
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlacedFd
        (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)) _
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)) cliIo hole2_hookStack
        ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro W γ tp
  let H := cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)
  have hStdinPlain :=
    h2kb_hookOk_of_withKeepLrFalse
      (h2kb_readStdin_okK mpl mmpl hLs hMm γ tp)
      (h2kb_readStdin_pre_keepSub_false hLs)
  have hStdinFd :=
    hookOk_withFdsGe3Closed
      (fun _ hfds =>
        fdsGe3Closed_h2k_readStdinGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
          (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack
          hfds)
      hStdinPlain
  exact
    { readStdin :=
        subroutine_ok_rocl_of_plain <|
          ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617)
            ⟨_, cliGhostExterns_readStdin_some (h2k_ghFixedK mpl mmpl)
              (cliExternsPlaced mmpl W) rfl, hStdinFd⟩
            (by decide)
      readFile :=
        lsReadFile_rocl_of_hookSat (callerProg := lsProg_617 H) (i := 617)
          (h2k_hole2_readFileLit_hookSat_lsRetAddr624AndFds mpl mmpl hLs hMm W γ tp)
      writeFile := h2kb_hole2_hioOf_writeFile mpl mmpl hLs hMm W γ tp
      writeStdout := h2kb_hole2_hioOf_writeStdout mpl mmpl hLs hMm W γ tp }

/-- Witness-packaged `MainIoOfPlacedFd` predicate for `w : F3CliElfGhostWitnessK mpl mmpl`. -/
def F3WitnessMainIoFd {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    @MainIoOfPlacedFd (libsignalPlacementOf mpl w.hblk w.hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W)) cliIo w.hookStack
      ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd)

theorem f3WitnessMainIoFd_mkF3CliElfGhostWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    F3WitnessMainIoFd (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) :=
  h2k_hole2_hioOfFd mpl mmpl hLs hMm

/-! ## `initD3ScopedRun` `MainEntryBudgetFitsCapOf` -/

private theorem h2k_byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private def h2k_kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem h2k_utf8_eq (s : String) : utf8 s = h2k_kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, h2k_kutf8, List.utf8Encode, h2k_byteArray_toList_eq_data]

private theorem h2k_tri_utf8_eq (s : String) :
    CryptoVerification.LibsignalTripleRatchetRepr.utf8 s = h2k_kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [CryptoVerification.LibsignalTripleRatchetRepr.utf8, h2k_kutf8, List.utf8Encode,
    h2k_byteArray_toList_eq_data]

private theorem h2k_toString_one : toString (1 : Nat) = "1" := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  have hd1 : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.mpr rfl
  exact String.toList_inj.mp (by rw [ht1, hd1, String.toList_singleton]; rfl)

private def h2k_peerAddrV (P : Party) : AddrV :=
  ⟨utf8 (partyAddressName P), 1#8⟩

private theorem h2k_addrParse_bytesOfString (P : Party) :
    addrParse uuidTryParse (bytesOfString (partyAddress P).text) = some (h2k_peerAddrV P) := by
  have hpni : pniPrefix = [0x50#8, 0x4e#8, 0x49#8, 0x3a#8] := by
    unfold pniPrefix; rw [h2k_tri_utf8_eq]; rfl
  unfold bytesOfString addrParse serviceIdParse h2k_peerAddrV
  rw [hpni, h2k_utf8_eq]
  cases P <;>
    simp only [Address.text, partyAddress, partyAddressName, h2k_toString_one,
      String.toList_append] <;>
    rfl

private theorem h2k_parseArgs_init (P : Party) (dir : String) :
    parseArgs uuidTryParse ((Cmd.init (partyAddress P) dir).argv.map bytesOfString) =
      some (.init (h2k_peerAddrV P) (bytesOfString dir)) := by
  have hi : bytesOfString "init" = utf8 "init" := by
    unfold bytesOfString; rw [h2k_utf8_eq]; rfl
  have hk : utf8 "init" ≠ utf8 "keygen" := by
    rw [h2k_utf8_eq, h2k_utf8_eq]; decide
  have ha := h2k_addrParse_bytesOfString P
  simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hi, hk, ha, Option.map_some,
    ↓reduceIte]

private theorem h2k_pathStr_length (p : List (BitVec 8)) :
    (pathStr p).length = p.length := by
  unfold pathStr
  simp [String.length]

private theorem h2k_pId_ok (P : Party) :
    let p := pathOf (utf8 "identities") (addrValOf (h2k_peerAddrV P)).name
    (∀ b ∈ p, b.toNat < 128) ∧ p.length ≤ 64 := by
  dsimp only [addrValOf, h2k_peerAddrV, pathOf]
  simp only [h2k_utf8_eq]
  refine ⟨fun b hb => ?_, ?_⟩
  · have hall :
        ((if h2k_kutf8 "identities" = [] then h2k_kutf8 (partyAddressName P)
          else
            h2k_kutf8 "identities" ++ h2k_kutf8 "/" ++
              h2k_kutf8 (partyAddressName P)).all
          fun x => decide (x.toNat < 128)) = true := by
      cases P <;> decide
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · cases P <;> decide

private theorem h2k_pSess_ok (P : Party) :
    let p := pathOf (utf8 "sessions") (addressText (addrValOf (h2k_peerAddrV P)))
    (∀ b ∈ p, b.toNat < 128) ∧ p.length ≤ 64 := by
  dsimp only [addrValOf, h2k_peerAddrV, addressText, decimalText, pathOf]
  rw [show (1#8 : BitVec 8).toNat = 1 from rfl, h2k_toString_one]
  simp only [h2k_utf8_eq]
  refine ⟨fun b hb => ?_, ?_⟩
  · have hall :
        ((if h2k_kutf8 "sessions" = [] then
            h2k_kutf8 (partyAddressName P) ++ h2k_kutf8 "." ++ h2k_kutf8 "1"
          else
            h2k_kutf8 "sessions" ++ h2k_kutf8 "/" ++
              (h2k_kutf8 (partyAddressName P) ++ h2k_kutf8 "." ++ h2k_kutf8 "1")).all
          fun x => decide (x.toNat < 128)) = true := by
      cases P <;> decide
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · cases P <;> decide

private theorem h2k_namedWrites_pair_bounds
    {p1 v1 p2 v2 : List (BitVec 8)}
    (h1 : (∀ b ∈ p1, b.toNat < 128) ∧ p1.length ≤ 64)
    (h2 : (∀ b ∈ p2, b.toNat < 128) ∧ p2.length ≤ 64) :
    (namedWrites [(p1, v1), (p2, v2)]).length ≤ 4 ∧
      ∀ pw ∈ namedWrites [(p1, v1), (p2, v2)], pw.1.length ≤ 64 := by
  have hasc : ∀ w ∈ [(p1, v1), (p2, v2)], ∀ b ∈ w.1, b.toNat < 128 := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact h1.1
    · exact h2.1
  rw [namedWrites_ascii _ hasc]
  refine ⟨by simp only [List.map, List.length_cons, List.length_nil]; omega, fun pw hpw => ?_⟩
  simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hpw
  rcases hpw with rfl | rfl
  · rw [h2k_pathStr_length]; exact h1.2
  · rw [h2k_pathStr_length]; exact h2.2

private theorem h2k_namedWrites_singleton_bounds
    {p1 v1 : List (BitVec 8)}
    (h1 : (∀ b ∈ p1, b.toNat < 128) ∧ p1.length ≤ 64) :
    (namedWrites [(p1, v1)]).length ≤ 4 ∧
      ∀ pw ∈ namedWrites [(p1, v1)], pw.1.length ≤ 64 := by
  have hasc : ∀ w ∈ [(p1, v1)], ∀ b ∈ w.1, b.toNat < 128 := by
    intro w hw
    simp only [List.mem_singleton] at hw
    subst hw
    exact h1.1
  rw [namedWrites_ascii _ hasc]
  refine ⟨by simp only [List.map, List.length_cons, List.length_nil]; omega, fun pw hpw => ?_⟩
  simp only [List.map, List.mem_singleton] at hpw
  subst hpw
  rw [h2k_pathStr_length]
  exact h1.2

private theorem h2k_initD3_nwDom
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) (nw : List (String × List (BitVec 8))) (out : List (BitVec 8))
    (hi : CliInitD3Inputs ⟨W.C, W.Q⟩ i)
    (ha : runAns (cliRunSemD2c_placed X W) i = some (some (nw, out))) :
    nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64 := by
  rcases hi with ⟨st, files, t, -, -, -, heq⟩
  have hargv : i.argv = (Cmd.init (partyAddress st.party.other) bundleDir).argv := heq.1
  unfold runAns at ha
  rw [hargv, h2k_parseArgs_init st.party.other bundleDir] at ha
  dsimp only at ha
  rcases hown : StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "address") with
    _ | ownB
  · rw [hown] at ha; cases ha
  · rw [hown] at ha; dsimp only at ha
    rcases hme : addrParse uuidTryParse ownB with _ | meV
    · rw [hme] at ha; cases ha
    · rw [hme] at ha; dsimp only at ha
      rcases hbv : readBundleV (runFiles i) (bytesOfString bundleDir)
          (h2k_peerAddrV st.party.other).device with _ | bv
      · rw [hbv] at ha; cases ha
      · rw [hbv] at ha; dsimp only at ha
        change finish (initDef X ⟨W.C, W.Q⟩ (runFiles i)
            (addrValOf (h2k_peerAddrV st.party.other)) (addrValOf meV) bv (coinsOf i))
          (fun _ => []) = some (some (nw, out)) at ha
        rcases hinit : initDef X ⟨W.C, W.Q⟩ (runFiles i)
            (addrValOf (h2k_peerAddrV st.party.other)) (addrValOf meV) bv (coinsOf i) with
          _ | (_ | ⟨g', v⟩)
        · rw [hinit] at ha; cases ha
        · rw [hinit] at ha; cases ha
        · rw [hinit] at ha
          simp only [finish, Option.some.injEq, Prod.mk.injEq] at ha
          rcases ha with ⟨rfl, _⟩
          unfold initDef at hinit
          dsimp only at hinit
          split at hinit
          · cases hinit
          · split at hinit
            · cases hinit
            · cases hinit
            · split at hinit
              · split at hinit
                · cases hinit
                · next x gs _ =>
                  injection hinit with h1
                  injection h1 with h2
                  obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                  unfold IdGhost.saveUpd
                  split
                  · have hw :
                        ({ identity :=
                             { own := StoresGhost.opened.identity.own,
                               peers := StoresGhost.opened.identity.peers.put
                                 (addrValOf (h2k_peerAddrV st.party.other)).name
                                 bv.idKey.serialize },
                           signed := StoresGhost.opened.signed,
                           kyber := StoresGhost.opened.kyber,
                           oneTime := StoresGhost.opened.oneTime,
                           sessions := StoresGhost.opened.sessions.put
                             (addressText (addrValOf (h2k_peerAddrV st.party.other)))
                             (CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) gs),
                           pub := StoresGhost.opened.pub } : StoresGhost).writes =
                        [(pathOf (utf8 "identities")
                            (addrValOf (h2k_peerAddrV st.party.other)).name,
                          bv.idKey.serialize),
                         (pathOf (utf8 "sessions")
                            (addressText (addrValOf (h2k_peerAddrV st.party.other))),
                          CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) gs)] := rfl
                    rw [hw]
                    exact h2k_namedWrites_pair_bounds
                      (h2k_pId_ok st.party.other) (h2k_pSess_ok st.party.other)
                  · have hw :
                        ({ identity := StoresGhost.opened.identity,
                           signed := StoresGhost.opened.signed,
                           kyber := StoresGhost.opened.kyber,
                           oneTime := StoresGhost.opened.oneTime,
                           sessions := StoresGhost.opened.sessions.put
                             (addressText (addrValOf (h2k_peerAddrV st.party.other)))
                             (CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) gs),
                           pub := StoresGhost.opened.pub } : StoresGhost).writes =
                        [(pathOf (utf8 "sessions")
                            (addressText (addrValOf (h2k_peerAddrV st.party.other))),
                          CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) gs)] := rfl
                    rw [hw]
                    exact h2k_namedWrites_singleton_bounds (h2k_pSess_ok st.party.other)
              · cases hinit

private theorem h2k_runEnv_init_eq
    {a₁ a₂ : RunArmEnvs} {g : RunCall} {peerV : AddrV} {dir : List (BitVec 8)}
    (hpre : a₁.pre = a₂.pre)
    (hi1 : a₁.init1 = a₂.init1)
    (hi2 : a₁.init2 = a₂.init2)
    (hi3 : a₁.init3 = a₂.init3)
    (hc : g.c = .init peerV dir) :
    RunEnv a₁ g = RunEnv a₂ g := by
  have h3 : ∀ meV, RunInit3Env a₁ g meV peerV dir = RunInit3Env a₂ g meV peerV dir := fun meV => by
    funext evs; unfold RunInit3Env; rw [hi3]
  have h2 : ∀ meV, RunInit2ChainEnv a₁ g meV peerV dir = RunInit2ChainEnv a₂ g meV peerV dir :=
    fun meV => by
      funext evs; unfold RunInit2ChainEnv; rw [hi2, h3 meV]
  have harm : ∀ me, RunArmAtMeEnv a₁ g me = RunArmAtMeEnv a₂ g me := fun me => by
    funext evs; unfold RunArmAtMeEnv; rw [hc]; dsimp only
    cases me with
    | none => dsimp only; rw [hi1]
    | some meV meG => dsimp only; rw [hi1, h2 meV]
  have hdisp : RunDispatchEnv a₁ g = RunDispatchEnv a₂ g := by
    funext evs; unfold RunDispatchEnv
    cases StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") with
    | error _ => rfl
    | ok ownB =>
      dsimp only
      cases addrParse uuidTryParse ownB with
      | none => dsimp only; rw [harm]
      | some meV => dsimp only; simp only [harm]
  unfold RunEnv RunCoreEnv
  rw [hpre, hdisp]

/-- `MainEntryBudgetFitsCapOf` for `initD3ScopedRun` at `canonOrFallbackRunEnvExact' pksmEnv`,
independent of `pksmEnv` and `decryptPrekey` slot envelopes (`g.c = .init _ _`). -/
theorem h2k_fitCap_initD3
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length →
      (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (pksmEnv : PksmGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
        (binaryKitRunSlotEnvsExact W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
          (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
        pksmEnv (cliRunSemD2c_placed X W)))
      (initD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))) := by
  let _ : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  have h0 :=
    mainEntryBudgetFitsCapOf_initD3ScopedRun_fixed
      (default : Image) (cliRunSemD2c_placed X W) X W
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
      cliRunBudgets
      (realCliDecPkBinaryWideSlotEnvFixed X W)
      (h2k_initD3_nwDom X W)
  intro i hok
  refine ⟨(h0 i hok).1, fun hne => ?_⟩
  refine ⟨((h0 i hok).2 hne).1, fun vcap evs_c c hc hv hp => ?_⟩
  have hm2 := ((h0 i hok).2 hne).2 vcap evs_c c hc hv hp
  refine ⟨hm2.1, fun evs_m3 hm3 => ?_⟩
  have hm3' := hm2.2 evs_m3 hm3
  refine ⟨hm3'.1, fun hin a resP callP storesP inpP coinsP hrun => ?_⟩
  rcases hrun.1 with ⟨st, files, t, -, -, -, heq⟩
  have hargv : i.argv = (Cmd.init (partyAddress st.party.other) bundleDir).argv := heq.1
  have hp' := hp
  rw [hargv, h2k_parseArgs_init st.party.other bundleDir] at hp'
  injection hp' with hc_eq
  let g : RunCall :=
    { i := i, c := c, a := a,
      res := resP, call := callP, stores := storesP, inp := inpP, coins := coinsP }
  have hEq :
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          pksmEnv (cliRunSemD2c_placed X W))
        g =
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsFixed W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (realCliDecPkBinaryWideSlotEnvFixed X W))
          PksmTryFromEnv (cliRunSemD2c_placed X W))
        g :=
    h2k_runEnv_init_eq rfl rfl rfl rfl hc_eq.symm
  have hgoal := hm3'.2 hin a resP callP storesP inpP coinsP hrun
  dsimp only at hgoal ⊢
  rwa [hEq]

/-! ## Witness-Parametric (`F3CliElfGhostWitnessK`) Spine-A Theorems -/

/-- Closes `GhostMainArmsOfWitnessK.hmain` from `hSpineB : h2ki_SpineBCanonSliceK w`. -/
theorem h2k_ghost_hmain_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hIoFd : F3WitnessMainIoFd w)
    (hSpineB : h2ki_SpineBCanonSliceK w) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
      617 cliProcessInputs (LibsignalFrozen mpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk cliBudgetLimits := by
  refine (mainOkCliExtPqB2NeedLocksPlacedAt_iff mpl mmpl
    (fun W => cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
    617 cliProcessInputs (LibsignalFrozen mpl)
    (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk cliBudgetLimits).mp ?_
  exact
    mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_cliBudgetLimits_of_kitEnvFits_and_runTightOf_preFd
      w.hblk w.hext_nodup
      (@instLsCodeInvFrozen (libsignalPlacementOf mpl w.hblk w.hext_nodup))
      (fun _ => w.ghFixed)
      (fun X W => @fits2_mkBinaryKitRealCalleeEnvsDecPk
        (libsignalPlacementOf mpl w.hblk w.hext_nodup)
        (@cliDecPkCanonSlotEnvExact' (libsignalPlacementOf mpl w.hblk w.hext_nodup) X W)
        (default : Image) (cliRunSemD2c_placed X W) X W)
      (canonOrFallbackRunEnvExact' PksmTryFromEnv mpl mmpl cliElfImage.brkStart w.hblk w.hext_nodup)
      rfl
      (fun _ γ tp => F3CliElfGhostWitnessK.hG w hLs γ tp)
      hIoFd
      (fun files path _ h => boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo files path h)
      w.hMainStk
      (fun _ X W i hi =>
        @realCliMainBinaryKitEnvOfExact'_fitsEnv_cliBudgetLimits_closed
          (libsignalPlacementOf mpl w.hblk w.hext_nodup)
          (default : Image) (cliRunSemD2c_placed X W) X W i hi)
      (fun _ X W γ tp g hi hparse hin _ evs hevs =>
        @hole_hmain_runEnvExact'_sub_binaryKit_closed
          (libsignalPlacementOf mpl w.hblk w.hext_nodup) _ PksmTryFromEnv
          (default : Image) (cliRunSemD2c_placed X W) X W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
          g hi hparse hin rfl rfl evs hevs)
      (fun h547 X W γ tp => hSpineB h547 X W γ tp)

/-- Closes entry-guarded `MainOkCliF3PqB2NeedLocksPlacedAtG` across `w.hTrFrozen` from `hSpineB`. -/
theorem h2k_hmain_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hIoFd : F3WitnessMainIoFd w)
    (hSpineB : h2ki_SpineBCanonSliceK w) :
    MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  mainOkCliF3PqG_of_block617TransferFixedG w.hTrFrozen
    (h2k_ghost_hmain_of_witnessK w hLs hIoFd hSpineB)

/-- Closes `GhostMainInitSemOfWitnessK w` from `hSpineB : h2ki_SpineBCanonSliceK w`. -/
theorem h2k_ghost_hinitSem_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hIoFd : F3WitnessMainIoFd w)
    (hSpineB : h2ki_SpineBCanonSliceK w) :
    GhostMainInitSemOfWitnessK w := by
  intro h547 X W
  refine ⟨cliRunSemD2c_placed X W, initRunSemOk_of_filesOk₀ rfl rfl rfl, ?_⟩
  exact ghostMainSubroutineD3_of_domScopedRunTight_preFd w.hblk w.hext_nodup w.ghFixed
    (@instLsCodeInvFrozen (libsignalPlacementOf mpl w.hblk w.hext_nodup))
    (CliInitD3Inputs ⟨W.C, W.Q⟩) (cliRunSemD2c_placed X W)
    rfl (F3CliElfGhostWitnessK.hG w hLs) (hIoFd W) w.hMainStk
    (fun γ tp => h2k_fitCap_initD3 w.hblk w.hext_nodup _ X W γ tp)
    (fun γ tp => hSpineB h547 X W γ tp)

/-- Closes entry-guarded `MainInitSemF3G` across `w.hTrFrozen` from `hSpineB : h2ki_SpineBCanonSliceK w`. -/
theorem h2k_hinitSem_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hIoFd : F3WitnessMainIoFd w)
    (hSpineB : h2ki_SpineBCanonSliceK w) :
    MainInitSemF3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  intro h547 X W
  obtain ⟨S, hSem, hOk⟩ := h2k_ghost_hinitSem_of_witnessK w hLs hIoFd hSpineB h547 X W
  exact ⟨S, hSem, w.hTrFrozen W (initD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)) hOk⟩

/-- Generic Spine-A Ghost Block-`617` closer for D3 `RunSem` slices (`hoverD3`, `huntyped`,
`hpathB`, `hvalidMatch`) at `w : F3CliElfGhostWitnessK`. -/
theorem h2k_ghost_d3MainSubroutine_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hIoFd : F3WitnessMainIoFd w)
    {SemOf : CliHooks → RunSem}
    {RunEnvOf : CliHooks → GhostName → BitVec 64 → RunCall → List AllocEvent → Prop}
    (DomOf : CliHooks → Inputs → Prop)
    (hfitCap : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
        (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse (RunEnvOf W γ tp)
        (domScopedRun (DomOf W) (runRel (SemOf W))))
    (hSpineB : h2ki_SpineBRunTightOfSemK w SemOf RunEnvOf)
    (h547 : mpl.base 547 ≠ 0#64) (W : CliHooks) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W')) 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (domScopedRun (DomOf W) (runRel (SemOf W))) cliProcessInputs) :=
  ghostMainSubroutineD3_of_domScopedRunTight_preFd w.hblk w.hext_nodup w.ghFixed
    (@instLsCodeInvFrozen (libsignalPlacementOf mpl w.hblk w.hext_nodup))
    (DomOf W) (SemOf W) rfl (F3CliElfGhostWitnessK.hG w hLs) (hIoFd W) w.hMainStk
    (hfitCap W) (hSpineB h547 W)

/-- Generic Spine-A Real `F3CodeOk` (entry-guarded) closer for D3 `RunSem` slices (`hoverD3`,
`huntyped`, `hpathB`, `hvalidMatch`) at `w : F3CliElfGhostWitnessK`. -/
theorem h2k_d3MainSubroutine_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hIoFd : F3WitnessMainIoFd w)
    {SemOf : CliHooks → RunSem}
    {RunEnvOf : CliHooks → GhostName → BitVec 64 → RunCall → List AllocEvent → Prop}
    (DomOf : CliHooks → Inputs → Prop)
    (hfitCap : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
        (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse (RunEnvOf W γ tp)
        (domScopedRun (DomOf W) (runRel (SemOf W))))
    (hSpineB : h2ki_SpineBRunTightOfSemK w SemOf RunEnvOf)
    (h547 : mpl.base 547 ≠ 0#64) (W : CliHooks) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (withEntryGuard (F3MemsetMemcpyEntryLrFalse mmpl)
          (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (F3CodeOk mpl mmpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
            cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
            (domScopedRun (DomOf W) (runRel (SemOf W))) cliProcessInputs)) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  w.hTrFrozen W (domScopedRun (DomOf W) (runRel (SemOf W)))
    (h2k_ghost_d3MainSubroutine_of_witnessK w hLs hIoFd DomOf hfitCap hSpineB h547 W)

/-- Untyped D3 `RunEnv` family at `[LibsignalPlacement]`, matching `hole_m24slot_untyped_assembly`. -/
abbrev h2k_untypedRunEnvAt
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    RunCall → List AllocEvent → Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  RunEnv
    (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (binaryKitRunSlotEnvsExact W
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliRunBudgets_placed (realCliInitBinarySlotEnvFixed W)
        (DecPkD3UntypedEnvOf
          (A := (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc)
          cliRunBudgets_placed (ReadFileRuleEnvFixed cliIo.rd)
          SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
      PksmTryFromEnv (cliRunSemD3 W))

/-- Closes `GhostMainOkUntypedOfWitnessK w` from `hSpineBUntyped`. -/
theorem h2k_ghost_huntyped_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hIoFd : F3WitnessMainIoFd w)
    (hSpineBUntyped :
      h2ki_SpineBRunTightOfSemK w cliRunSemD3
        (h2k_untypedRunEnvAt (mmpl := mmpl) w.hblk w.hext_nodup)) :
    GhostMainOkUntypedOfWitnessK w :=
  h2k_ghost_d3MainSubroutine_of_witnessK w hLs hIoFd
    (fun W => CliPqOrD3RecvInputs ⟨W.C, W.Q⟩)
    (fun W γ tp =>
      @hole_g5a_untyped_fitsCap (libsignalPlacementOf mpl w.hblk w.hext_nodup) W
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
    hSpineBUntyped

/-- Closes entry-guarded `MainOkUntypedD3F3G` across `w.hTrFrozen` from `hSpineBUntyped`. -/
theorem h2k_huntyped_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hIoFd : F3WitnessMainIoFd w)
    (hSpineBUntyped :
      h2ki_SpineBRunTightOfSemK w cliRunSemD3
        (h2k_untypedRunEnvAt (mmpl := mmpl) w.hblk w.hext_nodup)) :
    MainOkUntypedD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  h2k_d3MainSubroutine_of_witnessK w hLs hIoFd
    (fun W => CliPqOrD3RecvInputs ⟨W.C, W.Q⟩)
    (fun W γ tp =>
      @hole_g5a_untyped_fitsCap (libsignalPlacementOf mpl w.hblk w.hext_nodup) W
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
    hSpineBUntyped

/-! ## Concrete `h2k_ghFixedK` (`cliElfBytes`) Spine-A Closers -/

/-- Closes `h2asm_GhostMainArmsK.hmain` at `h2k_ghFixedK` from `hSpineB`. -/
theorem h2k_ghost_hmain_cliElfK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hSpineB :
      h2ki_SpineBCanonSliceAt (mmpl := mmpl)
        (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        (letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
         h2k_ghFixedK mpl mmpl)) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      617 cliProcessInputs (LibsignalFrozen mpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk cliBudgetLimits := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  refine (mainOkCliExtPqB2NeedLocksPlacedAt_iff mpl mmpl
    (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
    617 cliProcessInputs (LibsignalFrozen mpl)
    (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk cliBudgetLimits).mp ?_
  have hG := h2kb_hole2_hG mpl mmpl hLs hMm
  exact
    mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_cliBudgetLimits_of_kitEnvFits_and_runTightOf_preFd
      (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      (@instLsCodeInvFrozen
        (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)))
      (fun _ => h2k_ghFixedK mpl mmpl)
      (fun X W => @fits2_mkBinaryKitRealCalleeEnvsDecPk
        (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
        (@cliDecPkCanonSlotEnvExact'
          (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)) X W)
        (default : Image) (cliRunSemD2c_placed X W) X W)
      (canonOrFallbackRunEnvExact' PksmTryFromEnv mpl mmpl cliElfImage.brkStart
        (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
      rfl
      (fun _ γ tp => hG γ tp)
      (h2k_hole2_hioOfFd mpl mmpl hLs hMm)
      (fun files path _ h => boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo files path h)
      hole2_hMainStk
      (fun _ X W i hi =>
        @realCliMainBinaryKitEnvOfExact'_fitsEnv_cliBudgetLimits_closed
          (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
          (default : Image) (cliRunSemD2c_placed X W) X W i hi)
      (fun _ X W γ tp g hi hparse hin _ evs hevs =>
        @hole_hmain_runEnvExact'_sub_binaryKit_closed
          (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)) _ PksmTryFromEnv
          (default : Image) (cliRunSemD2c_placed X W) X W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
          g hi hparse hin rfl rfl evs hevs)
      (fun h547 X W γ tp => hSpineB h547 X W γ tp)

/-- Closes `MainOkCliF3PqB2NeedLocksPlacedAtG` at `h2k_ghFixedK` from `hBranch2` and `hSpineB`. -/
theorem h2k_hmain_cliElfK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hSpineB :
      h2ki_SpineBCanonSliceK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)) :
    MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  h2asm_hmain_cliElfKG mpl mmpl hLs hMm hBranch2
    (h2k_ghost_hmain_cliElfK mpl mmpl hLs hMm hSpineB)

/-- Closes `h2asm_GhostMainInitSemK` at `h2k_ghFixedK` from `hSpineB`. -/
theorem h2k_ghost_hinitSem_cliElfK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hSpineB :
      h2ki_SpineBCanonSliceAt (mmpl := mmpl)
        (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        (letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
         h2k_ghFixedK mpl mmpl)) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2asm_GhostMainInitSemK mpl mmpl := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hG := h2kb_hole2_hG mpl mmpl hLs hMm
  intro h547 X W
  refine ⟨cliRunSemD2c_placed X W, initRunSemOk_of_filesOk₀ rfl rfl rfl, ?_⟩
  exact ghostMainSubroutineD3_of_domScopedRunTight_preFd
    (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs) (h2k_ghFixedK mpl mmpl)
    (@instLsCodeInvFrozen
      (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)))
    (CliInitD3Inputs ⟨W.C, W.Q⟩) (cliRunSemD2c_placed X W)
    rfl hG (h2k_hole2_hioOfFd mpl mmpl hLs hMm W)
    hole2_hMainStk
    (fun γ tp =>
      h2k_fitCap_initD3 (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs) _ X W γ tp)
    (fun γ tp => hSpineB h547 X W γ tp)

/-- Closes `MainInitSemF3G` at `h2k_ghFixedK` from `hBranch2` and `hSpineB`. -/
theorem h2k_hinitSem_cliElfK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hSpineB :
      h2ki_SpineBCanonSliceK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)) :
    MainInitSemF3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  h2k_hinitSem_of_witnessK
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hLs
    (f3WitnessMainIoFd_mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hSpineB

/-- Closes `h2asm_GhostMainOkUntypedK` at `h2k_ghFixedK` from `hSpineBUntyped`. -/
theorem h2k_ghost_huntyped_cliElfK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hSpineBUntyped :
      h2ki_SpineBRunTightOfSemAt (mmpl := mmpl)
        (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        (letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
         h2k_ghFixedK mpl mmpl)
        cliElfImage.brkStart cliRunSemD3
        (h2k_untypedRunEnvAt (mmpl := mmpl) (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2asm_GhostMainOkUntypedK mpl mmpl := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hG := h2kb_hole2_hG mpl mmpl hLs hMm
  intro h547 W
  exact ghostMainSubroutineD3_of_domScopedRunTight_preFd
    (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs) (h2k_ghFixedK mpl mmpl)
    (@instLsCodeInvFrozen
      (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)))
    (CliPqOrD3RecvInputs ⟨W.C, W.Q⟩) (cliRunSemD3 W)
    rfl hG (h2k_hole2_hioOfFd mpl mmpl hLs hMm W)
    hole2_hMainStk
    (fun γ tp =>
      @hole_g5a_untyped_fitsCap
        (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)) W
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
    (hSpineBUntyped h547 W)

/-- Closes `MainOkUntypedD3F3G` at `h2k_ghFixedK` from `hBranch2` and `hSpineBUntyped`. -/
theorem h2k_huntyped_cliElfK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hSpineBUntyped :
      h2ki_SpineBRunTightOfSemK
        (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
        cliRunSemD3
        (h2k_untypedRunEnvAt (mmpl := mmpl) (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))) :
    MainOkUntypedD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  h2k_huntyped_of_witnessK
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hLs
    (f3WitnessMainIoFd_mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hSpineBUntyped

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineA
