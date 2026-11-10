/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5bCut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2LsRetAddrKeep
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinCanonPrime

/-!
# Spine-B (`signal_session::run`, Block `579`) Bridge (`ElfSlicesPqOomH2KSpineB`)

**Checked by Lean.**

Bridges `RunOkNoMatchPlacedBudgetFd.hrun_cli_sem_full_placed_fd` and
`hrun_cli_d2c_tight_full_placed_fd` to the Spine-B and Spine-C interfaces in
`ElfSlicesPqOomH2KIfaces`:
1. Closes `CliRunHooksBundleFd` unconditionally at `ghFixed := h2k_ghFixedK mpl mmpl`
   (`h2ksb_hole2_hHooksBundleFd`).
2. Reduces `h2ki_RunTightAt579PreFd`, `h2ki_SpineBCanonSlice{At,K}` (`hmain` and `hinitSem`), and
   `h2ki_SpineBRunTightOfSem{At,K}` (`huntyped`, `hoverD3`, `hpathB`, `hvalidMatch`) to
   `CliPubCalleesFrozenPlacedFd`, `SpineBPureFsCallees`, and the four Spine-C slot contracts
   (`464`, `463`, `521`, `520`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineB

open Arm64 (GhostName HookSat subroutine_ok)
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries (mallocngLib)
open CryptoVerification
  (LibsignalFullPlacement LibsignalHooks LibsignalPlacement blkPl_111 libsignalMutatedBlocks
   libsignalSessionExterns lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliIo cliRunBudgets cliRunBudgets_placed cliRunNeeds cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_590)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecSigGhost EncGhost PksmGhost RunSem mkSlot)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (CanonicalOrFallbackPksmEnv)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom (cliDecPkCanonSlotEnvExact')
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
  (DecPkD3UntypedEnvOf PqxdhAcceptBadKemErrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (defaultExtrasF3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (cliRunSemD3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (hookSat_withLsRetAddr624AndFds_of_withFds_keepLrAndFds withLsRetAddr624AndFds)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
  (pksmSlotSpecPlacedOkFs tryFromPlacedSpecOkFs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd
  (CliPubCalleesFrozenPlacedFd CliRunHooksBundleFd hrun_cli_sem_full_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudgetFd (RunArmEnvs RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs decSigSlotSpecFrozenPlaced encSlotSpecPlaced slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5bCut
  (g5ba_decSigSlotSpecFrozenPlaced_d2c_eq_d3 g5ba_encSlotSpecPlaced_d2c_eq_d3)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
  (h2asm_Branch2HookReplaysK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
  (h2kb_alloc_pre_keepSub_false h2kb_dealloc_pre_keepSub_false h2kb_hookOk_of_withKeepLrFalse
   h2kb_hole2_runHooksPlaced h2kb_realloc_pre_keepSub_false)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit
  (h2k_hole2_hReadSatK_withFds)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (h2k_ghFixedK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (CliInitSlotOkPlacedPreFd DecPkD2cSlotOkFrozenPlacedAtPreFd h2ki_DecryptSignalSlot463OkAtPreFd
   h2ki_EncryptSlot464OkAtPreFd h2ki_RunTightAt579PreFd h2ki_SpineBCanonSliceAt
   h2ki_SpineBCanonSliceK h2ki_SpineBRunTightOfSemAt h2ki_SpineBRunTightOfSemK
   h2ki_UntypedDecPkSlot520OkK h2ki_W1EncryptSlot464OkK h2ki_W2DecryptSignalSlot463OkK
   h2ki_W3InitSlot521OkK h2ki_W4DecPkCanonSlot520OkK slotWithFdsGe3Closed slotWithPreFdsGe3Closed)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
  (F3CliElfGhostWitnessK mkF3CliElfGhostWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2LsRetAddrKeep
  (h2lr_lsRetAddr624_keepSub_false)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact cliDecryptSignalBinaryKitSlotEnvExact cliEncryptBinaryKitSlotEnvExact
   libsignalFullPlacementOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinCanonPrime
  (canonOrFallbackRunEnvExact')

/-! ## Plain Allocator Bridges and `CliRunHooksBundleFd` -/

/-- Lift `w.hGSpqrK` (`h2k_CliGhostSpqrAllocHooksK`) to plain `CliGhostSpqrAllocHooks` via
`h2lr_lsRetAddr624_keepSub_false`. -/
theorem h2ksb_witness_hGSpqr {mpl mmpl : MultiPlacement}
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

/-- Lift `w.hGK` (`h2k_CliGhostAllocHooksK`) to plain `CliGhostAllocHooks`. -/
theorem h2ksb_witness_hG {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
    ∀ (γ : GhostName) (tp : BitVec 64),
      CliGhostAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits w.ghFixed :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  fun γ tp => (h2ksb_witness_hGSpqr w hLs γ tp).toCliGhostAllocHooks

/-- `HookSat` on `lsReadFileSym` at `h2k_ghFixedK mpl mmpl` (`0` `hBranch2`) for
`withLsRetAddr624AndFds (readFileSpecPlaced …)` at `cliRunBudgets.readFile`. -/
theorem h2ksb_hole2_readFile_hookSat_lsRetAddr624AndFds
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
  exact hookSat_withLsRetAddr624AndFds_of_withFds_keepLrAndFds
    (fun _ hlr => h2lr_lsRetAddr624_keepSub_false hLs hlr)
    (h2k_hole2_hReadSatK_withFds mpl mmpl hLs hMm W γ tp)

/-- Closes `CliRunHooksBundleFd` at `ghFixed := h2k_ghFixedK mpl mmpl` from
`h2kb_hole2_runHooksPlaced` and `h2ksb_hole2_readFile_hookSat_lsRetAddr624AndFds`. -/
theorem h2ksb_hole2_hHooksBundleFd
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundleFd
        (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
        mmpl (h2k_ghFixedK mpl mmpl) W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  fun W γ tp =>
    { runHooks := h2kb_hole2_runHooksPlaced mpl mmpl hLs hMm W γ tp
      readFileSat := h2ksb_hole2_readFile_hookSat_lsRetAddr624AndFds mpl mmpl hLs hMm W γ tp }

/-- Witness-packaged `CliRunHooksBundleFd` predicate for `w : F3CliElfGhostWitnessK mpl mmpl`. -/
def F3WitnessRunHooksBundleFd {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    @CliRunHooksBundleFd (libsignalPlacementOf mpl w.hblk w.hext_nodup)
      mmpl w.ghFixed W fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd)

theorem f3WitnessRunHooksBundleFd_mkF3CliElfGhostWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    F3WitnessRunHooksBundleFd (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) :=
  h2ksb_hole2_hHooksBundleFd mpl mmpl hLs hMm

/-! ## Pure-Callee `fs`-Preservation Bundle (`SpineBPureFsCallees`) -/

/-- Bundle of pure-callee `fs`-preservation contracts called from `signal_session::run`
(Block `579`): `kemDeserialize` (Block `590`), `tryFrom` (Block `85`), and `pksmTryFrom`
(Block `111`). -/
structure SpineBPureFsCallees [LibsignalPlacement]
    {M : AllocCostModel} (H : LibsignalHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (sEnvs : RunSlotEnvs) (PksmEnv : PksmGhost → List AllocEvent → Prop)
    (S : RunSem) (decPkNeed : Nat) : Prop where
  kemDeserialize :
    (slotWithFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).kemDeserialize).OkPlaced
      (lsProg_579 H) (blkPl_590).base
  tryFrom :
    subroutine_ok (lsProg_579 H) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim))
  pksmTryFrom :
    subroutine_ok (lsProg_579 H) blkPl_111.base
      (pksmSlotSpecPlacedOkFs M A lim PksmEnv S)

/-! ## Core `h2ki_RunTightAt579PreFd` Discharger -/

/-- Discharges `h2ki_RunTightAt579PreFd` via
`RunOkNoMatchPlacedBudgetFd.hrun_cli_sem_full_placed_fd` for any `S : RunSem` and
`aEnvs : RunSem → RunArmEnvs`. -/
theorem h2ksb_runTightAt579PreFd_of_slots
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (W : CliHooks)
    (sEnvs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      RunSlotEnvs)
    (aEnvs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      RunSem → RunArmEnvs)
    (S : RunSem) {decPkNeed : Nat}
    (h547 : mpl.base 547 ≠ 0#64)
    (hHooks :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliRunHooksBundleFd mmpl ghFixed W A lim (ReadFileRuleEnvFixed cliIo.rd))
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliPubCalleesFrozenPlacedFd mmpl ghFixed A lim
        (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) sEnvs aEnvs W)
    (henc :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).encrypt).OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hdecSig :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).decryptSignal).OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hinit :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).initiate).OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521))
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).decryptPrekey).OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      SpineBPureFsCallees (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
        A lim sEnvs (aEnvs S).pksmTryFrom S decPkNeed) :
    h2ki_RunTightAt579PreFd hblk hext_nodup
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
      A lim
      (letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
       RunEnv (aEnvs S))
      S := by
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  exact hrun_cli_sem_full_placed_fd mmpl ghFixed W S h547 hHooks hpub
    henc hdecSig hinit hdecPkNeed hdecPk
    hpureFs.kemDeserialize hpureFs.tryFrom hpureFs.pksmTryFrom

/-! ## `h2ki_SpineBCanonSliceAt` and `h2ki_SpineBCanonSliceK` (`hmain` and `hinitSem`) -/

/-- Reduces `h2ki_SpineBCanonSliceAt` to the four Spine-C slot contracts (`464`, `463`, `521`,
`520` at `cliDecPkCanonSlotEnvExact'`), `CliPubCalleesFrozenPlacedFd`, and `SpineBPureFsCallees`. -/
theorem h2ksb_spineBCanonSliceAt_of_slots
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hHooks :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliRunHooksBundleFd mmpl ghFixed W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (ReadFileRuleEnvFixed cliIo.rd))
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
              (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
            (CanonicalOrFallbackPksmEnv PksmTryFromEnv))
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (CanonicalOrFallbackPksmEnv PksmTryFromEnv)
          (cliRunSemD2c_placed X W)
          (cliDecryptPrekeyNeed cliRunBudgets))
    (hW1 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        h2ki_EncryptSlot464OkAtPreFd
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          X W)
    (hW2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        h2ki_DecryptSignalSlot463OkAtPreFd
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          X W)
    (hW3 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliInitSlotOkPlacedPreFd mmpl ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (realCliInitBinarySlotEnvFixed W) X W)
    (hW4 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        DecPkD2cSlotOkFrozenPlacedAtPreFd
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) X W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliDecPkCanonSlotEnvExact' X W)) :
    h2ki_SpineBCanonSliceAt (mmpl := mmpl) hblk hext_nodup ghFixed := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  intro h547 X W γ tp
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  let S := cliRunSemD2c_placed X W
  let sEnvs := binaryKitRunSlotEnvsExact W A cliRunBudgets
    (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W)
  let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
  exact h2ksb_runTightAt579PreFd_of_slots hLs hblk hext_nodup ghFixed
    A cliBudgetLimits W sEnvs
    (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      sEnvs (CanonicalOrFallbackPksmEnv PksmTryFromEnv))
    S
    (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets)
    h547 (hHooks W γ tp) (hpub X W γ tp)
    (hW1 h547 X W γ tp)
    (hW2 h547 X W γ tp)
    (hW3 h547 X W γ tp S sEnvs needs rfl rfl rfl rfl rfl)
    (by decide)
    (hW4 h547 X W γ tp S needs sEnvs rfl rfl rfl rfl rfl)
    (hpureFs X W γ tp)

/-- Witness-packaged `h2ki_SpineBCanonSliceK w` closer from the four Spine-C slot contracts. -/
theorem h2ksb_spineBCanonSlice_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hHooksFd : F3WitnessRunHooksBundleFd w)
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl w.ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
              (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
            (CanonicalOrFallbackPksmEnv PksmTryFromEnv))
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (CanonicalOrFallbackPksmEnv PksmTryFromEnv)
          (cliRunSemD2c_placed X W)
          (cliDecryptPrekeyNeed cliRunBudgets))
    (hW1 : h2ki_W1EncryptSlot464OkK w)
    (hW2 : h2ki_W2DecryptSignalSlot463OkK w)
    (hW3 : h2ki_W3InitSlot521OkK w)
    (hW4 : h2ki_W4DecPkCanonSlot520OkK w) :
    h2ki_SpineBCanonSliceK w :=
  h2ksb_spineBCanonSliceAt_of_slots hLs w.hblk w.hext_nodup w.ghFixed
    hHooksFd hpub hpureFs hW1 hW2 hW3 hW4

/-- Concrete `h2ki_SpineBCanonSliceK` closer at `mkF3CliElfGhostWitnessK`. -/
theorem h2ksb_spineBCanonSlice_mkWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl (h2k_ghFixedK mpl mmpl)
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
              (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
            (CanonicalOrFallbackPksmEnv PksmTryFromEnv))
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (CanonicalOrFallbackPksmEnv PksmTryFromEnv)
          (cliRunSemD2c_placed X W)
          (cliDecryptPrekeyNeed cliRunBudgets))
    (hW1 : h2ki_W1EncryptSlot464OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hW2 : h2ki_W2DecryptSignalSlot463OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hW3 : h2ki_W3InitSlot521OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hW4 : h2ki_W4DecPkCanonSlot520OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)) :
    h2ki_SpineBCanonSliceK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) :=
  h2ksb_spineBCanonSlice_of_witnessK
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hLs
    (f3WitnessRunHooksBundleFd_mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hpub hpureFs hW1 hW2 hW3 hW4

/-! ## `h2ki_SpineBRunTightOfSemAt` and `h2ki_SpineBRunTightOfSemK` (D3 `RunSem` Slices) -/

/-- Discharges `h2ki_SpineBRunTightOfSemAt` for any `SemOf : CliHooks → RunSem` and
`sEnvsOf` / `PksmEnvOf`. -/
theorem h2ksb_spineBRunTightOfSemAt_of_slots
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (brkStart : BitVec 64)
    (SemOf : CliHooks → RunSem)
    (sEnvsOf :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliHooks → GhostName → BitVec 64 → RunSlotEnvs)
    (PksmEnvOf :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliHooks → GhostName → BitVec 64 → PksmGhost → List AllocEvent → Prop)
    {decPkNeed : Nat}
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hHooks :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliRunHooksBundleFd mmpl ghFixed W
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (ReadFileRuleEnvFixed cliIo.rd))
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (sEnvsOf W γ tp)
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (sEnvsOf W γ tp) (PksmEnvOf W γ tp))
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (sEnvsOf W γ tp) (PksmEnvOf W γ tp) (SemOf W) decPkNeed)
    (henc :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).encrypt).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hdecSig :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).decryptSignal).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hinit :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).initiate).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521))
    (hdecPk :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).decryptPrekey).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)) :
    h2ki_SpineBRunTightOfSemAt (mmpl := mmpl) hblk hext_nodup ghFixed brkStart SemOf
      (fun W γ tp =>
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (sEnvsOf W γ tp) (PksmEnvOf W γ tp) (SemOf W))) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  intro h547 W γ tp
  exact h2ksb_runTightAt579PreFd_of_slots hLs hblk hext_nodup ghFixed
    (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits W
    (sEnvsOf W γ tp)
    (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (sEnvsOf W γ tp) (PksmEnvOf W γ tp))
    (SemOf W)
    (decPkNeed := decPkNeed)
    h547 (hHooks W γ tp) (hpub W γ tp)
    (henc h547 W γ tp) (hdecSig h547 W γ tp) (hinit h547 W γ tp)
    hdecPkNeed (hdecPk h547 W γ tp) (hpureFs W γ tp)

/-- Witness-packaged `h2ki_SpineBRunTightOfSemK w` closer for D3 `RunSem` slices. -/
theorem h2ksb_spineBRunTightOfSem_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hHooksFd : F3WitnessRunHooksBundleFd w)
    (SemOf : CliHooks → RunSem)
    (sEnvsOf :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      CliHooks → GhostName → BitVec 64 → RunSlotEnvs)
    (PksmEnvOf :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      CliHooks → GhostName → BitVec 64 → PksmGhost → List AllocEvent → Prop)
    {decPkNeed : Nat}
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl w.ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (sEnvsOf W γ tp)
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (sEnvsOf W γ tp) (PksmEnvOf W γ tp))
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (sEnvsOf W γ tp) (PksmEnvOf W γ tp) (SemOf W) decPkNeed)
    (henc :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).encrypt).OkPlaced
          (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hdecSig :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).decryptSignal).OkPlaced
          (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hinit :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).initiate).OkPlaced
          (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521))
    (hdecPk :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).decryptPrekey).OkPlaced
          (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)) :
    h2ki_SpineBRunTightOfSemK w SemOf
      (fun W γ tp =>
        letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (sEnvsOf W γ tp) (PksmEnvOf W γ tp) (SemOf W))) :=
  h2ksb_spineBRunTightOfSemAt_of_slots hLs w.hblk w.hext_nodup w.ghFixed cliElfImage.brkStart
    SemOf sEnvsOf PksmEnvOf hdecPkNeed hHooksFd hpub hpureFs henc hdecSig hinit hdecPk

/-! ## D3 Untyped (`cliRunSemD3`) Specialization (`huntyped`) -/

/-- Transport `slotWithPreFdsGe3Closed` on `encSlotSpecPlaced` from `cliRunSemD2c_placed X W` to
`cliRunSemD3 W` (`g5ba_encSlotSpecPlaced_d2c_eq_d3`). -/
theorem h2ksb_encSlot464_d3_of_d2c [LibsignalPlacement]
    {M : AllocCostModel} {H : LibsignalHooks}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (EncEnv : EncGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h : (slotWithPreFdsGe3Closed
      (mkSlot (encSlotSpecPlaced A lim EncEnv (cliRunSemD2c_placed X W))
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt)).OkPlaced
      (lsProg_579 H) (lsmpl.base 464)) :
    (slotWithPreFdsGe3Closed
      (mkSlot (encSlotSpecPlaced A lim EncEnv (cliRunSemD3 W))
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed)).encrypt)).OkPlaced
      (lsProg_579 H) (lsmpl.base 464) := by
  change (slotWithPreFdsGe3Closed
    (mkSlot (encSlotSpecPlaced A lim EncEnv (cliRunSemD3 W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt)).OkPlaced
    (lsProg_579 H) (lsmpl.base 464)
  rw [← g5ba_encSlotSpecPlaced_d2c_eq_d3 A lim EncEnv X W]
  exact h

/-- Transport `slotWithPreFdsGe3Closed` on `decSigSlotSpecFrozenPlaced` from
`cliRunSemD2c_placed X W` to `cliRunSemD3 W` (`g5ba_decSigSlotSpecFrozenPlaced_d2c_eq_d3`). -/
theorem h2ksb_decSigSlot463_d3_of_d2c [LibsignalPlacement]
    {M : AllocCostModel} {H : LibsignalHooks}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecSigEnv : DecSigGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h : (slotWithPreFdsGe3Closed
      (mkSlot (decSigSlotSpecFrozenPlaced A lim DecSigEnv (cliRunSemD2c_placed X W))
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal)).OkPlaced
      (lsProg_579 H) (lsmpl.base 463)) :
    (slotWithPreFdsGe3Closed
      (mkSlot (decSigSlotSpecFrozenPlaced A lim DecSigEnv (cliRunSemD3 W))
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed)).decryptSignal)).OkPlaced
      (lsProg_579 H) (lsmpl.base 463) := by
  change (slotWithPreFdsGe3Closed
    (mkSlot (decSigSlotSpecFrozenPlaced A lim DecSigEnv (cliRunSemD3 W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal)).OkPlaced
    (lsProg_579 H) (lsmpl.base 463)
  rw [← g5ba_decSigSlotSpecFrozenPlaced_d2c_eq_d3 A lim DecSigEnv X W]
  exact h

/-- Untyped D3 `RunSlotEnvs` family at `[LibsignalPlacement]`, matching
`ElfSlicesPqOomH2KIfaces.h2ki_UntypedDecPkSlot520OkK` and `ElfSlicesPqOomH2KSpineA.h2k_untypedRunEnvAt`. -/
noncomputable abbrev h2ksb_untypedSlotEnvs [LibsignalPlacement] {mmpl : MultiPlacement}
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64) : RunSlotEnvs :=
  binaryKitRunSlotEnvsExact W
    (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
    cliRunBudgets_placed (realCliInitBinarySlotEnvFixed W)
    (DecPkD3UntypedEnvOf
      (A := (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc)
      cliRunBudgets_placed (ReadFileRuleEnvFixed cliIo.rd)
      SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv)

/-- Witness-packaged Spine-B `huntyped` (`cliRunSemD3`) closer at `w : F3CliElfGhostWitnessK`
from Slots `464`, `463`, `521`, and `h2ki_UntypedDecPkSlot520OkK w`. -/
theorem h2ksb_spineBUntyped_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hHooksFd : F3WitnessRunHooksBundleFd w)
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl w.ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp)
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv)
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv
          (cliRunSemD3 W)
          (cliDecryptPrekeyNeed cliRunBudgets_placed))
    (hW1 : h2ki_W1EncryptSlot464OkK w)
    (hW2 : h2ki_W2DecryptSignalSlot463OkK w)
    (hW3 : h2ki_W3InitSlot521OkK w)
    (hSlot520 : h2ki_UntypedDecPkSlot520OkK w) :
    h2ki_SpineBRunTightOfSemK w cliRunSemD3
      (fun W γ tp =>
        letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv
            (cliRunSemD3 W))) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  exact h2ksb_spineBRunTightOfSem_of_witnessK w hLs hHooksFd cliRunSemD3
    (h2ksb_untypedSlotEnvs (mmpl := mmpl))
    (fun _ _ _ => PksmTryFromEnv)
    (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets_placed)
    (by decide)
    hpub hpureFs
    (fun h547 W γ tp =>
      h2ksb_encSlot464_d3_of_d2c
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliEncryptBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        defaultExtrasF3 W
        (hW1 h547 defaultExtrasF3 W γ tp))
    (fun h547 W γ tp =>
      h2ksb_decSigSlot463_d3_of_d2c
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliDecryptSignalBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        defaultExtrasF3 W
        (hW2 h547 defaultExtrasF3 W γ tp))
    (fun h547 W γ tp =>
      hW3 h547 defaultExtrasF3 W γ tp (cliRunSemD3 W)
        (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))
        rfl rfl rfl rfl rfl)
    hSlot520

/-- Concrete Spine-B `huntyped` closer at `mkF3CliElfGhostWitnessK`. -/
theorem h2ksb_spineBUntyped_mkWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl (h2k_ghFixedK mpl mmpl)
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp)
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv)
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv
          (cliRunSemD3 W)
          (cliDecryptPrekeyNeed cliRunBudgets_placed))
    (hW1 : h2ki_W1EncryptSlot464OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hW2 : h2ki_W2DecryptSignalSlot463OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hW3 : h2ki_W3InitSlot521OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hSlot520 : h2ki_UntypedDecPkSlot520OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)) :
    h2ki_SpineBRunTightOfSemK
      (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
      cliRunSemD3
      (fun W γ tp =>
        letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv
            (cliRunSemD3 W))) :=
  h2ksb_spineBUntyped_of_witnessK
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hLs
    (f3WitnessRunHooksBundleFd_mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hpub hpureFs hW1 hW2 hW3 hSlot520

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineB
