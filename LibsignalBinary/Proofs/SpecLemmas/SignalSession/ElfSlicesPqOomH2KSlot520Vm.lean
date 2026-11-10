/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridgeX
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBKitsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOfEnvGlue
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot463
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520VmPoll
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinVmHW4
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec

/-!
# Spine-C Slot `520` (`decryptPrekey`, D3 `validMatch`) Closure at `h2k_ghFixedK` (`ElfSlicesPqOomH2KSlot520Vm`)

**Checked by Lean.**

Discharges `ElfSlicesPqOomH2KD3JoinValidMatch.h2kd3_W4ValidMatchSlot520Ok{At,K}` unconditionally
via `ElfSlicesPqOomH2KSlot520VmPoll.h2k520vm_decPkValidMatchSlotOk_seqFree_targetGuarded_of_dirGet_frozen`
at `AllocWithFds.withFds`, `ElfTopJoinVmHW4.etjv_validMatchPoll_sub_dom0'`, and
`D3MatchingPathBKitsPlacedBudgetFd.slotOk_decPkFrozenPlaced_withFds_to_preFd`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520Vm

open Arm64 (GhostName HookOk HookSat subroutine_ok)
open Arm64.Obj (MultiPlacement)
open CryptoVerification
  (LibsignalFullPlacement LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives aesDecHookMallocng)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliRunBudgets cliRunBudgets_placed cliRunNeeds cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_589)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_lscro)
open LibsignalBinary.Heap (AllocEvent)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (aesDecBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridgeX (dpx_deserEnv)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
  (SessionGetPrev0Guard cliDecPkCanonSlotEnvExact' realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux (w4c_repairedStatesRecvEnvFam)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBKitsPlacedBudgetFd
  (slotOk_decPkFrozenPlaced_withFds_to_preFd)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOfEnvGlue
  (cli_tryDecrypt_of_tdEnv_at_518)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3 (cliRunSemD3ValidMatch)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (ReadFileRuleEnvFixed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (cliGhostAllocHooks_withFds fineAesDec_budget_withFds_hookOk withFds)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
  (pollTryDecryptPlacedSpecTPTight)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd (slotWithPreFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced dirGetSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
  (sessDeserialize_cli_dcan_byBytes_placed_ok)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
  (h2asm_Branch2HookReplaysK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
  (h2kb_hole2_hG h2kb_hole2_runHooksPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit
  (h2k_hole2_hReadSatK_withFds)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
  (h2k_ghFixedK h2k_readFileSpecK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot463
  (h2k463_dirGet_withFds_ok h2k463_spqrSeams_topStateGuarded_withFds)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520VmPoll
  (h2k520vm_decPkValidMatchSlotOk_seqFree_targetGuarded_of_dirGet_frozen)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
  (h2kb_hole2_hGSpqr_withFds h2kb_runHooksPlaced_withFds)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
  (F3CliElfGhostWitnessK mkF3CliElfGhostWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact libsignalFullPlacementOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinVmHW4
  (etjv_validMatchPoll_sub_dom0')
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
  (w4s2_SpqrRecvTopStateGuardedBytesEnv w4s2_TryDecryptTopStateGuardedEnv
   w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open VerifiedLibraries (mallocngLib)

/-! ## Spine-C D3 `validMatch` Slot-`520` Interfaces -/

/-- Explicit-argument Spine-C Slot `520` (`decryptPrekey`, D3 `validMatch`) pre-only
`FdsGe3Closed` interface. -/
def h2k520vm_W4ValidMatchSlot520OkAt
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
    let sEnvs := binaryKitRunSlotEnvsExact W A cliRunBudgets
      (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W)
    let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs
        (cliRunSemD3ValidMatch X W) needs).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)

abbrev h2k520vm_W4ValidMatchSlot520OkK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  h2k520vm_W4ValidMatchSlot520OkAt (mmpl := mmpl) w.hblk w.hext_nodup w.ghFixed

/-! ## Slot-`520` `validMatch` Closers -/

/-- Explicit-seam D3 `validMatch` Slot-`520` closer (`h2k520vm_W4ValidMatchSlot520OkAt`). -/
theorem h2k520vm_w4ValidMatchSlot520OkAt_of_seams
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    {SendEnv : CliHooks → SendCall → List AllocEvent → Prop}
    (hG :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostAllocHooks fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hAllocFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        AllocContractsFsPlaced
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hReadSatFd :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
          (withFdsGe3Closed
            (h2k_readFileSpecK cliIo.rd cliWrOk
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
              cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))))
    (hhWithFds :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
          cliBudgetLimits (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hSpqrWithFds :
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
          fineCostModel
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
          cliBudgetLimits mmpl ghFixed W (InitialStateEnv W.C.F)
          (fun st msg => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
          (SendEnv W)) :
    h2k520vm_W4ValidMatchSlot520OkAt (mmpl := mmpl) hblk hext_nodup ghFixed := by
  intro h547 X W γ tp
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  let H := cliGhostExterns ghFixed (cliExternsPlaced mmpl W)
  let sEnvs := binaryKitRunSlotEnvsExact W A cliRunBudgets
    (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W)
  let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
  have hGWf : CliGhostAllocHooks fineCostModel (withFds A) cliBudgetLimits ghFixed :=
    cliGhostAllocHooks_withFds (hG γ tp)
  have hhP := hhWithFds W γ tp
  have hGetPool :
      subroutine_ok (lsProg_589 H) (lsmpl.base 589)
        (dirGetSpecPlaced cliIo.rd cliWrOk (withFds A) cliBudgetLimits
          (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          cliRunBudgets.dirGetNeed) :=
    h2k463_dirGet_withFds_ok rfl hLs (hAllocFs W γ tp) hhP (hReadSatFd W γ tp)
  have hDeserPool :
      subroutine_ok (dpPollProgPlaced H) (lsmpl.base 46)
        (sessDeserializeSpecPlaced scopeKit (withFds A) cliBudgetLimits dpx_deserEnv) :=
    ls_transfer_lscro (callerProg := dpPollProgPlaced H)
      (sessDeserialize_cli_dcan_byBytes_placed_ok mmpl ghFixed W hGWf (fun _ hr => hr))
  have hAesDecPool :
      HookOk (aesDecHookMallocng mmpl W.C.D)
        (aesDecBudgetSpec W.C.D fineCostModel (withFds A) cliBudgetLimits) :=
    fineAesDec_budget_withFds_hookOk γ tp cliElfImage.brkStart cliBudgetLimits hPl_mng W.C.D
  have hTryDecPool :
      subroutine_ok (dpPollProgPlaced H) (lsmpl.base 508)
        (withLsCodeRoLoaded lsmpl
          (pollTryDecryptPlacedSpecTPTight W.C (withFds A) cliBudgetLimits 0#64 uuidTryParse
            (spqrV1 W.C.F W.Q.K) (w4s2_TryDecryptTopStateGuardedEnv W))) :=
    cli_tryDecrypt_of_tdEnv_at_518 (tdEnv := w4s2_TryDecryptTopStateGuardedEnv)
      mmpl ghFixed W 0#64 hGWf hAesDecPool (hSpqrWithFds W γ tp)
      (w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty W.C.F W.Q.K)
      (fun _ _ h => h)
  exact slotOk_decPkFrozenPlaced_withFds_to_preFd (A := A) (lim := cliBudgetLimits) rfl
    (h2k520vm_decPkValidMatchSlotOk_seqFree_targetGuarded_of_dirGet_frozen
      (A := withFds A) (lim := cliBudgetLimits)
      (ReadEnv := ReadFileRuleEnvFixed cliIo.rd)
      (DeserEnv := dpx_deserEnv)
      (tdEnv := w4s2_TryDecryptTopStateGuardedEnv W)
      (TargetEnv := fun g e =>
        SessionGetPrev0Guard g.F g.peer.val →
          realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed w4c_repairedStatesRecvEnvFam X W g e)
      mmpl ghFixed W X h547 hGWf hhP hGetPool hDeserPool (hSpqrWithFds W γ tp) hTryDecPool
      (cliRunSemD3ValidMatch X W) sEnvs needs
      (fun _ _ => Iff.rfl) rfl rfl (fun _ _ _ _ h => h) rfl
      (fun g evs hfOk0 hdOk0 hTight hevs0 _hPrev0 =>
        etjv_validMatchPoll_sub_dom0' A.repAlloc X W g evs hfOk0.1 hdOk0 hTight hevs0))

/-- Closes `h2k520vm_W4ValidMatchSlot520OkK w` at `w.ghFixed = h2k_ghFixedK mpl mmpl`. -/
theorem h2k520vm_w4ValidMatchSlot520OkK_of_ghFixed
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hgh :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      w.ghFixed = h2k_ghFixedK mpl mmpl) :
    h2k520vm_W4ValidMatchSlot520OkK w := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hgh' : w.ghFixed = h2k_ghFixedK mpl mmpl := hgh
  change h2k520vm_W4ValidMatchSlot520OkAt (mmpl := mmpl) (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs) w.ghFixed
  rw [hgh']
  exact h2k520vm_w4ValidMatchSlot520OkAt_of_seams hLs (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    (h2k_ghFixedK mpl mmpl) w.hPl_mng
    (fun γ tp => h2kb_hole2_hG mpl mmpl hLs hMm γ tp)
    (fun W γ tp => (h2kb_hole2_runHooksPlaced mpl mmpl hLs hMm W γ tp).allocFs)
    (fun W γ tp => h2k_hole2_hReadSatK_withFds mpl mmpl hLs hMm W γ tp)
    (fun W γ tp => h2kb_runHooksPlaced_withFds mpl mmpl hLs hMm W γ tp)
    (fun W γ tp =>
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2k463_spqrSeams_topStateGuarded_withFds mmpl (h2k_ghFixedK mpl mmpl) w.hPl_mng W γ tp
        cliElfImage.brkStart rfl (h2kb_hole2_hGSpqr_withFds mpl mmpl hLs hMm γ tp))

/-- Unconditional `h2k520vm_W4ValidMatchSlot520OkK` closer at
`mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2`. -/
theorem h2k520vm_w4ValidMatchSlot520OkK_mkWitness
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    h2k520vm_W4ValidMatchSlot520OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) :=
  h2k520vm_w4ValidMatchSlot520OkK_of_ghFixed
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) hLs hMm rfl

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520Vm
