/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsStage2PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBob
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAOverD3Wire
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot463
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec

/-!
# Spine-C Slot `520` (`decryptPrekey`, D3 `OverD3`) Closure at `h2k_ghFixedK` (`ElfSlicesPqOomH2KSlot520OverD3`)

**Checked by Lean.**

Discharges `ElfSlicesPqOomH2KD3JoinOverD3.h2kd3_W4OverD3Slot520Ok{At,K}` unconditionally via
`D3NonCanonValidOverPlacedBudgetFd.decPk_d3_validOver_tightRaw_slot520_preFd_of_kits` and
`DecPkPollKitsStage2PlacedBudgetFd.cliDecPkPollKitsPlacedOk_of_dirGet`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520OverD3

open Arm64 (GhostName HookOk HookSat subroutine_ok)
open Arm64.Obj (MultiPlacement)
open CryptoVerification
  (LibsignalFullPlacement LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives aesDecHookMallocng)
open CryptoVerification.LibsignalTripleRatchet (SendCall)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsReadFileSym
   lsRustAllocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliRunBudgets cliRunBudgets_placed cliRunNeeds cliWrOk)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns cliGhostExterns_other cliGhostExterns_shim)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Heap.SpecBudget (aesDecBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
  (ckx2_cliDecryptSignalBinaryKitSlotEnvExact ckx2_cliEncryptBinaryKitSlotEnvExact)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk (cliEncodeRawPrealloc_placed_ok)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact (hmx_binaryKitRunSlotEnvsSlotOf)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (EncodeRawPreallocPlacedOkX)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget
  (CliDecPkPollKitsPlacedOk)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget
  (cliRunSemOverV4)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudgetFd
  (decPk_d3_validOver_tightRaw_slot520_preFd_of_kits)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsStage2PlacedBudgetFd
  (cliDecPkPollKitsPlacedOk_of_dirGet)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBob
  (DecPkD3ValidOverOfEnv')
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAOverD3Wire
  (H7RADecPkOverValProjectedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (ReadFileRuleEnvFixed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (cliGhostAllocHooks_withFds fineAesDec_budget_withFds_hookOk withFds)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_589)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (slotWithPreFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_realloc_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced dirGetSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_lscro)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
  (sessDeserialize_cli_dcan_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
  (serContractsX_cli_placed)
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
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
  (h2kb_hole2_hGSpqr_withFds h2kb_runHooksPlaced_withFds)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
  (F3CliElfGhostWitnessK mkF3CliElfGhostWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (libsignalFullPlacementOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
  (w4s2_SpqrRecvTopStateGuardedBytesEnv w4s2_TryDecryptTopStateGuardedEnv
   w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open VerifiedLibraries (mallocngLib)

/-! ## Spine-C D3 `OverD3` Slot-`520` Interfaces -/

/-- `RunSlotEnvs` bundle for D3 `overD3` (definitionally equal to `h2kd3_overD3SlotEnvs`). -/
noncomputable abbrev h2k520od3_overD3SlotEnvs [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    RunSlotEnvs :=
  hmx_binaryKitRunSlotEnvsSlotOf
    (fun {_M'} A' B' => ckx2_cliEncryptBinaryKitSlotEnvExact W A' B')
    (fun {_M'} A' B' => ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A' B')
    A cliRunBudgets (realCliInitBinarySlotEnvFixed W)
    (H7RADecPkOverValProjectedEnv DecPkD3ValidOverOfEnv' A.repAlloc W X
      w4s2_TryDecryptTopStateGuardedEnv)

/-- Explicit-argument Spine-C Slot `520` (`decryptPrekey`, D3 `overD3`) pre-only `FdsGe3Closed`
interface. -/
def h2k520od3_W4OverD3Slot520OkAt
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
    let sEnvs := h2k520od3_overD3SlotEnvs A X W
    let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs
        (cliRunSemOverV4 X W) needs).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)

abbrev h2k520od3_W4OverD3Slot520OkK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  h2k520od3_W4OverD3Slot520OkAt (mmpl := mmpl) w.hblk w.hext_nodup w.ghFixed

/-! ## `{M} {A}`-Generic `growOneVecU8` Helper and Slot-`520` `OverD3` Closers -/

/-- `{M : AllocCostModel} {A : RustCliAllocBudget M}`-generic Block-`621` `growOneVecU8` caller
contract on `lsProg_51`. -/
theorem h2k520od3_growOneVecU8_lsProg51_withLsCl_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (CryptoVerification.lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621)
      (CryptoVerification.withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)) :=
  LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlacedBudget.growOneVecU8_caller_withLsCl_ok
    (callerProg := CryptoVerification.lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (i := 51)
    ((show CryptoVerification.lsHandleErrorSym =
          CryptoVerification.SpqrV1.Alloc.spqrHandleErrorSym by decide) ▸
      ((cliGhostExterns_other gh (cliExternsPlaced mmpl W)
          (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)).trans
        (CryptoVerification.SignalSession.Cli.Slots.cliExternsPlaced_panic_handle_error mmpl W)))
    ((show lsRustNoAllocShimSymCli =
          CryptoVerification.SpqrV1.Alloc.spqrRustNoAllocShimSym by decide) ▸
      (⟨ProofLib.hookNoop,
        (cliGhostExterns_shim gh _).trans (congrArg some hG.shim_eq),
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShim_hookOk⟩ :
        HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
          lsRustNoAllocShimSymCli
          LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimSpec))
    ((show lsRustAllocSymCli = CryptoVerification.SpqrV1.Alloc.spqrRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show lsRustReallocSymCli = CryptoVerification.SpqrV1.Alloc.spqrRustReallocSym by decide) ▸
      cliExternsPlaced_realloc_budget_sat mmpl gh W hG)

/-- Explicit-seam D3 `OverD3` Slot-`520` closer (`h2k520od3_W4OverD3Slot520OkAt`). -/
theorem h2k520od3_w4OverD3Slot520OkAt_of_seams
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
    h2k520od3_W4OverD3Slot520OkAt (mmpl := mmpl) hblk hext_nodup ghFixed := by
  intro h547 X W γ tp
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  let H := cliGhostExterns ghFixed (cliExternsPlaced mmpl W)
  let sEnvs := h2k520od3_overD3SlotEnvs A X W
  have hGWf : CliGhostAllocHooks fineCostModel (withFds A) cliBudgetLimits ghFixed :=
    cliGhostAllocHooks_withFds (hG γ tp)
  have hhP := hhWithFds W γ tp
  have hGetPool :
      subroutine_ok (lsProg_589 H) (lsmpl.base 589)
        (dirGetSpecPlaced cliIo.rd cliWrOk (withFds A) cliBudgetLimits
          (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          cliRunBudgets_placed.dirGetNeed) :=
    h2k463_dirGet_withFds_ok rfl hLs (hAllocFs W γ tp) hhP (hReadSatFd W γ tp)
  have hDeserPool :
      subroutine_ok (dpPollProgPlaced H) (lsmpl.base 46)
        (sessDeserializeSpecPlaced scopeKit (withFds A) cliBudgetLimits
          SessDeserializeCancelEnv) :=
    ls_transfer_lscro (callerProg := dpPollProgPlaced H)
      (sessDeserialize_cli_dcan_placed_ok mmpl ghFixed W hGWf (fun _ hr => hr))
  have hKits :
      CliDecPkPollKitsPlacedOk (withFds A) cliBudgetLimits cliRunBudgets
        (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv H :=
    cliDecPkPollKitsPlacedOk_of_dirGet mmpl ghFixed W cliRunBudgets h547 hhP hGetPool hDeserPool
  have hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H :=
    cliEncodeRawPrealloc_placed_ok (serContractsX_cli_placed mmpl ghFixed W (hG γ tp))
  have hGrow :
      subroutine_ok (CryptoVerification.lsProg_51 H) (lsmpl.base 621)
        (CryptoVerification.withLsCl lsmpl
          (growOneVecU8BudgetSpec fineCostModel (withFds A) cliBudgetLimits)) :=
    h2k520od3_growOneVecU8_lsProg51_withLsCl_ok mmpl ghFixed W hGWf
  have hAesDecPool :
      HookOk (aesDecHookMallocng mmpl W.C.D)
        (aesDecBudgetSpec W.C.D fineCostModel (withFds A) cliBudgetLimits) :=
    fineAesDec_budget_withFds_hookOk γ tp cliElfImage.brkStart cliBudgetLimits hPl_mng W.C.D
  exact decPk_d3_validOver_tightRaw_slot520_preFd_of_kits A cliBudgetLimits rfl mmpl ghFixed W X
    sEnvs h547 hGWf hhP hKits hRaw hGrow hAesDecPool (hSpqrWithFds W γ tp)
    (w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty W.C.F W.Q.K)
    (fun _ _ h => h)
    (fun g _evs h => ⟨g, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h⟩)

/-- Closes `h2k520od3_W4OverD3Slot520OkK w` at `w.ghFixed = h2k_ghFixedK mpl mmpl`. -/
theorem h2k520od3_w4OverD3Slot520OkK_of_ghFixed
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hgh :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      w.ghFixed = h2k_ghFixedK mpl mmpl) :
    h2k520od3_W4OverD3Slot520OkK w := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hgh' : w.ghFixed = h2k_ghFixedK mpl mmpl := hgh
  change h2k520od3_W4OverD3Slot520OkAt (mmpl := mmpl) (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs) w.ghFixed
  rw [hgh']
  exact h2k520od3_w4OverD3Slot520OkAt_of_seams hLs (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
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

/-- Unconditional `h2k520od3_W4OverD3Slot520OkK` closer at
`mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2`. -/
theorem h2k520od3_w4OverD3Slot520OkK_mkWitness
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    h2k520od3_W4OverD3Slot520OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) :=
  h2k520od3_w4OverD3Slot520OkK_of_ghFixed
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) hLs hMm rfl

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520OverD3
