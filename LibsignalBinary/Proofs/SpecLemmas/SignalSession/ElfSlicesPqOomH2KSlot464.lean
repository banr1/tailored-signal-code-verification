/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptSlotWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SessDeserStoreWithFds
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot464Cal
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2LsRetAddrKeep
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.V1MergeBlk325Cli
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesCountedR
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStatePlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Spine-C Slot `464` (`encrypt`) Closure at `h2k_ghFixedK` (`ElfSlicesPqOomH2KSlot464`)

**Checked by Lean.**

Discharges `h2ki_EncryptSlot464OkAtPreFd` and `h2ki_W1EncryptSlot464OkK` via
`AllocWithFds.withFds` and the `withFdsGe3Closed` Block-`589` `Dir::get` bridge
(`dirGet_placed_ok_of_h2k_fd`), instantiated at `h2k_ghFixedK mpl mmpl` and
`mkF3CliElfGhostWitnessK`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot464

open Arm64 (GhostName HookSat State subroutine_ok)
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries (mallocngLib)
open CryptoVerification
  (LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles ls_subroutine_ok_rocl_of_block subroutine_ok_withLsCodeRoLoaded_of_rocl)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.SignalSession
  (CliHooks cliBcmpHook cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsAesEncSym
   lsReadFileSym lsStringCloneSym)
open CryptoVerification.SignalSession.Cli (cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.KitInst (cliGhostExterns_blackBox)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliRunNeeds cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_589 lsProg_569 lsProg_589)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (mkSlot)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliExternsPlaced_bcmp cliGhostExterns cliGhostExterns_other)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets pathNeed)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_sat_of_cliExternsPlaced scopeKit)
open CryptoVerification.SpqrV1.Top.DecodeState (canonicalV1InnerHeap)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget
  (aesEncBudgetSpec libcruxHmacBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk (cliRunHooksPlaced_of_ghost)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (w1BinaryIdKitPlacedBudgetFixed w1BinarySessKitPlacedBudgetFixed)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (ReadFileRuleEnvFixed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (cliGhostExterns_aesEnc_withFds_hookSat cliGhostExterns_libcruxHmac_withFds_hookSat
   cliGhostSpqrAllocHooks_withFds withFds)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (encSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (w1IdKitPlaced w1SessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptSlotWithFds
  (subroutine_ok_encSlot_withFdsGe3Closed_of_withFds w1BinaryIdKitPlaced_withFds_okIE
   w1BinarySessKitPlaced_withFds_okSE)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunHooksPlaced path_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks cliExternsPlaced_bcmp_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (dirGetSpecPlaced pathSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
  (ofBytesEnv sessDeserialize_cli_dcan_byBytes_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
  (serializeCanonSeqFree_cli_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SessDeserStoreWithFds
  (subroutine_ok_path_withFdsGe3Closed_of_withFds)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
  (h2asm_Branch2HookReplaysK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (cliEncryptBinaryKitSlotEnvExact)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hPl_mng hole2_hblk hole2_hext_nodup hole2_keepSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
  (h2kb_alloc_pre_keepSub_false h2kb_dealloc_pre_keepSub_false
   h2kb_hole2_runHooksPlaced h2kb_hookOk_of_withKeepLrFalse h2kb_hookSat_of_withKeepLrFalse
   h2kb_realloc_pre_keepSub_false h2kb_stringCloneBudget_pre_keep_false)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit
  (dirGet_placed_ok_of_h2k_fd h2k_hole2_hReadSatK_withFds)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
  (h2k_CliGhostSpqrAllocHooksK h2k_ghFixedK h2k_readFileSpecK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (h2ki_EncryptSlot464OkAtPreFd h2ki_W1EncryptSlot464OkK
   okPlaced_slotWithPreFdsGe3Closed_of_withFdsGe3Closed slotWithFdsGe3Closed)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot464Cal
  (hole3_w1_inner_of_decodeState_at)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
  (cliRunHooksPlaced_of_ghost_withFds h2kb_hole2_hGSpqr_withFds h2kb_runHooksPlaced_withFds)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
  (F3CliElfGhostWitnessK mkF3CliElfGhostWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2LsRetAddrKeep
  (h2lr_lsRetAddr624_keepSub_false)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W1InnerTight
  (w1t_decodeStateCalleeContractsClPlacedX_cli)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.V1MergeBlk325Cli (v1StateMergeBlk325_cli)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesCountedR
  (e2ar_epochDirectionMerge_blk325_cl_ok_tight)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStatePlacedBudget
  (e2a_decodeState_cl_placed_ok_of_v1Merge_109)

/-! ## `bcmp` `.keepsFs` and `ghFixed`-Parametric Slot-`464` Producer -/

/-- `cliGhostExterns gh (cliExternsPlaced mmpl W)` satisfies `(withVmPreserved cliBcmpSpec).keepsFs`
at `"bcmp"` (`cliBcmpName`), since `cliBcmpHook` leaves `.fs` unchanged. -/
theorem cliGhostExterns_bcmp_keepsFs_sat
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "bcmp"
      (withVmPreserved cliBcmpSpec).keepsFs := by
  have hsat :=
    cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_bcmp_budget_sat mmpl W)
  rcases hsat with ⟨fn, hfn, hok⟩
  have hlookup :
      cliGhostExterns gh (cliExternsPlaced mmpl W) "bcmp" = some (cliBcmpHook W.bcmp) := by
    rw [cliGhostExterns_other gh (cliExternsPlaced mmpl W)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact cliExternsPlaced_bcmp mmpl W
  rw [hlookup] at hfn
  injection hfn with hfn_eq
  subst hfn_eq
  exact ⟨cliBcmpHook W.bcmp, hlookup, hok.keepsFs (fun _ => rfl)⟩

/-- `ghFixed`-parametric producer for `h2ki_EncryptSlot464OkAtPreFd` via
`AllocWithFds.withFds` and `dirGet_placed_ok_of_h2k_fd` on Block `589`. -/
theorem h2k_encryptSlot464OkAtPreFd_of_gh
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (ghFixed : CliGhostHooks)
    (h547 : mpl.base 547 ≠ 0#64)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (hGSpqrWf :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostSpqrAllocHooks fineCostModel
        (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
        cliBudgetLimits ghFixed)
    (hh :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      RunHooksPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hhWf :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      RunHooksPlaced
        (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
        cliBudgetLimits (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hReadSat :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
        (withFdsGe3Closed
          (h2k_readFileSpecK cliIo.rd cliWrOk
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    h2ki_EncryptSlot464OkAtPreFd
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      X W := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  let A0 := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  let H := cliGhostExterns ghFixed (cliExternsPlaced mmpl W)
  have hPathWf :
      subroutine_ok (lsProg_589 H) (lsmpl.base 596)
        (pathSpecPlaced (withFds A0) cliBudgetLimits PathEnv pathNeed) :=
    path_placed_ok (callerProg := lsProg_589 H) (i := 589) hhWf (Nat.le_refl pathNeed) (by decide)
  have hPathFd :
      subroutine_ok (lsProg_589 H) (lsmpl.base 596)
        (withFdsGe3Closed (pathSpecPlaced A0 cliBudgetLimits PathEnv pathNeed)) :=
    subroutine_ok_path_withFdsGe3Closed_of_withFds rfl hPathWf
  have hlr589 : hole2_keepSub ((blkPl_589).base + 336#64) = false :=
    h2lr_lsRetAddr624_keepSub_false hLs ⟨589, by decide, 336, by decide, rfl⟩
  have hGet589 :
      subroutine_ok (lsProg_589 H) (lsmpl.base 589)
        (withFdsGe3Closed
          (dirGetSpecPlaced cliIo.rd cliWrOk A0 cliBudgetLimits
            (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
            (RunBudgets.dirGetNeed ⟨cliRunBudgets.readFile⟩))) :=
    dirGet_placed_ok_of_h2k_fd
      (pathProg := lsProg_589 H) (jPath := 589)
      (fun _ hp => hp.2)
      hh.allocFs
      (cliGhostExterns_bcmp_keepsFs_sat mmpl ghFixed W)
      (by decide) (by decide)
      hPathFd
      hReadSat
      hlr589
      (hh.fs (lsProg_589 H) 589)
      (Nat.le_refl (RunBudgets.dirGetNeed ⟨cliRunBudgets.readFile⟩))
      (fun _ _ _ _ h => h)
  have hGWf : CliGhostAllocHooks fineCostModel (withFds A0) cliBudgetLimits ghFixed :=
    hGSpqrWf.toCliGhostAllocHooks
  have hDeser46Wf := sessDeserialize_cli_dcan_byBytes_placed_ok mmpl ghFixed W
    (Scope := scopeKit) (A := withFds A0) (lim := cliBudgetLimits) hGWf (fun _ h => h)
  have hDeser569Wf :
      subroutine_ok (lsProg_569 H) (lsmpl.base 46)
        (sessDeserializeSpecPlaced scopeKit (withFds A0) cliBudgetLimits
          (ofBytesEnv RecordDeserializeCancelEnv)) :=
    subroutine_ok_withLsCodeRoLoaded_of_rocl
      (ls_subroutine_ok_rocl_of_block (callerProg := lsProg_569 H) (j := 46)
        hDeser46Wf (by decide) (by decide) (by decide))
  have hSer52Wf := serializeCanonSeqFree_cli_placed mmpl ghFixed W hGWf
  have hSessKit :
      ∀ (F : FsFiles) (peer : AddrGhost),
        SessionOnlyKitPlacedOkSE (withFds A0) cliBudgetLimits
          (w1SessKitPlaced (withFds A0).repAlloc cliRunBudgets F peer)
          (w1BinarySessKitPlacedBudgetFixed (withFds A0).repAlloc cliRunBudgets F peer)
          scopeKit encodeRecord H :=
    fun F peer =>
      w1BinarySessKitPlaced_withFds_okSE rfl cliRunBudgets F peer h547
        hh hhWf hGet589 hDeser569Wf hSer52Wf
  have hIdKit :
      ∀ (F : FsFiles) (peer : AddrGhost),
        IdentityStoreKitPlacedOkI (withFds A0) cliBudgetLimits
          (w1IdKitPlaced (withFds A0).repAlloc cliRunBudgets F peer)
          (w1BinaryIdKitPlacedBudgetFixed (withFds A0).repAlloc cliRunBudgets F peer) H :=
    fun F peer =>
      w1BinaryIdKitPlaced_withFds_okIE rfl cliRunBudgets F peer h547
        hh hhWf hGet589 (cliGhostExterns_blackBox mmpl ghFixed W)
  have hc325 := w1t_decodeStateCalleeContractsClPlacedX_cli mmpl ghFixed W hGWf
  have h325Wf := e2a_decodeState_cl_placed_ok_of_v1Merge_109 (F := W.C.F) (K := W.Q.K)
    hc325
    (e2ar_epochDirectionMerge_blk325_cl_ok_tight hc325)
    (v1StateMergeBlk325_cli mmpl ghFixed W hGWf)
  have hAesEncWf :
      HookSat H lsAesEncSym (aesEncBudgetSpec W.C.E fineCostModel (withFds A0) cliBudgetLimits) :=
    cliGhostExterns_aesEnc_withFds_hookSat γ mmpl tp cliElfImage.brkStart
      (lim := cliBudgetLimits) rfl ghFixed W hPl_mng
  have hHmacWf :
      HookSat H spqrLibcruxHmacSym
        (libcruxHmacBudgetSpec W.C.F fineCostModel (withFds A0) cliBudgetLimits) :=
    cliGhostExterns_libcruxHmac_withFds_hookSat γ mmpl tp cliElfImage.brkStart
      (lim := cliBudgetLimits) rfl ghFixed W hPl_mng
  have hSlotWf := hole3_w1_inner_of_decodeState_at
    (mpl := mpl) (mmpl := mmpl) hLs hblk hext_nodup
    (withFds A0) ghFixed X W
    hGSpqrWf hhWf hAesEncWf hHmacWf hSessKit hIdKit h547 h325Wf
  have hSlotFd :
      (slotWithFdsGe3Closed
        (mkSlot
          (encSlotSpecPlaced A0 cliBudgetLimits
            (cliEncryptBinaryKitSlotEnvExact W A0 cliRunBudgets)
            (cliRunSemD2c_placed X W))
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt)).OkPlaced
        (lsProg_579 H) (lsmpl.base 464) :=
    fun stk hlo hhi => subroutine_ok_encSlot_withFdsGe3Closed_of_withFds rfl (hSlotWf stk hlo hhi)
  exact okPlaced_slotWithPreFdsGe3Closed_of_withFdsGe3Closed hSlotFd

/-! ## Closed Instantiations at `h2k_ghFixedK` and `F3CliElfGhostWitnessK` -/

/-- Closed `h2ki_EncryptSlot464OkAtPreFd` producer at `ghFixed := h2k_ghFixedK mpl mmpl`. -/
theorem h2k_encryptSlot464OkAtPreFd_of_ghFixedK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (h547 : mpl.base 547 ≠ 0#64)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2ki_EncryptSlot464OkAtPreFd
      (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      X W := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  exact h2k_encryptSlot464OkAtPreFd_of_gh
    mpl mmpl hLs (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs) (hole2_hPl_mng mmpl hMm)
    (h2k_ghFixedK mpl mmpl) h547 X W γ tp
    (h2kb_hole2_hGSpqr_withFds mpl mmpl hLs hMm γ tp)
    (h2kb_hole2_runHooksPlaced mpl mmpl hLs hMm W γ tp)
    (h2kb_runHooksPlaced_withFds mpl mmpl hLs hMm W γ tp)
    (h2k_hole2_hReadSatK_withFds mpl mmpl hLs hMm W γ tp)

/-- Witness-packaged `h2ki_W1EncryptSlot464OkK w` for any `w : F3CliElfGhostWitnessK mpl mmpl`
whose ghost table equals `h2k_ghFixedK mpl mmpl`. -/
theorem h2k_w1EncryptSlot464OkK_of_witnessK_ghFixedK
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hw_gh :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      w.ghFixed = h2k_ghFixedK mpl mmpl) :
    h2ki_W1EncryptSlot464OkK w := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  intro h547 X W γ tp
  rw [hw_gh]
  exact h2k_encryptSlot464OkAtPreFd_of_gh
    mpl mmpl hLs w.hblk w.hext_nodup w.hPl_mng
    (h2k_ghFixedK mpl mmpl) h547 X W γ tp
    (h2kb_hole2_hGSpqr_withFds mpl mmpl hLs hMm γ tp)
    (h2kb_hole2_runHooksPlaced mpl mmpl hLs hMm W γ tp)
    (h2kb_runHooksPlaced_withFds mpl mmpl hLs hMm W γ tp)
    (h2k_hole2_hReadSatK_withFds mpl mmpl hLs hMm W γ tp)

/-- Closes `h2ki_W1EncryptSlot464OkK` at `mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2`. -/
theorem h2k_w1EncryptSlot464OkK_mkWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    h2ki_W1EncryptSlot464OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) :=
  h2k_w1EncryptSlot464OkK_of_witnessK_ghFixedK hLs hMm
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) rfl

/-- Lift `h2k_CliGhostSpqrAllocHooksK` to plain `CliGhostSpqrAllocHooks` at any `[LibsignalPlacement]`
linked at `cliElfBytes`. -/
theorem cliGhostSpqrAllocHooks_of_h2k [LibsignalPlacement]
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {gh : CliGhostHooks}
    (hK : h2k_CliGhostSpqrAllocHooksK M A lim gh) :
    CliGhostSpqrAllocHooks M A lim gh :=
  { alloc := h2kb_hookOk_of_withKeepLrFalse hK.alloc (h2kb_alloc_pre_keepSub_false hlink)
    dealloc := h2kb_hookOk_of_withKeepLrFalse hK.dealloc (h2kb_dealloc_pre_keepSub_false hlink)
    realloc := h2kb_hookOk_of_withKeepLrFalse hK.realloc (h2kb_realloc_pre_keepSub_false hlink)
    alloc_fs := hK.alloc_fs
    dealloc_fs := hK.dealloc_fs
    realloc_fs := hK.realloc_fs
    alloc_fsT := hK.alloc_fsT
    dealloc_fsT := hK.dealloc_fsT
    realloc_fsT := hK.realloc_fsT
    shim_eq := hK.shim_eq
    memset := hK.memset
    memcpy := hK.memcpy
    memcpy_exact := hK.memcpy_exact
    memset_acp := hK.memset_acp
    allocZeroed :=
      h2kb_hookOk_of_withKeepLrFalse hK.allocZeroed (h2kb_alloc_pre_keepSub_false hlink)
    allocZeroed_fs := hK.allocZeroed_fs
    allocZeroed_fsT := hK.allocZeroed_fsT }

/-- Closes `h2ki_W1EncryptSlot464OkK w` for an abstract `w : F3CliElfGhostWitnessK mpl mmpl`
from `.fs`-preservation on `w.ghFixed.stringClone` and `withFdsGe3Closed` `readFile` `HookSat`. -/
theorem h2k_w1EncryptSlot464OkK_of_witnessK
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hStrFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (fn : State → State),
        cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W) lsStringCloneSym = some fn →
        ∀ s0 : State, (fn s0).fs = s0.fs)
    (hReadFds :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        HookSat (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
          (withFdsGe3Closed
            (h2k_readFileSpecK cliIo.rd cliWrOk
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
              cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))) :
    h2ki_W1EncryptSlot464OkK w := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  intro h547 X W γ tp
  have hGSpqr := cliGhostSpqrAllocHooks_of_h2k hLs (w.hGSpqrK γ tp)
  have hStrSat := h2kb_hookSat_of_withKeepLrFalse
    (w.hHooksBundleK W γ tp).runHooks.stringClone
    (h2kb_stringCloneBudget_pre_keep_false hLs)
  have hh := cliRunHooksPlaced_of_ghost mmpl w.ghFixed W hGSpqr w.hFs.stringClone_fsT hStrSat
  have hhWf := cliRunHooksPlaced_of_ghost_withFds mmpl w.ghFixed W hGSpqr
    w.hFs.stringClone_fsT hStrSat (hStrFs W)
  exact h2k_encryptSlot464OkAtPreFd_of_gh
    mpl mmpl hLs w.hblk w.hext_nodup w.hPl_mng
    w.ghFixed h547 X W γ tp
    (cliGhostSpqrAllocHooks_withFds hGSpqr)
    hh hhWf (hReadFds W γ tp)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot464
