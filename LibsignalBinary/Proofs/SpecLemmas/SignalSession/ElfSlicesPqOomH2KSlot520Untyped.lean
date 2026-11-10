/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec

/-!
# Spine-C Slot `520` (`decryptPrekey`, D3 Untyped) Bridge (`ElfSlicesPqOomH2KSlot520Untyped`)

**Checked by Lean.**

Bridges `D3BadKemRejectPlacedBudgetFd.decPkD3Untyped_slotOk_withFdsGe3Closed_of_pollKits` to
`ElfSlicesPqOomH2KIfaces.h2ki_UntypedDecPkSlot520OkK` (`slotWithPreFdsGe3Closed`), discharging the
`withFds` allocator and run-hook bundles at `h2k_ghFixedK mpl mmpl` via
`ElfSlicesPqOomH2KStrCloneFds` so only `CliDecPkPollKitsPlacedOkFds` remains.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520Untyped

open Arm64 (GhostName)
open Arm64.Obj (MultiPlacement)
open CryptoVerification (LibsignalFullPlacement LibsignalPlacement)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliRunBudgets cliRunBudgets_placed cliRunNeeds)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunGlue (cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
  (DecPkD3UntypedEnvOf PqxdhAcceptBadKemErrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd
  (CliDecPkPollKitsPlacedOkFds)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectPlacedBudgetFd
  (decPkD3Untyped_slotOk_withFdsGe3Closed_of_pollKits)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (defaultExtrasF3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (cliRunSemD3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (withFds)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
  (h2asm_Branch2HookReplaysK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (h2k_ghFixedK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (h2ki_UntypedDecPkSlot520OkK okPlaced_slotWithPreFdsGe3Closed_of_withFdsGe3Closed
   slotWithFdsGe3Closed)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
  (h2kb_hole2_hG_withFds h2kb_runHooksPlaced_withFds)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
  (F3CliElfGhostWitnessK mkF3CliElfGhostWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact libsignalFullPlacementOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup)
open VerifiedLibraries (mallocngLib)

/-! ## Witness-Parametric Bridge for `h2ki_UntypedDecPkSlot520OkK` -/

/-- Two-sided (`slotWithFdsGe3Closed`) Block-`520` D3 untyped `decrypt_prekey` contract over
`w : F3CliElfGhostWitnessK mpl mmpl`, given `withFds` hook bundles and `CliDecPkPollKitsPlacedOkFds`. -/
theorem h2ki_UntypedDecPkSlot520OkTwoSidedK_of_hooksAndPollKits
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hG_withFds :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostAllocHooks fineCostModel
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
          cliBudgetLimits w.ghFixed)
    (hh_withFds :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @RunHooksPlaced (libsignalPlacementOf mpl w.hblk w.hext_nodup) fineCostModel
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
          cliBudgetLimits
          (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W)))
    (hPollKits :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliDecPkPollKitsPlacedOkFds
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits cliRunBudgets (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
          (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
    mpl.base 547 ≠ 0#64 →
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      (slotWithFdsGe3Closed
        (slotsOfSigPkFrozenPlaced
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
            cliRunBudgets_placed (realCliInitBinarySlotEnvFixed W)
            (DecPkD3UntypedEnvOf
              (A := (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc)
              cliRunBudgets_placed (ReadFileRuleEnvFixed cliIo.rd)
              SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
          (cliRunSemD3 W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))).decryptPrekey).OkPlaced
        (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520) := by
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs w.hblk w.hext_nodup
  intro h547 W γ tp
  exact decPkD3Untyped_slotOk_withFdsGe3Closed_of_pollKits
    (A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
    (lim := cliBudgetLimits)
    rfl defaultExtrasF3 mmpl w.ghFixed W h547
    (hG_withFds γ tp)
    (hh_withFds W γ tp)
    (hPollKits h547 W γ tp)
    (cliRunSemD3 W)
    (binaryKitRunSlotEnvsExact W
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
      cliRunBudgets_placed (realCliInitBinarySlotEnvFixed W)
      (DecPkD3UntypedEnvOf
        (A := (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc)
        cliRunBudgets_placed (ReadFileRuleEnvFixed cliIo.rd)
        SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
    (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))
    (fun _ _ h => h) rfl rfl
    (fun _ _ _ _ h => ⟨⟨h.1.keyPairLt, h.1.preKeysWf, h.1.baseKeysLt⟩, h.2⟩)
    (by decide)

/-- Closes `h2ki_UntypedDecPkSlot520OkK w` (`slotWithPreFdsGe3Closed`) for an arbitrary
`w : F3CliElfGhostWitnessK mpl mmpl` from `withFds` hook bundles and `CliDecPkPollKitsPlacedOkFds`. -/
theorem h2ki_UntypedDecPkSlot520OkK_of_hooksAndPollKits
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hG_withFds :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostAllocHooks fineCostModel
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
          cliBudgetLimits w.ghFixed)
    (hh_withFds :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @RunHooksPlaced (libsignalPlacementOf mpl w.hblk w.hext_nodup) fineCostModel
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
          cliBudgetLimits
          (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W)))
    (hPollKits :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliDecPkPollKitsPlacedOkFds
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits cliRunBudgets (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
          (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) :
    h2ki_UntypedDecPkSlot520OkK w := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  intro h547 W γ tp
  exact okPlaced_slotWithPreFdsGe3Closed_of_withFdsGe3Closed
    (h2ki_UntypedDecPkSlot520OkTwoSidedK_of_hooksAndPollKits
      hLs w hG_withFds hh_withFds hPollKits h547 W γ tp)

/-! ## Specializations at `h2k_ghFixedK` and `mkF3CliElfGhostWitnessK` -/

/-- Closes `h2ki_UntypedDecPkSlot520OkK w` at `w.ghFixed = h2k_ghFixedK mpl mmpl` from
`CliDecPkPollKitsPlacedOkFds`. -/
theorem h2ki_UntypedDecPkSlot520OkK_of_ghFixedEq_and_pollKits
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hgh :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      w.ghFixed = h2k_ghFixedK mpl mmpl)
    (hPollKits :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliDecPkPollKitsPlacedOkFds
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits cliRunBudgets (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
          (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))) :
    h2ki_UntypedDecPkSlot520OkK w := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  have hgh' : w.ghFixed = h2k_ghFixedK mpl mmpl := hgh
  refine h2ki_UntypedDecPkSlot520OkK_of_hooksAndPollKits hLs w ?_ ?_ ?_
  · intro γ tp
    rw [hgh']
    exact h2kb_hole2_hG_withFds mpl mmpl hLs hMm γ tp
  · intro W γ tp
    rw [hgh']
    exact h2kb_runHooksPlaced_withFds mpl mmpl hLs hMm W γ tp
  · intro h547 W γ tp
    rw [hgh']
    exact hPollKits h547 W γ tp

/-- Closes `h2ki_UntypedDecPkSlot520OkK (mkF3CliElfGhostWitnessK …)` from
`D3BadKemP2TopPlacedBudgetFd.CliDecPkPollKitsPlacedOkFds`. -/
theorem h2ki_UntypedDecPkSlot520OkK_mkWitness_of_pollKits
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hPollKits :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliDecPkPollKitsPlacedOkFds
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits cliRunBudgets (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
          (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))) :
    h2ki_UntypedDecPkSlot520OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) :=
  h2ki_UntypedDecPkSlot520OkK_of_ghFixedEq_and_pollKits hLs hMm
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) rfl hPollKits

/-- Closes `h2ki_UntypedDecPkSlot520OkK w` at `w.ghFixed = h2k_ghFixedK mpl mmpl` from
`KitInst.DecPkPollKitsFdsPlacedBudget.CliDecPkPollKitsPlacedOkFds`. -/
theorem h2ki_UntypedDecPkSlot520OkK_of_ghFixedEq_and_kitInstPollKits
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hgh :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      w.ghFixed = h2k_ghFixedK mpl mmpl)
    (hPollKits :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget.CliDecPkPollKitsPlacedOkFds
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits cliRunBudgets (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
          (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))) :
    h2ki_UntypedDecPkSlot520OkK w := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  exact h2ki_UntypedDecPkSlot520OkK_of_ghFixedEq_and_pollKits hLs hMm w hgh
    (fun h547 W γ tp => CliDecPkPollKitsPlacedOkFds.ofKitInst (hPollKits h547 W γ tp))

/-- Closes `h2ki_UntypedDecPkSlot520OkK (mkF3CliElfGhostWitnessK …)` from
`KitInst.DecPkPollKitsFdsPlacedBudget.CliDecPkPollKitsPlacedOkFds`. -/
theorem h2ki_UntypedDecPkSlot520OkK_mkWitness_of_kitInstPollKits
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hPollKits :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget.CliDecPkPollKitsPlacedOkFds
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits cliRunBudgets (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
          (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))) :
    h2ki_UntypedDecPkSlot520OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  exact h2ki_UntypedDecPkSlot520OkK_mkWitness_of_pollKits mpl mmpl hLs hMm hBranch2
    (fun h547 W γ tp => CliDecPkPollKitsPlacedOkFds.ofKitInst (hPollKits h547 W γ tp))

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520Untyped
