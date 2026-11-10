/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W1InnerTight
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.V1MergeBlk325Cli
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesCountedR
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStatePlacedBudget

/-!
# Closed Block-464 `encrypt` (`W1`) Slot Witness

**Checked by Lean.**

Instantiates `Hole3W1InnerTight.w1t_hole3_w1_inner_of_e2a325` with the closed block-325
`decode_state`, block-299 `EpochDirection::merge`, and block-298 `V1State::merge` contracts.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W1InnerTightGlue

open Arm64 (GhostName HookSat)
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries (mallocngLib)
open CryptoVerification
  (LibsignalFullPlacement LibsignalPlacement libsignalMutatedBlocks
   libsignalSessionExterns libsignalSessionLib)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliRunNeeds cliWrOk)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (mkSlot)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks CliGhostHooksFs cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliRunHooksBundle)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (encSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W1InnerTight
  (w1t_cliEncryptBinaryKitSlotEnvExact w1t_hole3_w1_inner_of_e2a325 w1t_libsignalFullPlacementOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.V1MergeBlk325Cli
  (v1StateMergeBlk325_cli)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesCountedR
  (e2ar_epochDirectionMerge_blk325_cl_ok_tight)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStatePlacedBudget
  (e2a_decodeState_cl_placed_ok_of_v1Merge_109)

/-- Closed block-464 `encrypt` (`W1`) slot witness at `w1t_cliEncryptBinaryKitSlotEnvExact`. -/
theorem w1t_hole3_w1_inner_closed
    {elfBytes : List (BitVec 8)} {brkStart : BitVec 64}
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt elfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64) :
    letI : LibsignalFullPlacement := w1t_libsignalFullPlacementOf mpl hLs hblk hext_nodup
    (mkSlot
      (encSlotSpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (w1t_cliEncryptBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  exact w1t_hole3_w1_inner_of_e2a325
    hLs hblk hext_nodup ghFixed hPl_mng X W γ tp hGSpqr hFs hsat hHooks h547
    e2a_decodeState_cl_placed_ok_of_v1Merge_109
    e2ar_epochDirectionMerge_blk325_cl_ok_tight
    (v1StateMergeBlk325_cli mmpl ghFixed W hGSpqr.toCliGhostAllocHooks)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W1InnerTightGlue
