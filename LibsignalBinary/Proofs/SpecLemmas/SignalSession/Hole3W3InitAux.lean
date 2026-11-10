/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3BudgetFitsAux
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3VerifySigAux
public import LibsignalBinary.Specifications.SignalSession.CliElf

/-!
# Closed Block-521 `initiate` (`W3`) Slot Bridge

**Checked by Lean.**

Proves `w3m_hole3_w3_init`, discharging `CliInitSlotOkPlaced` at
`realCliInitBinarySlotEnvFixed W` by combining `w3m_verifySignature_vm_ok` and
`w3m_cliInitSlotOkPlacedAt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3InitAux

open Arm64 (GhostName HookSat subroutine_ok)
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries (mallocngLib)
open CryptoVerification
  (LibsignalFullPlacement LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks CliGhostHooksFs cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgPlaced)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
  (ExternNoAllocFailed W3GhostHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliInitSlotOkPlaced CliRunHooksBundle)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (spqrInitialStateInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
  (cliSpqrInitialState_initProg)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (InitialStateParamsEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3BudgetFitsAux
  (w3m_cliInitSlotOkPlacedAt w3m_initiate_budgetFits)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3VerifySigAux
  (w3m_verifySignature_vm_ok)

/-- Constructs `LibsignalFullPlacement` from `libsignalSessionLib.LinkedAt cliElfBytes mpl`. -/
@[instance_reducible]
def w3m_libsignalFullPlacementOf (mpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup) : LibsignalFullPlacement where
  toLibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  placeable := hLs.choose_spec.2.1

/-- Assembles `W3GhostHooks` from `CliGhostSpqrAllocHooks`, `CliGhostHooksFs`, `RunHooksPlaced`, and `lsReadFileSym` `HookSat`. -/
theorem w3m_ghostHooks [LibsignalPlacement]
    {M : AllocCostModel} {mmpl : MultiPlacement} {ghFixed : CliGhostHooks} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hGSpqr : CliGhostSpqrAllocHooks M A lim ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile
        (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : CliRunHooksBundle mmpl ghFixed W A lim (ReadFileRuleEnvFixed cliIo.rd)) :
    W3GhostHooks mmpl ghFixed W A lim (ReadFileRuleEnvFixed cliIo.rd) where
  alloc := hGSpqr
  strClone_fsT := hFs.stringClone_fsT
  stringClone := hHooks.runHooks.stringClone
  formatInner := hHooks.runHooks.formatInner
  readFile := hsat

/-- Lifts block-327 `spqrInitialStateInnerSpec` onto `initProgPlaced`. -/
theorem w3m_spqrInitialState_initProg_ok [LibsignalFullPlacement]
    {mmpl : MultiPlacement} (ghFixed : CliGhostHooks)
    (_hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks) (γ : GhostName) (tp brkStart : BitVec 64)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ghFixed)
    (_hHooks : CliRunHooksBundle mmpl ghFixed W
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (_h547 : lsmpl.base 547 ≠ 0#64) :
    subroutine_ok (initProgPlaced mmpl ghFixed W) (lsmpl.base 327)
      (withLsCodeRoLoaded lsmpl
        (spqrInitialStateInnerSpec (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits (InitialStateParamsEnv W.C.F) W.C.F)) :=
  cliSpqrInitialState_initProg mmpl ghFixed W hGSpqr

/-- Closed block-521 `initiate` (`W3`) slot witness at `realCliInitBinarySlotEnvFixed W`. -/
theorem w3m_hole3_w3_init
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (hGSpqr : @CliGhostSpqrAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns ghFixed (fun _ => none)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64) :
    letI : LibsignalFullPlacement := w3m_libsignalFullPlacementOf mpl hLs hblk hext_nodup
    CliInitSlotOkPlaced mmpl ghFixed
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (realCliInitBinarySlotEnvFixed W) X W := by
  let _ : LibsignalFullPlacement := w3m_libsignalFullPlacementOf mpl hLs hblk hext_nodup
  exact w3m_cliInitSlotOkPlacedAt mmpl ghFixed W X
    (w3m_ghostHooks hGSpqr hFs hsat hHooks)
    (w3m_spqrInitialState_initProg_ok ghFixed hPl_mng W γ tp cliElfImage.brkStart hGSpqr hHooks h547)
    (w3m_verifySignature_vm_ok ghFixed W hGSpqr.toCliGhostAllocHooks)
    hghNoAlloc
    (w3m_initiate_budgetFits W X)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3InitAux
