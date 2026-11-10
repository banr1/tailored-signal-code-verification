/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAOfEnvPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget

/-!
# Closed All-4-Kits `[LibsignalFullPlacement]` Stage P2 Path-A Wrapper

Instantiates `stageP2PathAQpan_cli_d3_at_frozen_placed_of_seams_ofEnv` at all four CLI store kits
(`self`, `spk`, `kpk`, `pk`) from `hDropNz` and `SpqrV1PlacedSeamsOfEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAFullPlacedBudget

open Arm64.Obj (MultiPlacement)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalFullPlacement LibsignalPlacement lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives modelPrims)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (SendCall VecArg)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (CliGhostHooks)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (cliKitStk)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAOfEnvPlacedBudget (
  stageP2PathAQpan_cli_d3_at_frozen_placed_of_seams_ofEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAPlacedBudget (
  P2PathAErrEnvD3Of P2PathAOkEnvD3Of StageP2PathAQpanCliD3AtFrozenPlacedBudgetStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv cliPollSelf_kitPlacedOk_stagesHooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  StageP2PathAEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliPollKpk_kitPlacedOk cliPollPk_kitPlacedOk cliPollSpk_kitPlacedOk cliStageP2KitEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)

/-- Canonical `[LibsignalFullPlacement]` D3 Path A Stage P2 error envelope (`P2PathAErrEnvD3Of`
instantiated at `InitializeBobV1OptFieldsEnv`, `AcceptOptFieldsEnv`, and the 4 CLI store kits). -/
abbrev cliP2PathAD3OptFieldsErrEnv [LibsignalPlacement]
    (A : RustAlloc)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets) :
    DecPkGhost → List AllocEvent → Prop :=
  P2PathAErrEnvD3Of (A := A) X W B
    (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
    (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
    (cliStageP2KitEnvs (A := A) ReadEnv B
      (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B) ReadEnv))

/-- Canonical `[LibsignalFullPlacement]` D3 Path A Stage P2 normal-exit (`+0x1778`) envelope
(`P2PathAOkEnvD3Of` instantiated at `InitializeBobV1OptFieldsEnv` and the 4 CLI store kits). -/
abbrev cliP2PathAD3OptFieldsOkEnv [LibsignalPlacement]
    (A : RustAlloc)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets) :
    DecPkGhost → List AllocEvent → Prop :=
  P2PathAOkEnvD3Of (A := A) X W B
    (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
    (cliStageP2KitEnvs (A := A) ReadEnv B
      (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B) ReadEnv))

/-- Instantiates `StageP2PathAQpanCliD3AtFrozenPlacedBudgetStmt` at all four CLI store kits
(`self`, `spk`, `kpk`, `pk`) from `hDropNz` and `SpqrV1PlacedSeamsOfEnv`. -/
theorem stageP2PathAQpan_cli_d3_full_placed_of_seams_ofEnv [LibsignalFullPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives) (mmpl : MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    {P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    (hErrEnv : ∀ g evs,
      cliP2PathAD3OptFieldsErrEnv A.repAlloc ReadEnv X W B g evs →
      P2PathAErrEnv g evs)
    (hOkEnv : ∀ g evs,
      cliP2PathAD3OptFieldsOkEnv A.repAlloc ReadEnv X W B g evs →
      P2PathAOkEnv g evs)
    (hFitsSplit : ∀ st_b g,
      FitsEnv M lim st_b (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv g) →
      FitsEnv M lim st_b
        (StageP2PathAEnv
          (cliP2PathAD3OptFieldsErrEnv A.repAlloc ReadEnv X W B)
          (cliP2PathAD3OptFieldsOkEnv A.repAlloc ReadEnv X W B)
          g))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W (InitialStateEnv W.C.F) RecvEnv SendEnv) :
    StageP2PathAQpanCliD3AtFrozenPlacedBudgetStmt A lim ReadEnv DeserEnv X mmpl gh W B
      P2PathAErrEnv P2PathAOkEnv :=
  stageP2PathAQpan_cli_d3_at_frozen_placed_of_seams_ofEnv A lim X mmpl gh W B
    (kitEnvs :=
      cliStageP2KitEnvs (A := A.repAlloc) ReadEnv B
        (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv))
    hErrEnv hOkEnv hFitsSplit hDropNz hG hSpqr
    (fun F0 peer _ _ _ _ hh hRead =>
      cliPollSelf_kitPlacedOk_stagesHooks mmpl gh W B F0 peer hDropNz hh hRead)
    (fun F0 _ spkId _ _ _ hh hRead =>
      cliPollSpk_kitPlacedOk mmpl gh W B F0 spkId hDropNz hh hRead)
    (fun F0 _ spkId kpkId _ kbk hh hRead =>
      cliPollKpk_kitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hRead)
    (fun F0 _ _ _ opkWord _ hh hRead =>
      cliPollPk_kitPlacedOk mmpl gh W B F0 opkWord hDropNz hh hRead)

/-- Concrete-envelope specialization of `stageP2PathAQpan_cli_d3_full_placed_of_seams_ofEnv`. -/
theorem StageP2PathAQpan_cli_d3_full_placed_of_seams [LibsignalFullPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives) (mmpl : MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W (InitialStateEnv W.C.F) RecvEnv SendEnv) :
    StageP2PathAQpanCliD3AtFrozenPlacedBudgetStmt A lim ReadEnv DeserEnv X mmpl gh W B
      (cliP2PathAD3OptFieldsErrEnv A.repAlloc ReadEnv X W B)
      (cliP2PathAD3OptFieldsOkEnv A.repAlloc ReadEnv X W B) :=
  stageP2PathAQpan_cli_d3_full_placed_of_seams_ofEnv A lim X mmpl gh W B
    (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => h) hDropNz hG hSpqr

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAFullPlacedBudget
