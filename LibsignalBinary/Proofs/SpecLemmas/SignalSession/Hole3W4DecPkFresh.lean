/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cSlotOkAtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.TryDecryptStmtOfSpqrPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1InstPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkR2

/-!
# Parametric Block-520 `decryptPrekey` (`W4`) Slot Reduction

Provides guard-aware envelope inclusion (`W4fGuardSlotIncl`), fixed-`cliRunBudgets`
callee extraction (`W4fPollCallees`), and Path-C-P3-parametric D2(c) poll assembly
(`W4fPollCustomP3SeqFreeEnv`, `w4f_decPkD2cSlotOk_frozen_customP3_parametric`) for
block-520 `decryptPrekey` under `LibsignalFrozen`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkFresh

open Arm64 (GhostName HookOk HookSat subroutine_ok)
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession (PublicKey SessionState SignalMessage)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalFullPlacement LibsignalPlacement lsmpl lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5Model)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (SessionExtraRel stageP1ProgPlaced)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (clearPending)
open CryptoVerification.E2E (
  PreKeyMessageFields ResponderPreKeySecrets UnreachedPqxdhPrimitives acceptInput
  aesDecHookMallocng modelPrims
)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives)
open CryptoVerification.E2E.Record (encSession encodeRecord)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost uuidTryParse
)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliGhostExterns withPanics_cliGhostExterns
)
open CryptoVerification.SignalSession.Cli.RunProofs (
  DecPkOkD2c SessMatchesPm pkStoreKeys pmOfE
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessPrev1KitPlaced
  dpPollProgPlaced pathAInitSession pathAInitState pmPreKeyId
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (FilesOkPeer loadRec scopeIn scopeKit)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv aesDecBudgetSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  StageP3ErrM3Env StageP3OkPrefixM3Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget (
  OverVerNe1e04CliAtFrozenPlacedBody
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (TryDecryptCliEnvOf)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (
  fineAesDec_budget_hookOk fineHookRustCliAllocBudget
)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase (
  CliDpPollOkD2cStateFrozenPlacedAt DecPkD2cSlotOkFrozenPlaced decPkD2cSlotOk_of_poll_frozen_placed
)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk (
  cliEncodeRawPrealloc_placed_ok cliFmtWrite_budget_sat cliFormatInner_budget_sat
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (EncodeRawPreallocPlacedOkX)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  ReadFileRuleEnvFixed hRead_of_hookSat
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget (
  CliRunHooksBundle
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget (
  cliPollStageP4Prev1SeqFreeEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget (
  overPollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  CliStageP4Prev1Envs StageP2OverEnv StageP4Prev1Env
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  CliPollStageP2Envs P2OverPathCErrEnvOf P2OverPathCOkEnvOf PromoteOverArchiveCanonSessEnv
  PromoteOverArchiveEnv stageP2PathCOver_qpan_cli_archive_full_placed_at_of_seams
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux (
  StageP2PathCOverQpanCliFrozenPlacedAtStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv cliPollSelf_kitPlacedOk_stagesHooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.TryDecryptStmtOfSpqrPlacedBudget (
  overPollTryDecrypt_placed_at_of_tdEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  StageP3ErrEnv StageP3OkPrefixEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget (
  CliDpPollTrustedEnv CliStageP1OkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1InstPlacedBudgetAux (
  StageP2PathAQpanCliFrozenPlacedAtStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliP2PathAOptFieldsErrEnv cliP2PathAOptFieldsOkEnv cliPollKpk_kitPlacedOk
  cliPollPk_kitPlacedOk cliPollSpk_kitPlacedOk stageP2PathA_qpan_cli_full_placed_at_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks CliGhostSpqrAllocHooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (
  SpqrV1PlacedSeams SpqrV1PlacedSeamsOfEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget (
  serContractsX_cli_placed
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## Guarded Envelope `FitsEnv` Refutation and Inclusion -/

/-- `FitsEnv M lim st (fun _ => True)` is unsatisfiable because allocations exceeding `MallocngMaxAllocSize` violate `withinMaxAlloc`. -/
theorem w4f_not_fitsEnv_top {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    ¬ FitsEnv M lim st (fun _ => True) := by
  intro h
  have h1 := h [AllocEvent.alloc (MallocngMaxAllocSize + 1)] trivial
  have h2 : (AllocEvent.alloc (MallocngMaxAllocSize + 1)).withinMaxAlloc := h1.1.1
  dsimp only [AllocEvent.withinMaxAlloc] at h2
  omega

/-- Guard-aware inclusion condition from `PollEnv` into `SlotEnv` under `FilesOkPeer`, `DecPkOkD2c`, and `FitsEnv`. -/
def W4fGuardSlotIncl {M : AllocCostModel} (lim : BudgetLimits) (W : CliHooks)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (PollEnv SlotEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (g : DecPkGhost) (st : M.σ),
    FilesOkPeer Scope g.F g.peer.val →
    DecPkOkD2c ⟨W.C, W.Q⟩ Scope g.F g.peer.val g.me.val g.msg →
    FitsEnv M lim st (SlotEnv g) →
    ∀ evs, PollEnv g evs → SlotEnv g evs

/-- Reduces `W4fGuardSlotIncl` on a guarded envelope `Guard g → InnerEnv g evs` to `Guard g → PollEnv g ⊆ InnerEnv g`. -/
theorem w4f_guardIncl_of_guarded_sub {M : AllocCostModel} {lim : BudgetLimits} {W : CliHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Guard : DecPkGhost → Prop}
    {PollEnv InnerEnv : DecPkGhost → List AllocEvent → Prop}
    (hSub : ∀ g,
      FilesOkPeer Scope g.F g.peer.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ Scope g.F g.peer.val g.me.val g.msg →
      Guard g →
      ∀ evs, PollEnv g evs → InnerEnv g evs) :
    W4fGuardSlotIncl (M := M) lim W Scope PollEnv (fun g evs => Guard g → InnerEnv g evs) := by
  intro g st hfPeer hdecOk hFits evs hPoll hGuard
  have _ : Guard g := by
    by_contra hng
    exact w4f_not_fitsEnv_top (hFits.mono fun _ _ hG => absurd hG hng)
  exact hSub g hfPeer hdecOk hGuard evs hPoll

/-! ## State-Aware Block-518 Monotonicity and Outer Slot Reduction -/

/-- Monotonizes `CliDpPollOkD2cStateFrozenPlacedAt` on block 518 along `W4fGuardSlotIncl`. -/
theorem w4f_dpPollOkD2cState_frozen_of_guardIncl [LibsignalFullPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PollEnv SlotEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hpoll : CliDpPollOkD2cStateFrozenPlacedAt A lim ReadEnv DeserEnv PollEnv mmpl gh W X B S Scope)
    (hIncl : W4fGuardSlotIncl (M := M) lim W Scope PollEnv SlotEnv) :
    CliDpPollOkD2cStateFrozenPlacedAt A lim ReadEnv DeserEnv SlotEnv mmpl gh W X B S Scope := by
  exact LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkR2.w4r2_dpPollOkD2cState_frozen_of_guardIncl
    mmpl gh W X B S Scope hpoll hIncl

/-- Reduces `DecPkD2cSlotOkFrozenPlaced` at `SlotEnv` to block-518 poll correctness at `PollEnv X` and `W4fGuardSlotIncl`. -/
theorem w4f_decPkD2cSlotOk_frozen_of_poll_and_guardIncl [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PollEnv : UnreachedPqxdhPrimitives → DecPkGhost → List AllocEvent → Prop}
    {SlotEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hpoll : ∀ X S,
      CliDpPollOkD2cStateFrozenPlacedAt A lim ReadEnv DeserEnv (PollEnv X)
        mmpl gh W X cliRunBudgets S scopeIn)
    (hIncl : ∀ X, W4fGuardSlotIncl (M := M) lim W scopeIn (PollEnv X) SlotEnv) :
    DecPkD2cSlotOkFrozenPlaced mmpl gh W A lim SlotEnv :=
  decPkD2cSlotOk_of_poll_frozen_placed mmpl gh W hh hRead hDeser fun X S =>
    w4f_dpPollOkD2cState_frozen_of_guardIncl mmpl gh W X cliRunBudgets S scopeIn
      (hpoll X S) (hIncl X)

/-! ## Fixed-`cliRunBudgets` Callee Extraction -/

/-- Fixed-`cliRunBudgets` callee bundle for block-518 `decryptPrekey` poll verification. -/
structure W4fPollCallees [LibsignalPlacement] (mmpl : MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (γ : GhostName) (tp brkStart : BitVec 64) : Prop where
  hG : CliGhostAllocHooks fineCostModel
    (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits gh
  hh : RunHooksPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
    (cliGhostExterns gh (cliExternsPlaced mmpl W))
  hReadPoll : subroutine_ok
    (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (lsρ lsReadFileSym)
    (readFileSpecPlaced cliIo.rd cliWrOk
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))
  hReadHelpers : subroutine_ok
    (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (lsρ lsReadFileSym)
    (readFileSpecPlaced cliIo.rd cliWrOk
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))
  hDeserPoll : subroutine_ok
    (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (lsmpl.base 46)
    (sessDeserializeSpecPlaced scopeKit
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (fun r => RecordDeserializeCancelEnv (encodeRecord r)))
  hDeserHelpers : subroutine_ok
    (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (lsmpl.base 46)
    (sessDeserializeSpecPlaced scopeKit
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (fun r => RecordDeserializeCancelEnv (encodeRecord r)))
  hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D)
    (aesDecBudgetSpec W.C.D fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits)
  hRaw : EncodeRawPreallocPlacedOkX
    (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc
    (cliGhostExterns gh (cliExternsPlaced mmpl W))

theorem w4f_dpPollProgPlaced_helpers_eq_poll [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  dsimp only [CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced,
    dpPollProgPlaced, stageP1ProgPlaced]
  rw [withPanics_cliGhostExterns mmpl gh W]

/-- Constructs `W4fPollCallees` from the non-ELF hypotheses of `hole3_w4_decPk`. -/
theorem w4f_pollCallees_of_f3Hooks [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits gh)
    (hsat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : CliRunHooksBundle mmpl gh W
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd)) :
    W4fPollCallees mmpl gh W γ tp brkStart := by
  let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
  have hG : CliGhostAllocHooks fineCostModel A cliBudgetLimits gh := hGSpqr.toCliGhostAllocHooks
  have hEq := w4f_dpPollProgPlaced_helpers_eq_poll mmpl gh W
  have hReadP : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)) :=
    hRead_of_hookSat hsat
  have hDeserP : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A cliBudgetLimits
        (fun r => RecordDeserializeCancelEnv (encodeRecord r))) := by
    exact LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkR2.w4r2_hDeserP
      mmpl gh W γ tp brkStart hG
  have hAesOk : HookOk (aesDecHookMallocng mmpl W.C.D)
      (aesDecBudgetSpec W.C.D fineCostModel A cliBudgetLimits) :=
    fineAesDec_budget_hookOk γ tp brkStart cliBudgetLimits hPl_mng W.C.D
  have hRaw : EncodeRawPreallocPlacedOkX A.repAlloc
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliEncodeRawPrealloc_placed_ok (serContractsX_cli_placed mmpl gh W hG)
  exact
    { hG := hG
      hh := hHooks.runHooks
      hReadPoll := hReadP
      hReadHelpers := hEq.symm ▸ hReadP
      hDeserPoll := hDeserP
      hDeserHelpers := hEq.symm ▸ hDeserP
      hAesDec := hAesOk
      hRaw := hRaw }

private theorem w4f_fmtWriteEnv_nonempty : ∃ evs, FmtWriteEnv evs := ⟨[], rfl⟩

private theorem w4f_formatInnerEnv_nonempty : ∃ evs, FormatInnerEnv evs := ⟨[], rfl⟩

/-- Block-507 `try_decrypt_with_state` contract on `dpPollProgPlaced`, parametric in `RecvBytesEnv` and `tdEnv`. -/
theorem w4f_try507_of_tdEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqrTd : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv W a evs) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))) :=
  overPollTryDecrypt_placed_at_of_tdEnv mmpl gh W ctl hG hAesDec hSpqrTd
    (cliFmtWrite_budget_sat mmpl gh W) (cliFormatInner_budget_sat mmpl gh W)
    hRecv_ne w4f_fmtWriteEnv_nonempty w4f_formatInnerEnv_nonempty htd

/-! ## Per-Path Stage and Poll Contracts -/

/-- Path-A Stage-P2 (`opt = none`) contract under `LibsignalFrozen` at `cliRunBudgets`. -/
theorem w4f_stageP2PathA_frozen_at_cliRunBudgets [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W) :
    StageP2PathAQpanCliFrozenPlacedAtStmt A lim ReadEnv X mmpl gh W cliRunBudgets
      (cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W cliRunBudgets
        (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
      (cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W cliRunBudgets
        (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv)) :=
  stageP2PathA_qpan_cli_full_placed_at_ok A lim (ReadEnv := ReadEnv) X mmpl gh W cliRunBudgets
    (senv := fun F0 peer =>
      cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv)
    hDropNz hG hSpqr
    (fun F0 peer hh_sk hReadB =>
      cliPollSelf_kitPlacedOk_stagesHooks mmpl gh W cliRunBudgets F0 peer hDropNz hh_sk hReadB)

/-- Fixed-`cliRunBudgets` Stage-P2 kit envelopes on Path-C Over. -/
def w4f_cliP2KitEnvsFixed [LibsignalPlacement] (A : RustAlloc)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (peer : AddrGhost) (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey) :
    CliPollStageP2Envs (A := A) cliRunBudgets F0 peer spkId kpkId opkWord kbk :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cSlotOkAtPlacedBudget.cliP2KitEnvsAt
    A ReadEnv cliRunBudgets F0 peer spkId kpkId opkWord kbk

/-- Sequence-free CLI Stage-P4 `Prev1` 4-kit envelope bundle. -/
abbrev w4f_cliPollStageP4Prev1SeqFreeEnvsAt [LibsignalPlacement] (A : RustAlloc)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) :
    CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk :=
  let e := cliPollStageP4Prev1SeqFreeEnvs A B F0 peer pid kpkId spkId kbk ReadEnv
  ⟨⟨e.opsEnv.storePollPrev1Env⟩, e.ikitEnv, e.pkKitEnv, e.kpkKitEnv⟩

/-- Path-C Stage-P2 Over (`PromoteOverArchiveEnv`) contract under `LibsignalFrozen` at `cliRunBudgets`. -/
theorem w4f_stageP2PathCOver_archive_frozen_at_cliRunBudgets [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives) (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hErrEnv : ∀ g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (w4f_cliP2KitEnvsFixed A.repAlloc ReadEnv) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv
        (w4f_cliP2KitEnvsFixed A.repAlloc ReadEnv) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W cliRunBudgets
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (w4f_cliP2KitEnvsFixed A.repAlloc ReadEnv))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W cliRunBudgets
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv
            (w4f_cliP2KitEnvsFixed A.repAlloc ReadEnv))
          g r)) :
    StageP2PathCOverQpanCliFrozenPlacedAtStmt A lim PromoteOverArchiveEnv
      X mmpl gh W cliRunBudgets P2OverErrEnv P2OverOkEnv :=
  stageP2PathCOver_qpan_cli_archive_full_placed_at_of_seams
    A lim X mmpl gh W cliRunBudgets (kitEnvs := w4f_cliP2KitEnvsFixed A.repAlloc ReadEnv)
    hErrEnv hOkEnv hFitsSplit hDropNz hG hSpqr
    (fun F0 peer _ _ _ _ hh_sk =>
      cliPollSelf_kitPlacedOk_stagesHooks mmpl gh W cliRunBudgets F0 peer hDropNz hh_sk hRead)
    (fun F0 _ spkId _ _ _ hh_sk =>
      cliPollSpk_kitPlacedOk mmpl gh W cliRunBudgets F0 spkId hDropNz hh_sk hRead)
    (fun F0 _ spkId kpkId _ kbk hh_sk =>
      cliPollKpk_kitPlacedOk mmpl gh W cliRunBudgets F0 kpkId spkId kbk hDropNz hh_sk hRead)
    (fun F0 _ _ _ opkWord _ hh_sk =>
      cliPollPk_kitPlacedOk mmpl gh W cliRunBudgets F0 opkWord hDropNz hh_sk hRead)

/-- Parametric Path-C Stage-P3 envelope bundle (`errEnv`, `verNeEnv`, `okPrefixEnv`). -/
structure W4fPathCP3Envs where
  errEnv : SessionGhost → SessionGhost → SessionState (List (BitVec 8)) → AddrGhost → AddrGhost →
    SignalMessageGhost → SignalMessage → List (BitVec 8) → List AllocEvent → Prop
  verNeEnv : SessionGhost → SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop
  okPrefixEnv : SessionGhost → SessionGhost → SessionState (List (BitVec 8)) → AddrGhost → AddrGhost →
    SignalMessageGhost → SignalMessage → List (BitVec 8) → List AllocEvent → Prop

/-- Tight Path-C Stage-P3 envelopes parameterized by `tdEnvW` and `verNeDecEnv`. -/
def w4f_tightPathCP3Envs (tdEnvW : TryDecryptEnvArgs → List AllocEvent → Prop)
    (verNeDecEnv : List (BitVec 8) → List AllocEvent → Prop) : W4fPathCP3Envs where
  errEnv := StageP3ErrEnv tdEnvW
  verNeEnv := StageP3VerNePrev1Env verNeDecEnv
  okPrefixEnv := StageP3OkPrefixEnv tdEnvW

/-- Widened Path-C Stage-P3 envelopes (`StageP3ErrM3Env`, `StageP3VerNePrev1Env`, `StageP3OkPrefixM3Env`). -/
def w4f_wideM3PathCP3Envs (tdEnvW : TryDecryptEnvArgs → List AllocEvent → Prop)
    (verNeDecEnv : List (BitVec 8) → List AllocEvent → Prop) : W4fPathCP3Envs where
  errEnv := StageP3ErrM3Env tdEnvW
  verNeEnv := StageP3VerNePrev1Env verNeDecEnv
  okPrefixEnv := StageP3OkPrefixM3Env tdEnvW

/-- Path-C-P3-parametric, sequence-free D2(c) poll trace envelope at `cliRunBudgets`. -/
def W4fPollCustomP3SeqFreeEnv [LibsignalPlacement] (A : RustAlloc)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (p3c : CliHooks → W4fPathCP3Envs)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let σ := cliKitStk cliRunBudgets
  let pid := pmPreKeyId g.msg
  let kbk := g.msg.baseKey
  let P1 := CliStageP1OkEnv (A := A) cliRunBudgets ReadEnv DeserEnv g
  let P2AErr := cliP2PathAOptFieldsErrEnv A ReadEnv X W cliRunBudgets
    (fun F0 peer => cliPollSelfBudgetEnv A F0 peer σ ReadEnv)
  let P2AOk := cliP2PathAOptFieldsOkEnv A ReadEnv X W cliRunBudgets
    (fun F0 peer => cliPollSelfBudgetEnv A F0 peer σ ReadEnv)
  CliDpPollTrustedEnv (A := A) W X cliRunBudgets ReadEnv DeserEnv P2AErr P2AOk (tdEnv W) g evs ∨
  ∃ (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8))),
    loadRec scopeIn g.F g.peer.val = .ok (some r) ∧
    r.currentSession = some s_old ∧
    ¬ SessMatchesPm s_old g.msg ∧
    StoresGhost.opened.identity.trusted cliIo.rd g.F g.peer.val g.msg.identityKey = .ok true ∧
    (SeqEnv P1 (P2OverErrEnv g r) evs ∨
     ∃ (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
       (kp : IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
       (recG : SessionGhost) (whisperG : SignalMessageGhost),
       g.msg = pmOfE m i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
       let enc_old := encSession (clearPending s_old)
       ((∃ G₁, CloneRel recG G₁ ∧
           SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
             ((p3c W).errEnv recG G₁ st0 g.peer g.me whisperG g.msg.message g.coins) evs) ∨
        SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
          ((p3c W).verNeEnv recG st0 enc_old) evs ∨
        ∃ G₁ G' pt,
          CloneRel recG G₁ ∧
          G₁.AfterTryDecrypt true G' ∧
          (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins st0).1 = .ok pt ∧
          let envs := w4f_cliPollStageP4Prev1SeqFreeEnvsAt A cliRunBudgets g.F g.peer pid
            m.kpkId m.spkId kbk ReadEnv
          let ses' : Session (List (BitVec 8)) :=
            { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
              state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins st0).2
              pendingPreKey := none
              pendingKyberPreKey := none }
          SeqEnv
            (SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
              ((p3c W).okPrefixEnv recG G₁ st0 g.peer g.me whisperG g.msg.message g.coins))
            (StageP4Prev1Env
              (cliPollSessPrev1KitPlaced A g.F g.peer σ) envs.opsEnv
              (cliPollIdKitPlaced A g.F g.peer σ) envs.ikitEnv
              (cliPollPkKitPlaced A g.F pid σ) envs.pkKitEnv
              (cliPollKpkKitPlaced A g.F m.kpkId m.spkId kbk σ) envs.kpkKitEnv
              StoresGhost.opened.sessions StoresGhost.opened.identity
              StoresGhost.opened.oneTime StoresGhost.opened.kyber
              g.peer.val g.msg.identityKey m.kpkId m.spkId kbk m.opkId G' ses' enc_old)
            evs))

/-- Block-518 D2(c) poll contract (`CliDpPollOkD2cStateFrozenPlacedAt`) at `W4fPollCustomP3SeqFreeEnv`. -/
theorem w4f_poll_d2c_customP3_seqFree_frozen_at [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PrevEncOK : List (BitVec 8) → Prop}
    {verNeDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p3c : CliHooks → W4fPathCP3Envs}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (S : RunSem)
    (hG : CliGhostAllocHooks M A lim gh)
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hTry0 : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hPrevEnc : ∀ r s_old, scopeIn r → r.currentSession = some s_old →
      PrevEncOK (encSession (clearPending s_old)))
    (hVerNeAt : OverVerNe1e04CliAtFrozenPlacedBody A lim PrevEncOK verNeDecEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hp3Err : ∀ recG G₁ st rem loc msgG msg rest evs,
      StageP3ErrM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs →
      (p3c W).errEnv recG G₁ st rem loc msgG msg rest evs)
    (hp3VerNe : ∀ recG st enc evs,
      StageP3VerNePrev1Env verNeDecEnv recG st enc evs →
      (p3c W).verNeEnv recG st enc evs)
    (hp3Ok : ∀ recG G₁ st rem loc msgG msg rest evs,
      StageP3OkPrefixM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs →
      (p3c W).okPrefixEnv recG G₁ st rem loc msgG msg rest evs)
    (hp3Fits : ∀ st_b recG st rem loc msgG msg msgVer enc rest,
      FitsEnv M lim st_b
        (fun evs =>
          (∃ G₁, CloneRel recG G₁ ∧ (p3c W).errEnv recG G₁ st rem loc msgG msg rest evs) ∨
          (p3c W).verNeEnv recG st enc evs ∨
          ∃ G₁, CloneRel recG G₁ ∧ (p3c W).okPrefixEnv recG G₁ st rem loc msgG msg rest evs) →
      FitsEnv M lim st_b
        (StageP3Prev1Env (tdEnv W) verNeDecEnv recG st rem loc msgG msg msgVer enc rest))
    (hErrEnv : ∀ g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (w4f_cliP2KitEnvsFixed A.repAlloc ReadEnv) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv
        (w4f_cliP2KitEnvsFixed A.repAlloc ReadEnv) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W cliRunBudgets
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (w4f_cliP2KitEnvsFixed A.repAlloc ReadEnv))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W cliRunBudgets
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv
            (w4f_cliP2KitEnvsFixed A.repAlloc ReadEnv))
          g r)) :
    CliDpPollOkD2cStateFrozenPlacedAt A lim ReadEnv DeserEnv
      (W4fPollCustomP3SeqFreeEnv A.repAlloc W X ReadEnv DeserEnv P2OverErrEnv P2OverOkEnv tdEnv p3c)
      mmpl gh W X cliRunBudgets S scopeIn := by
  exact LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkR2.w4r2_poll_d2c_customP3_seqFree_frozen_at_fns
    (p3ErrEnv := fun W' => (p3c W').errEnv)
    (p3VerNeEnv := fun W' => (p3c W').verNeEnv)
    (p3OkPrefixEnv := fun W' => (p3c W').okPrefixEnv)
    hDropNz mmpl gh W X S hG hSpqr hRaw hRead hTry0 hPrevEnc hVerNeAt
    hp3Err hp3VerNe hp3Ok hp3Fits hErrEnv hOkEnv hFitsSplit

/-- Parametric `DecPkD2cSlotOkFrozenPlaced` discharger from fixed-`cliRunBudgets` hooks and `W4fGuardSlotIncl`. -/
theorem w4f_decPkD2cSlotOk_frozen_customP3_parametric [LibsignalFullPlacement]
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      UnreachedPqxdhPrimitives → DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PrevEncOK : List (BitVec 8) → Prop}
    {verNeDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p3c : CliHooks → W4fPathCP3Envs}
    {SlotEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits gh)
    (hsat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : CliRunHooksBundle mmpl gh W
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (hSpqr : SpqrV1PlacedSeams fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits mmpl gh W)
    (hSpqrTd : SpqrV1PlacedSeamsOfEnv fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv W a evs)
    (hPrevEnc : ∀ r s_old, scopeIn r → r.currentSession = some s_old →
      PrevEncOK (encSession (clearPending s_old)))
    (hVerNeAt : OverVerNe1e04CliAtFrozenPlacedBody
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits PrevEncOK verNeDecEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hp3Err : ∀ recG G₁ st rem loc msgG msg rest evs,
      StageP3ErrM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs →
      (p3c W).errEnv recG G₁ st rem loc msgG msg rest evs)
    (hp3VerNe : ∀ recG st enc evs,
      StageP3VerNePrev1Env verNeDecEnv recG st enc evs →
      (p3c W).verNeEnv recG st enc evs)
    (hp3Ok : ∀ recG G₁ st rem loc msgG msg rest evs,
      StageP3OkPrefixM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs →
      (p3c W).okPrefixEnv recG G₁ st rem loc msgG msg rest evs)
    (hp3Fits : ∀ st_b recG st rem loc msgG msg msgVer enc rest,
      FitsEnv fineCostModel cliBudgetLimits st_b
        (fun evs =>
          (∃ G₁, CloneRel recG G₁ ∧ (p3c W).errEnv recG G₁ st rem loc msgG msg rest evs) ∨
          (p3c W).verNeEnv recG st enc evs ∨
          ∃ G₁, CloneRel recG G₁ ∧ (p3c W).okPrefixEnv recG G₁ st rem loc msgG msg rest evs) →
      FitsEnv fineCostModel cliBudgetLimits st_b
        (StageP3Prev1Env (tdEnv W) verNeDecEnv recG st rem loc msgG msg msgVer enc rest))
    (hErrEnv : ∀ X g r evs,
      P2OverPathCErrEnvOf (A := (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc)
        X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (w4f_cliP2KitEnvsFixed (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc
          (ReadFileRuleEnvFixed cliIo.rd)) g r evs →
      P2OverErrEnv X g r evs)
    (hOkEnv : ∀ X g r evs,
      P2OverPathCOkEnvOf (A := (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc)
        X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv
        (w4f_cliP2KitEnvsFixed (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc
          (ReadFileRuleEnvFixed cliIo.rd)) g r evs →
      P2OverOkEnv X g r evs)
    (hFitsSplit : ∀ X st_b g r,
      FitsEnv fineCostModel cliBudgetLimits st_b
        (StageP2OverEnv (P2OverErrEnv X) (P2OverOkEnv X) g r) →
      FitsEnv fineCostModel cliBudgetLimits st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc)
            X W cliRunBudgets
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (w4f_cliP2KitEnvsFixed (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc
              (ReadFileRuleEnvFixed cliIo.rd)))
          (P2OverPathCOkEnvOf (A := (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc)
            X W cliRunBudgets
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv
            (w4f_cliP2KitEnvsFixed (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc
              (ReadFileRuleEnvFixed cliIo.rd)))
          g r))
    (hIncl : ∀ X,
      W4fGuardSlotIncl (M := fineCostModel) cliBudgetLimits W scopeIn
        (W4fPollCustomP3SeqFreeEnv (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc
          W X (ReadFileRuleEnvFixed cliIo.rd)
          (fun r => RecordDeserializeCancelEnv (encodeRecord r))
          (P2OverErrEnv X) (P2OverOkEnv X) tdEnv p3c)
        SlotEnv) :
    DecPkD2cSlotOkFrozenPlaced mmpl gh W
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits SlotEnv := by
  have hCal := w4f_pollCallees_of_f3Hooks mmpl gh W γ tp brkStart hPl_mng hGSpqr hsat hHooks
  exact w4f_decPkD2cSlotOk_frozen_of_poll_and_guardIncl mmpl gh W hCal.hh
    hCal.hReadHelpers hCal.hDeserHelpers
    (fun X S =>
      w4f_poll_d2c_customP3_seqFree_frozen_at hDropNz mmpl gh W X S
        hCal.hG hSpqr hCal.hRaw hCal.hReadPoll
        (w4f_try507_of_tdEnv mmpl gh W 0#64 hCal.hG hCal.hAesDec hSpqrTd hRecv_ne htd)
        hPrevEnc hVerNeAt hp3Err hp3VerNe hp3Ok hp3Fits
        (hErrEnv X) (hOkEnv X) (hFitsSplit X))
    hIncl

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkFresh
