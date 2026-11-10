/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.TryDecryptStmtOfSpqrPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.WrapperOverPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import GeneratedLean.LibsignalSessionCode
import LibsignalBinary.Heap.IfaceBudget
import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Heap.RustStdAllocBudgetBridge
import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackPlaced
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Gen
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5Budget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNe
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevVerNePlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.BodyPlaced
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgePlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux
import LibsignalBinary.Proofs.Cli.PublicApi.StoreSession.CoinsTapePlaced
import LibsignalBinary.Proofs.Common.HookTrace
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.ErrExit
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberMarkFitPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecsPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Placed
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage4OverInstPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage4OverInstPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathACore
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCalleesPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureDefsPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntry
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePanicPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4ContPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4ContPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4PlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1Placed
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedInstPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFoldPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1InstPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CoinsBridgePlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePollPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1Budget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlaced
import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Common
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Record.FetchDecrypt
import ProofLib.SepLogic.WP
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Pointwise `(mmpl, gh, W)` `[LibsignalFullPlacement]` `DecPkD2cSlotOk` Discharger

Pointwise `(mmpl, gh, W)` dischargers for `OverDecPkD2cSlotOkFrozenPlaced` and fixed-`X`
`DecPkD2cSlotOkFrozenPlacedAt` at both `PromoteOverCanonSessEnv` and
`PromoteOverArchiveCanonSessEnv`, parametric in `ReadEnv`, `tdEnv`, and `DecPkEnv` with no
universal-`mmpl` premises.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false
namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cSlotOkAtPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalFullPlacement LibsignalPlacement lsmpl lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (stageP1ProgPlaced)
open CryptoVerification.E2E (
  UnreachedPqxdhPrimitives aesDecHookMallocng fmtWriteHook0 formatInnerHook0 modelPrims
)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced cliHookTablePlaced
  lsFmtWriteSym lsFormatInnerSym lsReadFileSym
  lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli
  lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other withPanics_cliGhostExterns
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (cliKitStk dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  fmtWrite_row_placed formatInner_row_placed scopeKit
)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fmtWriteHook0_budget_ok formatInnerHook0_budget_ok)
open LibsignalBinary.Heap.SpecBudget (
  FmtWriteEnv FormatInnerEnv aesDecBudgetSpec fmtWriteBudgetSpec formatInnerBudgetSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (
  TryDecryptCliEnv TryDecryptCliEnvOf
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (EncodeRawPreallocPlacedOkX)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget (
  cliPollStageP4Prev1Envs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget (
  overPollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  CliStageP4Prev1Envs StageP2OverEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPlacedBudget (
  CliDpPollD2cEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  CliPollStageP2Envs P2OverPathCErrEnvOf P2OverPathCOkEnvOf
  PromoteOverArchiveCanonSessEnv PromoteOverCanonSessEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.TryDecryptStmtOfSpqrPlacedBudget (
  overPollTryDecrypt_placed_at_of_spqr overPollTryDecrypt_placed_at_of_tdEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.WrapperOverPlacedBudget (
  DecPkD2cSlotOkFrozenPlacedAt OverDecPkD2cSlotOkFrozenPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliP2PathAOptFieldsErrEnv cliP2PathAOptFieldsOkEnv cliStageP2KitEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (
  SpqrRecvBytesEnv SpqrV1PlacedSeams SpqrV1PlacedSeamsOfEnv spqrRecvBytesEnv_nonempty
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## 1. Canonical Stage-P2 Kit Envelope Bundle & Formatting Hook Helpers -/

/-- Canonical CLI Stage-P2 kit envelope bundle at `(A, ReadEnv, B)`. -/
abbrev cliP2KitEnvsAt [LibsignalPlacement] (A : RustAlloc)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey) :
    CliPollStageP2Envs (A := A) B F0 peer spkId kpkId opkWord kbk :=
  cliStageP2KitEnvs (A := A) ReadEnv B
    (fun F0' peer' => cliPollSelfBudgetEnv A F0' peer' (cliKitStk B) ReadEnv)
    F0 peer spkId kpkId opkWord kbk

/-- Canonical CLI Stage-P4 `Prev1` 4-kit envelope bundle typed in
`PollOverPathCPlacedBudgetAux.CliStageP4Prev1Envs` (`rfl`-identical fields to
`PollOverP4ContPlacedBudget.cliPollStageP4Prev1Envs`). -/
abbrev cliPollStageP4Prev1EnvsAt [LibsignalPlacement] (A : RustAlloc)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) :
    CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk :=
  let e := cliPollStageP4Prev1Envs A B F0 peer pid kpkId spkId kbk ReadEnv
  ⟨⟨e.opsEnv.storePollPrev1Env⟩, e.ikitEnv, e.pkKitEnv, e.kpkKitEnv⟩

private theorem cliGhost_row_eq (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {sym : String} {f : State → State}
    (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (h1 : sym ≠ lsRustAllocSymCli := by decide)
    (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide)
    (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide)
    (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ lsReadFileSym := by decide)
    (h8 : sym ≠ CryptoVerification.SignalSession.lsReadStdinSym := by decide)
    (h9 : sym ≠ CryptoVerification.LibsignalTripleRatchet.lsMemsetSym := by decide)
    (h10 : sym ≠ CryptoVerification.LibsignalTripleRatchet.lsMemcpySym := by decide) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) sym = some f :=
  (cliGhostExterns_other gh (cliExternsPlaced mmpl W) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).trans
    (cliExternsPlaced_row mmpl W hrow)

/-- Closed `formatInnerBudgetSpec` `HookSat` on `cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliFormatInner_budget_sat {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetSpec M A lim) :=
  ⟨formatInnerHook0, cliGhost_row_eq mmpl gh W (formatInner_row_placed mmpl W),
    formatInnerHook0_budget_ok M A lim⟩

/-- Closed `fmtWriteBudgetSpec` `HookSat` on `cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliFmtWrite_budget_sat {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetSpec M A lim) :=
  ⟨fmtWriteHook0, cliGhost_row_eq mmpl gh W (fmtWrite_row_placed mmpl W),
    fmtWriteHook0_budget_ok M A lim⟩

private theorem fmtWriteEnv_nonempty : ∃ evs, FmtWriteEnv evs :=
  ⟨[], rfl⟩

private theorem formatInnerEnv_nonempty : ∃ evs, FormatInnerEnv evs :=
  ⟨[], rfl⟩

theorem dpPollProgPlaced_helpers_eq_poll [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  dsimp only [
    CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced,
    dpPollProgPlaced, stageP1ProgPlaced
  ]
  rw [withPanics_cliGhostExterns mmpl gh W]

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cSlotOkAtPlacedBudget

section At3Wrap_p1

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4ContPlacedBudget

open Arm64 Arm64.Process ProofLib

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification CryptoVerification.RustHeap

open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet hiding lsLogOff withLsCodeRoLoaded

open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open CryptoVerification.LibsignalSpqrV1 hiding Bytes

open CryptoVerification.E2E

open CryptoVerification.E2E.Bin

open CryptoVerification.E2E.Pqxdh

open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes

open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp Bytes eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0

open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

open CryptoVerification.E2E.Pqxdh.WireEntries

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr

open CryptoVerification.LibsignalPublicApi.StoreSession

open CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf

open CryptoVerification.LibsignalPublicApi.MessageDecrypt

open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary

open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

open CryptoVerification.SignalSession.Cli.Placed

open CryptoVerification.SignalSession.Cli.MainHops

open CryptoVerification.SignalSession.Cli.RunSkeleton hiding RunHooksPlaced

open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced

open CryptoVerification.SignalSession.Cli.RunProofs

open CryptoVerification.SignalSession.Cli.KitInst

open CryptoVerification.SignalSession.Coins

open CryptoVerification.SignalSession.Coins.Placed

open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  cliPollKpk_markOk_of_pmOfE_placed
  cliPollPk_removeIdOk_of_pmOfE_placed
  cliPollStageP4_fsAt_placed
  closure_pathA_p4_cont_placed
  cliFiles_eq_of_trace_eq_placed
  cliPollStageP1_fsAt_placed
  exit_entails_dpPollPost_placed
  cliPollStageP4Stack_placed_le_subStack
  pathAP4RemAtPlaced
  stageP3MidPathA_eq_p4_placed
  stageP4PathAExit_entails_exit_placed
  genP3Pre_placed genP3CallFrame_placed genP3S5PostFrame_placed
  stageP3DispatchOkMid_placed stageP3ErrPost_placed
  stageP4SharedPlaced stageP4RawPrePlaced stageP4PrePlaced stageP4ExitAtPlaced
  StageP4RawBranchPlaced StageP4BranchPlaced StageP4PathAPlacedStmt

open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)

open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)

open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)

open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (PreKeyStoreBudgetEnv)

open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (KyberPreKeyStoreBudgetEnv)

open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  genP3S5PostFrame_placed
  stageP3DispatchOkMid_placed
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced
  StageP4PathAEnv
  StageP4PathAMarkErrEnv
  StageP4PathAPlacedStmt
  StageP4PathAStoreStepEnv
  stageP4ExitAtPlaced
  stageP4PrePlaced
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAPlacedBudget (
  cliPollStageP4Stack_placed_le_subStack
  pathAP4RemAtPlaced
  stageP3MidPathA_eq_p4_placed
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4PlacedBudget (
  stageP4PathAExit_entails_exit_placed
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget (
  cliFiles_eq_of_trace_eq_placed
  exit_entails_dpPollPost_placed
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxHeartbeats 1200000 in
private theorem closure_pathA_p4_cont_placed_at_priv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv))
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    {opt : Option (SessionRecord (List (BitVec 8)))}
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok opt)
    (hcur : opt.bind (·.currentSession) = none)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
    (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
    (kitEnv : SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)))
    (pkKitEnv : PreKeyStoreBudgetEnv
      (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)))
    (kpkKitEnv : KyberPreKeyStoreBudgetEnv
      (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)))
    (hkitEnv : kitEnv =
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget.cliPollSessBudgetEnv
        A.repAlloc y.g.F y.g.peer (cliKitStk B) DeserEnv ReadEnv)
    (hikitEnv : ikitEnv =
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget.cliPollIdBudgetEnv
        A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
    (hpkKitEnv : pkKitEnv =
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget.cliPollPkBudgetEnv
        A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B) ReadEnv)
    (hkpkKitEnv : kpkKitEnv =
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget.cliPollKpkBudgetEnv
        A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) ReadEnv)
    (evs_pre : List AllocEvent)
    (recG G₁ G' : SessionGhost)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem P_s' R : SepProp)
    (pt : List (BitVec 8))
    (s0 s2 s' : State)
    (hpm_eq : y.g.msg = pmOfE m i)
    (hi : SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys y.g.F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
      (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hex : SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk))
    (hfits_p4 : FitsEnv M lim (M.stepEvents evs_pre y.st)
      (StageP4PathAEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
        (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)) pkKitEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)) kpkKitEnv
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        y.g.peer.val y.g.msg.identityKey m.opkId m.kpkId m.spkId y.g.msg.baseKey
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
            (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2
          pendingPreKey := none
          pendingKyberPreKey := none }))
    (hevs_ok : ∀ evs_p4,
      StageP4PathAStoreStepEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
        (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)) pkKitEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)) kpkKitEnv
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        y.g.peer.val y.g.msg.identityKey m.opkId m.kpkId m.spkId y.g.msg.baseKey
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
            (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2
          pendingPreKey := none
          pendingKyberPreKey := none } evs_p4 →
      DecPkEnv y.g (evs_pre ++ evs_p4))
    (hevs_markErr : ∀ evs_p4,
      StageP4PathAMarkErrEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)) kpkKitEnv
        StoresGhost.opened.identity StoresGhost.opened.kyber
        y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey evs_p4 →
      DecPkEnv y.g (evs_pre ++ evs_p4))
    (hmsg_fold :
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
    (hfiles2 : s2.fs.files = y.g.F)
    (htr2 : s2.trace = s0.trace)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_align2 : (s2.sp &&& 15#64 == 0#64) = true)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hver : (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      y.g.msg.message.messageVersion.zeroExtend 32)
    (hcl : CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁)
    (hdec_rel : G₁.AfterTryDecrypt true G')
    (hok : (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_ne : ptPtr ≠ 0#64)
    (hsteps2' : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s2 s')
    (hpc' : s'.pc = dpPollEntryPlaced + 0x34dc#64)
    (hrun' : s'.status = .Running)
    (hs'_sp : s'.sp = s2.sp)
    (htr' : s'.trace = s0.trace)
    (hvregs' : calleeSavedVRegs s' = calleeSavedVRegs s0)
    (hx19' : s'.readReg64 .x19 = y.fut)
    (hx24' : s'.readReg64 .x24 = s2.sp + 0x370#64)
    (hx25' : s'.readReg64 .x25 = s2.sp + 0x210#64)
    (hx26' : s'.readReg64 .x26 = y.out)
    (hx27' : s'.readReg64 .x27 = y.cx)
    (hx28' : s'.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hro' : StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem)
    (hent_s' : P_s' ⊢
      stageP3DispatchOkMid_placed A lim (M.stepEvents evs_pre y.st) s0 s2 s' y.fut y.out 8#64 8#64
        ptCap ptPtr pt 0#8 G'
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2 ∗
      genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.msg.message.senderRatchetKey y.g.coins))) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
    let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    let Fr_tail : SepProp :=
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32
    SepWPp prog (s0.readReg64 .x30) s' (P_s' ∗ F_p3)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5ModelPanicProp W.C W.Q.K y.g.peer y.g.me st0 y.g.msg.message
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins s0) := by
  subst hkitEnv; subst hikitEnv; subst hpkKitEnv; subst hkpkKitEnv
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
  let F_p3 : SepProp :=
    stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
      (coroOpkIdAtP4 y.fut m.opkId)
      (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
        ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
    stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
    ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    preKeyMsgRem ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
  let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
  let st0 := pathAInitState ⟨W.C, W.Q⟩ meE k m dk
  let st' := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
  let ses' : Session (List (BitVec 8)) :=
    { pathAInitSession ⟨W.C, W.Q⟩ meE k m dk with
      state := st', pendingPreKey := none, pendingKyberPreKey := none }
  let coinsPost := coinsAfterPlaced y.g.coinsP y.g.coins
    (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins)
  have hok_pair : genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0 =
      (.ok pt, st') := by
    rcases hg : genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0 with ⟨r1, r2⟩
    have hr1 : r1 = .ok pt := by rw [hg] at hok; exact hok
    subst hr1
    have hr2 : r2 = st' := by dsimp only [st']; rw [hg]
    subst hr2
    rfl
  obtain ⟨hKit', hLen'⟩ := pathA_recOk_of_tryDecrypt hdecOk hver hok
  have hex' : SessionExtraRel G' ses' := sessionExtraRel_of_clone_decRel hex hcl hdec_rel
  have hs'_sp0 : s'.sp = sp := hs'_sp.trans hs2_sp
  have hsp_ret : sp + 0xcd0#64 = s0.sp := sp_frame_sub_add s0.sp
  have hf' : s'.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps2' (htr'.trans htr2.symm)).trans hfiles2
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp4_64 : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64 :=
    Nat.le_trans
      (cliPollStageP4Stack_placed_le_subStack A.repAlloc y.g.F Slots.scopeKit y.g.peer
        pid m.kpkId m.spkId y.g.msg.baseKey B)
      hsub64
  have hwp4 := LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget.stageP4PathA_placed_inst
    hDropNz mmpl gh W B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
    hh hReadFile hDeser
    (M.stepEvents evs_pre y.st) s0 s'
    y.fut y.cx y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
    (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
    8#64 ptCap ptPtr 8#64
    m.opkId m.kpkId m.spkId 0#8 pt
    y.g.msg.identityKey y.g.msg.baseKey
    StoresGhost.opened.sessions StoresGhost.opened.identity
    StoresGhost.opened.oneTime StoresGhost.opened.kyber
    G' ses'
    (by decide) hex' ⟨hKit', hLen'⟩ rfl rfl
    (cliPollKpk_markOk_of_pmOfE_placed y.g.F m i σ hpm_eq)
    (cliPollPk_removeIdOk_of_pmOfE_placed y.g.F m i σ hpm_eq)
    hfits_p4 hpt_le hpt_lt hpt_ne hp4_64
    (cliPollStageP4_fsAt_placed hh y.g.F Slots.scopeKit y.g.peer pid m.spkId m.kpkId
      y.g.msg.baseKey B hf')
    hro' hpc' hrun'
    (hs'_sp ▸ hsp_align2) (htr' ▸ List.prefix_refl _)
    hx19' (hs'_sp ▸ hx24') (hs'_sp ▸ hx25') hx26' hx27' hx28' hvregs'
  intro R' hm hL
  have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_s')) hm
  have hmid := stageP3MidPathA_eq_p4_placed A lim (M.stepEvents evs_pre y.st) B y s0 s2 s'
    rngPtr 8#64 8#64 whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem coinsPost m.opkId
    (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId pt G' st'
    hs2_sp hs'_sp0 hsp_sub
  dsimp only at hmid
  have hm2 : s'.mem ⊨
      stageP4PrePlaced A lim (M.stepEvents evs_pre y.st) kit ikit pkKit kpkKit s0 s'
        y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
        8#64 ptCap ptPtr 8#64 m.opkId m.kpkId m.spkId 0#8 pt
        y.g.peer y.g.msg.identityKey y.g.msg.baseKey
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        G' st' ∗
      (pathAP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost ∗
        R') := by
    have hEq :
        ((stageP3DispatchOkMid_placed A lim (M.stepEvents evs_pre y.st) s0 s2 s' y.fut y.out
            8#64 8#64 ptCap ptPtr pt 0#8 G' st' ∗
          genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
            coinsPost) ∗ F_p3) ∗ R' =
        stageP4PrePlaced A lim (M.stepEvents evs_pre y.st) kit ikit pkKit kpkKit s0 s'
          y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
          (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
          8#64 ptCap ptPtr 8#64 m.opkId m.kpkId m.spkId 0#8 pt
          y.g.peer y.g.msg.identityKey y.g.msg.baseKey
          StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber
          G' st' ∗
        (pathAP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem
          coinsPost ∗ R') := by
      dsimp only [F_p3, sp, σ, kit, ikit, pkKit, spkKit, kpkKit]
      rw [hs2_sp, hmid, sepConj_assoc]
    exact hEq ▸ hm1
  obtain ⟨sf, hsteps_p4, hBranch⟩ := hwp4 _ hm2 hL
  refine ⟨sf, hsteps_p4, ?_⟩
  have hpre_id : y.g.msg.preKeyId = m.opkId := hpm_eq ▸ (pmOfE_preKeyId_spkId_baseKey_eq m i).1
  have hspk_id : y.g.msg.signedPreKeyId = m.spkId :=
    hpm_eq ▸ (pmOfE_preKeyId_spkId_baseKey_eq m i).2.1
  rcases hBranch with
    ⟨hpcm, hrunm, Pf, hmf, ⟨_hsteps'f, hspf, hcs_p4, hvregs_f, _hro_f, hBr⟩⟩ |
    ⟨_hpanf, _Pf, _hmf, hfalse⟩ |
    ⟨_, hoom⟩
  · cases hBr with
    | ok c evs_p4 hevs_p4 _hsave hmark _hrem _hstore htr_f hpost_f =>
      rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have htr_sf : sf.trace = s0.trace := by
        revert hevs_p4 _hrem htr_f
        generalize m.opkId = opk?
        rintro hevs_p4 _hrem htr_f _
        cases opk?
        · simpa [kit, ikit, kpkKit,
            cliPollSessKitPlaced, cliPollSessKit, cliSessionStoreSpec,
            cliPollIdKitPlaced, cliIdStoreSpecFullPlaced, cliPollIdKit, cliIdStoreSpecFull,
            cliIdentityStoreSpec,
            cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced,
            cliPollKpkKit, cliKpkStoreSpecFull, cliKyberPreKeyStoreSpec, cliKpkStoreSpec,
            htr'] using htr_f
        · simpa [kit, ikit, pkKit, kpkKit,
            cliPollSessKitPlaced, cliPollSessKit, cliSessionStoreSpec,
            cliPollIdKitPlaced, cliIdStoreSpecFullPlaced, cliPollIdKit, cliIdStoreSpecFull,
            cliIdentityStoreSpec,
            cliPollPkKitPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced, cliPollPkKit, cliPreKeyStoreSpec,
            cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced,
            cliPollKpkKit, cliKpkStoreSpecFull, cliKyberPreKeyStoreSpec, cliKpkStoreSpec,
            htr'] using htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ pathAP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost,
        hmf, ?_, hsf_sp, hcs_full⟩
      intro hsteps0f hm_f
      let kyber' := (kpkMarkOf cliIo.rd y.g.F StoresGhost.opened.kyber
        m.kpkId m.spkId y.g.msg.baseKey).2
      have hmark_eq : StoresGhost.opened.kyber.mark cliIo.rd y.g.F m.kpkId
          y.g.msg.signedPreKeyId y.g.msg.baseKey = (.ok (), kyber') := by
        rw [hspk_id]
        exact cliKpk_markRel_ok_to_mark (A := A.repAlloc) (b := 0#64)
          (s1 := σ.kpkGetShim) (s2 := σ.kpkGetPoll) (s3 := σ.kpkMarkShim) (s4 := σ.kpkMarkPoll)
          hmark
      obtain ⟨_, _, _, hDec, hWr⟩ :=
        decPkDef_pathA_ok X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hfPeer hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver hok_pair hmark_eq
      let oneTime' := match y.g.msg.preKeyId with
        | none => StoresGhost.opened.oneTime
        | some j => (Cli.removePreKey cliIo.rd y.g.F StoresGhost.opened.oneTime j).2
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := StoresGhost.opened.identity.saveUpd cliIo.rd y.g.F y.g.peer.val
            y.g.msg.identityKey
          kyber := kyber'
          oneTime := oneTime'
          sessions := StoresGhost.opened.sessions.put (Cli.addressText y.g.peer.val)
            (E2E.Record.encodeRecord ⟨some ses'⟩) }
      have hout : slotOutTr
          (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
          g' (.ok pt) s0.trace sf.trace :=
        slotOutTr_of_accept hS hDec hWr
      have hot_eq : g'.oneTime =
          (match m.opkId with
           | none => StoresGhost.opened.oneTime
           | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ())) := by
        dsimp only [g', oneTime', pkKit, cliPollPkKitPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
          cliPollPkKit, cliPreKeyStoreSpec]
        rw [hpre_id]
      have hpost_f' : Pf ⊢
          stageP4ExitAtPlaced A lim (M.stepEvents (evs_pre ++ evs_p4) y.st)
            kit ikit pkKit kpkKit s0 s' sf y.fut y.g.msgA y.g.peerA
            (y.g.msgA + 0xc8#64) (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64)
            (y.g.stores + 0x78#64) 8#64 ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut m.opkId)
            (vecResultAt A.repAlloc y.out (.ok pt)) m.kpkId m.spkId pt
            y.g.peer y.g.msg.identityKey y.g.msg.baseKey
            (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
            (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
            (match m.opkId with
             | none => StoresGhost.opened.oneTime
             | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ()))
            (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.ok ())) := by
        revert hevs_p4 _hrem htr_f hpost_f
        generalize m.opkId = opk?
        rintro hevs_p4 _hrem htr_f hpost_f
        cases opk? <;> (rw [M.stepEvents_append evs_pre evs_p4 y.st]; exact hpost_f)
      have hexit := stageP4PathAExit_entails_exit_placed A lim (M.stepEvents (evs_pre ++ evs_p4) y.st)
        B y s0 s' sf rngPtr 8#64 8#64
        whisperMsgPtr ptCap ptPtr whisperG (vecResultAt A.repAlloc y.out (.ok pt))
        preKeyMsgRem coinsPost m.opkId (y.g.msg.message.messageVersion.zeroExtend 32)
        pid m.kpkId m.spkId pt (.ok pt)
        (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
        (match m.opkId with
         | none => StoresGhost.opened.oneTime
         | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ()))
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.ok ()))
        g' hs'_sp0 hsp_sub (decResultAt_ok_entails_decResAt_anyHeap A.repAlloc y.out pt)
        hmsg_fold rfl rfl hot_eq rfl rfl rfl
      dsimp only at hexit
      have hm_f1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hpost_f')) hm_f
      have hm_f2 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm_f1
      have hm_f3 : sf.mem ⊨
          (decResAt A.repAlloc y.out (.ok pt) ∗
            storesAt A.repAlloc y.g.stores g' ∗
            protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
            protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
            preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
            FromRecordCallees.lsLogOff ∗
            A.pool lim (M.stepEvents (evs_pre ++ evs_p4) y.st) sf ∗
            (LsTokenInit ∗ coinsPost ∗ anyHeap) ∗
            dpFutDoneAt y.fut ∗
            memRegion y.cx 32 ∗
            memRegion sp 3280 ∗
            stackAt sp (dpClosSubStack B) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
        Arm64.Satisfies.mono (by sep_frame) hm_f2
      have hpost_goal := exit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y s0 sf
        (evs_pre ++ evs_p4) g' (.ok pt) (LsTokenInit ∗ coinsPost ∗ anyHeap)
        (hevs_ok evs_p4 hevs_p4) hh hsteps0f htr_sf hout
      exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm_f3
    | saveErr _evs_p4 _hevs_p4 hsave _ _ =>
      dsimp only [ikit, cliPollIdKitPlaced, cliIdStoreSpecFullPlaced] at hsave
      exact False.elim (cliId_saveRel_not_err hsave)
    | markErr c e evs_p4 hevs_p4 _hsave hmark htr_f hpost_f =>
      rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have htr_sf : sf.trace = s0.trace := by
        simpa [ikit, kpkKit,
          cliPollIdKitPlaced, cliIdStoreSpecFullPlaced, cliPollIdKit, cliIdStoreSpecFull,
          cliIdentityStoreSpec,
          cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced,
          cliPollKpkKit, cliKpkStoreSpecFull, cliKyberPreKeyStoreSpec, cliKpkStoreSpec,
          htr'] using htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ pathAP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost,
        hmf, ?_, hsf_sp, hcs_full⟩
      intro hsteps0f hm_f
      have hmark_err :
          (StoresGhost.opened.kyber.mark cliIo.rd y.g.F m.kpkId
            y.g.msg.signedPreKeyId y.g.msg.baseKey).1 = .error () := by
        rw [hspk_id]
        exact cliKpk_markRel_error_to_mark (A := A.repAlloc) (b := 0#64)
          (s1 := σ.kpkGetShim) (s2 := σ.kpkGetPoll) (s3 := σ.kpkMarkShim) (s4 := σ.kpkMarkPoll)
          hmark
      have hDec := decPkDef_pathA_mark_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg
        y.g.coins hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver hok_pair hmark_err
      let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val
            y.g.msg.identityKey (.ok c)
          kyber := kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId
            y.g.msg.baseKey (.error e) }
      have hout : slotOutTr
          (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
          g' (.error err) s0.trace sf.trace :=
        slotOutTr_of_reject g' hS nofun nofun hDec
      have hpost_f' : Pf ⊢
          stageP4ExitAtPlaced A lim (M.stepEvents (evs_pre ++ evs_p4) y.st)
            kit ikit pkKit kpkKit s0 s' sf y.fut y.g.msgA y.g.peerA
            (y.g.msgA + 0xc8#64) (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64)
            (y.g.stores + 0x78#64) 8#64 ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut m.opkId)
            (speErrAt kpkKit.markErr y.out e) m.kpkId m.spkId pt
            y.g.peer y.g.msg.identityKey y.g.msg.baseKey
            StoresGhost.opened.sessions
            (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
            StoresGhost.opened.oneTime
            (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.error e)) := by
        rw [M.stepEvents_append evs_pre evs_p4 y.st]
        exact hpost_f
      have hexit := stageP4PathAExit_entails_exit_placed A lim (M.stepEvents (evs_pre ++ evs_p4) y.st)
        B y s0 s' sf rngPtr 8#64 8#64
        whisperMsgPtr ptCap ptPtr whisperG (speErrAt kpkKit.markErr y.out e) preKeyMsgRem
        coinsPost m.opkId (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId
        pt (.error err) StoresGhost.opened.sessions StoresGhost.opened.oneTime
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.error e))
        g' hs'_sp0 hsp_sub
        (cliKpkMarkErrSpec_entails_decResAt_anyHeap A.repAlloc y.out e err)
        hmsg_fold rfl rfl rfl rfl rfl rfl
      dsimp only at hexit
      have hm_f1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hpost_f')) hm_f
      have hm_f2 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm_f1
      have hm_f3 : sf.mem ⊨
          (decResAt A.repAlloc y.out (.error err) ∗
            storesAt A.repAlloc y.g.stores g' ∗
            protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
            protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
            preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
            FromRecordCallees.lsLogOff ∗
            A.pool lim (M.stepEvents (evs_pre ++ evs_p4) y.st) sf ∗
            (LsTokenInit ∗ coinsPost ∗ anyHeap) ∗
            dpFutDoneAt y.fut ∗
            memRegion y.cx 32 ∗
            memRegion sp 3280 ∗
            stackAt sp (dpClosSubStack B) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
        Arm64.Satisfies.mono (by sep_frame) hm_f2
      have hpost_goal := exit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y s0 sf
        (evs_pre ++ evs_p4) g' (.error err) (LsTokenInit ∗ coinsPost ∗ anyHeap)
        (hevs_markErr evs_p4 hevs_p4) hh hsteps0f htr_sf hout
      exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm_f3
    | removeErr opkId _c _e _evs_p4 hopk _hevs_p4 _hsave _hmark hrem _ _ =>
      exact False.elim (cliPk_removeRel_not_err_of_pkStoreKeys (A := A.repAlloc) (b := 0#64)
        (pid := pid) (σ := σ) (e := _e) hk hopk hrem)
    | storeErr _c _evs_p4 _hevs_p4 _hsave _hmark _hrem hstore _ _ =>
      dsimp only [kit, cliPollSessKitPlaced] at hstore
      exact False.elim (cliSess_storeRel_not_err hstore)
  · exact hfalse.elim
  · exact (not_satisfies_false_sepConj hoom).elim

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4ContPlacedBudget
end At3Wrap_p1

section At3Wrap_p2

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudgetAux

open Arm64 Arm64.Process ProofLib

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification CryptoVerification.RustHeap

open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet hiding
  lsLogOff withLsCodeRoLoaded LibsignalCodeRoLoaded
  subroutine_ok_withLsCodeRoLoaded_of_plain
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded

open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open CryptoVerification.LibsignalSpqrV1 hiding Bytes

open CryptoVerification.E2E

open CryptoVerification.E2E.Bin hiding encodeRecord

open CryptoVerification.E2E.Record (encodeRecord)

open CryptoVerification.E2E.Pqxdh

open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes

open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp Bytes eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0

open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

open CryptoVerification.E2E.Pqxdh.WireEntries

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr

open CryptoVerification.LibsignalPublicApi.StoreSession

open CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

open CryptoVerification.LibsignalPublicApi.MessageDecrypt

open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary

open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

open CryptoVerification.SignalSession.Cli.Placed

open CryptoVerification.SignalSession.Cli.MainHops

open CryptoVerification.SignalSession.Cli.RunSkeleton hiding RunHooksPlaced

open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced

open CryptoVerification.SignalSession.Cli.RunProofs

open CryptoVerification.SignalSession.Cli.KitInst hiding
  cliPreKeyStoreSpecPlaced cliSignedPreKeyStoreSpecPlaced cliKyberPreKeyStoreSpecPlaced

open CryptoVerification.SignalSession.Coins

open CryptoVerification.SignalSession.Coins.Placed

open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  StageP2PathAQpanCliPlacedStmt
  stageP3_exit_pathA_to_pollPost_placed
  closure_pathA_placed_ok
  StageP2MatchedFramedCliPlacedStmt
  storesAt_opened_entails_cliPollStoresKitsAtPlaced
  sepWPp_pollGoal_frame_placed
  stageP3_exit_prevEmpty_to_pollPost_placed
  sepWPp_genP3_to_tailQpan_placed
  closure_pathB_placed_ok
  cliFiles_eq_of_trace_eq_placed
  cliPollStageP1_fsAt_placed
  cliPollStageP4Stack_placed_le_subStack
  cliPollStageP4MatchedStack_placed_le_subStack
  cliPollStageP4_fsAt_placed
  closure_pathA_p4_cont_placed
  stageP3ErrPathA_entails_exit_placed
  stageP3ErrPrevEmpty_entails_exit_placed
  pathAP4RemAtPlaced
  pathBP4RemAtPlaced
  stageP3MidPathA_eq_p4_placed
  stageP3MidPrevEmpty_eq_p4_placed
  stageP4PathAExit_entails_exit_placed
  stageP4MatchedExit_entails_exit_placed
  exit_entails_dpPollPost_placed
  sepWPp_genP3_to_pollGoal_placed
  closure_pathB_p4_cont_placed
  genP3Pre_placed genP3CallFrame_placed genP3S5PostFrame_placed
  stageP3DispatchOkMid_placed stageP3ErrPost_placed
  stageP3DispatchOkMidPrevEmpty_placed stageP3ErrPostPrevEmpty_placed
  stageP4SharedPlaced stageP4RawPrePlaced stageP4PrePlaced stageP4ExitAtPlaced
  StageP4RawBranchPlaced StageP4BranchPlaced StageP4PathAPlacedStmt
  stageP4MatchedSharedPlaced stageP4MatchedPrePlaced stageP4MatchedExitAtPlaced
  StageP4MatchedBranchPlaced StageP4MatchedPlacedStmt
  StageP2PathAErrPlaced StageP2PathACliPlacedStmt
  StageP3PrevEmptyVRegsPlacedStmt StageP3GenStepsVRegsPlacedStmt CliTryDecryptPqV1PlacedStmt

open CryptoVerification.SignalSession.Cli.Slots (cliGhostExterns_sat_of_cliExternsPlaced)

open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv
)

open LibsignalBinary.Heap.SpecBudget (withVmPreserved)

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget (
  chainClone3_placed_ok_of_hooks senderChainClone3_placed_ok_of_hooks
)

open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)

open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (KyberPreKeyStoreBudgetEnv)

open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (PreKeyStoreBudgetEnv)

open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)

open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  CliGhostHooks cliGhostExterns
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4ContPlacedBudget (
  closure_pathA_p4_cont_placed
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudget (
  stageP3_exit_pathA_to_pollPost_placed
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget (
  sepWPp_genP3_to_tailQpan_placed sepWPp_pollGoal_frame_placed
  storesAt_opened_entails_cliPollStoresKitsAtPlaced
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget (
  cliFiles_eq_of_trace_eq_placed exit_entails_dpPollPost_placed
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  ChainClone3OkPlaced SenderChainClone3OkPlaced
  StageP3Env StageP3ErrEnv StageP3GenStepsVRegsPlacedStmt StageP3OkPrefixEnv StageP3VerNeEnv
  genP3Pre_placed genP3S5PostFrame_placed pollTryDecryptPlacedSpecTPTight
  stageP3DispatchOkMid_placed stageP3ErrPost_placed
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced StageP2PathAEnv StageP4PathAEnv StageP4PathAMarkErrEnv
  StageP4PathAPlacedStmt StageP4PathAStoreStepEnv
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1InstPlacedBudgetAux (
  StageP2PathAQpanCliPlacedAtStmt
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  cliExternsPlaced_sessionMemcpyRegion_budget_sat
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)

open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)

open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)

open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem hookSat_sessionShimBudget_of_codec_p2 {H : LibsignalHooks}
    (h : HookSat H CryptoVerification.lsRustNoAllocShimSym
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec)) :
    HookSat H CryptoVerification.lsRustNoAllocShimSym sessionShimBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · exact ⟨hkeep, hsym, Or.inl ⟨hret, hcc, hpost⟩⟩
  · exact ⟨hkeep, hsym, Or.inr hrest⟩

private theorem cliChainClone3_budget_placed_ok_p2 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    ChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  chainClone3_placed_ok_of_hooks
    (hookSat_sessionShimBudget_of_codec_p2 hh.codecHooks.shim)
    hh.codecHooks.alloc
    ((show withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
        LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec from rfl) ▸
      hh.codecHooks.memcpy)

private theorem cliSenderChainClone3_budget_placed_ok_p2 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    SenderChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  senderChainClone3_placed_ok_of_hooks
    (hookSat_sessionShimBudget_of_codec_p2 hh.codecHooks.shim)
    hh.codecHooks.alloc
    ((show withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
        LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec from rfl) ▸
      hh.codecHooks.memcpy)

set_option maxHeartbeats 1200000 in
private theorem closure_pathA_frozen_placed_ok_at_priv [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hP2A : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudgetAux.StageP2PathAQpanCliFrozenPlacedAtStmt A lim ReadEnv X mmpl gh W B P2PathAErrEnv P2PathAOkEnv)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (kitEnv : SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)))
    (pkKitEnv : PreKeyStoreBudgetEnv
      (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)))
    (kpkKitEnv : ∀ kpkId spkId, KyberPreKeyStoreBudgetEnv
      (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey (cliKitStk B)))
    (hkitEnv : kitEnv =
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget.cliPollSessBudgetEnv
        A.repAlloc y.g.F y.g.peer (cliKitStk B) DeserEnv ReadEnv)
    (hikitEnv : ikitEnv =
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget.cliPollIdBudgetEnv
        A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
    (hpkKitEnv : pkKitEnv =
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget.cliPollPkBudgetEnv
        A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B) ReadEnv)
    (hkpkKitEnv : ∀ kpkId spkId, kpkKitEnv kpkId spkId =
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget.cliPollKpkBudgetEnv
        A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey (cliKitStk B) ReadEnv)
    (evs_p1 : List AllocEvent)
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok none))
    (hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv y.g))
    (hevs_p2_err : ∀ evs_p2, P2PathAErrEnv y.g evs_p2 → DecPkEnv y.g (evs_p1 ++ evs_p2))
    (hfits_p3 : ∀ evs_p2 m i k kp reg dk recG,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      FitsEnv M lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
        (StageP3Env tdEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
          y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins))
    (hfits_p4 : ∀ evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
        y.g.msg.message.messageVersion.zeroExtend 32 →
      CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv tdEnv recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me y.g.msgG.msg y.g.msg.message y.g.coins evs_p3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      FitsEnv M lim (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st)
        (StageP4PathAEnv
          (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
          (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)) pkKitEnv
          (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
            (kpkKitEnv m.kpkId m.spkId)
          StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber
          y.g.peer.val y.g.msg.identityKey m.opkId m.kpkId m.spkId y.g.msg.baseKey
          { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
            state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
              (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2
            pendingPreKey := none
            pendingKyberPreKey := none }))
    (hevs_ok : ∀ evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
        y.g.msg.message.messageVersion.zeroExtend 32 →
      CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv tdEnv recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me y.g.msgG.msg y.g.msg.message y.g.coins evs_p3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      StageP4PathAStoreStepEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
        (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)) pkKitEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (kpkKitEnv m.kpkId m.spkId)
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        y.g.peer.val y.g.msg.identityKey m.opkId m.kpkId m.spkId y.g.msg.baseKey
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
            (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2
          pendingPreKey := none
          pendingKyberPreKey := none } evs_p4 →
      DecPkEnv y.g (((evs_p1 ++ evs_p2) ++ evs_p3) ++ evs_p4))
    (hevs_markErr : ∀ evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
        y.g.msg.message.messageVersion.zeroExtend 32 →
      CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv tdEnv recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me y.g.msgG.msg y.g.msg.message y.g.coins evs_p3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      StageP4PathAMarkErrEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (kpkKitEnv m.kpkId m.spkId)
        StoresGhost.opened.identity StoresGhost.opened.kyber
        y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey evs_p4 →
      DecPkEnv y.g (((evs_p1 ++ evs_p2) ++ evs_p3) ++ evs_p4))
    (hevs_err : ∀ evs_p2 m i k kp reg dk recG G₁ G' evs_p3 e,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
        y.g.msg.message.messageVersion.zeroExtend 32 →
      CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
      G₁.AfterTryDecrypt false G' →
      StageP3ErrEnv tdEnv recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me y.g.msgG.msg y.g.msg.message y.g.coins evs_p3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .error e →
      e ≠ .panic →
      DecPkEnv y.g ((evs_p1 ++ evs_p2) ++ evs_p3))
    (hevs_verNe : ∀ evs_p2 m i k kp reg dk recG evs_p3,
      P2PathAOkEnv y.g evs_p2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version ≠
        y.g.msg.message.messageVersion.zeroExtend 32 →
      StageP3VerNeEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) evs_p3 →
      DecPkEnv y.g ((evs_p1 ++ evs_p2) ++ evs_p3))
    (hsteps01 : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s1)
    (htr1 : s1.trace = s0.trace)
    (hfr1 : CryptoVerification.LibsignalFrozen lsmpl s1.mem)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x0868#64)
    (hrun1 : s1.status = .Running)
    (hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    SepWPp prog (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  dsimp only [cliPollSessKitPlaced] at hload_rel
  have hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok none :=
    loadRec_of_cliPollSess_loadRel (A := A.repAlloc) (b := 0#64) (σ := σ)
      hinjK hsub hfPeer hload_rel
  have hcur : (none : Option (SessionRecord (List (BitVec 8)))).bind (·.currentSession) = none := rfl
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  have hs1_files : s1.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps01 htr1).trans hf0
  have hfiles1 : FsAt (fun f => f = y.g.F) True
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 :=
    .inr ⟨trivial, hh.fs (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) 518, hs1_files⟩
  let Fr_tail : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  have hpre_split :
      stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B)) ∗ Fr_tail := by
    dsimp only [Fr_tail]
    sep_frame
  refine sepWPp_conseq_pre hpre_split
    (sepWPp_pollGoal_frame_placed A lim DecPkEnv B S stk' y ?_)
  refine hP2A S Scope y StoresGhost.opened s0 s1 sp rngPtr v_a8 v_b8 v_d0 _ _
    hh hReadFile hDeser hfits_p2 hcoins hdecOk hsub hfPeer hloadS htrusted rfl hfiles1 hfr1
    (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hsp_sub hpc1 hrun1 hsp_align1 hregs1 ?_ ?_
  · intro sf Pf _ _ _ hsf_sp hcs_f hvregs_f _ hErr
    rcases hErr with ⟨err, evs_p2, hevs_p2, hne_p, hne_s, htr_f, hmodel, hpost_f⟩
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hpost_f' :
        Pf ⊢
          dpFutDoneAt y.fut ∗
          memRegion sp 3280 ∗
          decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          stackAt sp (dpClosSubStack B) ∗
          anyHeap := by
      rw [M.stepEvents_append evs_p1 evs_p2 y.st]
      exact hpost_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left hpost_f') hm_f
    have hm2 : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          anyHeap ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by dsimp only [Fr_tail]; sep_frame) hm1
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_of_reject StoresGhost.opened hS hne_p hne_s hmodel
    have hpost_goal := exit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y s0 sf
      (evs_p1 ++ evs_p2) StoresGhost.opened (.error err) anyHeap
      (hevs_p2_err evs_p2 hevs_p2) hh hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm2
  · intro evs_p2 s2 m i k kp reg dk recG whisperMsgPtr whisperG preKeyMsgRem
      hevs_p2 hwg_eq hpm_eq hi hk hkp hreg hacc hex hmsg_fold hsteps12 htr2 hpc2 hrun2
      hs2_sp hsp_align2 _ _ _ hvregs2 hfr2
    subst hwg_eq
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st0 := pathAInitState ⟨W.C, W.Q⟩ meE k m dk
    obtain ⟨_hIn0, _hver4, hSeeds, hRC, hPqLt⟩ := pathAInitSession_scopeIn ⟨W.C, W.Q⟩ meE k m dk
    have hsteps02 := Steps.trans hsteps01 hsteps12
    have htr20 : s2.trace = s0.trace := htr2.trans htr1
    have hs2_files : s2.fs.files = y.g.F :=
      (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps02 htr20).trans hf0
    have hpan_model : st0.version = y.g.msg.message.messageVersion.zeroExtend 32 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).1 = .error .panic →
        (dpSlotPollKStatePlaced A lim DecPkEnv B S).panics y.g := by
      intro hver hpan_s5
      show S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = none
      rw [hS]
      exact decPkDef_pathA_panic X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver hpan_s5
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    have hpre_p3 :
        LsTokenInit ∗
          genP3Pre_placed A lim (M.stepEvents evs_p2 (M.stepEvents evs_p1 y.st))
            s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG st0 y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
          stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
          F_p3 ⊢
        LsTokenInit ∗
          genP3Pre_placed A lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
            s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG st0 y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
          stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
          F_p3 := by
      rw [← M.stepEvents_append evs_p1 evs_p2 y.st]
      exact Entails.refl _
    refine sepWPp_conseq_pre hpre_p3
      (sepWPp_genP3_to_tailQpan_placed A lim DecPkEnv B S stk' y hpan_model ?_)
    refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudget.stageP3GenStepsVRegs_of_base_full_placed_ok
      (M.stepEvents (evs_p1 ++ evs_p2) y.st) (cliGhostExterns gh (cliExternsPlaced mmpl W)) W.C 0#64 W.Q.K
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudgetAux.StageP3CalleesM3BasePlaced.of_cliExternsPlaced mmpl gh W hG)
      (cliChainClone3_budget_placed_ok_p2 mmpl gh W hh)
      (cliSenderChainClone3_budget_placed_ok_p2 mmpl gh W hh)
      hTryDec
      s0 s2 y.fut y.cx y.out 8#64 8#64 y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8 y.g.coins
      recG st0 y.g.peer y.g.me y.g.msgG.msg y.g.msg.message F_p3 _
      (hfits_p3 evs_p2 m i k kp reg dk recG hevs_p2 hpm_eq hi hk hkp hreg hacc hex)
      (by decide) (Or.inr (distinctSid_of_decPkOk₀ hdecOk)) hSeeds hRC hPqLt
      hfr2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' evs_p3 pt ptCap ptPtr s' P_s' hver hcl hdec_rel hevs_p3 hok
        hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
        hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s'
      have hent_s'' :
          P_s' ⊢
            stageP3DispatchOkMid_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 s' y.fut y.out 8#64 8#64
              ptCap ptPtr pt 0#8 G'
              (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2 ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message
              (coinsAfterPlaced y.g.coinsP y.g.coins
                (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins)) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_s'
      have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced A.repAlloc σ y.g.stores
        hsub hfPeer hdecOk (pid := pid) (sid := m.spkId) (kid := m.kpkId) (kbk := y.g.msg.baseKey)
      have hunpack_p3 : P_s' ∗ F_p3 ⊢
          P_s' ∗
          (stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
              (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
              (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
              (coroOpkIdAtP4 y.fut m.opkId)
              (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
                ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
            stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
            ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
            ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRem ∗
            kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
            ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
            (cliPollPkKitPlaced A.repAlloc y.g.F pid σ).storeAt
              (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
            (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ).storeAt
              (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
            (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt
              (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
            dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
            memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) := by
        dsimp only [F_p3]
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
        refine Entails.trans (sepConj_mono_left hstores_in) ?_
        dsimp only [cliPollStoresKitsAtPlaced]
        sep_frame
      exact sepWPp_conseq_pre hunpack_p3
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4ContPlacedBudget.closure_pathA_p4_cont_placed_at_priv hDropNz B S hh hReadFile hDeser hS stk' hneed hstk63 y
          hfPeer hdecOk hloadS hcur htrusted m i k kp reg dk
          kitEnv ikitEnv pkKitEnv (kpkKitEnv m.kpkId m.spkId)
          hkitEnv hikitEnv hpkKitEnv (hkpkKitEnv m.kpkId m.spkId)
          ((evs_p1 ++ evs_p2) ++ evs_p3) recG G₁ G'
          rngPtr whisperMsgPtr ptCap ptPtr y.g.msgG.msg preKeyMsgRem P_s' R pt s0 s2 s'
          hpm_eq hi hk hkp hreg hacc hex
          (hfits_p4 evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt
            hevs_p2 hpm_eq hi hk hkp hreg hacc hex hver hcl hdec_rel hevs_p3 hok)
          (fun evs_p4 hevs_p4 =>
            hevs_ok evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4
              hevs_p2 hpm_eq hi hk hkp hreg hacc hex hver hcl hdec_rel hevs_p3 hok hevs_p4)
          (fun evs_p4 hevs_p4 =>
            hevs_markErr evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4
              hevs_p2 hpm_eq hi hk hkp hreg hacc hex hver hcl hdec_rel hevs_p3 hok hevs_p4)
          hmsg_fold hs2_files htr20 hs2_sp hsp_align2 hsp_sub
          hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
          hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s'')
    · intro G₁ G' evs_p3 e sf P_f hver hcl hdec_rel hevs_p3 herr hne_p hent_f
        hsf_sp htr_f hcs_f hvregs_f _hro_f
      have hent_f' :
          P_f ⊢
            ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
            memRegion (s2.sp + 0x3e0#64) 344 ∗
            stageP3ErrPost_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 sf y.fut y.out 8#64 e ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message
              (coinsAfterPlaced y.g.coinsP y.g.coins
                (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins)) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_f
      exact stageP3_exit_pathA_to_pollPost_placed B S hh hS stk' hneed hstk63 y
        ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 sf
        rngPtr whisperMsgPtr y.g.msgG.msg preKeyMsgRem
        (coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins))
        P_f R m.opkId m.kpkId m.spkId e
        (hevs_err evs_p2 m i k kp reg dk recG G₁ G' evs_p3 e
          hevs_p2 hpm_eq hi hk hkp hreg hacc hex hver hcl hdec_rel hevs_p3 herr hne_p)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathA_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver herr hne_p)
        hent_f' hsf_sp htr_f hcs_f hvregs_f
    · intro evs_p3 sf P_f hver_ne hevs_p3 hent_f hsf_sp htr_f hcs_f hvregs_f _hro_f
      have hent_f' :
          P_f ⊢
            ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
            memRegion (s2.sp + 0x3e0#64) 344 ∗
            stageP3ErrPost_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 sf y.fut y.out 8#64
              (.invalidMessage .preKey .decryptionFailed) ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message (coinsAtPlaced y.g.coinsP y.g.coins) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_f
      exact stageP3_exit_pathA_to_pollPost_placed B S hh hS stk' hneed hstk63 y
        ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 sf
        rngPtr whisperMsgPtr y.g.msgG.msg preKeyMsgRem (coinsAtPlaced y.g.coinsP y.g.coins)
        P_f R m.opkId m.kpkId m.spkId (.invalidMessage .preKey .decryptionFailed)
        (hevs_verNe evs_p2 m i k kp reg dk recG evs_p3
          hevs_p2 hpm_eq hi hk hkp hreg hacc hex hver_ne hevs_p3)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathA_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver_ne)
        hent_f' hsf_sp htr_f hcs_f hvregs_f

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudgetAux
end At3Wrap_p2

section At3Wrap_p3

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget

open Arm64 Arm64.Process ProofLib

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification CryptoVerification.RustHeap

open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet hiding lsLogOff withLsCodeRoLoaded

open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom

open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open CryptoVerification.LibsignalSpqrV1 hiding Bytes

open CryptoVerification.E2E

open CryptoVerification.E2E.Bin

open CryptoVerification.E2E.Pqxdh

open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes

open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp Bytes

open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

open CryptoVerification.E2E.Pqxdh.WireEntries

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr

open CryptoVerification.LibsignalPublicApi.StoreSession

open CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

open CryptoVerification.SignalSession.Cli.Placed

open CryptoVerification.SignalSession.Cli.MainHops

open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)

open CryptoVerification.SignalSession.Cli.RunSkeleton hiding RunHooksPlaced

open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced

open CryptoVerification.SignalSession.Cli.RunProofs

open CryptoVerification.SignalSession.Cli.KitInst

open CryptoVerification.SignalSession.Coins

open CryptoVerification.SignalSession.Coins.Placed

open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  cliFiles_eq_of_trace_eq_placed cliPollStageP1_fsAt_placed
  exit_entails_dpPollPost_placed dpPollOnPanic_of_modelPanic_placed
  sepWPp_genP3_to_pollGoal_placed fsAt_pathB_p4_placed
  stageP4MatchedStack_placed_le_pow64 closure_pathB_p4_cont_placed
  cliPollStageP4MatchedStack_placed_le_subStack
  stageP3ErrPrevEmpty_entails_exit_placed pathBP4RemAtPlaced
  stageP3MidPrevEmpty_eq_p4_placed stageP4MatchedExit_entails_exit_placed
  genP3Pre_placed genP3CallFrame_placed genP3S5PostFrame_placed
  stageP3DispatchOkMid_placed stageP3ErrPost_placed
  stageP3DispatchOkMidPrevEmpty_placed stageP3ErrPostPrevEmpty_placed
  stageP4MatchedSharedPlaced stageP4MatchedPrePlaced stageP4MatchedExitAtPlaced
  StageP4MatchedBranchPlaced StageP4MatchedPlacedStmt

open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)

open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)

open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)

open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget DpPollKStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (
  overExit_entails_dpPollPost_placed
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  genP3S5PostFrame_placed
  stageP3DispatchOkMidPrevEmpty_placed
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced
  StageP4MatchedEnv
  StageP4MatchedPlacedStmt
  StageP4MatchedStoreStepEnv
  stageP4MatchedExitAtPlaced
  stageP4MatchedPrePlaced
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBPlacedBudget (
  cliPollStageP4MatchedStack_placed_le_subStack
  pathBP4RemAtPlaced
  stageP3MidPrevEmpty_eq_p4_placed
  stageP4MatchedExit_entails_exit_placed
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxHeartbeats 800000 in
private theorem closure_pathB_p4_cont_placed_at_priv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv))
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (kitEnv : SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)))
    (hkitEnv : kitEnv =
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget.cliPollSessBudgetEnv
        A.repAlloc y.g.F y.g.peer (cliKitStk B) DeserEnv ReadEnv)
    (hikitEnv : ikitEnv =
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget.cliPollIdBudgetEnv
        A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
    (sess : Session (List (BitVec 8)))
    (evs_pre : List AllocEvent)
    (s0 s2 s' : State)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem P_s' R : SepProp)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (g : RecordGhost) (recG G₁ G' : SessionGhost)
    (pt : List (BitVec 8))
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hIn : Slots.scopeIn ⟨some sess⟩)
    (hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some ⟨some sess⟩))
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hMatch : SessMatchesPm sess y.g.msg)
    (hrem : sess.state.remoteIdentity = some y.g.msg.identityKey)
    (hex : SessionExtraRel recG sess)
    (hfits_p4 : FitsEnv M lim (M.stepEvents evs_pre y.st)
      (StageP4MatchedEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
        StoresGhost.opened.sessions StoresGhost.opened.identity
        y.g.peer.val y.g.msg.identityKey
        { sess with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
          pendingPreKey := none
          pendingKyberPreKey := none }))
    (hevs_ok : ∀ evs_p4,
      StageP4MatchedStoreStepEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
        StoresGhost.opened.sessions StoresGhost.opened.identity
        y.g.peer.val y.g.msg.identityKey
        { sess with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
          pendingPreKey := none
          pendingKyberPreKey := none } evs_p4 →
      DecPkEnv y.g (evs_pre ++ evs_p4))
    (hmsg_fold :
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
    (hs2_files : s2.fs.files = y.g.F)
    (htr20 : s2.trace = s0.trace)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hsp_align2 : (s2.sp &&& 15#64 == 0#64) = true)
    (hver : sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32)
    (hcl : CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁)
    (hdec_rel : G₁.AfterTryDecrypt true G')
    (hok : (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .ok pt)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_ne : ptPtr ≠ 0#64)
    (hsteps2' : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s2 s')
    (hpc' : s'.pc = dpPollEntryPlaced + 0x34dc#64)
    (hrun' : s'.status = .Running)
    (hs'_sp : s'.sp = s2.sp)
    (htr' : s'.trace = s0.trace)
    (hvregs' : calleeSavedVRegs s' = calleeSavedVRegs s0)
    (hx19' : s'.readReg64 .x19 = y.fut)
    (hx24' : s'.readReg64 .x24 = s2.sp + 0x370#64)
    (hx25' : s'.readReg64 .x25 = s2.sp + 0x210#64)
    (hx26' : s'.readReg64 .x26 = y.out)
    (hx27' : s'.readReg64 .x27 = y.cx)
    (hx28' : s'.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hro' : StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem)
    (hent_s' : P_s' ⊢
      stageP3DispatchOkMidPrevEmpty_placed A lim (M.stepEvents evs_pre y.st) s0 s2 s' y.fut y.out 8#64
        ptCap ptPtr g pt 0#8 G'
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2 ∗
      genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C sess.state y.g.msg.message.senderRatchetKey y.g.coins))) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
    let Fr_tail : SepProp :=
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32
    SepWPp prog (s0.readReg64 .x30) s'
      (P_s' ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
          (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
          (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
            ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
            memRegion (y.fut + 0x2a8#64) 4) ∗
        stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ∗
        ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
        kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
        memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5ModelPanicProp W.C W.Q.K y.g.peer y.g.me sess.state y.g.msg.message
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins s0) := by
  subst hkitEnv; subst hikitEnv
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
  let st' := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
  let ses' : Session (List (BitVec 8)) :=
    { sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }
  let coinsPost := coinsAfterPlaced y.g.coinsP y.g.coins
    (decryptDraws W.C sess.state y.g.msg.message.senderRatchetKey y.g.coins)
  obtain ⟨hDec, hWr, hKit', hLen'⟩ :=
    decPkDef_pathB_ok X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
      hfPeer hdecOk hIn hloadS htrusted hMatch hrem hver hok
  have hex' : SessionExtraRel G' ses' := sessionExtraRel_of_clone_decRel hex hcl hdec_rel
  have hs'_sp0 : s'.sp = sp := hs'_sp.trans hs2_sp
  have hsp_ret : sp + 0xcd0#64 = s0.sp := BitVec.sub_add_cancel s0.sp 0xcd0#64
  have hs'_files : s'.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps2' (htr'.trans htr20.symm)).trans hs2_files
  have hfs_p4 := cliPollStageP1_fsAt_placed hh y.g.F Slots.scopeKit y.g.peer B hs'_files
  have hp4_64 : stageP4MatchedCallStack kit ikit ≤ 2 ^ 64 :=
    stageP4MatchedStack_placed_le_pow64 A.repAlloc B hneed hstk63
  have hwp4 := LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget.stageP4Matched_placed_inst
    hDropNz mmpl gh W B y.g.F y.g.peer hh hReadFile hDeser
    (M.stepEvents evs_pre y.st) s0 s'
    y.fut y.g.msgA y.cx y.out y.g.peerA (y.g.msgA + 0xc8#64)
    (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
    y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
    g G' ses'
    hex' ⟨hKit', hLen'⟩ rfl rfl hfits_p4
    hpt_le hpt_lt hpt_ne hp4_64 hfs_p4 hro' hpc' hrun'
    (hs'_sp ▸ hsp_align2) (htr' ▸ List.prefix_refl _)
    hx19' (hs'_sp ▸ hx24') (hs'_sp ▸ hx25') hx26' hx27' hx28' hvregs'
  intro R' hm hL
  have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_s')) hm
  have hmid := stageP3MidPrevEmpty_eq_p4_placed A lim (M.stepEvents evs_pre y.st) B y
    s0 s2 s' rngPtr whisperMsgPtr ptCap ptPtr whisperG
    preKeyMsgRem coinsPost (y.g.msg.message.messageVersion.zeroExtend 32)
    opkHi kyberPreKeyId signedPreKeyId pt g G' st' hs2_sp hs'_sp0 hsp_sub
  dsimp only at hmid
  have hm2 : s'.mem ⊨
      stageP4MatchedPrePlaced A lim (M.stepEvents evs_pre y.st) kit ikit s0 s'
        y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
        y.g.peer y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
        g G' st' ∗
      (pathBP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost ∗ R') := by
    have hEq :
        ((stageP3DispatchOkMidPrevEmpty_placed A lim (M.stepEvents evs_pre y.st) s0 s2 s' y.fut y.out 8#64
            ptCap ptPtr g pt 0#8 G' st' ∗
          genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
            coinsPost) ∗
          stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
            (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
            (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
            (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
            (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
            (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
              ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
              memRegion (y.fut + 0x2a8#64) 4) ∗
          stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRem ∗
          ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
          kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
          memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) ∗ R' =
        stageP4MatchedPrePlaced A lim (M.stepEvents evs_pre y.st) kit ikit s0 s'
          y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
          (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
          y.g.peer y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
          g G' st' ∗
        (pathBP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost ∗ R') := by
      dsimp only [sp, σ, kit, ikit]
      rw [hs2_sp, hmid, sepConj_assoc]
    exact hEq ▸ hm1

  obtain ⟨sf, hsteps_p4, hBranch⟩ := hwp4 _ hm2 hL
  refine ⟨sf, hsteps_p4, ?_⟩
  rcases hBranch with
    ⟨hpcm, hrunm, Pf, hmf, ⟨_hsteps'f, hspf, hcs_p4, hvregs_f, _hro_f, hBr⟩⟩ |
    ⟨_hpanf, _Pf, _hmf, hfalse⟩ |
    ⟨_, hoom⟩
  · rcases hBr with
      ⟨c, evs_p4, hevs_p4, _hsave, _hstore, htr_f, hpost_f⟩ |
      ⟨_evs_p4, _hevs_p4, hsave, _, _⟩ |
      ⟨_, _evs_p4, _hevs_p4, _, hstore, _, _⟩
    · rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have htr_sf : sf.trace = s0.trace := by
        dsimp only [kit, ikit, cliPollSessKitPlaced, cliPollSessKit, cliSessionStoreSpec,
          cliPollIdKitPlaced, cliIdStoreSpecFullPlaced, cliPollIdKit, cliIdStoreSpecFull,
          cliIdentityStoreSpec] at htr_f
        simpa [htr'] using htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ pathBP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost,
        hmf, ?_, hsf_sp, hcs_full⟩
      intro hsteps0f hm_f
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := StoresGhost.opened.identity.saveUpd cliIo.rd y.g.F y.g.peer.val
            y.g.msg.identityKey
          sessions := StoresGhost.opened.sessions.put (Cli.addressText y.g.peer.val)
            (E2E.Record.encodeRecord ⟨some ses'⟩) }
      have hout : slotOutTr
          (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
          g' (.ok pt) s0.trace sf.trace :=
        slotOutTr_of_ok s0.trace sf.trace (by rw [hS]; exact hDec) hWr
      have hpost_f' :
          Pf ⊢ stageP4MatchedExitAtPlaced A lim (M.stepEvents (evs_pre ++ evs_p4) y.st) kit ikit
            s0 s' sf y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
            (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
            ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId
            (vecResultAt A.repAlloc y.out (.ok pt)) pt
            y.g.peer y.g.msg.identityKey
            (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
            (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c)) := by
        rw [M.stepEvents_append evs_pre evs_p4 y.st]
        exact hpost_f
      have hm_f1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hpost_f')) hm_f
      have hexit := stageP4MatchedExit_entails_exit_placed A lim (M.stepEvents (evs_pre ++ evs_p4) y.st)
        B y s0 s' sf rngPtr whisperMsgPtr ptCap ptPtr whisperG
        preKeyMsgRem coinsPost (y.g.msg.message.messageVersion.zeroExtend 32)
        opkHi kyberPreKeyId signedPreKeyId pid kid pt
        (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        g' hs'_sp0 hsp_sub hmsg_fold rfl rfl rfl rfl rfl rfl
      dsimp only at hexit
      have hm_f2 : sf.mem ⊨
          (stageP4MatchedExitAtPlaced A lim (M.stepEvents (evs_pre ++ evs_p4) y.st) kit ikit
              s0 s' sf y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
              (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
              ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId
              (vecResultAt A.repAlloc y.out (.ok pt)) pt
              y.g.peer y.g.msg.identityKey
              (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
              (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c)) ∗
            pathBP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
              (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost ∗
            pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
            spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
            kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
            dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub) ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            memRegion y.cx 32 ∗ R) :=
        Arm64.Satisfies.mono (by sep_frame) hm_f1
      have hm_f3 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm_f2
      have hm_f4 : sf.mem ⊨
          (decResAt A.repAlloc y.out (.ok pt) ∗
            storesAt A.repAlloc y.g.stores g' ∗
            protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
            protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
            preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
            FromRecordCallees.lsLogOff ∗
            A.pool lim (M.stepEvents (evs_pre ++ evs_p4) y.st) sf ∗
            (LsTokenInit ∗ coinsPost) ∗
            dpFutDoneAt y.fut ∗
            memRegion y.cx 32 ∗
            memRegion sp 3280 ∗
            stackAt sp (dpClosSubStack B) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
        Arm64.Satisfies.mono (by sep_frame) hm_f3
      have hpost_goal := exit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y s0 sf
        (evs_pre ++ evs_p4) g' (.ok pt) (LsTokenInit ∗ coinsPost) (hevs_ok evs_p4 hevs_p4)
        hh hsteps0f htr_sf hout
      exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm_f4
    · dsimp only [kit, ikit, cliPollIdKitPlaced, cliIdStoreSpecFullPlaced] at hsave
      exact False.elim (cliId_saveRel_not_err hsave)
    · dsimp only [kit, ikit, cliPollSessKitPlaced] at hstore
      exact False.elim (cliSess_storeRel_not_err hstore)
  · exact hfalse.elim
  · exact (not_satisfies_false_sepConj hoom).elim


/-! ## `LibsignalFrozen` Counterparts -/

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget
end At3Wrap_p3

section At3Wrap_p4

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget

open Arm64 Arm64.Process ProofLib

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification CryptoVerification.RustHeap

open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet hiding lsLogOff withLsCodeRoLoaded

open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open CryptoVerification.E2E

open CryptoVerification.E2E.Bin

open CryptoVerification.E2E.Pqxdh

open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes

open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp Bytes

open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr

open CryptoVerification.LibsignalPublicApi.StoreSession

open CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf

open CryptoVerification.LibsignalPublicApi.MessageDecrypt

open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary

open CryptoVerification.SignalSession

open CryptoVerification.SignalSession.Cli

open CryptoVerification.SignalSession.Cli.Placed

open CryptoVerification.SignalSession.Cli.MainHops

open CryptoVerification.LibsignalSpqrV1 hiding Bytes

open CryptoVerification.SignalSession.Cli.RunSkeleton hiding RunHooksPlaced

open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced

open CryptoVerification.SignalSession.Cli.RunProofs

open CryptoVerification.SignalSession.Cli.KitInst

open CryptoVerification.SignalSession.Coins

open CryptoVerification.SignalSession.Coins.Placed

open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  StageP2MatchedFramedCliPlacedStmt
  storesAt_opened_entails_cliPollStoresKitsAtPlaced
  sepWPp_pollGoal_frame_placed
  stageP3_exit_prevEmpty_to_pollPost_placed
  sepWPp_genP3_to_tailQpan_placed
  closure_pathB_placed_ok
  cliFiles_eq_of_trace_eq_placed
  cliPollStageP1_fsAt_placed
  cliPollStageP4MatchedStack_placed_le_subStack
  stageP3ErrPrevEmpty_entails_exit_placed
  pathBP4RemAtPlaced
  stageP3MidPrevEmpty_eq_p4_placed
  stageP4MatchedExit_entails_exit_placed
  exit_entails_dpPollPost_placed
  sepWPp_genP3_to_pollGoal_placed
  closure_pathB_p4_cont_placed
  genP3Pre_placed genP3CallFrame_placed genP3S5PostFrame_placed
  stageP3DispatchOkMid_placed stageP3ErrPost_placed
  stageP3DispatchOkMidPrevEmpty_placed stageP3ErrPostPrevEmpty_placed
  stageP4MatchedSharedPlaced stageP4MatchedPrePlaced stageP4MatchedExitAtPlaced
  StageP4MatchedBranchPlaced StageP4MatchedPlacedStmt
  StageP3PrevEmptyVRegsPlacedStmt CliTryDecryptPqV1PlacedStmt

open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
)

open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)

open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)

open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget (
  StageP2MatchedBridgeEnv
)

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget (
  StageP2MatchedEnv StageP2MatchedMismatchEnv
)

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget (
  chainClone3_placed_ok_of_hooks senderChainClone3_placed_ok_of_hooks
)

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget (
  drop_session_structure4_placed_ok_at
)

open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)

open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)

open CryptoVerification.SignalSession.Cli.Slots (cliGhostExterns_sat_of_cliExternsPlaced)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  cliExternsPlaced_sessionMemcpyRegion_budget_sat
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  genP3Pre_placed genP3S5PostFrame_placed
  stageP3DispatchOkMidPrevEmpty_placed stageP3ErrPostPrevEmpty_placed
  StageP3Env StageP3OkPrefixEnv StageP3ErrEnv StageP3VerNeEnv
  pollTryDecryptPlacedSpecTPTight CliTryDecryptPqV1PlacedStmt StageP3PrevEmptyVRegsPlacedStmt
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced StageP4MatchedEnv StageP4MatchedPlacedStmt StageP4MatchedStoreStepEnv
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBPlacedBudget (
  stageP3ErrPrevEmpty_entails_exit_placed
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget (
  cliFiles_eq_of_trace_eq_placed exit_entails_dpPollPost_placed closure_pathB_p4_cont_placed
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem hookSat_sessionShimBudget_of_codec_p4 {H : LibsignalHooks}
    (h : HookSat H CryptoVerification.lsRustNoAllocShimSym
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec)) :
    HookSat H CryptoVerification.lsRustNoAllocShimSym
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionShimBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · exact ⟨hkeep, hsym, Or.inl ⟨hret, hcc, hpost⟩⟩
  · exact ⟨hkeep, hsym, Or.inr hrest⟩

private theorem cliChainClone3_budget_placed_ok_p4 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    ClosureStageP2DefsPlacedBudget.ChainClone3OkPlaced A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  chainClone3_placed_ok_of_hooks
    (hookSat_sessionShimBudget_of_codec_p4 hh.codecHooks.shim)
    hh.codecHooks.alloc
    ((show LibsignalBinary.Heap.SpecBudget.withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
        LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec from rfl) ▸
      hh.codecHooks.memcpy)

private theorem cliSenderChainClone3_budget_placed_ok_p4 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    ClosureStageP2DefsPlacedBudget.SenderChainClone3OkPlaced A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  senderChainClone3_placed_ok_of_hooks
    (hookSat_sessionShimBudget_of_codec_p4 hh.codecHooks.shim)
    hh.codecHooks.alloc
    ((show LibsignalBinary.Heap.SpecBudget.withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
        LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec from rfl) ▸
      hh.codecHooks.memcpy)

private theorem cliDropSessionStructure4_budget_placed_ok_at_p4 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec M A lim)) :=
  drop_session_structure4_placed_ok_at (i := 518) hh.codecHooks.dealloc (by decide)

set_option maxHeartbeats 800000 in
private theorem closure_pathB_frozen_placed_ok_at_priv [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.CliGhostAllocHooks M A lim gh)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (kitEnv : SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)))
    (hkitEnv : kitEnv =
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget.cliPollSessBudgetEnv
        A.repAlloc y.g.F y.g.peer (cliKitStk B) DeserEnv ReadEnv)
    (hikitEnv : ikitEnv =
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget.cliPollIdBudgetEnv
        A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
    (evs_p1 : List AllocEvent)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2MatchedEnv sess y.g.msg.identityKey))
    (hevs_mismatch : sess.state.remoteIdentity ≠ some y.g.msg.identityKey →
      ∀ evs_p2, StageP2MatchedMismatchEnv evs_p2 →
        DecPkEnv y.g (evs_p1 ++ evs_p2))
    (hfits_p3 : sess.state.remoteIdentity = some y.g.msg.identityKey →
      ∀ evs_p2 recG,
        StageP2MatchedBridgeEnv evs_p2 →
        SessionExtraRel recG sess →
        FitsEnv M lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
          (StageP3Env tdEnv recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins))
    (hfits_p4 : sess.state.remoteIdentity = some y.g.msg.identityKey →
      sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
      ∀ evs_p2 recG G₁ G' evs_p3 pt,
        StageP2MatchedBridgeEnv evs_p2 →
        SessionExtraRel recG sess →
        CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv tdEnv recG G₁ sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          y.g.coins evs_p3 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .ok pt →
        FitsEnv M lim (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st)
          (StageP4MatchedEnv
            (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv
            (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
            StoresGhost.opened.sessions StoresGhost.opened.identity
            y.g.peer.val y.g.msg.identityKey
            { sess with
              state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
              pendingPreKey := none
              pendingKyberPreKey := none }))
    (hevs_ok : sess.state.remoteIdentity = some y.g.msg.identityKey →
      sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
      ∀ evs_p2 recG G₁ G' evs_p3 pt evs_p4,
        StageP2MatchedBridgeEnv evs_p2 →
        SessionExtraRel recG sess →
        CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv tdEnv recG G₁ sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          y.g.coins evs_p3 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .ok pt →
        StageP4MatchedStoreStepEnv
          (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
          StoresGhost.opened.sessions StoresGhost.opened.identity
          y.g.peer.val y.g.msg.identityKey
          { sess with
            state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
            pendingPreKey := none
            pendingKyberPreKey := none } evs_p4 →
        DecPkEnv y.g (((evs_p1 ++ evs_p2) ++ evs_p3) ++ evs_p4))
    (hevs_err : sess.state.remoteIdentity = some y.g.msg.identityKey →
      sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
      ∀ evs_p2 recG G₁ G' evs_p3 e,
        StageP2MatchedBridgeEnv evs_p2 →
        SessionExtraRel recG sess →
        CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        StageP3ErrEnv tdEnv recG G₁ sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          y.g.coins evs_p3 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .error e →
        e ≠ .panic →
        DecPkEnv y.g ((evs_p1 ++ evs_p2) ++ evs_p3))
    (hevs_verNe : sess.state.remoteIdentity = some y.g.msg.identityKey →
      sess.state.version ≠ y.g.msg.message.messageVersion.zeroExtend 32 →
      ∀ evs_p2 recG evs_p3,
        StageP2MatchedBridgeEnv evs_p2 →
        SessionExtraRel recG sess →
        StageP3VerNeEnv recG sess.state evs_p3 →
        DecPkEnv y.g ((evs_p1 ++ evs_p2) ++ evs_p3))
    (hsteps01 : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s1)
    (htr1 : s1.trace = s0.trace)
    (hfr1 : CryptoVerification.LibsignalFrozen lsmpl s1.mem)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x0868#64)
    (hrun1 : s1.status = .Running)
    (hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    SepWPp prog (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  let hP2 : StageP2MatchedFramedCliPlacedStmt :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedInstPlacedBudget.stageP2Matched_framed_cli_placed_ok
  dsimp only
  have hro1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem :=
    ⟨CryptoVerification.LibsignalCodeLoaded.of_codeLoaded hfr1.2, hfr1.1⟩
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
  dsimp only [cliPollSessKitPlaced] at hload_rel
  obtain ⟨hloadS, hr_eq, hIn, hMatch, _, _, hSeeds, hRC, hPqLt⟩ :=
    pathB_scopeIn_and_match hinjK hsub hfPeer hdecOk hload_rel hcur
  subst hr_eq
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  let F_p2 : SepProp :=
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
  let Fr_tail : SepProp :=
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced A.repAlloc σ y.g.stores
    hsub hfPeer hdecOk (pid := pid) (sid := sid) (kid := kid) (kbk := kbk)
  have hstk_split := stackAt_subStack_sub_eq sp B (rootStack_le_subStack B) hsp_sub
  have hpre_split :
      stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut (some ⟨some sess⟩) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      ((stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
          y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
        p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut (some ⟨some sess⟩) ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack) ∗ F_p2) ∗ Fr_tail := by
    rw [hstk_split]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores_in))))))) ?_
    unfold cliPollStoresKitsAtPlaced F_p2 Fr_tail
    sep_frame
  refine sepWPp_conseq_pre hpre_split (sepWPp_pollGoal_frame_placed A lim DecPkEnv B S stk' y ?_)
  refine hP2 mmpl gh W B S Slots.scopeKit y sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 F_p2 _ _
    hh hReadFile hDeser hfits_p2 hcoins hMatch hro1 (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hroot hpc1 hrun1 hsp_align1 hregs1 ?_ ?_
  · intro hrem_ne evs_p2 sf Pf hevs_p2 _ _ _ hsf_sp htr_f hcs_f hvregs_f _ hent_f
    let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hent_f' :
        Pf ⊢
          dpFutDoneAt y.fut ∗
          memRegion sp 3280 ∗
          apiDecResultAt A.repAlloc y.out
            (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          coinsInstalledPlaced y.g.coinsP y.g.coins ∗
          LsTokenInit ∗
          FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          stackAt sp rootStack := by
      rw [M.stepEvents_append evs_p1 evs_p2 y.st]
      exact hent_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_f')) hm_f
    have hdec_at := apiDecResultAt_proto_entails_decResAt A.repAlloc y.out
      (.invalidMessage .preKey .badCiphertext) err
    have hstores_out := cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc)
      (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    have hm2 : sf.mem ⊨
        apiDecResultAt A.repAlloc y.out (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer pid sid kid kbk σ
          y.g.stores StoresGhost.opened ∗
        (protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          (LsTokenInit ∗ coinsInstalledPlaced y.g.coinsP y.g.coins) ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
            stackAt sp rootStack) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by dsimp only [cliPollStoresKitsAtPlaced, F_p2, Fr_tail]; sep_frame) hm1
    have hm3 := Arm64.Satisfies.mono (sepConj_mono hdec_at (sepConj_mono_left hstores_out)) hm2
    rw [← hstk_split] at hm3
    have hm4 : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          (LsTokenInit ∗ coinsInstalledPlaced y.g.coinsP y.g.coins) ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by sep_frame) hm3
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_of_reject StoresGhost.opened hS (err := err) nofun nofun
        (decPkDef_pathB_remId_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS htrusted hMatch hrem_ne)
    have hpost_goal := exit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y s0 sf
      (evs_p1 ++ evs_p2) StoresGhost.opened (.error err)
      (LsTokenInit ∗ coinsInstalledPlaced y.g.coinsP y.g.coins)
      (hevs_mismatch hrem_ne evs_p2 hevs_p2) hh hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm4
  · intro hrem_eq evs_p2 s2 g recG whisperMsgPtr whisperG preKeyMsgRem
      opkHi kyberPreKeyId signedPreKeyId hevs_p2 hwg_eq hex hmsg_fold hsteps12 hpc2 hrun2
      hs2_sp hsp_align2 htr2 _ _ _ hvregs2 _hro2
    have hfr2 : CryptoVerification.LibsignalFrozen lsmpl s2.mem :=
      CryptoVerification.libsignalFrozen_of_keepsFrozen hfr1 hsteps12.keepsFrozen
    subst hwg_eq
    have hsteps02 := Steps.trans hsteps01 hsteps12
    have htr20 : s2.trace = s0.trace := htr2.trans htr1
    have hs2_files : s2.fs.files = y.g.F :=
      (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps02 htr20).trans hf0
    have hpan_model : sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .error .panic →
        (dpSlotPollKStatePlaced A lim DecPkEnv B S).panics y.g := by
      intro hver hpan_s5
      show S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = none
      rw [hS]
      exact decPkDef_pathB_panic X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS htrusted hMatch hrem_eq hver hpan_s5
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
        (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
         ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
         memRegion (y.fut + 0x2a8#64) 4) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    have hpre_p3 :
        (LsTokenInit ∗
          genP3Pre_placed A lim (M.stepEvents evs_p2 (M.stepEvents evs_p1 y.st))
            s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
          stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s2 y.fut y.out 8#64 g 0#8 ∗
          stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
            (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
            (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
            (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
            (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
            (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
             ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
             memRegion (y.fut + 0x2a8#64) 4) ∗
          stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRem) ∗ F_p2 ⊢
        LsTokenInit ∗
          genP3Pre_placed A lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
            s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
          stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s2 y.fut y.out 8#64 g 0#8 ∗
          F_p3 := by
      rw [← M.stepEvents_append evs_p1 evs_p2 y.st]
      dsimp only [F_p2, F_p3]
      sep_frame
    refine sepWPp_conseq_pre hpre_p3
      (sepWPp_genP3_to_tailQpan_placed A lim DecPkEnv B S stk' y hpan_model ?_)
    refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudget.stageP3PrevEmptyVRegs_of_base_full_placed_ok
      (M.stepEvents (evs_p1 ++ evs_p2) y.st) (cliGhostExterns gh (cliExternsPlaced mmpl W)) W.C 0#64 W.Q.K
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudgetAux.StageP3CalleesM3BasePlaced.of_cliExternsPlaced mmpl gh W hG)
      (cliChainClone3_budget_placed_ok_p4 mmpl gh W hh)
      (cliSenderChainClone3_budget_placed_ok_p4 mmpl gh W hh)
      hTryDec (cliDropSessionStructure4_budget_placed_ok_at_p4 mmpl gh W hh)
      s0 s2 y.fut y.cx y.out 8#64 y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8 y.g.coins
      g recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message F_p3 _
      (hfits_p3 hrem_eq evs_p2 recG hevs_p2 hex)
      (by decide) (Or.inr (distinctSid_of_decPkOk₀ hdecOk)) hSeeds hRC hPqLt
      hfr2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' evs_p3 pt ptCap ptPtr s' P_s' hver hcl hdec_rel hevs_p3 hok hpt_le hpt_lt hpt_ne
        hsteps2' hpc' hrun' hs'_sp htr' hvregs' hx19' hx24' hx25' hx26' hx27' hx28'
        hro' hent_s'
      have hent_s'' :
          P_s' ⊢
            stageP3DispatchOkMidPrevEmpty_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 s' y.fut y.out 8#64
              ptCap ptPtr g pt 0#8 G'
              (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2 ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message
              (coinsAfterPlaced y.g.coinsP y.g.coins
                (decryptDraws W.C sess.state y.g.msg.message.senderRatchetKey y.g.coins)) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_s'
      exact LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget.closure_pathB_p4_cont_placed_at_priv hDropNz mmpl gh W X B S Scope hh hReadFile hDeser hS stk' hneed hstk63
        y kitEnv ikitEnv hkitEnv hikitEnv sess ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 s'
        rngPtr whisperMsgPtr ptCap ptPtr y.g.msgG.msg preKeyMsgRem P_s' R
        opkHi kyberPreKeyId signedPreKeyId g recG G₁ G' pt
        hfPeer hdecOk hIn hloadS htrusted hMatch hrem_eq hex
        (hfits_p4 hrem_eq hver evs_p2 recG G₁ G' evs_p3 pt hevs_p2 hex hcl hdec_rel hevs_p3 hok)
        (fun evs_p4 hevs_p4 =>
          hevs_ok hrem_eq hver evs_p2 recG G₁ G' evs_p3 pt evs_p4
            hevs_p2 hex hcl hdec_rel hevs_p3 hok hevs_p4)
        hmsg_fold hs2_files htr20 hs2_sp hsp_sub hsp_align2 hver hcl hdec_rel hok
        hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
        hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s''
    · intro G₁ G' evs_p3 e sf P_f hver hcl hdec_rel hevs_p3 herr hne_p hent_f
        hsf_sp htr_f hcs_f hvregs_f _
      have hent_f' :
          P_f ⊢
            ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
            memRegion (s2.sp + 0x3e0#64) 344 ∗
            stageP3ErrPostPrevEmpty_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 sf y.fut y.out e ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message
              (coinsAfterPlaced y.g.coinsP y.g.coins
                (decryptDraws W.C sess.state y.g.msg.message.senderRatchetKey y.g.coins)) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_f
      exact stageP3_exit_prevEmpty_to_pollPost_placed B S hh hS stk' hneed hstk63
        y ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 sf rngPtr whisperMsgPtr y.g.msgG.msg
        preKeyMsgRem _ P_f R opkHi kyberPreKeyId signedPreKeyId e
        (hevs_err hrem_eq hver evs_p2 recG G₁ G' evs_p3 e hevs_p2 hex hcl hdec_rel hevs_p3 herr hne_p)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathB_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS htrusted hMatch hrem_eq hver herr hne_p)
        hent_f' hsf_sp htr_f hcs_f hvregs_f
    · intro evs_p3 sf P_f hver_ne hevs_p3 hent_f hsf_sp htr_f hcs_f hvregs_f _
      have hent_f' :
          P_f ⊢
            ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
            memRegion (s2.sp + 0x3e0#64) 344 ∗
            stageP3ErrPostPrevEmpty_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 sf y.fut y.out
              (.invalidMessage .preKey .decryptionFailed) ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message (coinsAtPlaced y.g.coinsP y.g.coins) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_f
      exact stageP3_exit_prevEmpty_to_pollPost_placed B S hh hS stk' hneed hstk63
        y ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 sf rngPtr whisperMsgPtr y.g.msgG.msg
        preKeyMsgRem _ P_f R opkHi kyberPreKeyId signedPreKeyId
        (.invalidMessage .preKey .decryptionFailed)
        (hevs_verNe hrem_eq hver_ne evs_p2 recG evs_p3 hevs_p2 hex hevs_p3)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathB_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS htrusted hMatch hrem_eq hver_ne)
        hent_f' hsf_sp htr_f hcs_f hvregs_f

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
end At3Wrap_p4

section At3Wrap_p5

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib

open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  CliGhostHooks cliGhostExterns
)

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification CryptoVerification.RustHeap

open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet hiding lsLogOff withLsCodeRoLoaded

open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open CryptoVerification.E2E CryptoVerification.E2E.Bin

open CryptoVerification.E2E.Pqxdh

open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes

open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp Bytes

open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over hiding
  stageP4Prev1SharedPlaced stageP4Prev1RawPrePlaced stageP4Prev1PrePlaced stageP4Prev1ExitAtPlaced

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr

open CryptoVerification.LibsignalPublicApi.StoreSession

open CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf

open CryptoVerification.LibsignalPublicApi.MessageDecrypt

open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary

open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

open CryptoVerification.SignalSession.Cli.Placed

open CryptoVerification.SignalSession.Cli.MainHops

open CryptoVerification.LibsignalSpqrV1 hiding Bytes

open CryptoVerification.SignalSession.Cli.RunSkeleton hiding RunHooksPlaced

open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced

open CryptoVerification.SignalSession.Cli.RunProofs

open CryptoVerification.SignalSession.Cli.KitInst

open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  stageP4Prev1CallStack_le_subStack_placed cliFiles_eq_of_trace_eq_placed
  cliPollStageP4Prev1_fsAt_placed pathC_recPrev1Ok_of_tryDecrypt_placed
  cliPollPrev1StoresKitsAtPlaced_entails_storesAt overGenP3S5PostFrame_placed
  overGenP3Pre_placed overStageP3ErrPostPrevEmpty_placed overPathAP4RemAtPlaced
  overExit_entails_dpPollPost_placed stageP3MidPathC_entails_p4_placed
  stageP4PathCExit_entails_exit_placed
  StageP4Prev1RawBranchPlaced StageP4Prev1BranchPlaced StageP4Prev1VRegsPlacedStmt
  closure_pathC_p4_cont_placed

open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv
)

open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (PreKeyStoreBudgetEnv)

open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)

open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (KyberPreKeyStoreBudgetEnv)

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgePlacedBudget (
  SerializePrev1EnvX
)

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1StorePlacedBudget (
  StageP4StorePrev1ExitEnv StorePrev1BudgetEnv StorePrev1StepEnv
)

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget (
  StageP4Prev1BranchPlaced StageP4Prev1ExitEnv StageP4Prev1NoneExitEnv StageP4Prev1NoneStepEnv
  StageP4Prev1RawBranchPlaced StageP4Prev1StepEnv StageP4Prev1StoreBranchEnv
  fitsEnv_prev1Step_of_exit
  stageP4Prev1ExitAtPlaced stageP4Prev1PrePlaced stageP4Prev1RawPrePlaced stageP4Prev1SharedPlaced
)

open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget (AddrTextValEnv)

open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)

open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)

open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (
  cliPollPrev1StoresKitsAtPlaced_entails_storesAt overExit_entails_dpPollPost_placed
  overGenP3S5PostFrame_placed overPathAP4RemAtPlaced pathC_recPrev1Ok_of_tryDecrypt_placed
  stageP3MidPathC_entails_p4_placed
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxHeartbeats 1200000 in
private theorem closure_pathC_p4_cont_placed_at_priv [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hp4Envs : p4Envs = fun B F0 peer pid kpkId spkId kbk =>
      cliPollStageP4Prev1Envs A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv)
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))}
    (evs_pre : List AllocEvent)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hs_old : Slots.scopeIn ⟨some s_old⟩)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r))
    (hcur : r.currentSession = some s_old)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hnot_match : ¬ SessMatchesPm s_old y.g.msg)
    (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
    (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
    (recG G₁ G' : SessionGhost)
    (rngPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr : BitVec 64)
    (whisperG : SignalMessageGhost)
    (preKeyMsgRem P_s' R : SepProp)
    (pt : List (BitVec 8))
    (s0 s2 s' : State)
    (hFits4 :
      let σ := cliKitStk B
      let pid := pmPreKeyId y.g.msg
      let prev1Kit := cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ
      let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
      let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
      let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
      let envs := p4Envs B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
      let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
      let ses' : Session (List (BitVec 8)) :=
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
          pendingPreKey := none
          pendingKyberPreKey := none }
      FitsEnv M lim (M.stepEvents evs_pre y.st)
        (StageP4Prev1ExitEnv prev1Kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
          kpkKit envs.kpkKitEnv StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber m.opkId y.g.peer.val
          y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey G' ses'
          (E2E.Record.encSession (Over.clearPending s_old))))
    (hEnv4 :
      let σ := cliKitStk B
      let pid := pmPreKeyId y.g.msg
      let prev1Kit := cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ
      let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
      let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
      let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
      let envs := p4Envs B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
      let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
      let ses' : Session (List (BitVec 8)) :=
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
          pendingPreKey := none
          pendingKyberPreKey := none }
      ∀ evs4,
        StageP4Prev1ExitEnv prev1Kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
          kpkKit envs.kpkKitEnv StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber m.opkId y.g.peer.val
          y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey G' ses'
          (E2E.Record.encSession (Over.clearPending s_old)) evs4 →
        DecPkEnv y.g (evs_pre ++ evs4))
    (hpm_eq : y.g.msg = pmOfE m i)
    (hi : SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys y.g.F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
      (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hex : SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk))
    (hmsg_fold :
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
    (hfiles2 : s2.fs.files = y.g.F)
    (htr2 : s2.trace = s0.trace)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_align2 : (s2.sp &&& 15#64 == 0#64) = true)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hver : (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      y.g.msg.message.messageVersion.zeroExtend 32)
    (hcl : CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁)
    (hdec_rel : G₁.AfterTryDecrypt true G')
    (hok : (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_ne : ptPtr ≠ 0#64)
    (hsteps2' : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s2 s')
    (hpc' : s'.pc = dpPollEntryPlaced + 0x34dc#64)
    (hrun' : s'.status = .Running)
    (hs'_sp : s'.sp = s2.sp)
    (htr' : s'.trace = s0.trace)
    (hvregs' : calleeSavedVRegs s' = calleeSavedVRegs s0)
    (hx19' : s'.readReg64 .x19 = y.fut)
    (hx24' : s'.readReg64 .x24 = s2.sp + 0x370#64)
    (hx25' : s'.readReg64 .x25 = s2.sp + 0x210#64)
    (hx26' : s'.readReg64 .x26 = y.out)
    (hx27' : s'.readReg64 .x27 = y.cx)
    (hx28' : s'.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hro' : StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem)
    (hent_s' : P_s' ⊢
      stageP3DispatchOkMidPrev1At_placed A lim (M.stepEvents evs_pre y.st) s0 s2 s'
        y.fut y.out 8#64 prevCap prevPtr ptCap ptPtr
        (E2E.Record.encSession (Over.clearPending s_old)) pt 0#8 G'
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2 ∗
      overGenP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (Coins.coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.msg.message.senderRatchetKey y.g.coins)) ∗
      Over.overScratch s2.sp) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
    let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    let Fr_tail : SepProp :=
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32
    SepWPp prog (s0.readReg64 .x30) s' (P_s' ∗ F_p3)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post
            y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5ModelPanicProp W.C W.Q.K y.g.peer y.g.me st0 y.g.msg.message
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins s0) := by
  subst hp4Envs
  dsimp only
  let st_pre := M.stepEvents evs_pre y.st
  let A_s : RustAlloc := A.atState lim st_pre s'
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
  let prev1Kit := cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ
  let ops : Over.StorePrev1Ops prev1Kit := cliPollStorePrev1OpsPlaced
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
  let envs := cliPollStageP4Prev1Envs A.repAlloc B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey ReadEnv
  let enc := E2E.Record.encSession (Over.clearPending s_old)
  let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
  let st0 := pathAInitState ⟨W.C, W.Q⟩ meE k m dk
  dsimp only at hFits4 hEnv4
  generalize hst'_eq :
    (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2 = st' at hent_s'
  generalize hcoins_eq :
    Coins.coinsAfterPlaced y.g.coinsP y.g.coins
      (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins) = coinsPost at hent_s'
  let ses' : Session (List (BitVec 8)) :=
    { pathAInitSession ⟨W.C, W.Q⟩ meE k m dk with
      state := st', pendingPreKey := none, pendingKyberPreKey := none }
  rw [hst'_eq] at hFits4 hEnv4
  have hok_pair : genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0 =
      (.ok pt, st') := Prod.ext hok hst'_eq
  have hex' : SessionExtraRel G' ses' := sessionExtraRel_of_clone_decRel hex hcl hdec_rel
  have hs'_sp0 : s'.sp = sp := hs'_sp.trans hs2_sp
  have hsp_ret : sp + 0xcd0#64 = s0.sp := sp_frame_sub_add s0.sp
  have hf' : s'.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed hh hsteps2' (htr'.trans htr2.symm)).trans hfiles2
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp4_64 : stageP4CallStack prev1Kit ikit pkKit kpkKit ≤ 2 ^ 64 :=
    Nat.le_trans
      (stageP4Prev1CallStack_le_subStack_placed A.repAlloc y.g.F y.g.peer pid m.kpkId m.spkId
        y.g.msg.baseKey B)
      hsub64
  intro R' hm hL
  have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_s')) hm
  have hmid := stageP3MidPathC_entails_p4_placed A lim st_pre B y s0 s2 s' rngPtr 8#64 prevCap
    prevPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem coinsPost m.opkId
    (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId enc pt G' st'
    hs2_sp hs'_sp0 hsp_sub
  dsimp only at hmid
  have hp5f : overGenP3S5PostFrame_placed A.repAlloc = overGenP3S5PostFrame_placed A_s := rfl
  have hk1 : kit.storeAt = (cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ).storeAt := rfl
  have hk2 : ikit.identityAt = (cliPollIdKitPlaced A_s y.g.F y.g.peer σ).identityAt := rfl
  have hk3 : pkKit.storeAt = (cliPollPkKitPlaced A_s y.g.F pid σ).storeAt := rfl
  have hk4 : spkKit.storeAt = (cliPollSpkKitPlaced A_s y.g.F m.spkId σ).storeAt := rfl
  have hk5 : kpkKit.storeAt =
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt := rfl
  have hk6 : dirAt A.repAlloc = dirAt A_s := rfl
  have hm1' : s'.mem ⊨
      (Over.stageP3DispatchOkMidPrev1Placed A_s s0 s2 y.fut y.out 8#64
          prevCap prevPtr ptCap ptPtr enc pt 0#8 G' st' ∗
        overGenP3S5PostFrame_placed A_s sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
          (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
          coinsPost ∗
        Over.overScratch s2.sp) ∗
      (stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      (cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ).storeAt
        (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      (cliPollIdKitPlaced A_s y.g.F y.g.peer σ).identityAt
        y.g.stores StoresGhost.opened.identity ∗
      (cliPollPkKitPlaced A_s y.g.F pid σ).storeAt
        (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      (cliPollSpkKitPlaced A_s y.g.F m.spkId σ).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt
        (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A_s (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) ∗ R' := by
    unfold stageP3DispatchOkMidPrev1At_placed at hm1
    rw [hp5f, hk1, hk2, hk3, hk4, hk5, hk6] at hm1
    simpa only [hs2_sp, sepConj_assoc] using hm1
  have hp4_pre_eq :
      Over.stageP4Prev1PrePlaced 0#64
        (cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ)
        (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
        (cliPollPkKitPlaced A_s y.g.F pid σ)
        (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey σ)
        s0 s' y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
        prevCap prevPtr ptCap ptPtr 8#64 m.opkId m.kpkId m.spkId 0#8 pt enc
        y.g.peer y.g.msg.identityKey y.g.msg.baseKey
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        G' st' =
      stageP4Prev1PrePlaced A lim st_pre prev1Kit ikit pkKit kpkKit s0 s'
        y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
        prevCap prevPtr ptCap ptPtr 8#64 m.opkId m.kpkId m.spkId 0#8 pt enc
        y.g.peer y.g.msg.identityKey y.g.msg.baseKey
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        G' st' := by
    unfold Over.stageP4Prev1PrePlaced Over.stageP4Prev1RawPrePlaced Over.stageP4Prev1SharedPlaced
      stageP4Prev1PrePlaced stageP4Prev1RawPrePlaced stageP4Prev1SharedPlaced
    have hpa : protocolAddressAt A_s = protocolAddressAt A.repAlloc := rfl
    have hpv : prevVecAt A_s = prevVecAt A.repAlloc := rfl
    have hss : sessionStateAt A_s = sessionStateAt A.repAlloc := rfl
    have hlv : A_s.live = A.live := rfl
    have hs1 : (cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ).ss_vt = prev1Kit.ss_vt := rfl
    have hs2 : (cliPollIdKitPlaced A_s y.g.F y.g.peer σ).id_vt = ikit.id_vt := rfl
    have hs3 : (cliPollPkKitPlaced A_s y.g.F pid σ).pk_vt = pkKit.pk_vt := rfl
    have hs4 : (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).kpk_vt =
        kpkKit.kpk_vt := rfl
    have hc : stageP4CallStack
        (cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ)
        (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
        (cliPollPkKitPlaced A_s y.g.F pid σ)
        (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey σ) =
      stageP4CallStack prev1Kit ikit pkKit kpkKit := rfl
    have hst1 : (cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ).storeAt = prev1Kit.storeAt := rfl
    have hst2 : (cliPollIdKitPlaced A_s y.g.F y.g.peer σ).identityAt = ikit.identityAt := rfl
    have hst3 : (cliPollPkKitPlaced A_s y.g.F pid σ).storeAt = pkKit.storeAt := rfl
    have hst4 : (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt =
        kpkKit.storeAt := rfl
    rw [hpa, hpv, hss, hlv, hs1, hs2, hs3, hs4, hc, hst1, hst2, hst3, hst4,
      RustCliAllocBudget.atState_pool]
  have hp4_rem_eq :
      overPathAP4RemAtPlaced A_s B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost =
      overPathAP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem
        coinsPost := rfl
  have hm2 : s'.mem ⊨
      stageP4Prev1PrePlaced A lim st_pre prev1Kit ikit pkKit kpkKit s0 s'
        y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
        prevCap prevPtr ptCap ptPtr 8#64 m.opkId m.kpkId m.spkId 0#8 pt enc
        y.g.peer y.g.msg.identityKey y.g.msg.baseKey
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        G' st' ∗
      (overPathAP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost ∗
        R') := by
    rw [← sepConj_assoc] at hm1' ⊢
    rw [← hp4_pre_eq, ← hp4_rem_eq]
    exact Arm64.Satisfies.mono (sepConj_mono_left hmid) hm1'
  have hm_sess : s'.mem ⊨ sessionStateAt A.repAlloc (y.fut + 0xf8#64) G' st' ∗ anyHeap := by
    refine Arm64.Satisfies.mono ?_ hm2
    unfold stageP4Prev1PrePlaced stageP4Prev1RawPrePlaced
    have hcomm : ∀ A1 A2 S A3 A4 : SepProp,
        (A1 ∗ A2 ∗ S ∗ A3) ∗ A4 ⊢ S ∗ anyHeap := fun A1 A2 S A3 A4 =>
      Entails.trans (Entails.of_eq (by ac_rfl : (A1 ∗ A2 ∗ S ∗ A3) ∗ A4 = S ∗ (A1 ∗ A2 ∗ A3 ∗ A4)))
        (sepConj_mono_right (entails_anyHeap _))
    exact hcomm _ _ _ _ _
  have hex0 : SessionExtraRel G'
      { pathAInitSession ⟨W.C, W.Q⟩ meE k m dk with
        state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
        pendingPreKey := none
        pendingKyberPreKey := none } := by
    rw [hst'_eq]; exact hex'
  have hm_sess0 : s'.mem ⊨ sessionStateAt A.repAlloc (y.fut + 0xf8#64) G'
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2 ∗ anyHeap := by
    rw [hst'_eq]; exact hm_sess
  have hrecOk : ops.RecPrev1Ok G' ses' enc := by
    have hr := pathC_recPrev1Ok_of_tryDecrypt_placed (A := A.repAlloc) (σ := σ)
      hs_old hdecOk hver hok hex0 hm_sess0
    dsimp only at hr
    rw [hst'_eq] at hr
    exact hr
  have hwp4 := LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage4OverInstPlacedBudget.stageP4Prev1_placed_inst
    hDropNz mmpl gh W B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
    hh hReadFile st_pre
    s0 s'
    y.fut y.cx y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
    (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
    prevCap prevPtr ptCap ptPtr 8#64
    m.opkId m.kpkId m.spkId 0#8 pt enc
    y.g.msg.identityKey y.g.msg.baseKey
    StoresGhost.opened.sessions StoresGhost.opened.identity
    StoresGhost.opened.oneTime StoresGhost.opened.kyber
    G' ses'
    hFits4 hex' hrecOk rfl rfl
    (cliPollKpk_markOk_of_pmOfE (A := A.repAlloc) 0#64 y.g.F m i σ hpm_eq)
    (cliPollPk_removeIdOk_of_pmOfE (A := A.repAlloc) 0#64 y.g.F m i σ hpm_eq)
    hpt_le hpt_lt hpt_ne hp4_64
    (cliPollStageP4Prev1_fsAt_placed A.repAlloc hh y.g.F y.g.peer pid m.kpkId m.spkId
      y.g.msg.baseKey σ hf')
    hro' hpc' hrun'
    (hs'_sp ▸ hsp_align2) (htr' ▸ List.prefix_refl _)
    hx19' (hs'_sp ▸ hx24') (hs'_sp ▸ hx25') hx26' hx27' hx28' hvregs'
  obtain ⟨sf, hsteps_p4, hBranch⟩ := hwp4 _ hm2 hL
  refine ⟨sf, hsteps_p4, ?_⟩
  have hpre_id : y.g.msg.preKeyId = m.opkId := hpm_eq ▸ (pmOfE_preKeyId_spkId_baseKey_eq m i).1
  have hspk_id : y.g.msg.signedPreKeyId = m.spkId :=
    hpm_eq ▸ (pmOfE_preKeyId_spkId_baseKey_eq m i).2.1
  rcases hBranch with
    ⟨hpcm, hrunm, Pf, hmf, ⟨_hsteps'f, hspf, hcs_p4, hvregs_f, _hro_f, hBr⟩⟩ |
    ⟨_, _, _, hpan_false⟩ |
    ⟨_, hoom⟩
  · rcases hBr with
      ⟨c, evs4, hevs4, _hsave, hmark, _hrem, _hstore, htr_f, hpost_f⟩ |
      ⟨_evs4, _hevs4, hsave, _, _⟩ |
      ⟨c, e, evs4, hevs4, _hsave, hmark, htr_f, hpost_f⟩ |
      ⟨opkId, _c, e, _evs4, hopk, _hevs4, _hsave, _hmark, hrem, _, _⟩ |
      ⟨_c, _evs4, _hevs4, _hsave, _hmark, _hrem, hstore, _, _⟩
    · rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have hevs_exit : StageP4Prev1ExitEnv prev1Kit envs.opsEnv ikit envs.ikitEnv
          pkKit envs.pkKitEnv kpkKit envs.kpkKitEnv
          StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber
          m.opkId y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey
          G' ses' enc evs4 := by
        cases hop : m.opkId <;>
          simp only [hop, StageP4Prev1ExitEnv, StageP4Prev1NoneExitEnv,
            StageP4Prev1StoreBranchEnv] at hevs4 ⊢ <;>
          exact Or.inl hevs4
      have hevs_tot : DecPkEnv y.g (evs_pre ++ evs4) := hEnv4 evs4 hevs_exit
      have hpost_f' : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents (evs_pre ++ evs4) y.st)
          prev1Kit ikit pkKit kpkKit s0 s' sf
          y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
          (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
          ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut m.opkId)
          (vecResultAt A.repAlloc y.out (.ok pt)) m.kpkId m.spkId pt
          y.g.peer y.g.msg.identityKey y.g.msg.baseKey
          (ops.storeUpdatePrev1 StoresGhost.opened.sessions y.g.peer.val G' ses' enc (.ok ()))
          (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
          (match m.opkId with
           | none => StoresGhost.opened.oneTime
           | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ()))
          (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.ok ())) := by
        rw [M.stepEvents_append evs_pre evs4 y.st]
        revert hevs4 _hrem htr_f hpost_f
        cases m.opkId <;> intro _ _ _ hp <;> exact hp
      have htr_sf : sf.trace = s0.trace := by
        have h1 : ikit.saveEvs y.g.peer.val y.g.msg.identityKey (.ok c) = [] := rfl
        have h2 : kpkKit.markEvs m.kpkId m.spkId y.g.msg.baseKey (.ok ()) = [] := rfl
        have h4 : ops.storeEvsPrev1 y.g.peer.val G' ses' enc (.ok ()) = [] := rfl
        revert hevs4 _hrem htr_f hpost_f
        cases m.opkId with
        | none =>
          intro _ _ htr_f _
          dsimp only at htr_f
          rw [h1, h2, h4, List.append_nil, List.append_nil, List.append_nil,
            List.append_nil, htr'] at htr_f
          exact htr_f
        | some opkId =>
          intro _ _ htr_f _
          have h3 : pkKit.removeEvs opkId (.ok ()) = [] := rfl
          dsimp only at htr_f
          rw [h1, h2, h3, h4, List.append_nil, List.append_nil, List.append_nil,
            List.append_nil, htr'] at htr_f
          exact htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ overPathAP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost,
        hmf, ?_, hsf_sp, hcs_full⟩
      intro hsteps0f hm_f
      let kyber' := (kpkMarkOf cliIo.rd y.g.F StoresGhost.opened.kyber
        m.kpkId m.spkId y.g.msg.baseKey).2
      have hmark_eq : StoresGhost.opened.kyber.mark cliIo.rd y.g.F m.kpkId
          y.g.msg.signedPreKeyId y.g.msg.baseKey = (.ok (), kyber') := by
        rw [hspk_id]
        exact cliKpk_markRel_ok_to_mark (A := A.repAlloc) (b := 0#64)
          (s1 := σ.kpkGetShim) (s2 := σ.kpkGetPoll) (s3 := σ.kpkMarkShim) (s4 := σ.kpkMarkPoll)
          hmark
      obtain ⟨hDec, hWr⟩ :=
        decPkDefD2c_pathC_ok X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hfPeer hdecOk hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver hok_pair
          hmark_eq
      let oneTime' := match y.g.msg.preKeyId with
        | none => StoresGhost.opened.oneTime
        | some j => (Cli.removePreKey cliIo.rd y.g.F StoresGhost.opened.oneTime j).2
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := StoresGhost.opened.identity.saveUpd cliIo.rd y.g.F y.g.peer.val
            y.g.msg.identityKey
          kyber := kyber'
          oneTime := oneTime'
          sessions := StoresGhost.opened.sessions.put (Cli.addressText y.g.peer.val)
            (Over.encodeRecordPrev1 ses' enc) }
      have hot_eq : g'.oneTime =
          (match m.opkId with
           | none => StoresGhost.opened.oneTime
           | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ())) := by
        dsimp only [g', oneTime', pkKit, cliPollPkKitPlaced,
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
          cliPreKeyStoreSpec]
        rw [hpre_id]
      exact p4_finish_dpPollPost_placed A lim DecPkEnv B S hh stk' hneed hstk63 y s0 s' sf
        (evs_pre ++ evs4) rngPtr whisperMsgPtr ptCap ptPtr whisperG Pf
        (vecResultAt A.repAlloc y.out (.ok pt)) preKeyMsgRem coinsPost R
        m.opkId (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId pt (.ok pt)
        (ops.storeUpdatePrev1 StoresGhost.opened.sessions y.g.peer.val G' ses' enc (.ok ()))
        (match m.opkId with
         | none => StoresGhost.opened.oneTime
         | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ()))
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.ok ()))
        g' hevs_tot hs'_sp0 hsp_sub (decResultAt_ok_entails_decResAt_anyHeap A.repAlloc y.out pt)
        hmsg_fold rfl rfl hot_eq rfl rfl rfl hpost_f' hsteps0f htr_sf
        (slotOutTr_d2c_of_accept hS hDec hWr) hm_f
    · exact False.elim (cliId_saveRel_not_err (A := A.repAlloc) (b := 0#64)
        (F0 := y.g.F) (peer := y.g.peer) (σ := σ) hsave)
    · rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have hevs_exit : StageP4Prev1ExitEnv prev1Kit envs.opsEnv ikit envs.ikitEnv
          pkKit envs.pkKitEnv kpkKit envs.kpkKitEnv
          StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber
          m.opkId y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey
          G' ses' enc evs4 := by
        cases m.opkId with
        | none => exact Or.inr (Or.inl hevs4)
        | some _ => exact Or.inr (Or.inr (Or.inl hevs4))
      have hevs_tot : DecPkEnv y.g (evs_pre ++ evs4) := hEnv4 evs4 hevs_exit
      have hpost_f' : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents (evs_pre ++ evs4) y.st)
          prev1Kit ikit pkKit kpkKit s0 s' sf
          y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
          (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
          ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut m.opkId)
          (speErrAt kpkKit.markErr y.out e) m.kpkId m.spkId pt
          y.g.peer y.g.msg.identityKey y.g.msg.baseKey
          StoresGhost.opened.sessions
          (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
          StoresGhost.opened.oneTime
          (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId
            y.g.msg.baseKey (.error e)) := by
        rw [M.stepEvents_append evs_pre evs4 y.st]; exact hpost_f
      have htr_sf : sf.trace = s0.trace := by
        have h1 : ikit.saveEvs y.g.peer.val y.g.msg.identityKey (.ok c) = [] := rfl
        have h2 : kpkKit.markEvs m.kpkId m.spkId y.g.msg.baseKey (.error e) = [] := rfl
        rw [h1, h2, List.append_nil, List.append_nil, htr'] at htr_f
        exact htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ overPathAP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost,
        hmf, ?_, hsf_sp, hcs_full⟩
      intro hsteps0f hm_f
      have hmark_err :
          (StoresGhost.opened.kyber.mark cliIo.rd y.g.F m.kpkId
            y.g.msg.signedPreKeyId y.g.msg.baseKey).1 = .error () := by
        rw [hspk_id]
        exact cliKpk_markRel_error_to_mark (A := A.repAlloc) (b := 0#64)
          (s1 := σ.kpkGetShim) (s2 := σ.kpkGetPoll) (s3 := σ.kpkMarkShim) (s4 := σ.kpkMarkPoll)
          hmark
      have hDec := decPkDefD2c_pathC_mark_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg
        y.g.coins hdecOk hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver hok_pair
        hmark_err
      let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val
            y.g.msg.identityKey (.ok c)
          kyber := kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId
            y.g.msg.baseKey (.error e) }
      exact p4_finish_dpPollPost_placed A lim DecPkEnv B S hh stk' hneed hstk63 y s0 s' sf
        (evs_pre ++ evs4) rngPtr whisperMsgPtr ptCap ptPtr whisperG Pf
        (speErrAt kpkKit.markErr y.out e) preKeyMsgRem coinsPost R
        m.opkId (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId pt (.error err)
        StoresGhost.opened.sessions StoresGhost.opened.oneTime
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.error e))
        g' hevs_tot hs'_sp0 hsp_sub
        (cliPollKpk_markErr_entails_decResAt_anyHeap A.repAlloc 0#64 y.g.F m.kpkId m.spkId
          y.g.msg.baseKey σ y.out e err)
        hmsg_fold rfl rfl rfl rfl rfl rfl hpost_f' hsteps0f htr_sf
        (slotOutTr_d2c_of_reject g' hS nofun nofun hDec) hm_f
    · exact False.elim (cliPk_removeRel_not_err_of_pkStoreKeys (A := A.repAlloc) (b := 0#64)
        (pid := pid) (σ := σ) (e := e) hk hopk hrem)
    · exact False.elim (by cases hstore)
  · exact hpan_false.elim
  · exact (not_satisfies_false_sepConj hoom).elim

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
end At3Wrap_p5

section At3Wrap_p6

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget

open Arm64 Arm64.Process ProofLib

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification CryptoVerification.RustHeap

open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet hiding lsLogOff withLsCodeRoLoaded

open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom

open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding dropSessionStructureLocal2Spec

open CryptoVerification.LibsignalTripleRatchet.Record

open CryptoVerification.E2E CryptoVerification.E2E.Bin

open CryptoVerification.E2E.Pqxdh

open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes

open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp Bytes

open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

open CryptoVerification.E2E.Pqxdh.WireEntries

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 hiding
  ChainClone3OkPlaced SenderChainClone3OkPlaced

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over hiding
  stageP4Prev1SharedPlaced stageP4Prev1PrePlaced stageP4Prev1ExitAtPlaced

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr

open CryptoVerification.LibsignalPublicApi.StoreSession

open CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf

open CryptoVerification.LibsignalPublicApi.MessageDecrypt

open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary

open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

open CryptoVerification.SignalSession.Cli.Placed

open CryptoVerification.SignalSession.Cli.MainHops

open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)

open CryptoVerification.LibsignalSpqrV1 hiding Bytes

open CryptoVerification.SignalSession.Cli.RunSkeleton hiding RunHooksPlaced

open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced

open CryptoVerification.SignalSession.Cli.RunProofs

open CryptoVerification.SignalSession.Cli.KitInst

open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  cliChainClone3_placed_ok cliSenderChainClone3_placed_ok cliDropSessionStructure4_placed_ok_at
  cliFsAt_of_files_eq_placed cliFiles_eq_of_trace_eq_placed
  cliPollStageP4Prev1_fsAt_placed storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c
  pathC_recPrev1Ok_of_tryDecrypt_placed
  overGenP3S5PostFrame_placed
  overGenP3Pre_placed overStageP3ErrPostPrevEmpty_placed overPathAP4RemAtPlaced
  overExit_entails_dpPollPost_placed stageP3MidPathC_entails_p4_placed
  stageP4PathCExit_entails_exit_placed stageP3ErrPathC_entails_exit_placed
  stageP3_exit_pathC_to_pollPost_placed
  StageP2OverErrPlaced StageP2OverQpanCliPlacedStmt
  StageP4Prev1RawBranchPlaced StageP4Prev1BranchPlaced StageP4Prev1VRegsPlacedStmt
  overSepWPp_pollGoal_frame_placed overSepWPp_genP3_to_tailQpan_placed
  overPollTryDecryptPlacedSpecP overPollTryDecryptPlacedSpecTPTight
  OverCliTryDecryptPqV1PlacedStmt StageP3Prev1VRegsAtPlacedStmt StageP3Prev1VRegsA0PlacedStmt
  closure_pathC_p4_cont_placed closure_pathC_placed_ok

open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)

open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)

open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)

open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollKStateBudget DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env
)

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux (
  VerNeTopEnv
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  ChainClone3OkPlaced SenderChainClone3OkPlaced
  StageP3OkPrefixEnv StageP3ErrEnv
  pollTryDecryptPlacedSpecP pollTryDecryptPlacedSpecTPTight
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (
  pathC_recPrev1Ok_of_tryDecrypt_placed
  overGenP3Pre_placed overGenP3S5PostFrame_placed overPathAP4RemAtPlaced
  overExit_entails_dpPollPost_placed stageP3MidPathC_entails_p4_placed
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem x29_eq_sp_add_c70_pathC_placed_p6 {s0 s2 : State}
    (hx29 : s2.readReg64 .x29 = s0.sp - 0x60#64)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64) :
    s2.readReg64 .x29 = s2.sp + 0xc70#64 := by
  rw [hx29, hs2_sp]; bv_omega

set_option maxHeartbeats 800000 in
private theorem p4_finish_dpPollPost_placed_p6 [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (B : RunBudgets) (S : RunSem)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 s' sf : State) (evs : List AllocEvent)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64)
    (whisperG : SignalMessageGhost)
    (Pf outAt preKeyMsgRem coinsPost R : SepProp)
    (opkId? : Option (BitVec 32)) (msgVer pid kpkId spkId : BitVec 32)
    (pt : List (BitVec 8))
    (ans : Except (ApiError AddrVal Unit) (List (BitVec 8)))
    (sess1 oneTime1 : DirGhost) (id1 : IdGhost) (kyber1 : KyberGhost)
    (g' : StoresGhost)
    (hevs : DecPkEnv y.g evs)
    (hs'_sp0 : s'.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hout_ent : outAt ⊢ decResAt A.repAlloc y.out ans ∗ anyHeap)
    (hmsg_fold :
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
    (hsess : g'.sessions = sess1)
    (hsigned : g'.signed = StoresGhost.opened.signed)
    (honeTime : g'.oneTime = oneTime1)
    (hid : g'.identity = id1)
    (hkyber : g'.kyber = kyber1)
    (hpub : g'.pub = StoresGhost.opened.pub)
    (hpost_f : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs y.st) 0#64
      (cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollPkKitPlaced A.repAlloc y.g.F pid (cliKitStk B))
      (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey (cliKitStk B))
      s0 s' sf y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
      (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
      ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut opkId?) outAt kpkId spkId pt
      y.g.peer y.g.msg.identityKey y.g.msg.baseKey sess1 id1 oneTime1 kyber1)
    (hsteps0f : Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s0 sf)
    (htr_sf : sf.trace = s0.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' ans s0.trace sf.trace)
    (hm_f : sf.mem ⊨
      (Pf ∗ overPathAP4RemAtPlaced A.repAlloc B y (s0.sp - 0xcd0#64) rngPtr whisperMsgPtr whisperG
        msgVer pid kpkId spkId preKeyMsgRem coinsPost) ∗
      ((memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
        memRegion y.cx 32) ∗ R)) :
    sf.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post y s0 sf ∗
      R := by
  let sp := s0.sp - 0xcd0#64
  have hexit := stageP4PathCExitAt_entails_exit_placed A lim (M.stepEvents evs y.st) B y s0 s' sf
    rngPtr 8#64 whisperMsgPtr ptCap ptPtr whisperG outAt preKeyMsgRem coinsPost opkId? msgVer
    pid kpkId spkId pt ans sess1 oneTime1 id1 kyber1 g' hs'_sp0 hsp_sub hout_ent hmsg_fold
    hsess hid honeTime hsigned hkyber hpub
  dsimp only at hexit
  have hm_f1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hpost_f)) hm_f
  have hm_f2 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm_f1
  have hm_f3 : sf.mem ⊨
      (decResAt A.repAlloc y.out ans ∗
        storesAt A.repAlloc y.g.stores g' ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        FromRecordCallees.lsLogOff ∗
        A.pool lim (M.stepEvents evs y.st) sf ∗
        (LsTokenInit ∗ coinsPost ∗ anyHeap) ∗
        dpFutDoneAt y.fut ∗
        memRegion y.cx 32 ∗
        memRegion sp 3280 ∗
        stackAt sp (dpClosSubStack B) ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
    Arm64.Satisfies.mono (by sep_frame) hm_f2
  have hpost_goal := overExit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y
    s0 sf evs g' ans (LsTokenInit ∗ coinsPost ∗ anyHeap) hevs
    (hh.fs (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) 518) hsteps0f htr_sf hout
  exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm_f3

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env
)

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux (
  VerNeTopEnv
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  StageP2OverQpanCliFrozenPlacedStmt
)

private theorem stageP4Prev1Env_of_exitEnv_p6 {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b}
    {opsEnv : LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1StorePlacedBudget.StorePrev1BudgetEnv kit}
    {ikit : IdentityStoreSpec A b}
    {ikitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.IdentityStoreBudgetEnv ikit}
    {pkKit : PreKeyStoreSpec A b}
    {pkKitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget.PreKeyStoreBudgetEnv pkKit}
    {kpkKit : KyberPreKeyStoreSpec A b}
    {kpkKitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget.KyberPreKeyStoreBudgetEnv kpkKit}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {pst0 : pkKit.PkState} {kst0 : kpkKit.KpkState}
    {opkId? : Option (BitVec 32)}
    {rem : AddrVal} {remoteIk : IdentityKey}
    {kyberPreKeyId signedPreKeyId : BitVec 32} {baseKey : PublicKey}
    {G : SessionGhost} {ss : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {evs : List AllocEvent}
    (hevs : LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget.StageP4Prev1ExitEnv
      kit opsEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
      sst0 ist0 pst0 kst0 opkId? rem remoteIk kyberPreKeyId signedPreKeyId baseKey G ss enc evs) :
    StageP4Prev1Env kit ⟨opsEnv.storePollPrev1Env⟩ ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
      sst0 ist0 pst0 kst0 rem remoteIk kyberPreKeyId signedPreKeyId baseKey opkId? G ss enc evs := by
  cases opkId? with
  | none =>
    have hopt : OptRemoveStepEnv pkKit pkKitEnv pst0 none [] := rfl
    rcases hevs with hst | hmark | hsave
    · rcases hst with hs | ⟨_, _, rfl, hs, hm | ⟨_, _, rfl, hm, hstore⟩⟩
      · exact Or.inr (Or.inr (Or.inr (LibsignalBinary.Heap.SeqEnv.inl hs)))
      · exact Or.inr (Or.inr (Or.inr
          (LibsignalBinary.Heap.SeqEnv.append hs (LibsignalBinary.Heap.SeqEnv.inl hm))))
      · exact Or.inr (Or.inr (Or.inr
          (LibsignalBinary.Heap.SeqEnv.append hs
            (LibsignalBinary.Heap.SeqEnv.append hm
              (LibsignalBinary.Heap.SeqEnv.append hopt hstore)))))
    · exact Or.inr (Or.inl hmark)
    · exact Or.inl hsave
  | some opkId =>
    rcases hevs with hst | hrem | hmark | hsave
    · exact Or.inr (Or.inr (Or.inr hst))
    · exact Or.inr (Or.inr (Or.inl hrem))
    · exact Or.inr (Or.inl hmark)
    · exact Or.inl hsave

set_option maxHeartbeats 1200000 in
private theorem closure_pathC_frozen_placed_ok_at_priv [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hp4Envs : p4Envs = fun B F0 peer pid kpkId spkId kbk =>
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cSlotOkAtPlacedBudget.cliPollStageP4Prev1EnvsAt A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hP2O : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget.StageP2OverQpanCliMemInvPlacedAtXStmt
      (CryptoVerification.LibsignalFrozen lsmpl) A lim X mmpl g W P2OverErrEnv P2OverOkEnv)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.readFileSpecPlaced
        cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hTry0 : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (evs_p1 : List AllocEvent)
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hFits2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r))
    (hEnvErr2 : ∀ evs2, P2OverErrEnv y.g r evs2 → DecPkEnv y.g (evs_p1 ++ evs2))
    (hFits3 : ∀ evs2 m i k kp reg dk recG whisperG,
      P2OverOkEnv y.g r evs2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      FitsEnv M lim (M.stepEvents (evs_p1 ++ evs2) y.st)
        (StageP3Prev1Env (tdEnv W) VerNeTopEnv recG
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
          y.g.peer y.g.me whisperG y.g.msg.message
          (y.g.msg.message.messageVersion.zeroExtend 32)
          (E2E.Record.encSession (Over.clearPending s_old)) y.g.coins))
    (hEnvErr3 : ∀ evs2 evs3 m k (kp : RecordCodecs.IdentityKeyPair) reg dk recG G₁ whisperG,
      P2OverOkEnv y.g r evs2 →
      CloneRel recG G₁ →
      StageP3ErrEnv (tdEnv W) recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me whisperG y.g.msg.message y.g.coins evs3 →
      DecPkEnv y.g (evs_p1 ++ evs2 ++ evs3))
    (hEnvVerNe3 : ∀ evs2 evs3 m k (kp : RecordCodecs.IdentityKeyPair) reg dk recG,
      P2OverOkEnv y.g r evs2 →
      StageP3VerNePrev1Env VerNeTopEnv recG
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        (E2E.Record.encSession (Over.clearPending s_old)) evs3 →
      DecPkEnv y.g (evs_p1 ++ evs2 ++ evs3))
    (hFits4 : ∀ evs2 evs3 m i k kp reg dk recG G₁ G' pt whisperG,
      P2OverOkEnv y.g r evs2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv (tdEnv W) recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me whisperG y.g.msg.message y.g.coins evs3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      let σ := cliKitStk B
      let pid := pmPreKeyId y.g.msg
      let envs := p4Envs B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
      let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
      let ses' : Session (List (BitVec 8)) :=
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
          pendingPreKey := none
          pendingKyberPreKey := none }
      FitsEnv M lim (M.stepEvents (evs_p1 ++ evs2 ++ evs3) y.st)
        (StageP4Prev1Env
          (cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ) envs.opsEnv
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ) envs.ikitEnv
          (cliPollPkKitPlaced A.repAlloc y.g.F pid σ) envs.pkKitEnv
          (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ) envs.kpkKitEnv
          StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber
          y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey m.opkId G' ses'
          (E2E.Record.encSession (Over.clearPending s_old))))
    (hEnv4 : ∀ evs2 evs3 evs4 m i k kp reg dk recG G₁ G' pt whisperG,
      P2OverOkEnv y.g r evs2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv (tdEnv W) recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me whisperG y.g.msg.message y.g.coins evs3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      let σ := cliKitStk B
      let pid := pmPreKeyId y.g.msg
      let envs := p4Envs B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
      let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
      let ses' : Session (List (BitVec 8)) :=
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
          pendingPreKey := none
          pendingKyberPreKey := none }
      StageP4Prev1Env
        (cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ) envs.opsEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ) envs.ikitEnv
        (cliPollPkKitPlaced A.repAlloc y.g.F pid σ) envs.pkKitEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ) envs.kpkKitEnv
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey m.opkId G' ses'
        (E2E.Record.encSession (Over.clearPending s_old)) evs4 →
      DecPkEnv y.g (evs_p1 ++ evs2 ++ evs3 ++ evs4))
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok (some r)))
    (hcur : r.currentSession = some s_old)
    (hnot_match : ¬ SessMatchesPm s_old y.g.msg)
    (hsteps01 : Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s0 s1)
    (htr1 : s1.trace = s0.trace)
    (hfr1 : CryptoVerification.LibsignalFrozen lsmpl s1.mem)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x0868#64)
    (hrun1 : s1.status = .Running)
    (hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)) :
    let prog := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    let st_p1 := M.stepEvents evs_p1 y.st
    SepWPp prog (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim st_p1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).post
            y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).onPanic
            y s0 sf ∗ R)) := by
  subst hp4Envs
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let st_p1 := M.stepEvents evs_p1 y.st
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  have hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r) :=
    loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload_rel
  have hr_eq : r = ⟨some s_old⟩ := by cases r; simpa using hcur
  have hs_old : Slots.scopeIn ⟨some s_old⟩ := hr_eq ▸ hsub r (scope_of_loadRec_some hfPeer hloadS)
  have hver_old : s_old.state.sessionVersion = 4#32 := by
    have hv := hdecOk.sessVer4 r s_old hloadS hcur
    unfold SessionState.version at hv
    split at hv <;> simp_all
  have hprevOK : Over.OverPrevEncOK (E2E.Record.encSession (Over.clearPending s_old)) :=
    Over.overPrevEncOK_clearPending_of_scopeIn_placed hs_old hver_old
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  have hs1_files : s1.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed hh hsteps01 htr1).trans hf0
  have hfiles1 : FsAt (fun f => f = y.g.F) True
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 :=
    cliFsAt_of_files_eq_placed hh trivial rfl hs1_files
  let Fr_tail : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  have hpre_split :
      stageP2PostP1At (A.atState lim st_p1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      (stageP2PostP1At (A.atState lim st_p1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B)) ∗ Fr_tail := by
    dsimp only [Fr_tail]
    sep_frame
  refine sepWPp_conseq_pre hpre_split
    (overSepWPp_pollGoal_frame_placed A lim DecPkEnv B S stk' y ?_)
  refine hP2O B S Scope y st_p1 r s_old StoresGhost.opened s0 s1 sp rngPtr v_a8 v_b8 v_d0 _ _
    hh hFits2 hcoins hdecOk hsub hfPeer hloadS hcur hnot_match htrusted rfl
    hfiles1 hfr1 (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hsp_sub hpc1 hrun1 hsp_align1 hregs1 ?_ ?_
  · intro sf Pf _ _ _ hsf_sp hcs_f hvregs_f _ hErr
    rcases hErr with ⟨err, evs2, hevs2, hne_p, hne_s, htr_f, hmodel, hpost_f⟩
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left hpost_f) hm_f
    have hstep_eq : M.stepEvents evs2 st_p1 = M.stepEvents (evs_p1 ++ evs2) y.st :=
      (M.stepEvents_append evs_p1 evs2 y.st).symm
    rw [hstep_eq] at hm1
    have hm2 : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs2) y.st) sf ∗
          anyHeap ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by dsimp only [Fr_tail]; sep_frame) hm1
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_d2c_of_reject StoresGhost.opened hS hne_p hne_s hmodel
    have hpost_goal := overExit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y
      s0 sf (evs_p1 ++ evs2) StoresGhost.opened (.error err) anyHeap (hEnvErr2 evs2 hevs2)
      (hh.fs (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) 518) hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm2
  · intro s2 evs_p2 m i k kp reg dk recG prevCap prevPtr whisperMsgPtr whisperG preKeyMsgRem
      hevs2 hcap_nz hpm_eq hi hk hkp hreg hacc hex hmsg_fold hsteps12 htr2 hpc2 hrun2
      hs2_sp hsp_align2 _ _ hx29_2 hvregs2 hfr2
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st0 := pathAInitState ⟨W.C, W.Q⟩ meE k m dk
    let st_p2 := M.stepEvents (evs_p1 ++ evs_p2) y.st
    have hst_p2_eq : M.stepEvents evs_p2 st_p1 = st_p2 :=
      (M.stepEvents_append evs_p1 evs_p2 y.st).symm
    obtain ⟨_hIn0, hver4, hSeeds, hRC, hPqLt⟩ := pathAInitSession_scopeIn ⟨W.C, W.Q⟩ meE k m dk
    have hsteps02 := Steps.trans hsteps01 hsteps12
    have htr20 : s2.trace = s0.trace := htr2.trans htr1
    have hs2_files : s2.fs.files = y.g.F :=
      (cliFiles_eq_of_trace_eq_placed hh hsteps02 htr20).trans hf0
    have hpan_model : st0.version = y.g.msg.message.messageVersion.zeroExtend 32 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).1 = .error .panic →
        (dpSlotPollKStatePlaced A lim DecPkEnv B S).panics y.g := by
      intro hver hpan_s5
      show S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = none
      rw [hS]
      exact decPkDefD2c_pathC_panic X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver hpan_s5
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    have hpre_p3 :
        LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_p1) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG st0 y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         Over.stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (E2E.Record.encSession (Over.clearPending s_old)) 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
           (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
            ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗
         storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ⊢
        LsTokenInit ∗
         overGenP3Pre_placed A lim st_p2 s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
           whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG st0 y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         Over.stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (E2E.Record.encSession (Over.clearPending s_old)) 0#8 ∗
         Over.overScratch s2.sp ∗
         F_p3 := by
      rw [hst_p2_eq, stageP3StackFrameAt_eq_over sp (y.g.msgA + 0xc8#64) y.g.peerA, hs2_sp]
      dsimp only [F_p3, sp]
      sep_frame
    refine sepWPp_conseq_pre hpre_p3
      (overSepWPp_genP3_to_tailQpan_placed A lim DecPkEnv B S stk' y hpan_model ?_)
    refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudget.stageP3_prev1_full_placed_ok
      mmpl g W st_p2 hG
      hh.alloc (cliChainClone3_placed_ok mmpl g W hh) (cliSenderChainClone3_placed_ok mmpl g W hh)
      hTry0
      (cliDropSessionStructure4_placed_ok_at mmpl g W hh
        (callerProg := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 518))
      s0 s2 y.fut y.cx y.out 8#64 prevCap prevPtr y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8
      (E2E.Record.encSession (Over.clearPending s_old)) y.g.coins
      recG st0 y.g.peer y.g.me whisperG y.g.msg.message F_p3 _
      (hFits3 evs_p2 m i k kp reg dk recG whisperG hevs2 hpm_eq hi hk hkp hreg hacc hex)
      (by decide) hcap_nz hprevOK hver4
      (Or.inr (distinctSid_of_decPkOk₀ hdecOk.toDecPkOk₀_emptyScope)) hSeeds hRC hPqLt
      hfr2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot)
      (x29_eq_sp_add_c70_pathC_placed_p6 hx29_2 hs2_sp) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' evs_p3 pt ptCap ptPtr s' P_s' hver hcl hdec_rel hevs3 hok
        hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
        hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s'
      have hstep_p3_eq : M.stepEvents evs_p3 st_p2 = M.stepEvents (evs_p1 ++ evs_p2 ++ evs_p3) y.st :=
        (M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st).symm
      rw [hstep_p3_eq] at hent_s'
      have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c A.repAlloc σ
        y.g.stores hsub hfPeer hdecOk pid m.spkId m.kpkId y.g.msg.baseKey
      have hunpack_p3 : P_s' ∗ F_p3 ⊢
          P_s' ∗
          (stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
              (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
              (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
              (coroOpkIdAtP4 y.fut m.opkId)
              (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
                ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
            stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
            ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
            ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRem ∗
            kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
            ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
            (cliPollPkKitPlaced A.repAlloc y.g.F pid σ).storeAt
              (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
            (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ).storeAt
              (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
            (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt
              (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
            dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
            memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) := by
        dsimp only [F_p3]
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
        refine Entails.trans (sepConj_mono_left hstores_in) ?_
        dsimp only [cliPollStoresKitsAtPlaced]
        sep_frame
      exact sepWPp_conseq_pre hunpack_p3
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget.closure_pathC_p4_cont_placed_at_priv A lim DecPkEnv
          (ReadEnv := ReadEnv)
          (p4Envs := fun B F0 peer pid kpkId spkId kbk =>
            LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget.cliPollStageP4Prev1Envs A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv)
          hDropNz rfl
          (mmpl := mmpl) (gh := g) (W := W) (X := X)
          B S (Scope := Scope)
          (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.runHooks_to_stages hh)
          hReadFile hS stk' hneed hstk63 y
          (evs_p1 ++ evs_p2 ++ evs_p3)
          hfPeer hs_old hdecOk hloadS hcur htrusted hnot_match m i k kp reg dk recG G₁ G'
          rngPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem P_s' R pt s0 s2 s'
          ((hFits4 evs_p2 evs_p3 m i k kp reg dk recG G₁ G' pt whisperG
            hevs2 hpm_eq hi hk hkp hreg hacc hex hcl hdec_rel hevs3 hok).mono
            (fun _ he => stageP4Prev1Env_of_exitEnv_p6 he))
          (fun evs4 hevs4 =>
            hEnv4 evs_p2 evs_p3 evs4 m i k kp reg dk recG G₁ G' pt whisperG
              hevs2 hpm_eq hi hk hkp hreg hacc hex hcl hdec_rel hevs3 hok
              (stageP4Prev1Env_of_exitEnv_p6 hevs4))
          hpm_eq hi hk hkp hreg hacc hex hmsg_fold hs2_files htr20 hs2_sp hsp_align2 hsp_sub
          hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
          hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s')
    · intro G₁ _G' evs_p3 e sf P_f hver hcl _hdec_rel hevs3 herr hne_p hent_f
        hsf_sp htr_f hcs_f hvregs_f _hro_f
      have hstep_p3_eq : M.stepEvents evs_p3 st_p2 = M.stepEvents (evs_p1 ++ evs_p2 ++ evs_p3) y.st :=
        (M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st).symm
      rw [hstep_p3_eq] at hent_f
      have hent_any : P_f ⊢
          ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
          memRegion (s2.sp + 0x3e0#64) 344 ∗
          overStageP3ErrPostPrevEmptyAt_placed A lim (M.stepEvents (evs_p1 ++ evs_p2 ++ evs_p3) y.st)
            s0 s2 sf y.fut y.out e ∗
          overGenP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
            (Coins.coinsAfterPlaced y.g.coinsP y.g.coins
              (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins)) ∗
          Over.overScratch s2.sp ∗
          anyHeap := by
        refine Entails.trans hent_f ?_
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right
            (Entails.trans (Entails.of_eq (sepConj_emp (Over.overScratch s2.sp)).symm)
              (sepConj_mono_right (entails_anyHeap emp))))))
      exact stageP3_exit_pathC_to_pollPost_placed A lim DecPkEnv B S hh hS stk' hneed hstk63 y
        s0 s2 sf (evs_p1 ++ evs_p2 ++ evs_p3) rngPtr whisperMsgPtr whisperG preKeyMsgRem
        (Coins.coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins))
        P_f R m.opkId m.kpkId m.spkId e
        (hEnvErr3 evs_p2 evs_p3 m k kp reg dk recG G₁ whisperG hevs2 hcl hevs3)
        hs2_sp hsp_sub hmsg_fold
        (decPkDefD2c_pathC_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver herr hne_p)
        hent_any hsf_sp htr_f hcs_f hvregs_f
    · intro evs_p3 sf P_f hver_ne hevs3 hent_f hsf_sp htr_f hcs_f hvregs_f _hro_f
      have hstep_p3_eq : M.stepEvents evs_p3 st_p2 = M.stepEvents (evs_p1 ++ evs_p2 ++ evs_p3) y.st :=
        (M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st).symm
      rw [hstep_p3_eq] at hent_f
      exact stageP3_exit_pathC_to_pollPost_placed A lim DecPkEnv B S hh hS stk' hneed hstk63 y
        s0 s2 sf (evs_p1 ++ evs_p2 ++ evs_p3) rngPtr whisperMsgPtr whisperG preKeyMsgRem
        (Coins.coinsAtPlaced y.g.coinsP y.g.coins) P_f R m.opkId m.kpkId m.spkId
        (.invalidMessage .preKey .decryptionFailed)
        (hEnvVerNe3 evs_p2 evs_p3 m k kp reg dk recG hevs2 hevs3)
        hs2_sp hsp_sub hmsg_fold
        (decPkDefD2c_pathC_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver_ne)
        hent_f hsf_sp htr_f hcs_f hvregs_f

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget
end At3Wrap_p6

section At3Wrap_p7

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib

open CryptoGames.LibsignalSession (PublicKey SignalMessage)

open CryptoGames.LibsignalSessionApi (Session SessionRecord)

open CryptoVerification (LibsignalPlacement lsmpl lsρ)

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5Model)

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  SessionExtraRel sp_sub_cd0_align_std3 stageP1CallStack
)

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (clearPending)

open CryptoVerification.E2E (
  PreKeyMessageFields UnreachedPqxdhPrimitives acceptInput modelPrims
)

open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeyCoroInitAt)

open CryptoVerification.E2E.Record (encSession)

open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)

open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)

open CryptoVerification.LibsignalPublicApiRepr (preKeyMsgAt)

open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)

open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)

open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)

open CryptoVerification.RecordCodecs (IdentityKeyPair)

open CryptoVerification.RustHeap (RustAlloc)

open CryptoVerification.SignalSession (CliHooks)

open CryptoVerification.SignalSession.Cli (
  StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSignedPreKeyVtSym dirAt
)

open CryptoVerification.SignalSession.Cli.KitInst (
  cliKyberPreKeyStoreSpecPlaced cliPreKeyStoreSpecPlaced cliSignedPreKeyStoreSpecPlaced
)

open CryptoVerification.SignalSession.Cli.MainHops (cliIo coinsInstalledPlaced)

open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost RunSem dpPollNeed dpSlotArgsPlaced
)

open CryptoVerification.SignalSession.Cli.RunProofs (
  DecPkOk₀ SessMatchesPm decPkDef decPkDefD2c decPkDefD2c_eq_decPkDef_of_match
  decPkDefD2c_eq_decPkDef_of_noCurrent dpFutStartAt pkStoreKeys pmOfE
)

open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit StageP1PostRegs cliIdStoreSpecFullPlaced cliId_trustRel_eq_of_trusted
  cliKitStk cliKpkStoreSpecFullPlaced cliPollIdKit cliPollIdKitPlaced cliPollKpkKitPlaced
  cliPollPkKitPlaced cliPollSessKit cliPollSessKitPlaced cliPollSessPrev1KitPlaced
  cliPollSpkKitPlaced cliPollStoresKitsAtPlaced cliSess_loadRel_isOk closStackUnusedP1OkAt
  clos_stack_3280_split_for_p1_ok coroUnusedP1At
  currentSession_some_of_cliPollSessPlaced_loadRel dpClosSubStack
  dpFutStartAt_split_for_p1_placed dpPollNeed_eq_frame_add_subStack
  loadRec_of_cliPollSessPlaced_loadRel pathAInitSession pathAInitState pmKyberId pmPreKeyId
  preKeyMsgAt_eq_idKey_sep preKeyMsgRemIdKeyAt sepWPp_conseq_pre sepWPp_sepExists_left
  stageP1CallStack_le_subStack stageP1Ok_trace_eq_placed stackAt_poll_entry_split
  stackAt_subStack_split subStack_le_sp_of_dpPollNeed subroutine_ok_of_sepWPp_steps
  trusted_ok_of_filesOkPeer
)

open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)

open CryptoVerification.SignalSession.Cli.Slots (loadRec scopeKit)

open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget (
  StageP2MatchedEnv
)

open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget (
  OverCliTryDecryptPqV1PlacedStmt closure_pathC_placed_ok
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  CliStageP4Prev1Envs StageP2OverEnv StageP4Prev1Env
  storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlacedBudget (
  CliDpPollOkD2cStatePlacedAt CliDpPollOkD2cStatePlacedStmt D2cStagesPlacedStmt
  closure_untrusted_d2c_placed_ok dpPollPre_unpack_d2c_placed sepWPp_pollGoal_of_decPk_eq_placed
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget (
  dpPollEntrySpatialPlaced
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudgetAux (
  closure_pathA_placed_ok_at p1Ok_recombine_entails_stageP2_placed_budget sepWPp_bind_p1_noPanic
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget (
  closure_pathB_placed_ok
)

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env
)

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux (
  VerNeTopEnv
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  StageP3Env StageP3ErrEnv StageP3OkPrefixEnv StageP3VerNeEnv
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  StageP2PathAEnv
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget (
  CliDpPollTrustedEnv CliStageP1OkEnv PollBaseStagesPlacedStmt
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  cliPollStageP1_fsAt_placed runHooks_to_stages
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget (
  stageP1_ok_placed_inst
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv cliPollSessBudgetEnv
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpSlotPollKStatePlaced
)

open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudget (
  StageP2PathAQpanCliFrozenPlacedStmt closure_pathA_frozen_placed_ok
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget (
  StageP2MatchedFramedCliPlacedStmt closure_pathB_frozen_placed_ok
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  StageP3GenStepsVRegsFrozenPlacedStmt StageP3PrevEmptyVRegsFrozenPlacedStmt
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  StageP4MatchedPlacedStmt StageP4PathAPlacedStmt
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget (
  closure_pathC_frozen_placed_ok
)

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlacedBudget (
  CliDpPollOkD2cStateFrozenPlacedAt D2cStagesFrozenPlacedStmt DpPollEntryPureD2cFrozenPlaced
  closure_untrusted_d2c_frozen_placed_ok dpPollPre_unpack_d2c_frozen_placed
  sepWPp_pollGoal_of_decPk_eq_frozen_placed
)

set_option maxHeartbeats 1000000 in
private theorem closure_trusted_d2c_frozen_placed_at_priv [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hP2A : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudgetAux.StageP2PathAQpanCliFrozenPlacedAtStmt
      A lim ReadEnv X mmpl gh W B P2PathAErrEnv P2PathAOkEnv)
    (hP2Over : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget.StageP2OverQpanCliMemInvPlacedAtXStmt
      (CryptoVerification.LibsignalFrozen lsmpl) A lim X mmpl gh W P2OverErrEnv P2OverOkEnv)
    (hTry0 : subroutine_ok (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns gh
          (CryptoVerification.SignalSession.cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget.overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64
          CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse
          (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hp4Envs : p4Envs = fun B F0 peer pid kpkId spkId kbk =>
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cSlotOkAtPlacedBudget.cliPollStageP4Prev1EnvsAt A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv)
    (hEnv : ∀ g evs,
      CliDpPollD2cEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs) :
    CliDpPollOkD2cStateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope := by
  intro hh_skel hReadFile hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_d2c_frozen_placed (W := W) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre
  have hfits_all := hpure.fits.mono (hEnv y.g)
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    exact closure_untrusted_d2c_frozen_placed_ok A lim hDropNz mmpl gh W X B S Scope hh_skel hReadFile hDeser
      hinjK hsub hS stk' hneed' hstk63 y
      (hfits_all.mono fun _ h => Or.inl (Or.inl h))
      (fun evs h => hEnv y.g evs (Or.inl (Or.inl h)))
      R s0 hpc hrun hsp hpure.fr hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer
      hpure.decPkOk htrusted hm_base
  | true =>
    dsimp only
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    have hh := runHooks_to_stages hh_skel
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
    let kitEnv := cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer σ DeserEnv ReadEnv
    let ikitEnv := cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer σ ReadEnv
    let pkKitEnv := cliPollPkBudgetEnv A.repAlloc y.g.F pid σ ReadEnv
    let kpkKitEnv := fun kpkId spkId =>
      cliPollKpkBudgetEnv A.repAlloc y.g.F kpkId spkId kbk σ ReadEnv
    let sp := s0.sp - 0xcd0#64
    have hsp_align0 : (s0.sp &&& 15#64 == 0#64) = true := by
      simpa [State.spAligned] using hsp
    have hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat :=
      (subStack_le_sp_of_dpPollNeed hneed' hpure.stk_le_sp).1
    have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c A.repAlloc σ
      y.g.stores hsub hpure.filesOkPeer hpure.decPkOk pid sid kid kbk
    have hm_stores : s0.mem ⊨
        memRegion y.out 48 ∗
          dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
          memRegion y.cx 32 ∗
          cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
            pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          coinsInstalledPlaced y.g.coinsP y.g.coins ∗
          LsTokenInit ∗
          lsLogOff ∗
          A.pool lim y.st s0 ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          stackAt s0.sp stk' ∗
          R :=
      Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hent_stores)))) hm_base
    have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
      have := dpPollNeed_eq_frame_add_subStack B; omega
    have hp1_le := stageP1CallStack_le_subStack (A := A.repAlloc)
      0#64 y.g.F scopeKit y.g.peer B
    have hp1_64 : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
    rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
        preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
        stackAt_poll_entry_split s0.sp B stk' hneed' hstk63,
        stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64,
        clos_stack_3280_split_for_p1_ok s0.sp] at hm_stores
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
    rcases hm_stores with ⟨u_98, u_a0, u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
      b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
    rw [← ProofLib.memRegion_cells (y.fut + 0x250#64) 6 (by decide)] at hm_flat
    simp only [Nat.reduceMul] at hm_flat
    dsimp only [cliPollStoresKitsAtPlaced] at hm_flat
    let P_p1 : SepProp :=
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
      cells (y.fut + 0x70#64) 14 ∗
      cells (y.fut + 0xe0#64) 4 ∗
      memRegion (y.fut + 0x100#64) 336 ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      cells (y.fut + 0x2c8#64) 25 ∗
      ((y.fut + 0x390#64) ↦₈ b_390) ∗
      ((y.fut + 0x398#64) ↦₆₄ u_398) ∗
      ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗
      cells (y.fut + 0x428#64) 8 ∗
      cells (y.fut + 0x490#64) 4 ∗
      ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
      (sp ↦₆₄ v_sp0) ∗
      ((sp + 0x98#64) ↦₆₄ u_98) ∗
      ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
      ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
      ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
      ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
      ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
      ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
      ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x3e0#64) 368 ∗
      cells (s0.sp - 0x60#64) 12 ∗
      lsLogOff ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      A.pool lim y.st s0 ∗
      stackAt sp (stageP1CallStack kit ikit)
    let Fr_inner : SepProp :=
      memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗
      closStackUnusedP1OkAt sp ∗
      memRegion y.out 48 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP1CallStack kit ikit) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit
    have hm_split : s0.mem ⊨ (P_p1 ∗ Fr_inner) ∗ R :=
      Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
        cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
        cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced, cliPreKeyStoreSpecPlaced,
        cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
        cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
    refine ⟨P_p1 ∗ Fr_inner, R, hm_split, ?_⟩
    have hfits_p1 : FitsEnv M lim y.st (CliStageP1OkEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g) :=
      hfits_all.mono fun _ h => Or.inl (Or.inr (Or.inl h))
    have hwp := stageP1_ok_placed_inst hDropNz mmpl gh W B y.g.F y.g.peer y.g.msg.identityKey
      hh hReadFile hDeser y.st StoresGhost.opened.sessions StoresGhost.opened.identity
      hp1_64 rfl rfl
      (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
        StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
      (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
        StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
        cliId_trustRel_eq_of_trusted htrusted h)
      hfits_p1
      s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
      v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
      b_390 b_4f2
      hpure.ro
      (cliPollStageP1_fsAt_placed hh_skel y.g.F scopeKit y.g.peer B hpure.files_eq)
      hpc hrun hsp_align0 rfl hpure.x0 hpure.x1 hpure.x2
    refine sepWPp_bind_p1_noPanic hwp rfl ?_
    intro s1 P_1 hsteps01 hpc1 hrun1 hq1
    rcases hq1 with ⟨⟨opt, evs_p1, hevs_p1, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
      hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
      hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, _hro1⟩
    have hfr1 : CryptoVerification.LibsignalFrozen lsmpl s1.mem :=
      CryptoVerification.libsignalFrozen_of_keepsFrozen hpure.fr hsteps01.keepsFrozen
    have htr1 : s1.trace = s0.trace := stageP1Ok_trace_eq_placed htr_evs
    have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true :=
      hs1_sp ▸ sp_sub_cd0_align_std3 hsp_align0
    have hregs1 : StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64)
        (lsρ cliKyberPreKeyVtSym) :=
      ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
       hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1⟩
    refine sepWPp_conseq_pre (sepConj_mono_left hent_1) ?_
    simp only [sepExists_sepConj_left]
    refine sepWPp_sepExists_left fun v_a8 =>
      sepWPp_sepExists_left fun v_b8 =>
      sepWPp_sepExists_left fun v_d0 => ?_
    have hrecomb := p1Ok_recombine_entails_stageP2_placed_budget stk' hneed' hstk63 y
      (M.stepEvents evs_p1 y.st) s0 s1 coins v_a8 v_b8 v_d0 opt
    dsimp only at hrecomb
    refine sepWPp_conseq_pre hrecomb ?_
    let S0 : RunSem := { S with decryptPrekey := decPkDef X ⟨W.C, W.Q⟩ Scope }
    let y0 : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S0) :=
      ⟨y.out, y.fut, y.cx, y.g, y.st⟩
    cases opt with
    | none =>
      have hloadNone : loadRec Scope y.g.F y.g.peer.val = .ok none :=
        loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hpure.filesOkPeer hload_rel
      have hnone : ∀ r', loadRec Scope y.g.F y.g.peer.val = .ok (some r') →
          r'.currentSession = none := by
        intro r' hr'; rw [hloadNone] at hr'; cases hr'
      have hdecOk0 : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg :=
        hpure.decPkOk.toDecPkOk₀_of_noCurrent hnone
      have hEq : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
          S0.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins := by
        dsimp only [S0]
        rw [hS]
        exact decPkDefD2c_eq_decPkDef_of_noCurrent X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val
          y.g.me.val y.g.msg y.g.coins hnone
      refine sepWPp_pollGoal_of_decPk_eq_frozen_placed stk' y s0 s1 _ R hEq ?_
      have hfits_p2 :
          FitsEnv M lim (M.stepEvents evs_p1 y.st)
            (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv y.g) :=
        (hfits_all.mono fun _ h =>
          Or.inl (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inl h⟩)))).seq_right hevs_p1
      have hevs_p2_err : ∀ evs_p2, P2PathAErrEnv y.g evs_p2 → DecPkEnv y.g (evs_p1 ++ evs_p2) :=
        fun evs_p2 he2 =>
          hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inl
            ⟨hload_rel, Or.inl (SeqEnv.append hevs_p1 (Or.inl he2))⟩))))
      refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudgetAux.closure_pathA_frozen_placed_ok_at_priv mmpl gh W X B S0 Scope
        (fun {_DecPkEnv _DeserEnv _st_b} => hP2A)
        hDropNz hG hh hReadFile hDeser hTry0
        hinjK hsub rfl stk' hneed' hstk63 y0 kitEnv ikitEnv pkKitEnv kpkKitEnv
        rfl rfl rfl (fun _ _ => rfl) evs_p1 s0 s1 coins
        v_a8 v_b8 v_d0 R hpure.files_eq hpure.filesOkPeer hdecOk0 hpure.coins_lt htrusted
        hload_rel hfits_p2 hevs_p2_err
        ?_ ?_ ?_ ?_ ?_ ?_
        hsteps01 htr1 hfr1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
      · intro evs_p2 m i k kp reg dk recG he2 hpm hi hk hkp hreg hacc hex
        exact (hfits_all.mono fun _ h =>
          Or.inl (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
            hpm, hi, hk, hkp, hreg, hacc, hex, Or.inl h⟩⟩)))).seq_right
          (SeqEnv.append hevs_p1 he2)
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt he2 hpm hi hk hkp hreg hacc hex
          hver hcl hdec he3 hok
        exact (hfits_all.mono fun _ h =>
          Or.inl (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
            hpm, hi, hk, hkp, hreg, hacc, hex,
            Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok, h⟩⟩⟩)))).seq_right
          (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4 he2 hpm hi hk hkp hreg hacc hex
          hver hcl hdec he3 hok he4
        exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk,
          recG, hpm, hi, hk, hkp, hreg, hacc, hex,
          Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok,
            SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
              (Or.inr (Or.inr (Or.inr he4)))⟩⟩⟩))))
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4 he2 hpm hi hk hkp hreg hacc hex
          hver hcl hdec he3 hok he4
        exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk,
          recG, hpm, hi, hk, hkp, hreg, hacc, hex,
          Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok,
            SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
              (Or.inr (Or.inl he4))⟩⟩⟩))))
      · intro evs_p2 m i k kp reg dk recG G₁ _G' evs_p3 _e he2 hpm hi hk hkp hreg hacc hex
          hver hcl _hdec he3 _herr _hne
        have he3_env : StageP3Env (tdEnv W) recG
            (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
          dsimp only [y0, dpSlotPollKStatePlaced] at hver
          unfold StageP3Env
          simp only [hver, ↓reduceIte]
          exact ⟨G₁, hcl, he3⟩
        exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk,
          recG, hpm, hi, hk, hkp, hreg, hacc, hex,
          Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩))))
      · intro evs_p2 m i k kp reg dk recG evs_p3 he2 hpm hi hk hkp hreg hacc hex hver_ne he3
        have he3_env : StageP3Env (tdEnv W) recG
            (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
          dsimp only [y0, dpSlotPollKStatePlaced] at hver_ne
          unfold StageP3Env
          simp only [hver_ne, ↓reduceIte]
          exact he3
        exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk,
          recG, hpm, hi, hk, hkp, hreg, hacc, hex,
          Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩))))
    | some r =>
      obtain ⟨sess, hcur⟩ := currentSession_some_of_cliPollSessPlaced_loadRel hload_rel
      have hloadSome : loadRec Scope y.g.F y.g.peer.val = .ok (some r) :=
        loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hpure.filesOkPeer hload_rel
      rcases Classical.em (SessMatchesPm sess y.g.msg) with hmatch | hnot_match
      · have hdecOk0 : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg :=
          hpure.decPkOk.toDecPkOk₀_of_match hloadSome hcur hmatch
        have hEq : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
            S0.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins := by
          dsimp only [S0]
          rw [hS]
          exact decPkDefD2c_eq_decPkDef_of_match X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val
            y.g.me.val y.g.msg y.g.coins hloadSome hcur hmatch
        refine sepWPp_pollGoal_of_decPk_eq_frozen_placed stk' y s0 s1 _ R hEq ?_
        have hfits_p2 :
            FitsEnv M lim (M.stepEvents evs_p1 y.st)
              (StageP2MatchedEnv sess y.g.msg.identityKey) :=
          (hfits_all.mono fun _ h =>
            Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur, Or.inl h⟩)))).seq_right
            hevs_p1
        refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget.closure_pathB_frozen_placed_ok_at_priv
          mmpl gh W hDropNz hG X B S0 Scope hh hReadFile hDeser hTry0 hinjK hsub rfl
          stk' hneed' hstk63 y0 kitEnv ikitEnv rfl rfl evs_p1 r sess s0 s1 coins v_a8 v_b8 v_d0 R
          hpure.files_eq hpure.filesOkPeer hdecOk0 hpure.coins_lt htrusted hload_rel hcur hfits_p2
          ?_ ?_ ?_ ?_ ?_ ?_
          hsteps01 htr1 hfr1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
        · intro hne evs_p2 he2
          have he2_env : StageP2MatchedEnv sess y.g.msg.identityKey evs_p2 := by
            dsimp only [y0, dpSlotPollKStatePlaced] at hne
            unfold StageP2MatchedEnv
            simp only [hne, ↓reduceIte]
            exact he2
          exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inr
            ⟨r, sess, hload_rel, hcur, Or.inl (SeqEnv.append hevs_p1 he2_env)⟩))))
        · intro hrem evs_p2 recG he2 hex
          exact (hfits_all.mono fun _ h =>
            Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
              Or.inr ⟨hrem, recG, hex, Or.inl h⟩⟩)))).seq_right (SeqEnv.append hevs_p1 he2)
        · intro hrem hver evs_p2 recG G₁ G' evs_p3 pt he2 hex hcl hdec he3 hok
          exact (hfits_all.mono fun _ h =>
            Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
              Or.inr ⟨hrem, recG, hex, Or.inr ⟨hver, G₁, G', pt, hcl, hdec, hok, h⟩⟩⟩)))).seq_right
            (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
        · intro hrem hver evs_p2 recG G₁ G' evs_p3 pt evs_p4 he2 hex hcl hdec he3 hok he4
          exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
            Or.inr ⟨hrem, recG, hex, Or.inr ⟨hver, G₁, G', pt, hcl, hdec, hok,
              SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3) (Or.inr he4)⟩⟩⟩))))
        · intro hrem hver evs_p2 recG G₁ _G' evs_p3 _e he2 hex hcl _hdec he3 _herr _hne
          have he3_env : StageP3Env (tdEnv W) recG sess.state y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
            dsimp only [y0, dpSlotPollKStatePlaced] at hver
            unfold StageP3Env
            simp only [hver, ↓reduceIte]
            exact ⟨G₁, hcl, he3⟩
          exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
            Or.inr ⟨hrem, recG, hex,
              Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩))))
        · intro hrem hver_ne evs_p2 recG evs_p3 he2 hex he3
          have he3_env : StageP3Env (tdEnv W) recG sess.state y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
            dsimp only [y0, dpSlotPollKStatePlaced] at hver_ne
            unfold StageP3Env
            simp only [hver_ne, ↓reduceIte]
            exact he3
          exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
            Or.inr ⟨hrem, recG, hex,
              Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩))))
      · refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget.closure_pathC_frozen_placed_ok_at_priv A lim DecPkEnv
          (ReadEnv := ReadEnv) (p4Envs := p4Envs)
          hDropNz hp4Envs
          mmpl gh W hG X B S Scope hP2Over hh_skel hReadFile hTry0 hinjK hsub hS stk' hneed' hstk63 y evs_p1 r sess
          s0 s1 coins v_a8 v_b8 v_d0 R
          ((hfits_all.mono fun _ h =>
            Or.inr ⟨r, sess, hload_rel, hcur, hnot_match, Or.inl h⟩).seq_right hevs_p1)
          (fun evs2 he2 =>
            hEnv y.g _ (Or.inr ⟨r, sess, hload_rel, hcur, hnot_match,
              Or.inl (SeqEnv.append hevs_p1 (Or.inl he2))⟩))
          ?_ ?_ ?_ ?_ ?_
          hpure.files_eq hpure.filesOkPeer hpure.decPkOk hpure.coins_lt htrusted
          hload_rel hcur hnot_match
          hsteps01 htr1 hfr1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
        · intro evs2 m i k kp reg dk recG whisperG he2 hpm hi hk hkp hreg hacc hex
          exact (hfits_all.mono fun _ h =>
            Or.inr ⟨r, sess, hload_rel, hcur, hnot_match,
              Or.inr (Or.inl ⟨m, i, k, kp, reg, dk, recG, whisperG,
                hpm, hi, hk, hkp, hreg, hacc, hex, h⟩)⟩).seq_right
            (SeqEnv.append hevs_p1 he2)
        · intro evs2 evs3 m k kp reg dk recG G₁ whisperG he2 hcl he3
          exact hEnv y.g _ (Or.inr ⟨r, sess, hload_rel, hcur, hnot_match,
            Or.inr (Or.inr (Or.inl ⟨m, k, kp, reg, dk, recG, G₁, whisperG, hcl,
              SeqEnv.append (SeqEnv.append hevs_p1 he2) he3⟩))⟩)
        · intro evs2 evs3 m k kp reg dk recG he2 he3
          exact hEnv y.g _ (Or.inr ⟨r, sess, hload_rel, hcur, hnot_match,
            Or.inr (Or.inr (Or.inr (Or.inl ⟨m, k, kp, reg, dk, recG,
              SeqEnv.append (SeqEnv.append hevs_p1 he2) he3⟩)))⟩)
        · intro evs2 evs3 m i k kp reg dk recG G₁ G' pt whisperG
            he2 hpm hi hk hkp hreg hacc hex hcl hdec he3 hok
          exact (hfits_all.mono fun _ h =>
            Or.inr ⟨r, sess, hload_rel, hcur, hnot_match,
              Or.inr (Or.inr (Or.inr (Or.inr
                ⟨m, i, k, kp, reg, dk, recG, G₁, G', pt, whisperG,
                  hpm, hi, hk, hkp, hreg, hacc, hex, hcl, hdec, hok, h⟩)))⟩).seq_right
            (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
        · intro evs2 evs3 evs4 m i k kp reg dk recG G₁ G' pt whisperG
            he2 hpm hi hk hkp hreg hacc hex hcl hdec he3 hok _σ _pid _envs _st0 _ses' he4
          exact hEnv y.g _ (Or.inr ⟨r, sess, hload_rel, hcur, hnot_match,
            Or.inr (Or.inr (Or.inr (Or.inr
              ⟨m, i, k, kp, reg, dk, recG, G₁, G', pt, whisperG,
                hpm, hi, hk, hkp, hreg, hacc, hex, hcl, hdec, hok,
                SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3) he4⟩)))⟩)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPlacedBudget
end At3Wrap_p7

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cSlotOkAtPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalFullPlacement LibsignalPlacement lsmpl lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (stageP1ProgPlaced)
open CryptoVerification.E2E (
  UnreachedPqxdhPrimitives aesDecHookMallocng fmtWriteHook0 formatInnerHook0 modelPrims
)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced cliHookTablePlaced
  lsFmtWriteSym lsFormatInnerSym lsReadFileSym
  lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli
  lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other withPanics_cliGhostExterns
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (cliKitStk dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  fmtWrite_row_placed formatInner_row_placed scopeKit
)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fmtWriteHook0_budget_ok formatInnerHook0_budget_ok)
open LibsignalBinary.Heap.SpecBudget (
  FmtWriteEnv FormatInnerEnv aesDecBudgetSpec fmtWriteBudgetSpec formatInnerBudgetSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (
  TryDecryptCliEnv TryDecryptCliEnvOf
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (EncodeRawPreallocPlacedOkX)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget (
  cliPollStageP4Prev1Envs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget (
  overPollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  CliStageP4Prev1Envs StageP2OverEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPlacedBudget (
  CliDpPollD2cEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  CliPollStageP2Envs P2OverPathCErrEnvOf P2OverPathCOkEnvOf
  PromoteOverArchiveCanonSessEnv PromoteOverCanonSessEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.TryDecryptStmtOfSpqrPlacedBudget (
  overPollTryDecrypt_placed_at_of_spqr overPollTryDecrypt_placed_at_of_tdEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.WrapperOverPlacedBudget (
  DecPkD2cSlotOkFrozenPlacedAt OverDecPkD2cSlotOkFrozenPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliP2PathAOptFieldsErrEnv cliP2PathAOptFieldsOkEnv cliStageP2KitEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (
  SpqrRecvBytesEnv SpqrV1PlacedSeams SpqrV1PlacedSeamsOfEnv spqrRecvBytesEnv_nonempty
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

private theorem cliGrowOneVecU8_lsProg51_withLsCl_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (CryptoVerification.lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621)
      (CryptoVerification.withLsCl lsmpl
        (LibsignalBinary.Heap.RustStdAllocBudgetBridge.growOneVecU8BudgetSpec M A lim)) :=
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
        (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_shim gh _).trans
          (congrArg some hG.shim_eq),
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShim_hookOk⟩ :
        HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsRustNoAllocShimSymCli
          LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimSpec))
    ((show lsRustAllocSymCli = CryptoVerification.SpqrV1.Alloc.spqrRustAllocSym by decide) ▸
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliExternsPlaced_alloc_budget_sat
        mmpl gh W hG)
    ((show lsRustReallocSymCli = CryptoVerification.SpqrV1.Alloc.spqrRustReallocSym by decide) ▸
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliExternsPlaced_realloc_budget_sat
        mmpl gh W hG)

private theorem decPkD2cSlotOk_at_X_of_p2Over [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ B : RunBudgets,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hTry : ∀ ctl : BitVec 64,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 508)
        (withLsCodeRoLoaded lsmpl
          (overPollTryDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse
            (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hP2Over :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget.StageP2OverQpanCliMemInvPlacedAtXStmt
        (CryptoVerification.LibsignalFrozen lsmpl) A lim X mmpl gh W P2OverErrEnv P2OverOkEnv)
    (hEnv : ∀ g evs,
      CliDpPollD2cEnv (A := A.repAlloc) W X cliRunBudgets ReadEnv DeserEnv
        (cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        (cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        P2OverErrEnv P2OverOkEnv tdEnv
        (fun B F0 peer pid kpkId spkId kbk =>
          cliPollStageP4Prev1EnvsAt A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv)
        g evs →
      DecPkEnv g evs) :
    DecPkD2cSlotOkFrozenPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W)) X W A lim
      DecPkEnv := by
  intro S needs sEnvs hsDec hfiles hdec hdecOk hneed
  rw [hsDec]
  have hEq := dpPollProgPlaced_helpers_eq_poll mmpl gh W
  exact LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.WrapperOverPlacedBudget.cliDecryptPrekey_slotOk_d2c_of_pollAt_full_placed
    (prog := CryptoVerification.SignalSession.Cli.Run.Placed.lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
    A lim ReadEnv DeserEnv DecPkEnv mmpl gh W (by decide)
    X cliRunBudgets S CryptoVerification.SignalSession.Cli.Slots.scopeIn needs
    hh (hEq.symm ▸ hRead cliRunBudgets) (hEq.symm ▸ hDeser)
    CryptoVerification.SignalSession.Cli.Slots.encodeInjOn_deserializeScopeP_Q
    (fun _ h => h) hdec
    (fun _ _ _ _ hf hd => ⟨(hfiles ▸ hf).1, hdecOk ▸ hd⟩)
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPlacedBudget.closure_trusted_d2c_frozen_placed_at_priv hDropNz mmpl gh hG W X cliRunBudgets S
      CryptoVerification.SignalSession.Cli.Slots.scopeIn
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.stageP2PathA_qpan_cli_full_placed_at_ok
        A lim (ReadEnv := ReadEnv) X mmpl gh W cliRunBudgets
        (senv := fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv)
        hDropNz hG hSpqr
        (fun F0 peer hh_sk hReadB =>
          LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget.cliPollSelf_kitPlacedOk_stagesHooks
            mmpl gh W cliRunBudgets F0 peer hDropNz hh_sk hReadB))
      hP2Over (hTry 0#64) rfl hEnv)
    hneed

/-! ## 2. Block-`507` `hTry`-Parametric Pointwise Dischargers (`_of_tryDec`) -/

/-- Fixed-`(mmpl, gh, W, X)` `DecPkD2cSlotOkFrozenPlacedAt` discharger at `PromoteOverCanonSessEnv`,
parametric in `ReadEnv`, `DeserEnv`, `P2OverErrEnv`, `P2OverOkEnv`, `tdEnv`, and `DecPkEnv`, with
zero universal-`mmpl` premises. -/
theorem decPkD2cSlotOk_full_placed_at_X_of_tryDec [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ B : RunBudgets,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hTry : ∀ ctl : BitVec 64,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 508)
        (withLsCodeRoLoaded lsmpl
          (overPollTryDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse
            (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hErrEnv : ∀ B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          g r))
    (hEnv : ∀ g evs,
      CliDpPollD2cEnv (A := A.repAlloc) W X cliRunBudgets ReadEnv DeserEnv
        (cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        (cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        P2OverErrEnv P2OverOkEnv tdEnv
        (fun B F0 peer pid kpkId spkId kbk =>
          cliPollStageP4Prev1EnvsAt A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv)
        g evs →
      DecPkEnv g evs) :
    DecPkD2cSlotOkFrozenPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W)) X W A lim
      DecPkEnv := by
  exact decPkD2cSlotOk_at_X_of_p2Over mmpl gh W X hDropNz hG hh hRead hDeser hSpqr hTry
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget.stageP2Over_qpan_cli_full_placed_at_of_pathC
      (fun B =>
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget.stageP2PathCOver_qpan_cli_full_placed_at_of_seams
          A lim X mmpl gh W B (kitEnvs := cliP2KitEnvsAt A.repAlloc ReadEnv B)
          (hErrEnv B) (hOkEnv B) (hFitsSplit B) hDropNz hG hSpqr
          (fun F0 peer _ _ _ _ hh_sk =>
            LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget.cliPollSelf_kitPlacedOk_stagesHooks
              mmpl gh W B F0 peer hDropNz hh_sk (hRead B))
          (fun F0 _ spkId _ _ _ hh_sk =>
            LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollSpk_kitPlacedOk
              mmpl gh W B F0 spkId hDropNz hh_sk (hRead B))
          (fun F0 _ spkId kpkId _ kbk hh_sk =>
            LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollKpk_kitPlacedOk
              mmpl gh W B F0 kpkId spkId kbk hDropNz hh_sk (hRead B))
          (fun F0 _ _ _ opkWord _ hh_sk =>
            LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollPk_kitPlacedOk
              mmpl gh W B F0 opkWord hDropNz hh_sk (hRead B)))
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget.cliPromoteMatchingMissGen_placed_ok
        A.repAlloc mmpl gh W)
      (fun hh_sk =>
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget.cliPromoteOverGen_placed_ok
          mmpl gh W hh_sk (cliGrowOneVecU8_lsProg51_withLsCl_ok mmpl gh W hG) hRaw))
    hEnv

/-- Fixed-`(mmpl, gh, W, X)` `DecPkD2cSlotOkFrozenPlacedAt` discharger at tight
`PromoteOverArchiveCanonSessEnv` (`ArchiveCoreEnv`), with zero universal-`mmpl` premises. -/
theorem decPkD2cSlotOk_full_placed_at_X_archive_of_tryDec [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ B : RunBudgets,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hTry : ∀ ctl : BitVec 64,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 508)
        (withLsCodeRoLoaded lsmpl
          (overPollTryDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse
            (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hErrEnv : ∀ B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          g r))
    (hEnv : ∀ g evs,
      CliDpPollD2cEnv (A := A.repAlloc) W X cliRunBudgets ReadEnv DeserEnv
        (cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        (cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        P2OverErrEnv P2OverOkEnv tdEnv
        (fun B F0 peer pid kpkId spkId kbk =>
          cliPollStageP4Prev1EnvsAt A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv)
        g evs →
      DecPkEnv g evs) :
    DecPkD2cSlotOkFrozenPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W)) X W A lim
      DecPkEnv := by
  exact decPkD2cSlotOk_at_X_of_p2Over mmpl gh W X hDropNz hG hh hRead hDeser hSpqr hTry
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget.stageP2Over_qpan_cli_full_placed_at_of_pathC
      (fun B =>
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget.stageP2PathCOver_qpan_cli_archive_full_placed_at_of_seams
          A lim X mmpl gh W B (kitEnvs := cliP2KitEnvsAt A.repAlloc ReadEnv B)
          (hErrEnv B) (hOkEnv B) (hFitsSplit B) hDropNz hG hSpqr
          (fun F0 peer _ _ _ _ hh_sk =>
            LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget.cliPollSelf_kitPlacedOk_stagesHooks
              mmpl gh W B F0 peer hDropNz hh_sk (hRead B))
          (fun F0 _ spkId _ _ _ hh_sk =>
            LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollSpk_kitPlacedOk
              mmpl gh W B F0 spkId hDropNz hh_sk (hRead B))
          (fun F0 _ spkId kpkId _ kbk hh_sk =>
            LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollKpk_kitPlacedOk
              mmpl gh W B F0 kpkId spkId kbk hDropNz hh_sk (hRead B))
          (fun F0 _ _ _ opkWord _ hh_sk =>
            LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollPk_kitPlacedOk
              mmpl gh W B F0 opkWord hDropNz hh_sk (hRead B)))
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget.cliPromoteMatchingMissGen_placed_ok
        A.repAlloc mmpl gh W)
      (fun hh_sk =>
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget.cliPromoteOverGen_archive_placed_ok
          mmpl gh W hh_sk (cliGrowOneVecU8_lsProg51_withLsCl_ok mmpl gh W hG) hRaw))
    hEnv

/-- `∀ X`-packaged `OverDecPkD2cSlotOkFrozenPlaced` discharger from Block-`507` `hTry` at
`PromoteOverCanonSessEnv`. -/
theorem decPkD2cSlotOk_full_placed_at_of_tryDec [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ B : RunBudgets,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hTry : ∀ ctl : BitVec 64,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 508)
        (withLsCodeRoLoaded lsmpl
          (overPollTryDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse
            (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hErrEnv : ∀ X B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          g r))
    (hEnv : ∀ X g evs,
      CliDpPollD2cEnv (A := A.repAlloc) W X cliRunBudgets ReadEnv DeserEnv
        (cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        (cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        P2OverErrEnv P2OverOkEnv tdEnv
        (fun B F0 peer pid kpkId spkId kbk =>
          cliPollStageP4Prev1EnvsAt A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv)
        g evs →
      DecPkEnv g evs) :
    OverDecPkD2cSlotOkFrozenPlaced mmpl gh W A lim DecPkEnv :=
  fun X =>
    decPkD2cSlotOk_full_placed_at_X_of_tryDec mmpl gh W X hDropNz hG hh hRead hDeser hSpqr hRaw
      hTry (hErrEnv X) (hOkEnv X) (hFitsSplit X) (hEnv X)

/-- `∀ X`-packaged `OverDecPkD2cSlotOkFrozenPlaced` discharger from Block-`507` `hTry` at tight
`PromoteOverArchiveCanonSessEnv` (`ArchiveCoreEnv`). -/
theorem decPkD2cSlotOk_full_placed_at_archive_of_tryDec [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ B : RunBudgets,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hTry : ∀ ctl : BitVec 64,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 508)
        (withLsCodeRoLoaded lsmpl
          (overPollTryDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse
            (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hErrEnv : ∀ X B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          g r))
    (hEnv : ∀ X g evs,
      CliDpPollD2cEnv (A := A.repAlloc) W X cliRunBudgets ReadEnv DeserEnv
        (cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        (cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        P2OverErrEnv P2OverOkEnv tdEnv
        (fun B F0 peer pid kpkId spkId kbk =>
          cliPollStageP4Prev1EnvsAt A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv)
        g evs →
      DecPkEnv g evs) :
    OverDecPkD2cSlotOkFrozenPlaced mmpl gh W A lim DecPkEnv :=
  fun X =>
    decPkD2cSlotOk_full_placed_at_X_archive_of_tryDec mmpl gh W X hDropNz hG hh hRead hDeser hSpqr
      hRaw hTry (hErrEnv X) (hOkEnv X) (hFitsSplit X) (hEnv X)

/-! ## 3. Primary `SpqrV1PlacedSeams` + Parametric `tdEnv` Dischargers (`_of_seams` & `_of_spqr`) -/

/-- Primary pointwise discharger: proves `OverDecPkD2cSlotOkFrozenPlaced mmpl gh W A lim DecPkEnv`
(`rfl`-equal to `DecPkD2cSlotOkFrozenPlaced`) at fixed `(mmpl, gh, W)` with no universal-`mmpl`
premises, parametric in `ReadEnv`, `tdEnv`, and `DecPkEnv`. -/
theorem decPkD2cSlotOk_full_placed_at_of_seams [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ B : RunBudgets,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hSpqrTd : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv W a evs := by intros _ _ h; exact h)
    (hErrEnv : ∀ X B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          g r))
    (hEnv : ∀ X g evs,
      CliDpPollD2cEnv (A := A.repAlloc) W X cliRunBudgets ReadEnv DeserEnv
        (cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        (cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        P2OverErrEnv P2OverOkEnv tdEnv
        (fun B F0 peer pid kpkId spkId kbk =>
          cliPollStageP4Prev1EnvsAt A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv)
        g evs →
      DecPkEnv g evs) :
    OverDecPkD2cSlotOkFrozenPlaced mmpl gh W A lim DecPkEnv :=
  decPkD2cSlotOk_full_placed_at_of_tryDec mmpl gh W hDropNz hG hh hRead hDeser hSpqr hRaw
    (fun ctl =>
      overPollTryDecrypt_placed_at_of_tdEnv mmpl gh W ctl hG hAesDec hSpqrTd
        (cliFmtWrite_budget_sat mmpl gh W) (cliFormatInner_budget_sat mmpl gh W)
        hRecv_ne fmtWriteEnv_nonempty formatInnerEnv_nonempty htd)
    hErrEnv hOkEnv hFitsSplit hEnv

/-- Fixed-`X` companion to `decPkD2cSlotOk_full_placed_at_of_seams` (`DecPkD2cSlotOkFrozenPlacedAt`). -/
theorem decPkD2cSlotOk_full_placed_at_X_of_seams [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ B : RunBudgets,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hSpqrTd : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv W a evs := by intros _ _ h; exact h)
    (hErrEnv : ∀ B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          g r))
    (hEnv : ∀ g evs,
      CliDpPollD2cEnv (A := A.repAlloc) W X cliRunBudgets ReadEnv DeserEnv
        (cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        (cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        P2OverErrEnv P2OverOkEnv tdEnv
        (fun B F0 peer pid kpkId spkId kbk =>
          cliPollStageP4Prev1EnvsAt A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv)
        g evs →
      DecPkEnv g evs) :
    DecPkD2cSlotOkFrozenPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W)) X W A lim
      DecPkEnv :=
  decPkD2cSlotOk_full_placed_at_X_of_tryDec mmpl gh W X hDropNz hG hh hRead hDeser hSpqr hRaw
    (fun ctl =>
      overPollTryDecrypt_placed_at_of_tdEnv mmpl gh W ctl hG hAesDec hSpqrTd
        (cliFmtWrite_budget_sat mmpl gh W) (cliFormatInner_budget_sat mmpl gh W)
        hRecv_ne fmtWriteEnv_nonempty formatInnerEnv_nonempty htd)
    hErrEnv hOkEnv hFitsSplit hEnv

/-- Tight `PromoteOverArchiveCanonSessEnv` (`ArchiveCoreEnv`) companion to
`decPkD2cSlotOk_full_placed_at_of_seams`, parametric in `ReadEnv`, `tdEnv`, and `DecPkEnv`. -/
theorem decPkD2cSlotOk_full_placed_at_archive_of_seams [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ B : RunBudgets,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hSpqrTd : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv W a evs := by intros _ _ h; exact h)
    (hErrEnv : ∀ X B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          g r))
    (hEnv : ∀ X g evs,
      CliDpPollD2cEnv (A := A.repAlloc) W X cliRunBudgets ReadEnv DeserEnv
        (cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        (cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        P2OverErrEnv P2OverOkEnv tdEnv
        (fun B F0 peer pid kpkId spkId kbk =>
          cliPollStageP4Prev1EnvsAt A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv)
        g evs →
      DecPkEnv g evs) :
    OverDecPkD2cSlotOkFrozenPlaced mmpl gh W A lim DecPkEnv :=
  decPkD2cSlotOk_full_placed_at_archive_of_tryDec mmpl gh W hDropNz hG hh hRead hDeser hSpqr hRaw
    (fun ctl =>
      overPollTryDecrypt_placed_at_of_tdEnv mmpl gh W ctl hG hAesDec hSpqrTd
        (cliFmtWrite_budget_sat mmpl gh W) (cliFormatInner_budget_sat mmpl gh W)
        hRecv_ne fmtWriteEnv_nonempty formatInnerEnv_nonempty htd)
    hErrEnv hOkEnv hFitsSplit hEnv

/-- Fixed-`X` tight `PromoteOverArchiveCanonSessEnv` (`ArchiveCoreEnv`) companion to
`decPkD2cSlotOk_full_placed_at_archive_of_seams` (`DecPkD2cSlotOkFrozenPlacedAt`). -/
theorem decPkD2cSlotOk_full_placed_at_X_archive_of_seams [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ B : RunBudgets,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hSpqrTd : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv W a evs := by intros _ _ h; exact h)
    (hErrEnv : ∀ B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          g r))
    (hEnv : ∀ g evs,
      CliDpPollD2cEnv (A := A.repAlloc) W X cliRunBudgets ReadEnv DeserEnv
        (cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        (cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        P2OverErrEnv P2OverOkEnv tdEnv
        (fun B F0 peer pid kpkId spkId kbk =>
          cliPollStageP4Prev1EnvsAt A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv)
        g evs →
      DecPkEnv g evs) :
    DecPkD2cSlotOkFrozenPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W)) X W A lim
      DecPkEnv :=
  decPkD2cSlotOk_full_placed_at_X_archive_of_tryDec mmpl gh W X hDropNz hG hh hRead hDeser hSpqr
    hRaw
    (fun ctl =>
      overPollTryDecrypt_placed_at_of_tdEnv mmpl gh W ctl hG hAesDec hSpqrTd
        (cliFmtWrite_budget_sat mmpl gh W) (cliFormatInner_budget_sat mmpl gh W)
        hRecv_ne fmtWriteEnv_nonempty formatInnerEnv_nonempty htd)
    hErrEnv hOkEnv hFitsSplit hEnv

/-- Coarse-`TryDecryptCliEnv` convenience specialization of `decPkD2cSlotOk_full_placed_at_of_seams`
requiring only a single `hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W`. -/
theorem decPkD2cSlotOk_full_placed_at_of_spqr [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ B : RunBudgets,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hErrEnv : ∀ X B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          g r))
    (hEnv : ∀ X g evs,
      CliDpPollD2cEnv (A := A.repAlloc) W X cliRunBudgets ReadEnv DeserEnv
        (cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        (cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        P2OverErrEnv P2OverOkEnv
        (fun W' => TryDecryptCliEnv W'.C (spqrV1 W'.C.F W'.Q.K))
        (fun B F0 peer pid kpkId spkId kbk =>
          cliPollStageP4Prev1EnvsAt A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv)
        g evs →
      DecPkEnv g evs) :
    OverDecPkD2cSlotOkFrozenPlaced mmpl gh W A lim DecPkEnv :=
  decPkD2cSlotOk_full_placed_at_of_tryDec mmpl gh W hDropNz hG hh hRead hDeser hSpqr hRaw
    (fun ctl => overPollTryDecrypt_placed_at_of_spqr mmpl gh W ctl hG hAesDec hSpqr)
    hErrEnv hOkEnv hFitsSplit hEnv

/-- Coarse-`TryDecryptCliEnv` + `PromoteOverArchiveCanonSessEnv` convenience specialization of
`decPkD2cSlotOk_full_placed_at_archive_of_seams`. -/
theorem decPkD2cSlotOk_full_placed_at_archive_of_spqr [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ B : RunBudgets,
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hErrEnv : ∀ X B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv (cliP2KitEnvsAt A.repAlloc ReadEnv B))
          g r))
    (hEnv : ∀ X g evs,
      CliDpPollD2cEnv (A := A.repAlloc) W X cliRunBudgets ReadEnv DeserEnv
        (cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        (cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        P2OverErrEnv P2OverOkEnv
        (fun W' => TryDecryptCliEnv W'.C (spqrV1 W'.C.F W'.Q.K))
        (fun B F0 peer pid kpkId spkId kbk =>
          cliPollStageP4Prev1EnvsAt A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv)
        g evs →
      DecPkEnv g evs) :
    OverDecPkD2cSlotOkFrozenPlaced mmpl gh W A lim DecPkEnv :=
  decPkD2cSlotOk_full_placed_at_archive_of_tryDec mmpl gh W hDropNz hG hh hRead hDeser hSpqr hRaw
    (fun ctl => overPollTryDecrypt_placed_at_of_spqr mmpl gh W ctl hG hAesDec hSpqr)
    hErrEnv hOkEnv hFitsSplit hEnv

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cSlotOkAtPlacedBudget
