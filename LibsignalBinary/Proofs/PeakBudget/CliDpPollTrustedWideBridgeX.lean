/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3AuxPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4AuxPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2AuxPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1StorePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBob
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlacedBudget
public import LibsignalBinary.Proofs.E2E.Record.Support.Phi
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cSlotOkAtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget

/-!
# Guarded wide `W4` (`decrypt_prekey`) poll trace inclusions and slot wrappers

**Checked by Lean.** Establishes trace inclusions from the `decrypt_prekey` poll stage envelopes
(Stages P1, P2 `Matched`/`PathA`/`Over`, P3 `prevEmpty`/`M3`, and P4 `SeqFree`) into the `W4Binary*`
wide slot envelopes, unsatisfiability of `FitsEnv` on `⊤` at `cliBudgetLimits`, and
`PeerSpqrStateTight640` split-on-guard `DecPkD2cSlotOk` wrappers and consumer eliminators.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridgeX

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (IdentityKey PublicKey SessionState ShaCompress SignalMessage)
open CryptoGames.LibsignalSessionApi (ApiError Session SessionRecord)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalFrozen LibsignalFullPlacement LibsignalHooks
  LibsignalPlacement libsignalFrozen_of_keepsFrozen lsmpl lsρ
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  mismatchRemoteIkStrPlaced_length
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (clearPending)
open CryptoVerification.Cli.E2E.V1 (bobSpqrParams)
open CryptoVerification.E2E (
  PreKeyMessageFields UnreachedPqxdhPrimitives acceptInput aesDecHookMallocng modelPrims
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput Bytes DRKey Primitives bytesToBv8 ofSignalPqxdhAcceptKeysInput
  structuralPrims_initiatorModelPrims
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  acceptKeys_some_lengths ofSignalPqxdhPrimitives
)
open CryptoVerification.E2E.Record (encSession encodeRecord lenField msgField)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall SendCall)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (
  CliHooks CliPqxdhInputs Inputs cliExternsPlaced lsReadFileSym
)
open CryptoVerification.SignalSession.Cli (ReadRule StoresGhost utf8)
open CryptoVerification.SignalSession.Cli.MainHops (
  AddrV cliIo cliRunBudgets cliWrOk parseArgs
)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost RunSem addrValOf dpPollNeed runFiles slotOut slotTrace
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOkD2c decPkDefD2c pkStoreKeys pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSelfKitPlaced
  cliPollSessKitPlaced cliPollSessPrev1KitPlaced cliPollSpkKitPlaced dpPollEntryPlaced
  dpPollProgPlaced hdrOpkIdBv?_mkPathAHdr mkPathAHdr
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (EncodeInjOn FilesOkPeer filesOk₀ scopeIn scopeKit)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost uuidTryParse
)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.SpecBudget (aesDecBudgetSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  BobSpqrInitialStateEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget (
  P2Sub1To3Arm1Env P2Sub1To3Arm2Env P2Sub1To3OkEnv P2Sub1To4Arm3Env P2Sub1To4OkEnv P2Sub4OkEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget (
  P2Sub1Env boxAllocEnv_iff_eq boxAllocEvents p2Sub1Events
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3AuxPlacedBudget (
  P2Sub3TailAllocEnv p2Sub3TailAllocEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4AuxPlacedBudget (
  p2Sub4NoneEnv_iff_boxAllocEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget (
  P2Sub6Env P2V1Arm4Env P2V1Arm5EnvOfAcceptErr P2V1Arm6EnvOfBob P2V1OkEnvOfBob
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudgetAux (
  StageP2MatchedBridgeEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget (
  StageP2MatchedEnv StageP2MatchedMismatchEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  StageP3ErrM3Env StageP3M3Env StageP3OkPrefixM3Env StageP3VerNeM3Env stageP3M3TryDecryptEnvArgs
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget (
  P2OverV1OkEnvOfBobAndProm
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1StorePlacedBudget (
  StorePrev1StepEnv
)
open LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget (bobSpqrGhost)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (
  AcceptOptFieldsEnv acceptOptFieldsEvents
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlacedBudget (
  InitBobSessionBuildEnv initBobSessionBuildEvents
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget (
  KemKeyPairFromPubPrivEnv
)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs (
  W4BinaryAcceptWideEnv W4BinaryPromoteArchiveEnv W4BinarySessStorePrev1StepEnv
  W4BinarySessStoreStepEnv W4BinaryStageP2MatchedWideEnv
)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked (
  SpqrRecvC07C09aBytesEnv TryDecryptCliLinkedEnv
)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux (
  CliDpPollD2cLinkedEnv StageP3Prev1WideVRegsPlacedStmt
  closure_trusted_d2c_wide_frozen_placed_ok overPollTryDecrypt_placed_at_linked
)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase (
  CliDpPollOkD2cStateFrozenPlacedAt CliDpPollOkD2cStateMemInvAt DecPkD2cSlotOkFrozenPlaced
  DecPkD2cSlotOkFrozenPlacedAt DecPkD2cSlotOkPlacedAtOf DecPkD2cSlotOkPlacedOf
  StageP2OverQpanCliMemInvPlacedStmt StageP2PathAQpanCliMemInvAtStmt decPkD2cSlotOk_of_poll_frozen_placed
  decPkSlotSpecBasePlaced decPkSlotSpecPlacedOf extract_withMemInv slotsOfDecPkPlacedOf withMemInv
)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs (
  realCliDecPkBinaryWideSlotEnvGuardedFixed
)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (
  W4BinaryIdSaveStepEnvAllFixed W4BinaryIdTrustStepEnvAllFixed W4BinaryKpkGetStepEnvAllFixed
  W4BinaryKpkMarkStepEnvFixed W4BinaryPkGetStepEnvAllFixed W4BinaryPkRemoveStepEnvAllFixed
  W4BinarySelfKpStepEnvAllFixed W4BinarySelfRegIdStepEnvAllFixed W4BinarySessLoadStepEnvAllFixed
  W4BinarySpkGetStepEnvAllFixed W4BinaryStageP1OkEnvAllFixed W4BinaryStageP1UntrustedEnvAllFixed
  W4BinaryStageP2PathAWideEnvAllFixed W4BinaryStageP4MatchedWideEnvAllFixed
  W4BinaryStageP4PathAWideEnvAllFixed W4BinaryStageP4PathCWideEnvAllFixed
  realCliDecPkBinaryWideSlotEnvFixed
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (
  IterSeqEnv ModelHyps PhaseCreditSpec
)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak (ArchivedTrialIterEnv)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (RecordGhostValid)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak (
  W4BobSessionBuildEnv W4BoundedEvs nonFreeCount phaseCredit_seq_freeOnly
  phaseCredit_w4BoundedEvs_small
)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec (
  OptStageEnv W4ErrTailWideEnv W4StageP2MatchedCheckEnv W4StageP3WideEnv
  W4TryDecryptCloneFailWideEnv optStageEnv_nil w4ErrTailWideEnv_of_freeOnly
  w4StageP2MatchedCheckEnv_of_bridge33 w4StageP2MatchedCheckEnv_of_mismatch70
  w4StageP3WideEnv_of_err w4StageP3WideEnv_of_okPrefix w4StageP3WideEnv_of_verNe
)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers (
  W4BoxedStoreStepEnv boxedDeallocPred_to_w4BoxedStoreStep rustDealloc8_freeOnly
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (SaveStepEnv TrustStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (LoadStepEnv StoreStepEnv)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (IkpPostCleanupEnv IkpSubEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  ReadFileRuleEnvFixed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cSlotOkAtPlacedBudget (
  cliP2KitEnvsAt cliPollStageP4Prev1EnvsAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget (
  cliPollSessPrev1SeqFreeBudgetEnv cliPollSessPrev1SeqFreeStorePollEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  StageP4Prev1Env StageP4Prev1VRegsPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlacedBudget (
  dpPollPost_mono_of_decPk_eq_placed dpPollPre_unpack_d2c_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  P2OverPathCErrEnvOf P2OverPathCOkEnvOf PromoteOverArchiveCanonSessEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget (
  StageP2MatchedFramedCliPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  StageP3Env StageP3ErrEnv StageP3OkPrefixEnv StageP3VerNeEnv stageP3TryDecryptEnvArgs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  MarkStepEnv OptRemoveStepEnv RemoveStepEnv StageP3GenStepsVRegsPlacedStmt
  StageP3PrevEmptyVRegsPlacedStmt StageP4MatchedEnv StageP4MatchedPlacedStmt StageP4PathAEnv
  StageP4PathAPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget (
  CliStageP1OkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  CliDpPollUntrustedEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1InstPlacedBudgetAux (
  P2PathAErrEnvOf P2PathAOkEnvOf
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliP2PathAOptFieldsErrEnv cliP2PathAOptFieldsOkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv cliPollSessBudgetEnv
  cliPollSessSeqFreeBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget (
  OptIkpTryFromEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget decPkSlotSpecPlaced dpPollSpecStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  SegCloneEnv TryDecryptEnvArgs
)

/-! ## `W4` poll stage envelope abbreviations -/

/-- Canonical `RecordDeserializeCancelEnv` `DeserEnv` over `SessionRecord`. -/
abbrev dpx_deserEnv (r : SessionRecord (List (BitVec 8))) : List AllocEvent → Prop :=
  RecordDeserializeCancelEnv (encodeRecord r)

/-- Canonical Stage P2 Path A error envelope at `ReadFileRuleEnvFixed cliIo.rd`. -/
abbrev dpx_p2PathAErrEnv [LibsignalPlacement] (A : RustAlloc)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) : DecPkGhost → List AllocEvent → Prop :=
  cliP2PathAOptFieldsErrEnv A (ReadFileRuleEnvFixed cliIo.rd) X W cliRunBudgets
    (fun F0 peer =>
      cliPollSelfBudgetEnv A F0 peer (cliKitStk cliRunBudgets) (ReadFileRuleEnvFixed cliIo.rd))

/-- Canonical Stage P2 Path A normal-exit envelope at `ReadFileRuleEnvFixed cliIo.rd`. -/
abbrev dpx_p2PathAOkEnv [LibsignalPlacement] (A : RustAlloc)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) : DecPkGhost → List AllocEvent → Prop :=
  cliP2PathAOptFieldsOkEnv A (ReadFileRuleEnvFixed cliIo.rd) X W cliRunBudgets
    (fun F0 peer =>
      cliPollSelfBudgetEnv A F0 peer (cliKitStk cliRunBudgets) (ReadFileRuleEnvFixed cliIo.rd))

/-- Canonical Stage P2 Over (Path C) error envelope at `ReadFileRuleEnvFixed cliIo.rd`. -/
abbrev dpx_p2OverErrEnv [LibsignalPlacement] (A : RustAlloc)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop :=
  P2OverPathCErrEnvOf (A := A) X W cliRunBudgets
    (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
    (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
    (cliP2KitEnvsAt A (ReadFileRuleEnvFixed cliIo.rd) cliRunBudgets)

/-- Canonical Stage P2 Over (Path C) normal-exit envelope at `PromoteOverArchiveCanonSessEnv`
and `ReadFileRuleEnvFixed cliIo.rd`. -/
abbrev dpx_p2OverOkEnv [LibsignalPlacement] (A : RustAlloc)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop :=
  P2OverPathCOkEnvOf (A := A) X W cliRunBudgets
    (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
    PromoteOverArchiveCanonSessEnv
    (cliP2KitEnvsAt A (ReadFileRuleEnvFixed cliIo.rd) cliRunBudgets)

/-! ## Unsatisfiability of `FitsEnv` on `⊤` at `cliBudgetLimits` -/

/-- No cost-model state `st` can satisfy `FitsEnv fineCostModel cliBudgetLimits st (fun _ => True)`:
a single allocation exceeding `cliBudgetLimits.physCap` violates the physical RAM inequality. -/
theorem dpx_not_fitsEnv_top_cliBudgetLimits {st : fineCostModel.σ} :
    ¬ FitsEnv fineCostModel cliBudgetLimits st (fun _ => True) := by
  intro h
  have hev : FitsEvents fineCostModel cliBudgetLimits st [.alloc (cliBudgetLimits.physCap + 1)] :=
    h [.alloc (cliBudgetLimits.physCap + 1)] trivial
  rcases hev with ⟨⟨_, _, hram, _⟩, _⟩
  have hreq : cliBudgetLimits.physCap + 1 ≤
      fineCostModel.stepReserve (.alloc (cliBudgetLimits.physCap + 1)) st :=
    fineCostModel.req_le_stepReserve (.alloc (cliBudgetLimits.physCap + 1)) st
  omega

/-! ## Split-on-guard `DecPkD2cSlotOk` and poll wrappers -/

private theorem dpx_dpPollPre_mono_fits [LibsignalPlacement] (CodeOk : Memory → Prop)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {E₁ E₂ : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim E₁ B S))
    (R : SepProp) (s0 : State)
    (hSub_y : ∀ evs, E₂ y.g evs → E₁ y.g evs)
    (hpre : s0.mem ⊨
      (withMemInv CodeOk
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim E₁ B S) stk')).pre y s0 ∗ R) :
    let y₂ : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim E₂ B S) :=
      ⟨y.out, y.fut, y.cx, y.g, y.st⟩
    s0.mem ⊨
      (withMemInv CodeOk
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim E₂ B S) stk')).pre y₂ s0 ∗ R := by
  dsimp only
  obtain ⟨hcode0, hpre0⟩ := extract_withMemInv hpre
  dsimp only [withMemInv]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcode0, Satisfies.mono (sepConj_mono_left ?_) hpre0⟩
  dsimp only [dpPollSpecStateBudget, dpSlotPollKStatePlaced]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left ?_))))
  refine Entails.pure_left fun ⟨h1, h2, h3, hfit⟩ => ?_
  have hEq : (s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
      S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg ∧ FitsEnv M lim y.st (E₂ y.g)) = True :=
    propext ⟨fun _ => trivial, fun _ => ⟨h1, h2, h3, hfit.mono hSub_y⟩⟩
  rw [hEq, pure_true, emp_sepConj]
  exact Entails.refl _

/-- Generic `CodeOk`-parameterized poll-level split-on-guard wrapper: splits on
`PeerSpqrStateTight640`, applies `hSub` when true, and closes the `⊤` branch via
`dpx_not_fitsEnv_top_cliBudgetLimits`. -/
theorem dpx_cliDpPollOkD2cStateMemInvAt_guarded_of_poll [LibsignalPlacement]
    (CodeOk : Memory → Prop)
    (hro : ∀ m, CodeOk m → LibsignalCodeRoLoaded lsmpl m)
    {A : RustCliAllocBudget fineCostModel}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PollEnv TargetEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hpoll : CliDpPollOkD2cStateMemInvAt CodeOk A cliBudgetLimits ReadEnv DeserEnv PollEnv
      mmpl gh W X B S Scope)
    (hSub : ∀ g evs,
      FilesOkPeer Scope g.F g.peer.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ Scope g.F g.peer.val g.me.val g.msg →
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
        W.C.F W.Q.K g.F g.peer.val →
      PollEnv g evs →
      TargetEnv g evs) :
    CliDpPollOkD2cStateMemInvAt CodeOk A cliBudgetLimits ReadEnv DeserEnv
      (fun g evs =>
        LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
          W.C.F W.Q.K g.F g.peer.val →
        TargetEnv g evs)
      mmpl gh W X B S Scope := by
  intro hh_skel hReadFile hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  let GuardedEnv : DecPkGhost → List AllocEvent → Prop := fun g evs =>
    LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
      W.C.F W.Q.K g.F g.peer.val → TargetEnv g evs
  have hp := hpoll hh_skel hReadFile hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  refine subroutine_ok.of_codeLoaded fun y R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcode0, hpre0⟩ := extract_withMemInv hpre
  have hpre_ro : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A cliBudgetLimits GuardedEnv B S) stk')).pre
        y s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hro s0.mem hcode0, hpre0⟩
  obtain ⟨hpure, _⟩ :=
    dpPollPre_unpack_d2c_placed (W := W) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre_ro
  by_cases hT :
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
        W.C.F W.Q.K y.g.F y.g.peer.val
  · have hSub_y : ∀ evs, PollEnv y.g evs → GuardedEnv y.g evs :=
      fun evs hevs _ => hSub y.g evs hpure.filesOkPeer hpure.decPkOk hT hevs
    have hpre₂ := dpx_dpPollPre_mono_fits CodeOk stk' y R s0 hSub_y hpre
    refine hp.mono_outcome ⟨y.out, y.fut, y.cx, y.g, y.st⟩ R s0 hpc hrun hpre₂ hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hpan⟩ | ⟨code, hex_st, hex⟩ | ⟨ho_st, ho⟩
    · exact Or.inl ⟨hret, hcc,
        Satisfies.mono
          (sepConj_mono_left (dpPollPost_mono_of_decPk_eq_placed stk' y s0 sf hSub_y rfl))
          hpost⟩
    · exact Or.inr (Or.inl ⟨hp_st, hpan⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hex⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))
  · exact False.elim
      (dpx_not_fitsEnv_top_cliBudgetLimits (hpure.fits.mono fun _ _ h => False.elim (hT h)))

/-- `LibsignalFrozen` poll-level split-on-guard wrapper targeting `realCliDecPkBinaryWideSlotEnvGuardedFixed X₀ W`. -/
theorem dpx_cliDpPollOkD2cStateFrozenPlacedAt_guarded_of_poll [LibsignalPlacement]
    {A : RustCliAllocBudget fineCostModel}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PollEnv : DecPkGhost → List AllocEvent → Prop}
    (X₀ : UnreachedPqxdhPrimitives)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hpoll : CliDpPollOkD2cStateFrozenPlacedAt A cliBudgetLimits ReadEnv DeserEnv PollEnv
      mmpl gh W X B S Scope)
    (hSub : ∀ g evs,
      FilesOkPeer Scope g.F g.peer.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ Scope g.F g.peer.val g.me.val g.msg →
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
        W.C.F W.Q.K g.F g.peer.val →
      PollEnv g evs →
      realCliDecPkBinaryWideSlotEnvFixed X₀ W g evs) :
    CliDpPollOkD2cStateFrozenPlacedAt A cliBudgetLimits ReadEnv DeserEnv
      (realCliDecPkBinaryWideSlotEnvGuardedFixed X₀ W)
      mmpl gh W X B S Scope :=
  dpx_cliDpPollOkD2cStateMemInvAt_guarded_of_poll (LibsignalFrozen lsmpl)
    (fun _ hf => ⟨LibsignalCodeLoaded.of_codeLoaded hf.2, hf.1⟩)
    mmpl gh W X B S Scope hpoll hSub

/-- Lifts a Block-`518` `PollEnv` proof and conditional trace inclusion into `DecPkD2cSlotOkFrozenPlaced`. -/
theorem dpx_decPkD2cSlotOk_frozen_placed_guarded_of_poll [LibsignalFullPlacement]
    {A : RustCliAllocBudget fineCostModel}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PollEnv : UnreachedPqxdhPrimitives → DecPkGhost → List AllocEvent → Prop}
    (X₀ : UnreachedPqxdhPrimitives)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A cliBudgetLimits (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A cliBudgetLimits cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A cliBudgetLimits DeserEnv))
    (hpoll : ∀ X S,
      CliDpPollOkD2cStateFrozenPlacedAt A cliBudgetLimits ReadEnv DeserEnv (PollEnv X)
        mmpl gh W X cliRunBudgets S scopeIn)
    (hSub : ∀ X g evs,
      FilesOkPeer scopeIn g.F g.peer.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
        W.C.F W.Q.K g.F g.peer.val →
      PollEnv X g evs →
      realCliDecPkBinaryWideSlotEnvFixed X₀ W g evs) :
    DecPkD2cSlotOkFrozenPlaced mmpl gh W A cliBudgetLimits
      (realCliDecPkBinaryWideSlotEnvGuardedFixed X₀ W) :=
  decPkD2cSlotOk_of_poll_frozen_placed mmpl gh W hh hRead hDeser fun X S =>
    dpx_cliDpPollOkD2cStateFrozenPlacedAt_guarded_of_poll X₀ mmpl gh W X cliRunBudgets S scopeIn
      (hpoll X S) (hSub X)

private theorem dpx_decPkSlotPost_mono [LibsignalPlacement] (CodeOk : Memory → Prop)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {E₁ E₂ : DecPkGhost → List AllocEvent → Prop} {S : RunSem}
    (stk : Nat) (x : DecPkGhost) (st : M.σ) (s0 sf : State)
    (hSub_x : ∀ evs, E₁ x evs → E₂ x evs) :
    (decPkSlotSpecPlacedOf CodeOk A lim E₁ S stk).post (x, st) s0 sf ⊢
      (decPkSlotSpecPlacedOf CodeOk A lim E₂ S stk).post (x, st) s0 sf := by
  dsimp only [decPkSlotSpecPlacedOf, withMemInv, decPkSlotSpecBasePlaced, decPkSlotSpecPlaced,
    withLsCodeRoLoaded]
  refine Entails.sepExists_elim fun evs => Entails.trans ?_ (Entails.sepExists_intro evs)
  refine Entails.sepExists_elim fun g' => Entails.trans ?_ (Entails.sepExists_intro g')
  refine Entails.sepExists_elim fun e => Entails.trans ?_ (Entails.sepExists_intro e)
  refine Entails.pure_left fun ⟨hevs, htr, hout⟩ => ?_
  have hφ : E₂ x evs ∧ slotTrace s0 sf ∧
      slotOut (S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins) g' e s0 sf :=
    ⟨hSub_x evs hevs, htr, hout⟩
  have hEqP : (E₂ x evs ∧ slotTrace s0 sf ∧
      slotOut (S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins) g' e s0 sf) = True :=
    propext ⟨fun _ => trivial, fun _ => hφ⟩
  rw [hEqP, pure_true, emp_sepConj]
  exact Entails.refl _

/-- Generic `CodeOk`-parameterized slot-level split-on-guard wrapper from conditional inclusion into `TargetEnv`. -/
theorem dpx_decPkD2cSlotOkPlacedAtOf_guarded_of_sub [LibsignalPlacement]
    (CodeOk : Memory → Prop)
    {A : RustCliAllocBudget fineCostModel}
    {PollEnv TargetEnv : DecPkGhost → List AllocEvent → Prop}
    (H : LibsignalHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hSlot : DecPkD2cSlotOkPlacedAtOf CodeOk H X W A cliBudgetLimits PollEnv)
    (hSub : ∀ g evs,
      FilesOkPeer scopeIn g.F g.peer.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
        W.C.F W.Q.K g.F g.peer.val →
      PollEnv g evs →
      TargetEnv g evs) :
    DecPkD2cSlotOkPlacedAtOf CodeOk H X W A cliBudgetLimits
      (fun g evs =>
        LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
          W.C.F W.Q.K g.F g.peer.val →
        TargetEnv g evs) := by
  intro S needs sEnvs hsDec hfiles hdec hdecOk hneed stk hstk1 hstk2
  let GuardedEnv : DecPkGhost → List AllocEvent → Prop := fun g evs =>
    LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
      W.C.F W.Q.K g.F g.peer.val → TargetEnv g evs
  have hok_poll :=
    hSlot S needs { sEnvs with decryptPrekey := PollEnv } rfl hfiles hdec hdecOk hneed stk
      hstk1 hstk2
  dsimp only [slotsOfDecPkPlacedOf] at hok_poll ⊢
  rw [hsDec]
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcode0, hpre0⟩ := extract_withMemInv hpre
  dsimp only [decPkSlotSpecBasePlaced] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le, hfit⟩,
    hspatial⟩ := hpre0
  have hfPeer : FilesOkPeer scopeIn x.F x.peer.val := (hfiles ▸ hfOk).1
  have hdOk' : DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn x.F x.peer.val x.me.val x.msg := hdecOk ▸ hdOk
  by_cases hT :
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
        W.C.F W.Q.K x.F x.peer.val
  · have hSub_x : ∀ evs, PollEnv x evs → GuardedEnv x evs :=
      fun evs hevs _ => hSub x evs hfPeer hdOk' hT hevs
    have hfit_poll : FitsEnv fineCostModel cliBudgetLimits st (PollEnv x) :=
      hfit.mono hSub_x
    have hpre₁ : s0.mem ⊨
        (decPkSlotSpecPlacedOf CodeOk A cliBudgetLimits PollEnv S stk).pre (x, st) s0 ∗ R := by
      dsimp only [decPkSlotSpecPlacedOf, withMemInv, decPkSlotSpecBasePlaced]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcode0, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le, hfit_poll⟩,
        hspatial⟩
    refine hok_poll.mono_outcome (x, st) R s0 hpc hrun hpre₁ hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hpan⟩ | ⟨code, hex_st, hex⟩ | ⟨ho_st, ho⟩
    · exact Or.inl ⟨hret, hcc,
        Satisfies.mono
          (sepConj_mono_left (dpx_decPkSlotPost_mono CodeOk stk x st s0 sf hSub_x))
          hpost⟩
    · exact Or.inr (Or.inl ⟨hp_st, hpan⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hex⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))
  · exact False.elim
      (dpx_not_fitsEnv_top_cliBudgetLimits (hfit.mono fun _ _ h => False.elim (hT h)))

/-- Pointwise `(H, X, W)` `DecPkD2cSlotOkFrozenPlacedAt` split-on-guard wrapper. -/
theorem dpx_decPkD2cSlotOkFrozenPlacedAt_guarded_of_sub [LibsignalPlacement]
    {A : RustCliAllocBudget fineCostModel}
    {PollEnv : DecPkGhost → List AllocEvent → Prop}
    (X₀ : UnreachedPqxdhPrimitives)
    (H : LibsignalHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hSlot : DecPkD2cSlotOkFrozenPlacedAt H X W A cliBudgetLimits PollEnv)
    (hSub : ∀ g evs,
      FilesOkPeer scopeIn g.F g.peer.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
        W.C.F W.Q.K g.F g.peer.val →
      PollEnv g evs →
      realCliDecPkBinaryWideSlotEnvFixed X₀ W g evs) :
    DecPkD2cSlotOkFrozenPlacedAt H X W A cliBudgetLimits
      (realCliDecPkBinaryWideSlotEnvGuardedFixed X₀ W) :=
  dpx_decPkD2cSlotOkPlacedAtOf_guarded_of_sub (LibsignalFrozen lsmpl) H X W hSlot hSub

/-- `∀ X`-quantified `DecPkD2cSlotOkFrozenPlaced` split-on-guard wrapper. -/
theorem dpx_decPkD2cSlotOkFrozenPlaced_guarded_of_sub [LibsignalPlacement]
    {A : RustCliAllocBudget fineCostModel}
    {PollEnv : UnreachedPqxdhPrimitives → DecPkGhost → List AllocEvent → Prop}
    (X₀ : UnreachedPqxdhPrimitives)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hSlot : ∀ X,
      DecPkD2cSlotOkFrozenPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W)) X W
        A cliBudgetLimits (PollEnv X))
    (hSub : ∀ X g evs,
      FilesOkPeer scopeIn g.F g.peer.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
        W.C.F W.Q.K g.F g.peer.val →
      PollEnv X g evs →
      realCliDecPkBinaryWideSlotEnvFixed X₀ W g evs) :
    DecPkD2cSlotOkFrozenPlaced mmpl gh W A cliBudgetLimits
      (realCliDecPkBinaryWideSlotEnvGuardedFixed X₀ W) :=
  fun X => dpx_decPkD2cSlotOkFrozenPlacedAt_guarded_of_sub X₀
    (cliGhostExterns gh (cliExternsPlaced mmpl W)) X W (hSlot X) (hSub X)

/-- Split-on-guard `DecPkD2cSlotOkFrozenPlaced` wrapper around
`DecPkD2cSlotOkLinkedAux.dpPoll_d2c_wide_sepWPp_of_codeOk` / `closure_trusted_d2c_wide_frozen_placed_ok`
at `DecPkEnv := realCliDecPkBinaryWideSlotEnvGuardedFixed X₀ W` (`fineCostModel`,
`cliBudgetLimits`), parameterized by conditional trace inclusion `hSub`. -/
theorem dpx_decPkD2cSlotOk_frozen_placed_guarded_of_linked [LibsignalFullPlacement]
    {A : RustCliAllocBudget fineCostModel}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (X₀ : UnreachedPqxdhPrimitives)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks fineCostModel A cliBudgetLimits gh)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D)
      (aesDecBudgetSpec W.C.D fineCostModel A cliBudgetLimits))
    (hSpqrLinked : SpqrV1PlacedSeamsOfEnv fineCostModel A cliBudgetLimits mmpl gh W InitEnv
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv)
    (hh : RunHooksPlaced A cliBudgetLimits (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A cliBudgetLimits cliRunBudgets.readFile
        (ReadFileRuleEnvFixed cliIo.rd)))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A cliBudgetLimits dpx_deserEnv))
    (hP2A : ∀ X, StageP2PathAQpanCliMemInvAtStmt (LibsignalFrozen lsmpl)
      A cliBudgetLimits (ReadFileRuleEnvFixed cliIo.rd) X mmpl gh W cliRunBudgets
      (dpx_p2PathAErrEnv A.repAlloc X W) (dpx_p2PathAOkEnv A.repAlloc X W))
    (hP3A : StageP3GenStepsVRegsPlacedStmt)
    (hP4A : StageP4PathAPlacedStmt)
    (hP2B : StageP2MatchedFramedCliPlacedStmt)
    (hP3B : StageP3PrevEmptyVRegsPlacedStmt)
    (hP4B : StageP4MatchedPlacedStmt)
    (hP2O : StageP2OverQpanCliMemInvPlacedStmt (LibsignalFrozen lsmpl)
      A cliBudgetLimits P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1WideVRegsPlacedStmt A cliBudgetLimits
      (fun W => TryDecryptCliLinkedEnv W.C W.Q.K))
    (hP4O : StageP4Prev1VRegsPlacedStmt A cliBudgetLimits
      (fun B F0 peer pid kpkId spkId kbk =>
        cliPollStageP4Prev1EnvsAt A.repAlloc B F0 peer pid kpkId spkId kbk
          (ReadFileRuleEnvFixed cliIo.rd)))
    (hSub : ∀ X g evs,
      FilesOkPeer scopeIn g.F g.peer.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
        W.C.F W.Q.K g.F g.peer.val →
      CliDpPollD2cLinkedEnv (A := A.repAlloc) W X cliRunBudgets
        (ReadFileRuleEnvFixed cliIo.rd)
        dpx_deserEnv
        (dpx_p2PathAErrEnv A.repAlloc X W)
        (dpx_p2PathAOkEnv A.repAlloc X W)
        P2OverErrEnv
        P2OverOkEnv
        (fun B F0 peer pid kpkId spkId kbk =>
          cliPollStageP4Prev1EnvsAt A.repAlloc B F0 peer pid kpkId spkId kbk
            (ReadFileRuleEnvFixed cliIo.rd))
        g evs →
      realCliDecPkBinaryWideSlotEnvFixed X₀ W g evs) :
    DecPkD2cSlotOkFrozenPlaced mmpl gh W A cliBudgetLimits
      (realCliDecPkBinaryWideSlotEnvGuardedFixed X₀ W) :=
  dpx_decPkD2cSlotOk_frozen_placed_guarded_of_poll X₀ mmpl gh W hh hRead hDeser
    (fun X S =>
      closure_trusted_d2c_wide_frozen_placed_ok hDropNz mmpl gh W X cliRunBudgets S scopeIn hG
        (hP2A X) hP3A hP4A hP2B hP3B hP4B hP2O hP3O hP4O
        (overPollTryDecrypt_placed_at_linked mmpl gh W 0#64 hG hAesDec hSpqrLinked)
        (fun _ _ h => h))
    hSub

/-! ## Consumer `hRunSub` guard eliminators -/

/-- Discharges a `PeerSpqrStateTight640`-guarded `DecPkEnv` back to unguarded
`realCliDecPkBinaryWideSlotEnvFixed X W x evs` from any `PeerSpqrStateTight640` witness. -/
theorem dpx_realCliDecPkBinaryWideSlotEnvFixed_of_guarded_tight [LibsignalPlacement]
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔ realCliDecPkBinaryWideSlotEnvGuardedFixed X W g e)
    (hTight : LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
      W.C.F W.Q.K x.F x.peer.val)
    (hevs : DecPkEnv x evs) :
    realCliDecPkBinaryWideSlotEnvFixed X W x evs :=
  ((hSlot x evs).mp hevs) hTight

/-- Discharges the `PeerSpqrStateTight640` guard from `CliPqxdhInputs ⟨W.C, W.Q⟩ i` at `.recv peer`. -/
theorem dpx_realCliDecPkBinaryWideSlotEnvFixed_of_guarded_cliPqInputs_recv [LibsignalPlacement]
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {i : Inputs} {peer : AddrV}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔ realCliDecPkBinaryWideSlotEnvGuardedFixed X W g e)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hF : x.F = runFiles i) (hpeer : x.peer.val = addrValOf peer)
    (hevs : DecPkEnv x evs) :
    realCliDecPkBinaryWideSlotEnvFixed X W x evs := by
  apply dpx_realCliDecPkBinaryWideSlotEnvFixed_of_guarded_tight hSlot _ hevs
  rw [hF, hpeer]
  exact LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.peerSpqrStateTight640_of_cliPqInputs_recv
    hi hparse

/-! ## Stage P1, Stage P2 (`Matched`), and Stage P4 (`SeqFree`) inclusions -/

private theorem dpx_seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) : SeqEnv E₁' E₂' evs :=
  h.elim (fun hE1 => Or.inl (h1 evs hE1))
    fun ⟨e₁, e₂, heq, hE1, hE2⟩ => Or.inr ⟨e₁, e₂, heq, h1 e₁ hE1, h2 e₂ hE2⟩

private theorem dpx_seqEnv_optStage_nil_left {E F : List AllocEvent → Prop}
    {evs : List AllocEvent} (h : F evs) : SeqEnv (OptStageEnv E) F evs :=
  Or.inr ⟨[], evs, rfl, Or.inl (fun _ hm => nomatch hm), h⟩

private theorem dpx_seqEnv_optStage_step {E E' F F' : List AllocEvent → Prop}
    (hE : ∀ evs, E evs → E' evs) (hF : ∀ evs, F evs → F' evs)
    {evs : List AllocEvent} (h : SeqEnv E F evs) : SeqEnv (OptStageEnv E') F' evs :=
  dpx_seqEnv_mono (fun e he => Or.inr (hE e he)) hF h

/-- `load_session` boxed step inclusion into `W4BinarySessLoadStepEnvAllFixed` (`cliPollSessBudgetEnv`). -/
theorem dpx_loadStep_sub_w4SessLoadAllFixed [LibsignalPlacement] {A : RustAlloc}
    {B : RunBudgets} {F0 : FsFiles} {peer : AddrGhost} {evs : List AllocEvent}
    (h : LoadStepEnv
      (cliPollSessKitPlaced A F0 scopeKit peer (cliKitStk B))
      (cliPollSessBudgetEnv A F0 peer (cliKitStk B) dpx_deserEnv (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.sessions peer.val evs) :
    W4BinarySessLoadStepEnvAllFixed cliIo.rd F0 peer evs :=
  boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h

/-- `load_session` boxed step inclusion into `W4BinarySessLoadStepEnvAllFixed` (`cliPollSessSeqFreeBudgetEnv`). -/
theorem dpx_loadStepSeqFree_sub_w4SessLoadAllFixed [LibsignalPlacement] {A : RustAlloc}
    {B : RunBudgets} {F0 : FsFiles} {peer : AddrGhost} {evs : List AllocEvent}
    (h : LoadStepEnv
      (cliPollSessKitPlaced A F0 scopeKit peer (cliKitStk B))
      (cliPollSessSeqFreeBudgetEnv A F0 peer (cliKitStk B) dpx_deserEnv
        (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.sessions peer.val evs) :
    W4BinarySessLoadStepEnvAllFixed cliIo.rd F0 peer evs :=
  boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h

/-- `is_trusted_identity` boxed step inclusion into `W4BinaryIdTrustStepEnvAllFixed`. -/
theorem dpx_trustStep_sub_w4IdTrustAllFixed [LibsignalPlacement] {A : RustAlloc}
    {B : RunBudgets} {F0 : FsFiles} {peer : AddrGhost} {remoteIk : IdentityKey}
    {evs : List AllocEvent}
    (h : TrustStepEnv
      (cliPollIdKitPlaced A F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A F0 peer (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.identity peer.val remoteIk .receiving evs) :
    W4BinaryIdTrustStepEnvAllFixed cliIo.rd F0 peer remoteIk evs :=
  boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h

/-- Stage P1 untrusted-rejection envelope inclusion (`CliDpPollUntrustedEnv` ⊆
`W4BinaryStageP1UntrustedEnvAllFixed`). -/
theorem dpx_cliDpPollUntrustedEnv_sub_w4StageP1UntrustedAllFixed [LibsignalPlacement]
    {A : RustAlloc} {B : RunBudgets} {g : DecPkGhost} {evs : List AllocEvent}
    (h : CliDpPollUntrustedEnv (A := A) B (ReadFileRuleEnvFixed cliIo.rd) dpx_deserEnv g evs) :
    W4BinaryStageP1UntrustedEnvAllFixed cliIo.rd g.F g.peer g.msg.identityKey evs :=
  dpx_seqEnv_mono
    (fun _ hl => dpx_loadStep_sub_w4SessLoadAllFixed hl)
    (fun _ ht => dpx_seqEnv_mono
      (fun _ htr => dpx_trustStep_sub_w4IdTrustAllFixed htr)
      (fun _ hcl => hcl) ht)
    h

/-- Stage P1 trusted-path envelope inclusion (`CliStageP1OkEnv` ⊆ `W4BinaryStageP1OkEnvAllFixed`). -/
theorem dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed [LibsignalPlacement]
    {A : RustAlloc} {B : RunBudgets} {g : DecPkGhost} {evs : List AllocEvent}
    (h : CliStageP1OkEnv (A := A) B (ReadFileRuleEnvFixed cliIo.rd) dpx_deserEnv g evs) :
    W4BinaryStageP1OkEnvAllFixed cliIo.rd g.F g.peer g.msg.identityKey evs :=
  dpx_seqEnv_mono
    (fun _ hl => dpx_loadStep_sub_w4SessLoadAllFixed hl)
    (fun _ htr => Or.inr (dpx_trustStep_sub_w4IdTrustAllFixed htr))
    h

/-- Stage P2 Path-B `StageP2MatchedBridgeEnv` inclusion into `W4StageP2MatchedCheckEnv`. -/
theorem dpx_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedCheck {evs : List AllocEvent}
    (h : StageP2MatchedBridgeEnv evs) :
    W4StageP2MatchedCheckEnv evs := by
  rw [h]
  exact w4StageP2MatchedCheckEnv_of_bridge33
    (Or.inr ⟨rustAllocEvents 33 1, rustDeallocEvents 33 1, rfl, rfl, Or.inl rfl⟩)

/-- Stage P2 Path-B `StageP2MatchedMismatchEnv` inclusion into `W4StageP2MatchedCheckEnv`. -/
theorem dpx_stageP2MatchedMismatchEnv_sub_w4StageP2MatchedCheck {evs : List AllocEvent}
    (h : StageP2MatchedMismatchEnv evs) :
    W4StageP2MatchedCheckEnv evs := by
  rcases h with hbr | ⟨e₁, e₂, rfl, hbr, e_str, e_free, hstr, hfree, rfl⟩
  · exact dpx_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedCheck hbr
  · rw [hbr, hstr]
    change W4StageP2MatchedCheckEnv
      ((rustAllocEvents 33 1 ++ rustDeallocEvents 33 1) ++ (rustAllocEvents _ 1 ++ e_free))
    rw [mismatchRemoteIkStrPlaced_length, List.append_assoc]
    exact w4StageP2MatchedCheckEnv_of_mismatch70
      (Or.inr ⟨rustAllocEvents 33 1,
        rustDeallocEvents 33 1 ++ (rustAllocEvents 70 1 ++ e_free), rfl, rfl,
        Or.inr ⟨rustDeallocEvents 33 1, rustAllocEvents 70 1 ++ e_free, rfl, rfl,
          Or.inr ⟨rustAllocEvents 70 1, e_free, rfl, rfl, hfree⟩⟩⟩)

/-- Stage P2 Path-B `StageP2MatchedEnv` inclusion into `W4StageP2MatchedCheckEnv`. -/
theorem dpx_stageP2MatchedEnv_sub_w4StageP2MatchedCheck
    {sess : Session (List (BitVec 8))} {remIdKey : IdentityKey} {evs : List AllocEvent}
    (h : StageP2MatchedEnv sess remIdKey evs) :
    W4StageP2MatchedCheckEnv evs := by
  unfold StageP2MatchedEnv at h
  split at h
  · exact dpx_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedCheck h
  · exact dpx_stageP2MatchedMismatchEnv_sub_w4StageP2MatchedCheck h

/-- Stage P2 Path-B `StageP2MatchedBridgeEnv` inclusion into `W4BinaryStageP2MatchedWideEnv`. -/
theorem dpx_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedWide {α : Type}
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    {evs : List AllocEvent} (h : StageP2MatchedBridgeEnv evs) :
    W4BinaryStageP2MatchedWideEnv DecEnv TrialEnv DropEnv xs g_arch r_arch evs :=
  Or.inl (dpx_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedCheck h)

/-- Stage P2 Path-B `StageP2MatchedEnv` inclusion into `W4BinaryStageP2MatchedWideEnv`. -/
theorem dpx_stageP2MatchedEnv_sub_w4StageP2MatchedWide {α : Type}
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    {sess : Session (List (BitVec 8))} {remIdKey : IdentityKey} {evs : List AllocEvent}
    (h : StageP2MatchedEnv sess remIdKey evs) :
    W4BinaryStageP2MatchedWideEnv DecEnv TrialEnv DropEnv xs g_arch r_arch evs :=
  Or.inl (dpx_stageP2MatchedEnv_sub_w4StageP2MatchedCheck h)

/-- `save_identity` boxed step inclusion into `W4BinaryIdSaveStepEnvAllFixed`. -/
theorem dpx_saveStep_sub_w4IdSaveAllFixed [LibsignalPlacement] {A : RustAlloc}
    {B : RunBudgets} {F0 : FsFiles} {peer : AddrGhost} {remoteIk : IdentityKey}
    {evs : List AllocEvent}
    (h : SaveStepEnv
      (cliPollIdKitPlaced A F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A F0 peer (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.identity peer.val remoteIk evs) :
    W4BinaryIdSaveStepEnvAllFixed cliIo.rd F0 peer remoteIk evs :=
  boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h

/-- `mark_kyber_pre_key_used` boxed step inclusion into `W4BinaryKpkMarkStepEnvFixed`. -/
theorem dpx_markStep_sub_w4KpkMarkFixed [LibsignalPlacement] {A : RustAlloc}
    {B : RunBudgets} {F0 : FsFiles} {kpkId₀ spkId₀ kyberPreKeyId signedPreKeyId : BitVec 32}
    {kbk₀ baseKey : PublicKey} {evs : List AllocEvent}
    (h : MarkStepEnv
      (cliPollKpkKitPlaced A F0 kpkId₀ spkId₀ kbk₀ (cliKitStk B))
      (cliPollKpkBudgetEnv A F0 kpkId₀ spkId₀ kbk₀ (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.kyber kyberPreKeyId signedPreKeyId baseKey evs) :
    W4BinaryKpkMarkStepEnvFixed cliIo.rd F0 kyberPreKeyId signedPreKeyId baseKey evs :=
  boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h

/-- `remove_pre_key` boxed step inclusion into `W4BinaryPkRemoveStepEnvAllFixed`. -/
theorem dpx_removeStep_sub_w4PkRemoveAllFixed [LibsignalPlacement] {A : RustAlloc}
    {B : RunBudgets} {F0 : FsFiles} {pid₀ opkId : BitVec 32} {evs : List AllocEvent}
    (h : RemoveStepEnv
      (cliPollPkKitPlaced A F0 pid₀ (cliKitStk B))
      (cliPollPkBudgetEnv A F0 pid₀ (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.oneTime opkId evs) :
    W4BinaryPkRemoveStepEnvAllFixed cliIo.rd F0 opkId evs :=
  boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h

private theorem dpx_optRemoveStep_sub_w4PkRemoveAllFixed [LibsignalPlacement] {A : RustAlloc}
    {B : RunBudgets} {F0 : FsFiles} {pid₀ : BitVec 32} {opkId? : Option (BitVec 32)}
    {evs : List AllocEvent}
    (h : OptRemoveStepEnv
      (cliPollPkKitPlaced A F0 pid₀ (cliKitStk B))
      (cliPollPkBudgetEnv A F0 pid₀ (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.oneTime opkId? evs) :
    OptStageEnv
      (if opkId?.isSome then W4BinaryPkRemoveStepEnvAllFixed cliIo.rd F0 (opkId?.getD 0#32)
       else (· = [])) evs := by
  cases opkId? with
  | none => exact Or.inr h
  | some opkId => exact Or.inr (dpx_removeStep_sub_w4PkRemoveAllFixed h)

/-- `0`-prev `store_session` boxed step inclusion at `cliPollSessSeqFreeBudgetEnv` into
`W4BinarySessStoreStepEnv`, producing `(g_out0, r_out0)` with `RecordGhostValid g_out0 r_out0`
and `r_out0 = ⟨none⟩ ∨ r_out0 = r`. -/
theorem dpx_storeStepSeqFree_sub_w4SessStore [LibsignalPlacement] {A : RustAlloc}
    {B : RunBudgets} {F0 : FsFiles} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {r : SessionRecord (List (BitVec 8))} {evs : List AllocEvent}
    (h : StoreStepEnv
      (cliPollSessKitPlaced A F0 scopeKit peer (cliKitStk B))
      (cliPollSessSeqFreeBudgetEnv A F0 peer (cliKitStk B) DeserEnv ReadEnv)
      StoresGhost.opened.sessions peer.val r evs) :
    ∃ (g_out0 : RecordGhost) (r_out0 : SessionRecord (List (BitVec 8))),
      RecordGhostValid g_out0 r_out0 ∧
      (r_out0 = ⟨none⟩ ∨ r_out0 = r) ∧
      W4BinarySessStoreStepEnv peer g_out0 r_out0 evs := by
  have hgv_none : RecordGhostValid ⟨0#64, 0#64, none⟩ ⟨none⟩ := trivial
  rcases h with hbox | ⟨e_box, e_rest, rfl, hbox, hpoll_drop⟩
  · exact ⟨⟨0#64, 0#64, none⟩, ⟨none⟩, hgv_none, Or.inl rfl, Or.inl hbox⟩
  · rcases hpoll_drop with hpoll | ⟨e_poll, e_drop, rfl, hpoll, hdrop⟩
    · rcases hpoll with haddr | ⟨e_addr, e_sp, rfl, haddr, hsp⟩
      · exact ⟨⟨0#64, 0#64, none⟩, ⟨none⟩, hgv_none, Or.inl rfl,
          Or.inr ⟨e_box, e_rest, rfl, hbox, Or.inl (Or.inl haddr)⟩⟩
      · rcases hsp with ⟨g_out0, hgv, hser⟩ | ⟨e_ser, e_put, rfl, ⟨g_out0, hgv, hser⟩, hput⟩
        · exact ⟨g_out0, r, hgv, Or.inr rfl,
            Or.inr ⟨e_box, e_addr ++ e_sp, rfl, hbox,
              Or.inl (Or.inr ⟨e_addr, e_sp, rfl, haddr, Or.inl hser⟩)⟩⟩
        · exact ⟨g_out0, r, hgv, Or.inr rfl,
            Or.inr ⟨e_box, e_addr ++ (e_ser ++ e_put), rfl, hbox,
              Or.inl (Or.inr ⟨e_addr, e_ser ++ e_put, rfl, haddr,
                Or.inr ⟨e_ser, e_put, rfl, hser, hput⟩⟩)⟩⟩
    · have hf_drop : FreeOnlyEvs e_drop := rustDealloc8_freeOnly hdrop
      rcases hpoll with haddr | ⟨e_addr, e_sp, rfl, haddr, hsp⟩
      · exact ⟨⟨0#64, 0#64, none⟩, ⟨none⟩, hgv_none, Or.inl rfl,
          Or.inr ⟨e_box, e_poll ++ e_drop, rfl, hbox,
            Or.inr ⟨e_poll, e_drop, rfl, Or.inl haddr, hf_drop⟩⟩⟩
      · rcases hsp with ⟨g_out0, hgv, hser⟩ | ⟨e_ser, e_put, rfl, ⟨g_out0, hgv, hser⟩, hput⟩
        · exact ⟨g_out0, r, hgv, Or.inr rfl,
            Or.inr ⟨e_box, (e_addr ++ e_sp) ++ e_drop, rfl, hbox,
              Or.inr ⟨e_addr ++ e_sp, e_drop, rfl,
                Or.inr ⟨e_addr, e_sp, rfl, haddr, Or.inl hser⟩, hf_drop⟩⟩⟩
        · exact ⟨g_out0, r, hgv, Or.inr rfl,
            Or.inr ⟨e_box, (e_addr ++ (e_ser ++ e_put)) ++ e_drop, rfl, hbox,
              Or.inr ⟨e_addr ++ (e_ser ++ e_put), e_drop, rfl,
                Or.inr ⟨e_addr, e_ser ++ e_put, rfl, haddr,
                  Or.inr ⟨e_ser, e_put, rfl, hser, hput⟩⟩, hf_drop⟩⟩⟩

/-- `prev1` `store_session` boxed step inclusion at `cliPollSessPrev1SeqFreeBudgetEnv` into
`W4BinarySessStorePrev1StepEnv`. -/
theorem dpx_storePrev1StepSeqFree_sub_w4SessStorePrev1 [LibsignalPlacement] {A : RustAlloc}
    {B : RunBudgets} {F0 : FsFiles} {peer : AddrGhost}
    {G : SessionGhost} {ss : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {evs : List AllocEvent}
    (h : StorePrev1StepEnv
      (cliPollSessPrev1KitPlaced A F0 peer (cliKitStk B))
      (cliPollSessPrev1SeqFreeBudgetEnv A F0 peer (cliKitStk B))
      StoresGhost.opened.sessions peer.val G ss enc evs) :
    W4BinarySessStorePrev1StepEnv peer G ss enc evs :=
  boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h

/-- Stage P4 Path-B (`Matched`) `SeqFree` inclusion into `W4BinaryStageP4MatchedWideEnvAllFixed`. -/
theorem dpx_stageP4MatchedSeqFree_sub_w4StageP4MatchedAllFixed [LibsignalPlacement]
    {A : RustAlloc} {B : RunBudgets} {F0 : FsFiles} {peer : AddrGhost} {remoteIk : IdentityKey}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ss : Session (List (BitVec 8))} {evs : List AllocEvent}
    (h : StageP4MatchedEnv
      (cliPollSessKitPlaced A F0 scopeKit peer (cliKitStk B))
      (cliPollSessSeqFreeBudgetEnv A F0 peer (cliKitStk B) DeserEnv
        (ReadFileRuleEnvFixed cliIo.rd))
      (cliPollIdKitPlaced A F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A F0 peer (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.sessions StoresGhost.opened.identity
      peer.val remoteIk ss evs) :
    ∃ (g_out0 : RecordGhost) (r_out0 : SessionRecord (List (BitVec 8))),
      RecordGhostValid g_out0 r_out0 ∧
      (r_out0 = ⟨none⟩ ∨ r_out0 = ⟨some ss⟩) ∧
      W4BinaryStageP4MatchedWideEnvAllFixed cliIo.rd F0 peer remoteIk g_out0 r_out0 evs := by
  have hgv_none : RecordGhostValid ⟨0#64, 0#64, none⟩ ⟨none⟩ := trivial
  rcases h with hsaveErr | hstore
  · exact ⟨⟨0#64, 0#64, none⟩, ⟨none⟩, hgv_none, Or.inl rfl,
      dpx_seqEnv_optStage_step
        (fun _ hs => dpx_saveStep_sub_w4IdSaveAllFixed hs)
        (fun _ hf => dpx_seqEnv_optStage_nil_left hf) hsaveErr⟩
  · rcases hstore with hsave | ⟨e_save, e_rest, rfl, hsave, hst_free⟩
    · exact ⟨⟨0#64, 0#64, none⟩, ⟨none⟩, hgv_none, Or.inl rfl,
        Or.inl (Or.inr (dpx_saveStep_sub_w4IdSaveAllFixed hsave))⟩
    · rcases hst_free with hst | ⟨e_st, e_free, rfl, hst, hfree⟩
      · obtain ⟨g_out0, r_out0, hgv, hr, hst'⟩ := dpx_storeStepSeqFree_sub_w4SessStore hst
        exact ⟨g_out0, r_out0, hgv, hr,
          Or.inr ⟨e_save, e_rest, rfl, Or.inr (dpx_saveStep_sub_w4IdSaveAllFixed hsave),
            Or.inl (Or.inr hst')⟩⟩
      · obtain ⟨g_out0, r_out0, hgv, hr, hst'⟩ := dpx_storeStepSeqFree_sub_w4SessStore hst
        exact ⟨g_out0, r_out0, hgv, hr,
          Or.inr ⟨e_save, e_st ++ e_free, rfl, Or.inr (dpx_saveStep_sub_w4IdSaveAllFixed hsave),
            Or.inr ⟨e_st, e_free, rfl, Or.inr hst', hfree⟩⟩⟩

/-- Stage P4 Path-A (`0`-prev) `SeqFree` inclusion into `W4BinaryStageP4PathAWideEnvAllFixed`. -/
theorem dpx_stageP4PathASeqFree_sub_w4StageP4PathAAllFixed [LibsignalPlacement]
    {A : RustAlloc} {B : RunBudgets} {F0 : FsFiles} {peer : AddrGhost} {remoteIk : IdentityKey}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {pid₀ kpkId₀ spkId₀ kyberPreKeyId signedPreKeyId : BitVec 32}
    {kbk₀ baseKey : PublicKey} {opkId? : Option (BitVec 32)}
    {ss : Session (List (BitVec 8))} {evs : List AllocEvent}
    (h : StageP4PathAEnv
      (cliPollSessKitPlaced A F0 scopeKit peer (cliKitStk B))
      (cliPollSessSeqFreeBudgetEnv A F0 peer (cliKitStk B) DeserEnv
        (ReadFileRuleEnvFixed cliIo.rd))
      (cliPollIdKitPlaced A F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A F0 peer (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      (cliPollPkKitPlaced A F0 pid₀ (cliKitStk B))
      (cliPollPkBudgetEnv A F0 pid₀ (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      (cliPollKpkKitPlaced A F0 kpkId₀ spkId₀ kbk₀ (cliKitStk B))
      (cliPollKpkBudgetEnv A F0 kpkId₀ spkId₀ kbk₀ (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.sessions StoresGhost.opened.identity
      StoresGhost.opened.oneTime StoresGhost.opened.kyber
      peer.val remoteIk opkId? kyberPreKeyId signedPreKeyId baseKey ss evs) :
    ∃ (g_out0 : RecordGhost) (r_out0 : SessionRecord (List (BitVec 8))),
      RecordGhostValid g_out0 r_out0 ∧
      (r_out0 = ⟨none⟩ ∨ r_out0 = ⟨some ss⟩) ∧
      W4BinaryStageP4PathAWideEnvAllFixed opkId?.isSome cliIo.rd F0 peer remoteIk
        kyberPreKeyId signedPreKeyId (opkId?.getD 0#32) baseKey g_out0 r_out0 evs := by
  have hgv_none : RecordGhostValid ⟨0#64, 0#64, none⟩ ⟨none⟩ := trivial
  rcases h with hsaveErr | hmarkErr | hremErr | hstore
  · exact ⟨⟨0#64, 0#64, none⟩, ⟨none⟩, hgv_none, Or.inl rfl,
      dpx_seqEnv_optStage_step
        (fun _ hs => dpx_saveStep_sub_w4IdSaveAllFixed hs)
        (fun _ hf => dpx_seqEnv_optStage_nil_left
          (dpx_seqEnv_optStage_nil_left (dpx_seqEnv_optStage_nil_left hf)))
        hsaveErr⟩
  · exact ⟨⟨0#64, 0#64, none⟩, ⟨none⟩, hgv_none, Or.inl rfl,
      dpx_seqEnv_optStage_step
        (fun _ hs => dpx_saveStep_sub_w4IdSaveAllFixed hs)
        (fun _ hm => dpx_seqEnv_optStage_step
          (fun _ hmk => dpx_markStep_sub_w4KpkMarkFixed hmk)
          (fun _ hf => dpx_seqEnv_optStage_nil_left (dpx_seqEnv_optStage_nil_left hf)) hm)
        hmarkErr⟩
  · cases opkId? with
    | none => exact False.elim hremErr
    | some opkId =>
      exact ⟨⟨0#64, 0#64, none⟩, ⟨none⟩, hgv_none, Or.inl rfl,
        dpx_seqEnv_optStage_step
          (fun _ hs => dpx_saveStep_sub_w4IdSaveAllFixed hs)
          (fun _ hm => dpx_seqEnv_optStage_step
            (fun _ hmk => dpx_markStep_sub_w4KpkMarkFixed hmk)
            (fun _ hr => dpx_seqEnv_optStage_step
              (fun _ hrm => dpx_removeStep_sub_w4PkRemoveAllFixed hrm)
              (fun _ hf => dpx_seqEnv_optStage_nil_left hf) hr) hm)
          hremErr⟩
  · rcases hstore with hsave | ⟨e_save, e₂, rfl, hsave, h₂⟩
    · exact ⟨⟨0#64, 0#64, none⟩, ⟨none⟩, hgv_none, Or.inl rfl,
        Or.inl (Or.inr (dpx_saveStep_sub_w4IdSaveAllFixed hsave))⟩
    · rcases h₂ with hmark | ⟨e_mark, e₃, rfl, hmark, h₃⟩
      · exact ⟨⟨0#64, 0#64, none⟩, ⟨none⟩, hgv_none, Or.inl rfl,
          Or.inr ⟨e_save, e₂, rfl, Or.inr (dpx_saveStep_sub_w4IdSaveAllFixed hsave),
            Or.inl (Or.inr (dpx_markStep_sub_w4KpkMarkFixed hmark))⟩⟩
      · rcases h₃ with hrem | ⟨e_rem, e₄, rfl, hrem, h₄⟩
        · exact ⟨⟨0#64, 0#64, none⟩, ⟨none⟩, hgv_none, Or.inl rfl,
            Or.inr ⟨e_save, e_mark ++ e₃, rfl, Or.inr (dpx_saveStep_sub_w4IdSaveAllFixed hsave),
              Or.inr ⟨e_mark, e₃, rfl, Or.inr (dpx_markStep_sub_w4KpkMarkFixed hmark),
                Or.inl (dpx_optRemoveStep_sub_w4PkRemoveAllFixed hrem)⟩⟩⟩
        · rcases h₄ with hst | ⟨e_st, e_free, rfl, hst, hfree⟩
          · obtain ⟨g_out0, r_out0, hgv, hr, hst'⟩ := dpx_storeStepSeqFree_sub_w4SessStore hst
            exact ⟨g_out0, r_out0, hgv, hr,
              Or.inr ⟨e_save, e_mark ++ (e_rem ++ e₄), rfl,
                Or.inr (dpx_saveStep_sub_w4IdSaveAllFixed hsave),
                Or.inr ⟨e_mark, e_rem ++ e₄, rfl,
                  Or.inr (dpx_markStep_sub_w4KpkMarkFixed hmark),
                  Or.inr ⟨e_rem, e₄, rfl, dpx_optRemoveStep_sub_w4PkRemoveAllFixed hrem,
                    Or.inl (Or.inr hst')⟩⟩⟩⟩
          · obtain ⟨g_out0, r_out0, hgv, hr, hst'⟩ := dpx_storeStepSeqFree_sub_w4SessStore hst
            exact ⟨g_out0, r_out0, hgv, hr,
              Or.inr ⟨e_save, e_mark ++ (e_rem ++ (e_st ++ e_free)), rfl,
                Or.inr (dpx_saveStep_sub_w4IdSaveAllFixed hsave),
                Or.inr ⟨e_mark, e_rem ++ (e_st ++ e_free), rfl,
                  Or.inr (dpx_markStep_sub_w4KpkMarkFixed hmark),
                  Or.inr ⟨e_rem, e_st ++ e_free, rfl, dpx_optRemoveStep_sub_w4PkRemoveAllFixed hrem,
                    Or.inr ⟨e_st, e_free, rfl, Or.inr hst', hfree⟩⟩⟩⟩⟩

/-- Stage P4 Path-C (`prev1`) `SeqFree` inclusion (`PollOverPathCPlacedBudgetAux.StageP4Prev1Env`
at `cliPollSessPrev1SeqFreeStorePollEnv`, matching `cliPollStageP4Prev1SeqFreeEnvsAux`) into
`W4BinaryStageP4PathCWideEnvAllFixed`. -/
theorem dpx_stageP4Prev1SeqFree_sub_w4StageP4PathCAllFixed [LibsignalPlacement]
    {A : RustAlloc} {B : RunBudgets} {F0 : FsFiles} {peer : AddrGhost} {remoteIk : IdentityKey}
    {pid₀ kpkId₀ spkId₀ kyberPreKeyId signedPreKeyId : BitVec 32}
    {kbk₀ baseKey : PublicKey} {opkId? : Option (BitVec 32)}
    {G : SessionGhost} {ss : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {evs : List AllocEvent}
    (h : StageP4Prev1Env
      (cliPollSessPrev1KitPlaced A F0 peer (cliKitStk B))
      { storePrev1PollEnv := cliPollSessPrev1SeqFreeStorePollEnv }
      (cliPollIdKitPlaced A F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A F0 peer (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      (cliPollPkKitPlaced A F0 pid₀ (cliKitStk B))
      (cliPollPkBudgetEnv A F0 pid₀ (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      (cliPollKpkKitPlaced A F0 kpkId₀ spkId₀ kbk₀ (cliKitStk B))
      (cliPollKpkBudgetEnv A F0 kpkId₀ spkId₀ kbk₀ (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.sessions StoresGhost.opened.identity
      StoresGhost.opened.oneTime StoresGhost.opened.kyber
      peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey opkId? G ss enc evs) :
    W4BinaryStageP4PathCWideEnvAllFixed opkId?.isSome cliIo.rd F0 peer remoteIk
      kyberPreKeyId signedPreKeyId (opkId?.getD 0#32) baseKey G ss enc evs := by
  rcases h with hsaveErr | hmarkErr | hremErr | hstore
  · exact dpx_seqEnv_optStage_step
      (fun _ hs => dpx_saveStep_sub_w4IdSaveAllFixed hs)
      (fun _ hf => dpx_seqEnv_optStage_nil_left
        (dpx_seqEnv_optStage_nil_left (dpx_seqEnv_optStage_nil_left hf)))
      hsaveErr
  · exact dpx_seqEnv_optStage_step
      (fun _ hs => dpx_saveStep_sub_w4IdSaveAllFixed hs)
      (fun _ hm => dpx_seqEnv_optStage_step
        (fun _ hmk =>
          boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) hmk)
        (fun _ hf => dpx_seqEnv_optStage_nil_left (dpx_seqEnv_optStage_nil_left hf)) hm)
      hmarkErr
  · cases opkId? with
    | none => exact False.elim hremErr
    | some opkId =>
      exact dpx_seqEnv_optStage_step
        (fun _ hs => dpx_saveStep_sub_w4IdSaveAllFixed hs)
        (fun _ hm => dpx_seqEnv_optStage_step
          (fun _ hmk =>
            boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) hmk)
          (fun _ hr => dpx_seqEnv_optStage_step
            (fun _ hrm =>
              boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) hrm)
            (fun _ hf => dpx_seqEnv_optStage_nil_left hf) hr) hm)
        hremErr
  · exact dpx_seqEnv_optStage_step
      (fun _ hs => dpx_saveStep_sub_w4IdSaveAllFixed hs)
      (fun _ hm => dpx_seqEnv_optStage_step
        (fun _ hmk =>
          boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) hmk)
        (fun _ hr => dpx_seqEnv_mono
          (fun _ hrm => by
            cases opkId? with
            | none => exact Or.inr hrm
            | some opkId =>
              exact Or.inr
                (boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) hrm))
          (fun _ hst => dpx_seqEnv_optStage_step
            (fun _ hsp =>
              boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) hsp)
            (fun _ hf => hf) hst) hr) hm)
      hstore

/-! ## Stage P2 (`PathA` and `Over` / `PathC`) and Stage P3 non-`VerNe` inclusions -/

/-! ### `dpx_W4BobSessionBuildEnv9`, `dpx_W4OptBoxedStoreStepEnv`, handshake, and archive lemmas -/

private theorem dpx_nonFreeCount_append (a b : List AllocEvent) :
    nonFreeCount (a ++ b) = nonFreeCount a + nonFreeCount b := by
  induction a with
  | nil => simp [nonFreeCount]
  | cons hd tl ih =>
    cases hd <;> simp [nonFreeCount, ih, Nat.add_right_comm]

private theorem dpx_nonFreeCount_eq_zero_of_freeOnly {evs : List AllocEvent}
    (h : FreeOnlyEvs evs) : nonFreeCount evs = 0 := by
  induction evs with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨al, sz, rfl⟩ := h hd List.mem_cons_self
    exact ih (fun e he => h e (List.mem_cons_of_mem _ he))

/-- `initBobSessionBuildEvents` performs `9` allocations (`≤ 68` B) and therefore is NOT contained
in the `6`-op `W4BobSessionBuildEnv`. -/
theorem dpx_not_w4BobSessionBuildEnv_initBobSessionBuildEvents :
    ¬ W4BobSessionBuildEnv initBobSessionBuildEvents := by
  have h9 : nonFreeCount initBobSessionBuildEvents = 9 := by decide
  rintro (⟨h6, _⟩ | ⟨e₁, e₂, heq, ⟨h6, _⟩, hfo⟩)
  · omega
  · have hsum : nonFreeCount (e₁ ++ e₂) = 9 := by rw [← heq, h9]
    rw [dpx_nonFreeCount_append, dpx_nonFreeCount_eq_zero_of_freeOnly hfo] at hsum
    omega

/-- `9`-allocation (`≤ 68` B) responder `SessionState::new` build envelope (`SeqEnv (W4BoundedEvs 9 68) FreeOnlyEvs`). -/
abbrev dpx_W4BobSessionBuildEnv9 : List AllocEvent → Prop :=
  SeqEnv (W4BoundedEvs 9 68) FreeOnlyEvs

theorem dpx_initBobSessionBuildEnv_sub_w4BobSessionBuildEnv9 {evs : List AllocEvent}
    (h : InitBobSessionBuildEnv evs) :
    dpx_W4BobSessionBuildEnv9 evs := by
  rw [h]
  refine Or.inl ?_
  unfold W4BoundedEvs
  decide

/-- Small-regime `PhaseCreditSpec` for `dpx_W4BobSessionBuildEnv9` (`9 * 9675 = 87075` B cum,
`Δlive = 0`, `Δpeak = 0`, `maxReq = 68`). -/
theorem dpx_phaseCredit_w4BobSessionBuildEnv9_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hSmall : 68 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M dpx_W4BobSessionBuildEnv9 87075 0 0 68 :=
  phaseCredit_seq_freeOnly hM (phaseCredit_w4BoundedEvs_small hM 9 68 hSmall)

/-- Optional-box store-step combinator `SeqEnv (OptStageEnv (BoxAllocEnv boxBytes)) inner`. -/
abbrev dpx_W4OptBoxedStoreStepEnv (boxBytes : Nat) (inner : List AllocEvent → Prop) :
    List AllocEvent → Prop :=
  SeqEnv (OptStageEnv (BoxAllocEnv boxBytes)) inner

/-- `SelfKp` store step wrapped with `OptStageEnv (BoxAllocEnv 16)`. -/
abbrev dpx_W4BinarySelfKpStepOptEnvAllFixed (rd : ReadRule) (files : FsFiles) :
    List AllocEvent → Prop :=
  dpx_W4OptBoxedStoreStepEnv 16
    (SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd files
        StoresGhost.opened.identity.own (utf8 "identity-key-pair"))
      (SeqEnv
        (OptIkpTryFromEnv (StoresGhost.opened.identity.own.get rd files (utf8 "identity-key-pair")))
        FreeOnlyEvs))

private theorem dpx_freeOnlyEvs_append {e1 e2 : List AllocEvent}
    (h1 : FreeOnlyEvs e1) (h2 : FreeOnlyEvs e2) : FreeOnlyEvs (e1 ++ e2) := by
  intro ev hev
  rw [List.mem_append] at hev
  rcases hev with hm1 | hm2
  · exact h1 ev hm1
  · exact h2 ev hm2

private theorem dpx_optIkpTryFromEnv_nil
    (gr : Except Unit (List (BitVec 8))) : OptIkpTryFromEnv gr [] := by
  cases gr with
  | ok bs => exact IkpSubEnv.of_cleanup IkpPostCleanupEnv.nil
  | error u => cases u; rfl

private theorem dpx_seq_opt_freeOnly_absorb {D Opt : List AllocEvent → Prop}
    (hOptNil : Opt []) {evs : List AllocEvent}
    (h : SeqEnv (SeqEnv D (SeqEnv Opt FreeOnlyEvs)) FreeOnlyEvs evs) :
    SeqEnv D (SeqEnv Opt FreeOnlyEvs) evs := by
  rcases h with h1 | ⟨e1, ef2, rfl, h1, hf2⟩
  · exact h1
  · rcases h1 with hd | ⟨ed, eof, rfl, hd, hof⟩
    · exact Or.inr ⟨e1, ef2, rfl, hd, Or.inr ⟨[], ef2, (List.nil_append ef2).symm, hOptNil, hf2⟩⟩
    · rcases hof with hopt | ⟨eo, ef1, rfl, hopt, hf1⟩
      · exact Or.inr ⟨ed, eof ++ ef2, by simp only [List.append_assoc], hd,
          Or.inr ⟨eof, ef2, rfl, hopt, hf2⟩⟩
      · exact Or.inr ⟨ed, eo ++ (ef1 ++ ef2), by simp only [List.append_assoc], hd,
          Or.inr ⟨eo, ef1 ++ ef2, rfl, hopt, dpx_freeOnlyEvs_append hf1 hf2⟩⟩

private theorem dpx_cliSelfKpOptBoxed_sub_opt {rd : ReadRule} {files : FsFiles}
    {evs : List AllocEvent}
    (h : dpx_W4OptBoxedStoreStepEnv 16
      (SeqEnv
        (SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd files
            StoresGhost.opened.identity.own (utf8 "identity-key-pair"))
          (SeqEnv
            (OptIkpTryFromEnv
              (StoresGhost.opened.identity.own.get rd files (utf8 "identity-key-pair")))
            FreeOnlyEvs))
        FreeOnlyEvs) evs) :
    dpx_W4BinarySelfKpStepOptEnvAllFixed rd files evs :=
  dpx_seqEnv_mono (fun _ hb => hb)
    (fun _ hi => dpx_seq_opt_freeOnly_absorb (dpx_optIkpTryFromEnv_nil _) hi) h

theorem dpx_w4BinarySelfKpStepAllFixed_sub_opt {rd : ReadRule} {files : FsFiles}
    {evs : List AllocEvent} (h : W4BinarySelfKpStepEnvAllFixed rd files evs) :
    dpx_W4BinarySelfKpStepOptEnvAllFixed rd files evs :=
  h

/-- Block-`79` `AcceptOptFieldsEnv P inp` emits `≤ 6` allocations of `≤ 192` B across all 7
branches. -/
theorem dpx_acceptOptFieldsEnv_sub_w4BoundedEvs {P : Primitives} {inp : AcceptKeysInput}
    {evs : List AllocEvent} (h : AcceptOptFieldsEnv P inp evs) :
    W4BoundedEvs 6 192 evs := by
  rw [h]
  unfold acceptOptFieldsEvents W4BoundedEvs
  dsimp only
  split
  · decide
  · split
    · decide
    · split
      · decide
      · split
        · decide
        · split
          · decide
          · split <;> decide

/-- Block-`79` `AcceptOptFieldsEnv P inp` lands in `W4BinaryAcceptWideEnv x_res hasOpk` for any
`x_res` and `hasOpk`. -/
theorem dpx_acceptOptFieldsEnv_sub_w4AcceptWide {P : Primitives} {inp : AcceptKeysInput}
    (x_res : DoReserveCall) (hasOpk : Bool) {evs : List AllocEvent}
    (h : AcceptOptFieldsEnv P inp evs) :
    W4BinaryAcceptWideEnv x_res hasOpk evs :=
  Or.inr (Or.inl (dpx_acceptOptFieldsEnv_sub_w4BoundedEvs h))

theorem dpx_bobSpqrInitialStateEnv_eq_initialStateEnv (F : ShaCompress) (pqrKey : Bytes) :
    BobSpqrInitialStateEnv F pqrKey = InitialStateEnv F (bobSpqrGhost 0#64 pqrKey) :=
  rfl

/-- `BobBuildEnv`-parametric `W4BinaryInitBobWideEnv`. -/
abbrev dpx_W4BinaryInitBobWideEnvOf (BobBuildEnv : List AllocEvent → Prop)
    (F : ShaCompress) (x_res : DoReserveCall) (hasOpk : Bool)
    (x_spqr : InitialStateGhost) (evs : List AllocEvent) : Prop :=
  SeqEnv (W4BinaryAcceptWideEnv x_res hasOpk)
    (OptStageEnv (SeqEnv (InitialStateEnv F x_spqr) (OptStageEnv BobBuildEnv))) evs

/-- `InitializeBobV1OptFieldsEnv P F inp drKey` inclusion into `dpx_W4BinaryInitBobWideEnvOf`. -/
theorem dpx_initializeBobV1OptFieldsEnv_sub_w4InitBobWideOf
    {BobBuildEnv : List AllocEvent → Prop}
    (hBuild : ∀ e, InitBobSessionBuildEnv e → BobBuildEnv e)
    {P : Primitives} {F : ShaCompress} {inp : AcceptKeysInput} {drKey : DRKey}
    (x_res : DoReserveCall) (hasOpk : Bool) {evs : List AllocEvent}
    (h : InitializeBobV1OptFieldsEnv P F inp drKey evs) :
    dpx_W4BinaryInitBobWideEnvOf BobBuildEnv F x_res hasOpk
      (bobSpqrGhost 0#64 drKey.pqrKey) evs :=
  dpx_seqEnv_mono
    (fun _ ha => dpx_acceptOptFieldsEnv_sub_w4AcceptWide x_res hasOpk ha)
    (fun _ hs => Or.inr (dpx_seqEnv_mono
      (fun _ hi => hi)
      (fun e hb => Or.inr (hBuild e hb)) hs))
    h

theorem dpx_initializeBobV1OptFieldsEnv_sub_w4InitBobWide9
    {P : Primitives} {F : ShaCompress} {inp : AcceptKeysInput} {drKey : DRKey}
    (x_res : DoReserveCall) (hasOpk : Bool) {evs : List AllocEvent}
    (h : InitializeBobV1OptFieldsEnv P F inp drKey evs) :
    dpx_W4BinaryInitBobWideEnvOf dpx_W4BobSessionBuildEnv9 F x_res hasOpk
      (bobSpqrGhost 0#64 drKey.pqrKey) evs :=
  dpx_initializeBobV1OptFieldsEnv_sub_w4InitBobWideOf
    (fun _ hb => dpx_initBobSessionBuildEnv_sub_w4BobSessionBuildEnv9 hb) x_res hasOpk h

/-- `PromoteOverArchiveCanonSessEnv sess` inclusion into `W4BinaryPromoteArchiveEnv g_arch r_arch`
whenever `r_arch.currentSession = some (clearPending sess)`. -/
theorem dpx_promoteOverArchiveCanonSessEnv_sub_w4PromoteArchive
    (g_arch : RecordGhost) {sess : Session (List (BitVec 8))}
    {r_arch : SessionRecord (List (BitVec 8))}
    (hcur : r_arch.currentSession = some (clearPending sess))
    {evs : List AllocEvent} (h : PromoteOverArchiveCanonSessEnv sess evs) :
    W4BinaryPromoteArchiveEnv g_arch r_arch evs := by
  have hlen : (encSession (clearPending sess)).length ≤ (encodeRecord r_arch).length := by
    simp only [encodeRecord, hcur, Option.map_some, msgField, lenField, List.length_append]
    omega
  refine Or.inr ?_
  rcases h with h96 | hnil
  · exact dpx_seqEnv_mono (fun _ hf => hf)
      (fun _ hn => dpx_seqEnv_mono
        (fun _ heq => ⟨(encSession (clearPending sess)).length, hlen, heq⟩)
        (fun _ h9 => dpx_seqEnv_mono
          (fun _ he9 => by rw [he9]; unfold W4BoundedEvs; decide)
          (fun _ hf => hf) h9) hn) h96
  · exact dpx_seqEnv_mono (fun _ hf => hf)
      (fun _ hn => dpx_seqEnv_mono
        (fun _ heq => ⟨(encSession (clearPending sess)).length, hlen, heq⟩)
        (fun _ h0 => dpx_seqEnv_mono
          (fun _ he0 => by rw [he0]; unfold W4BoundedEvs; decide)
          (fun _ hf => hf) h0) hn) hnil

/-! ### Parametric `(KpStepEnv, BobBuildEnv)` Stage-P2 wide envelopes and inclusions -/

/-- `(KpStepEnv, BobBuildEnv)`-parametric Stage P2 Path-A wide envelope. -/
abbrev dpx_W4BinaryStageP2PathAWideEnvAllFixedOf
    (KpStepEnv BobBuildEnv : List AllocEvent → Prop)
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (spkId kpkId opkId : BitVec 32)
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (SeqEnv (W4BoundedEvs 1 33) FreeOnlyEvs))
    (SeqEnv (OptStageEnv (W4BinarySpkGetStepEnvAllFixed rd files spkId))
      (SeqEnv (OptStageEnv (W4BinaryKpkGetStepEnvAllFixed rd files kpkId))
        (SeqEnv (OptStageEnv (SeqEnv KemKeyPairFromPubPrivEnv FreeOnlyEvs))
          (SeqEnv (OptStageEnv (SeqEnv (W4BoundedEvs 1 21) FreeOnlyEvs))
            (SeqEnv (OptStageEnv (if hasOpk then W4BinaryPkGetStepEnvAllFixed rd files opkId else (· = [])))
              (SeqEnv (OptStageEnv KpStepEnv)
                (SeqEnv (OptStageEnv (dpx_W4BinaryInitBobWideEnvOf BobBuildEnv F x_res hasOpk x_spqr))
                  (SeqEnv (OptStageEnv (W4BinarySelfRegIdStepEnvAllFixed rd files))
                    W4ErrTailWideEnv)))))))) evs

/-- `(KpStepEnv, BobBuildEnv)`-parametric Stage P2 Path-C (`Over`) wide envelope. -/
abbrev dpx_W4BinaryStageP2PathCWideEnvAllFixedOf {α : Type}
    (KpStepEnv BobBuildEnv : List AllocEvent → Prop)
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    (CurTrialFailEnv : List AllocEvent → Prop)
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (spkId kpkId opkId : BitVec 32)
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    (evs : List AllocEvent) : Prop :=
  SeqEnv
    (OptStageEnv
      (W4TryDecryptCloneFailWideEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
        (· = dropClonedSessionEvents G_cur st_cur)))
    (SeqEnv (OptStageEnv (IterSeqEnv (ArchivedTrialIterEnv DecEnv TrialEnv DropEnv) xs))
      (SeqEnv (OptStageEnv (SeqEnv (W4BoundedEvs 1 33) FreeOnlyEvs))
        (SeqEnv (OptStageEnv (W4BinarySpkGetStepEnvAllFixed rd files spkId))
          (SeqEnv (OptStageEnv (W4BinaryKpkGetStepEnvAllFixed rd files kpkId))
            (SeqEnv (OptStageEnv (SeqEnv KemKeyPairFromPubPrivEnv FreeOnlyEvs))
              (SeqEnv (OptStageEnv (SeqEnv (W4BoundedEvs 1 21) FreeOnlyEvs))
                (SeqEnv (OptStageEnv (if hasOpk then W4BinaryPkGetStepEnvAllFixed rd files opkId else (· = [])))
                  (SeqEnv (OptStageEnv KpStepEnv)
                    (SeqEnv (OptStageEnv (dpx_W4BinaryInitBobWideEnvOf BobBuildEnv F x_res hasOpk x_spqr))
                      (SeqEnv (OptStageEnv (W4BinarySelfRegIdStepEnvAllFixed rd files))
                        (SeqEnv (OptStageEnv (W4BinaryPromoteArchiveEnv g_arch r_arch))
                          W4ErrTailWideEnv))))))))))) evs

private theorem dpx_seqEnv_opt_tail {A B : List AllocEvent → Prop}
    {ea eb : List AllocEvent} (ha : A ea) (hb : eb = [] ∨ B eb) :
    SeqEnv A B (ea ++ eb) := by
  rcases hb with rfl | hb
  · rw [List.append_nil]; exact Or.inl ha
  · exact Or.inr ⟨ea, eb, rfl, ha, hb⟩

private theorem dpx_pubKey33_dealloc_mem :
    OptStageEnv (SeqEnv (W4BoundedEvs 1 33) FreeOnlyEvs)
      (publicKeySerializeEvents ++ rustDeallocEvents 33 1) := by
  refine Or.inr (Or.inr ⟨publicKeySerializeEvents, rustDeallocEvents 33 1, rfl,
    by unfold W4BoundedEvs; decide, ?_⟩)
  intro ev hev
  simp only [rustDeallocEvents, List.mem_singleton] at hev
  subst hev
  exact ⟨1, 33, rfl⟩

private theorem dpx_box16_mem : BoxAllocEnv 16 (boxAllocEvents 16) :=
  (boxAllocEnv_iff_eq 16 _).mpr rfl

private theorem dpx_p2Sub3TailAlloc_mem (e : List AllocEvent) (h : P2Sub3TailAllocEnv e) :
    W4BoundedEvs 1 21 e := by
  rw [h]
  unfold W4BoundedEvs
  decide

private theorem dpx_chain5_of_parts
    {S1 S2 S3 S4 S5 Tail : List AllocEvent → Prop}
    {e1 e2 e3 e4 e5 et : List AllocEvent}
    (h1 : OptStageEnv S1 e1) (h2 : OptStageEnv S2 e2) (h3 : OptStageEnv S3 e3)
    (h4 : OptStageEnv S4 e4) (h5 : OptStageEnv S5 e5) (ht : et = [] ∨ Tail et) :
    SeqEnv (OptStageEnv S1)
      (SeqEnv (OptStageEnv S2)
        (SeqEnv (OptStageEnv S3)
          (SeqEnv (OptStageEnv S4)
            (SeqEnv (OptStageEnv S5) Tail))))
      ((e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ et) := by
  simp only [List.append_assoc]
  exact dpx_seqEnv_opt_tail h1
    (Or.inr (dpx_seqEnv_opt_tail h2
      (Or.inr (dpx_seqEnv_opt_tail h3
        (Or.inr (dpx_seqEnv_opt_tail h4
          (Or.inr (dpx_seqEnv_opt_tail h5 ht))))))))

private theorem dpx_p2Sub1To3Arm1_decomp {spkPoll : List AllocEvent → Prop}
    {evs : List AllocEvent} (h : P2Sub1To3Arm1Env 16 spkPoll evs) :
    ∃ e1 e2,
      evs = e1 ++ e2 ++ ([] : List AllocEvent) ++ [] ++ [] ∧
      OptStageEnv (SeqEnv (W4BoundedEvs 1 33) FreeOnlyEvs) e1 ∧
      OptStageEnv (W4BoxedStoreStepEnv 16 spkPoll) e2 := by
  rcases h with rfl | ⟨es1, espk, rfl, rfl, hspk⟩
  · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1, boxAllocEvents 16, ?_,
      dpx_pubKey33_dealloc_mem, Or.inr (Or.inl dpx_box16_mem)⟩
    simp only [p2Sub1Events, List.append_nil]
  · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1, boxAllocEvents 16 ++ espk, ?_,
      dpx_pubKey33_dealloc_mem, Or.inr (Or.inr ⟨boxAllocEvents 16, espk, rfl, dpx_box16_mem, hspk⟩)⟩
    simp only [p2Sub1Events, List.append_assoc, List.append_nil]

private theorem dpx_p2Sub1To3Arm2_decomp {spkPoll kpkPoll : List AllocEvent → Prop}
    {evs : List AllocEvent} (h : P2Sub1To3Arm2Env 16 spkPoll 16 kpkPoll evs) :
    ∃ e1 e2 e3,
      evs = e1 ++ e2 ++ e3 ++ ([] : List AllocEvent) ++ [] ∧
      OptStageEnv (SeqEnv (W4BoundedEvs 1 33) FreeOnlyEvs) e1 ∧
      OptStageEnv (W4BoxedStoreStepEnv 16 spkPoll) e2 ∧
      OptStageEnv (W4BoxedStoreStepEnv 16 kpkPoll) e3 := by
  rcases h with rfl | ⟨es1, erest, rfl, rfl, hspk_rest⟩
  · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1, boxAllocEvents 16, [], ?_,
      dpx_pubKey33_dealloc_mem, Or.inr (Or.inl dpx_box16_mem), optStageEnv_nil _⟩
    simp only [p2Sub1Events, List.append_nil]
  · rcases hspk_rest with hspk | ⟨espk, efr_rest, rfl, hspk, hfr_rest⟩
    · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1, boxAllocEvents 16 ++ erest, [], ?_,
        dpx_pubKey33_dealloc_mem,
        Or.inr (Or.inr ⟨boxAllocEvents 16, erest, rfl, dpx_box16_mem, Or.inl hspk⟩),
        optStageEnv_nil _⟩
      simp only [p2Sub1Events, List.append_assoc, List.append_nil]
    · rcases hfr_rest with hfr | ⟨efr, ekpk_all, rfl, hfr, hkpk_all⟩
      · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
          boxAllocEvents 16 ++ (espk ++ efr_rest), [], ?_,
          dpx_pubKey33_dealloc_mem,
          Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr_rest, rfl, dpx_box16_mem,
            Or.inr ⟨espk, efr_rest, rfl, hspk, hfr⟩⟩),
          optStageEnv_nil _⟩
        simp only [p2Sub1Events, List.append_assoc, List.append_nil]
      · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
          boxAllocEvents 16 ++ (espk ++ efr), ekpk_all, ?_,
          dpx_pubKey33_dealloc_mem,
          Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr, rfl, dpx_box16_mem,
            Or.inr ⟨espk, efr, rfl, hspk, hfr⟩⟩),
          Or.inr hkpk_all⟩
        simp only [p2Sub1Events, List.append_assoc, List.append_nil]

private theorem dpx_p2Sub1To3Ok_decomp {spkPoll kpkPoll : List AllocEvent → Prop}
    {evs : List AllocEvent} (h : P2Sub1To3OkEnv 16 spkPoll 16 kpkPoll evs) :
    ∃ e1 e2 e3 e4 e5,
      evs = e1 ++ e2 ++ e3 ++ e4 ++ e5 ∧
      OptStageEnv (SeqEnv (W4BoundedEvs 1 33) FreeOnlyEvs) e1 ∧
      OptStageEnv (W4BoxedStoreStepEnv 16 spkPoll) e2 ∧
      OptStageEnv (W4BoxedStoreStepEnv 16 kpkPoll) e3 ∧
      OptStageEnv (SeqEnv KemKeyPairFromPubPrivEnv FreeOnlyEvs) e4 ∧
      OptStageEnv (SeqEnv (W4BoundedEvs 1 21) FreeOnlyEvs) e5 := by
  rcases h with rfl | ⟨es1, erest, rfl, rfl, hspk_rest⟩
  · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1, boxAllocEvents 16, [], [], [], ?_,
      dpx_pubKey33_dealloc_mem, Or.inr (Or.inl dpx_box16_mem), optStageEnv_nil _,
      optStageEnv_nil _, optStageEnv_nil _⟩
    simp only [p2Sub1Events, List.append_nil]
  · rcases hspk_rest with hspk | ⟨espk, efr1_rest, rfl, hspk, hfr1_rest⟩
    · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
        boxAllocEvents 16 ++ erest, [], [], [], ?_,
        dpx_pubKey33_dealloc_mem,
        Or.inr (Or.inr ⟨boxAllocEvents 16, erest, rfl, dpx_box16_mem, Or.inl hspk⟩),
        optStageEnv_nil _, optStageEnv_nil _, optStageEnv_nil _⟩
      simp only [p2Sub1Events, List.append_assoc, List.append_nil]
    · rcases hfr1_rest with hfr1 | ⟨efr1, ekbox_rest, rfl, hfr1, hkbox_rest⟩
      · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
          boxAllocEvents 16 ++ (espk ++ efr1_rest), [], [], [], ?_,
          dpx_pubKey33_dealloc_mem,
          Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr1_rest, rfl, dpx_box16_mem,
            Or.inr ⟨espk, efr1_rest, rfl, hspk, hfr1⟩⟩),
          optStageEnv_nil _, optStageEnv_nil _, optStageEnv_nil _⟩
        simp only [p2Sub1Events, List.append_assoc, List.append_nil]
      · rcases hkbox_rest with hkbox | ⟨ekbox, ekpk_rest, rfl, hkbox, hkpk_rest⟩
        · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
            boxAllocEvents 16 ++ (espk ++ efr1), ekbox_rest, [], [], ?_,
            dpx_pubKey33_dealloc_mem,
            Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr1, rfl, dpx_box16_mem,
              Or.inr ⟨espk, efr1, rfl, hspk, hfr1⟩⟩),
            Or.inr (Or.inl hkbox), optStageEnv_nil _, optStageEnv_nil _⟩
          simp only [p2Sub1Events, List.append_assoc, List.append_nil]
        · rcases hkpk_rest with hkpk | ⟨ekpk, efr2_rest, rfl, hkpk, hfr2_rest⟩
          · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
              boxAllocEvents 16 ++ (espk ++ efr1), ekbox ++ ekpk_rest, [], [], ?_,
              dpx_pubKey33_dealloc_mem,
              Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr1, rfl, dpx_box16_mem,
                Or.inr ⟨espk, efr1, rfl, hspk, hfr1⟩⟩),
              Or.inr (Or.inr ⟨ekbox, ekpk_rest, rfl, hkbox, Or.inl hkpk⟩),
              optStageEnv_nil _, optStageEnv_nil _⟩
            simp only [p2Sub1Events, List.append_assoc, List.append_nil]
          · rcases hfr2_rest with hfr2 | ⟨efr2, ekem_rest, rfl, hfr2, hkem_rest⟩
            · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
                boxAllocEvents 16 ++ (espk ++ efr1), ekbox ++ (ekpk ++ efr2_rest), [], [], ?_,
                dpx_pubKey33_dealloc_mem,
                Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr1, rfl, dpx_box16_mem,
                  Or.inr ⟨espk, efr1, rfl, hspk, hfr1⟩⟩),
                Or.inr (Or.inr ⟨ekbox, ekpk ++ efr2_rest, rfl, hkbox,
                  Or.inr ⟨ekpk, efr2_rest, rfl, hkpk, hfr2⟩⟩),
                optStageEnv_nil _, optStageEnv_nil _⟩
              simp only [p2Sub1Events, List.append_assoc, List.append_nil]
            · rcases hkem_rest with hkem | ⟨ekem, efr3_rest, rfl, hkem, hfr3_rest⟩
              · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
                  boxAllocEvents 16 ++ (espk ++ efr1), ekbox ++ (ekpk ++ efr2), ekem_rest, [], ?_,
                  dpx_pubKey33_dealloc_mem,
                  Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr1, rfl, dpx_box16_mem,
                    Or.inr ⟨espk, efr1, rfl, hspk, hfr1⟩⟩),
                  Or.inr (Or.inr ⟨ekbox, ekpk ++ efr2, rfl, hkbox,
                    Or.inr ⟨ekpk, efr2, rfl, hkpk, hfr2⟩⟩),
                  Or.inr (Or.inl hkem), optStageEnv_nil _⟩
                simp only [p2Sub1Events, List.append_assoc, List.append_nil]
              · rcases hfr3_rest with hfr3 | ⟨efr3, e21_all, rfl, hfr3, h21_all⟩
                · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
                    boxAllocEvents 16 ++ (espk ++ efr1), ekbox ++ (ekpk ++ efr2),
                    ekem ++ efr3_rest, [], ?_,
                    dpx_pubKey33_dealloc_mem,
                    Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr1, rfl, dpx_box16_mem,
                      Or.inr ⟨espk, efr1, rfl, hspk, hfr1⟩⟩),
                    Or.inr (Or.inr ⟨ekbox, ekpk ++ efr2, rfl, hkbox,
                      Or.inr ⟨ekpk, efr2, rfl, hkpk, hfr2⟩⟩),
                    Or.inr (Or.inr ⟨ekem, efr3_rest, rfl, hkem, hfr3⟩), optStageEnv_nil _⟩
                  simp only [p2Sub1Events, List.append_assoc, List.append_nil]
                · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
                    boxAllocEvents 16 ++ (espk ++ efr1), ekbox ++ (ekpk ++ efr2),
                    ekem ++ efr3, e21_all, ?_,
                    dpx_pubKey33_dealloc_mem,
                    Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr1, rfl, dpx_box16_mem,
                      Or.inr ⟨espk, efr1, rfl, hspk, hfr1⟩⟩),
                    Or.inr (Or.inr ⟨ekbox, ekpk ++ efr2, rfl, hkbox,
                      Or.inr ⟨ekpk, efr2, rfl, hkpk, hfr2⟩⟩),
                    Or.inr (Or.inr ⟨ekem, efr3, rfl, hkem, hfr3⟩),
                    Or.inr (dpx_seqEnv_mono dpx_p2Sub3TailAlloc_mem (fun _ hf => hf) h21_all)⟩
                  simp only [p2Sub1Events, List.append_assoc]

private theorem dpx_p2Sub4Ok_decomp {pkPoll : BitVec 32 → List AllocEvent → Prop}
    {opkId? : Option (BitVec 32)} {e4 : List AllocEvent}
    (h4 : P2Sub4OkEnv 16 pkPoll 16 opkId? e4) :
    ∃ e6 ekp_box,
      e4 = e6 ++ ekp_box ∧
      OptStageEnv
        (if opkId?.isSome then W4BoxedStoreStepEnv 16 (pkPoll (opkId?.getD 0#32)) else (· = []))
        e6 ∧
      OptStageEnv (BoxAllocEnv 16) ekp_box := by
  cases opkId? with
  | none =>
    exact ⟨[], e4, rfl, optStageEnv_nil _, Or.inr ((p2Sub4NoneEnv_iff_boxAllocEnv 16 e4).mp h4)⟩
  | some id =>
    dsimp only [P2Sub4OkEnv, Option.isSome_some, Option.getD_some, ↓reduceIte] at h4 ⊢
    rcases h4 with hpbox | ⟨epbox, epk_rest, rfl, hpbox, hpk_rest⟩
    · exact ⟨e4, [], (List.append_nil _).symm, Or.inr (Or.inl hpbox), optStageEnv_nil _⟩
    · rcases hpk_rest with hpk | ⟨epk, efr_rest, rfl, hpk, hfr_rest⟩
      · exact ⟨epbox ++ epk_rest, [], (List.append_nil _).symm,
          Or.inr (Or.inr ⟨epbox, epk_rest, rfl, hpbox, Or.inl hpk⟩), optStageEnv_nil _⟩
      · rcases hfr_rest with hfr | ⟨efr, ekp_box, rfl, hfr, hkp_box⟩
        · exact ⟨epbox ++ (epk ++ efr_rest), [], (List.append_nil _).symm,
            Or.inr (Or.inr ⟨epbox, epk ++ efr_rest, rfl, hpbox, Or.inr ⟨epk, efr_rest, rfl, hpk, hfr⟩⟩),
            optStageEnv_nil _⟩
        · refine ⟨epbox ++ (epk ++ efr), ekp_box, ?_,
            Or.inr (Or.inr ⟨epbox, epk ++ efr, rfl, hpbox, Or.inr ⟨epk, efr, rfl, hpk, hfr⟩⟩),
            Or.inr hkp_box⟩
          simp only [List.append_assoc]

private theorem dpx_p2Sub1To4Ok_decomp {spkPoll kpkPoll : List AllocEvent → Prop}
    {pkPoll : BitVec 32 → List AllocEvent → Prop}
    {opkId? : Option (BitVec 32)} {e14 : List AllocEvent}
    (h14 : P2Sub1To4OkEnv 16 spkPoll 16 kpkPoll 16 pkPoll 16 opkId? e14) :
    ∃ e1 e2 e3 e4 e5 e6 ekp_box,
      e14 = (e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ e6 ++ ekp_box ∧
      OptStageEnv (SeqEnv (W4BoundedEvs 1 33) FreeOnlyEvs) e1 ∧
      OptStageEnv (W4BoxedStoreStepEnv 16 spkPoll) e2 ∧
      OptStageEnv (W4BoxedStoreStepEnv 16 kpkPoll) e3 ∧
      OptStageEnv (SeqEnv KemKeyPairFromPubPrivEnv FreeOnlyEvs) e4 ∧
      OptStageEnv (SeqEnv (W4BoundedEvs 1 21) FreeOnlyEvs) e5 ∧
      OptStageEnv
        (if opkId?.isSome then W4BoxedStoreStepEnv 16 (pkPoll (opkId?.getD 0#32)) else (· = []))
        e6 ∧
      OptStageEnv (BoxAllocEnv 16) ekp_box := by
  rcases h14 with h13 | ⟨es13, es4, rfl, h13, h4⟩
  · obtain ⟨e1, e2, e3, e4, e5, rfl, he1, he2, he3, he4, he5⟩ := dpx_p2Sub1To3Ok_decomp h13
    refine ⟨e1, e2, e3, e4, e5, [], [], ?_, he1, he2, he3, he4, he5,
      optStageEnv_nil _, optStageEnv_nil _⟩
    simp only [List.append_nil]
  · obtain ⟨e1, e2, e3, e4, e5, rfl, he1, he2, he3, he4, he5⟩ := dpx_p2Sub1To3Ok_decomp h13
    obtain ⟨e6, ekp_box, rfl, he6, hekp⟩ := dpx_p2Sub4Ok_decomp h4
    refine ⟨e1, e2, e3, e4, e5, e6, ekp_box, ?_, he1, he2, he3, he4, he5, he6, hekp⟩
    simp only [List.append_assoc]

private theorem dpx_arm1_to_pathA
    {KpStepEnv BobBuildEnv : List AllocEvent → Prop}
    {rd : ReadRule} {files : FsFiles}
    {spkId : BitVec 32} (kpkId : BitVec 32) (opkId? : Option (BitVec 32))
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    {spkPoll : List AllocEvent → Prop}
    (hspkEq : W4BoxedStoreStepEnv 16 spkPoll = W4BinarySpkGetStepEnvAllFixed rd files spkId)
    {evs : List AllocEvent} (h1 : P2Sub1To3Arm1Env 16 spkPoll evs) :
    dpx_W4BinaryStageP2PathAWideEnvAllFixedOf KpStepEnv BobBuildEnv
      opkId?.isSome rd files spkId kpkId (opkId?.getD 0#32) F x_res x_spqr evs := by
  obtain ⟨e1, e2, heq, he1, he2⟩ := dpx_p2Sub1To3Arm1_decomp h1
  rw [hspkEq] at he2
  have heq' : evs = (e1 ++ e2 ++ [] ++ [] ++ []) ++ [] := by simp only [heq, List.append_nil]
  rw [heq']
  exact dpx_chain5_of_parts he1 he2 (optStageEnv_nil _) (optStageEnv_nil _) (optStageEnv_nil _)
    (Or.inl rfl)

private theorem dpx_arm2_to_pathA
    {KpStepEnv BobBuildEnv : List AllocEvent → Prop}
    {rd : ReadRule} {files : FsFiles}
    {spkId kpkId : BitVec 32} (opkId? : Option (BitVec 32))
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    {spkPoll kpkPoll : List AllocEvent → Prop}
    (hspkEq : W4BoxedStoreStepEnv 16 spkPoll = W4BinarySpkGetStepEnvAllFixed rd files spkId)
    (hkpkEq : W4BoxedStoreStepEnv 16 kpkPoll = W4BinaryKpkGetStepEnvAllFixed rd files kpkId)
    {evs : List AllocEvent} (h2 : P2Sub1To3Arm2Env 16 spkPoll 16 kpkPoll evs) :
    dpx_W4BinaryStageP2PathAWideEnvAllFixedOf KpStepEnv BobBuildEnv
      opkId?.isSome rd files spkId kpkId (opkId?.getD 0#32) F x_res x_spqr evs := by
  obtain ⟨e1, e2, e3, heq, he1, he2, he3⟩ := dpx_p2Sub1To3Arm2_decomp h2
  rw [hspkEq] at he2
  rw [hkpkEq] at he3
  have heq' : evs = (e1 ++ e2 ++ e3 ++ [] ++ []) ++ [] := by simp only [heq, List.append_nil]
  rw [heq']
  exact dpx_chain5_of_parts he1 he2 he3 (optStageEnv_nil _) (optStageEnv_nil _) (Or.inl rfl)

private theorem dpx_arm3_to_pathA
    {KpStepEnv BobBuildEnv : List AllocEvent → Prop}
    {rd : ReadRule} {files : FsFiles}
    {spkId kpkId : BitVec 32} {opkId? : Option (BitVec 32)}
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    {spkPoll kpkPoll : List AllocEvent → Prop}
    {pkPoll : BitVec 32 → List AllocEvent → Prop}
    (hspkEq : W4BoxedStoreStepEnv 16 spkPoll = W4BinarySpkGetStepEnvAllFixed rd files spkId)
    (hkpkEq : W4BoxedStoreStepEnv 16 kpkPoll = W4BinaryKpkGetStepEnvAllFixed rd files kpkId)
    (hpkEq : W4BoxedStoreStepEnv 16 (pkPoll (opkId?.getD 0#32)) =
      W4BinaryPkGetStepEnvAllFixed rd files (opkId?.getD 0#32))
    {evs : List AllocEvent} (h3 : P2Sub1To4Arm3Env 16 spkPoll 16 kpkPoll 16 pkPoll opkId? evs) :
    dpx_W4BinaryStageP2PathAWideEnvAllFixedOf KpStepEnv BobBuildEnv
      opkId?.isSome rd files spkId kpkId (opkId?.getD 0#32) F x_res x_spqr evs := by
  cases opkId? with
  | none => exact False.elim h3
  | some id =>
    dsimp only [P2Sub1To4Arm3Env, Option.isSome_some, Option.getD_some, ↓reduceIte] at h3 hpkEq ⊢
    rcases h3 with h13 | ⟨es13, epk_all, rfl, h13, hpk_all⟩
    · obtain ⟨e1, e2, e3, e4, e5, rfl, he1, he2, he3, he4, he5⟩ := dpx_p2Sub1To3Ok_decomp h13
      rw [hspkEq] at he2
      rw [hkpkEq] at he3
      have hrew : e1 ++ e2 ++ e3 ++ e4 ++ e5 = (e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ [] :=
        (List.append_nil _).symm
      rw [hrew]
      exact dpx_chain5_of_parts he1 he2 he3 he4 he5 (Or.inl rfl)
    · obtain ⟨e1, e2, e3, e4, e5, rfl, he1, he2, he3, he4, he5⟩ := dpx_p2Sub1To3Ok_decomp h13
      rw [hspkEq] at he2
      rw [hkpkEq] at he3
      have hpk_mem : W4BinaryPkGetStepEnvAllFixed rd files id epk_all := by
        rw [← hpkEq]; exact hpk_all
      exact dpx_chain5_of_parts he1 he2 he3 he4 he5
        (Or.inr (Or.inl (Or.inr hpk_mem)))

/-- Arms 1–3 inclusion into `dpx_W4BinaryStageP2PathAWideEnvAllFixedOf` for arbitrary `(KpStepEnv, BobBuildEnv)`. -/
theorem dpx_p2Sub1To4Arms1To3_sub_w4StageP2PathAOf
    {KpStepEnv BobBuildEnv : List AllocEvent → Prop}
    {rd : ReadRule} {files : FsFiles}
    {spkId kpkId : BitVec 32} {opkId? : Option (BitVec 32)}
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    {spkPoll kpkPoll : List AllocEvent → Prop}
    {pkPoll : BitVec 32 → List AllocEvent → Prop}
    (hspkEq : W4BoxedStoreStepEnv 16 spkPoll = W4BinarySpkGetStepEnvAllFixed rd files spkId)
    (hkpkEq : W4BoxedStoreStepEnv 16 kpkPoll = W4BinaryKpkGetStepEnvAllFixed rd files kpkId)
    (hpkEq : W4BoxedStoreStepEnv 16 (pkPoll (opkId?.getD 0#32)) =
      W4BinaryPkGetStepEnvAllFixed rd files (opkId?.getD 0#32))
    {evs : List AllocEvent}
    (h : P2Sub1To3Arm1Env 16 spkPoll evs ∨
      P2Sub1To3Arm2Env 16 spkPoll 16 kpkPoll evs ∨
      P2Sub1To4Arm3Env 16 spkPoll 16 kpkPoll 16 pkPoll opkId? evs) :
    dpx_W4BinaryStageP2PathAWideEnvAllFixedOf KpStepEnv BobBuildEnv
      opkId?.isSome rd files spkId kpkId (opkId?.getD 0#32) F x_res x_spqr evs := by
  rcases h with h1 | h2 | h3
  · exact dpx_arm1_to_pathA kpkId opkId? F x_res x_spqr hspkEq h1
  · exact dpx_arm2_to_pathA opkId? F x_res x_spqr hspkEq hkpkEq h2
  · exact dpx_arm3_to_pathA F x_res x_spqr hspkEq hkpkEq hpkEq h3

private def dpx_dummySpqrGhost : InitialStateGhost :=
  { pA := 0#64
    ret := 0#64
    akPtr := 1#64
    p := { direction := .b2a, version := .v1, minVersion := .v1, authKey := [] } }

private theorem dpx_pathC_wrap_pathA {α : Type}
    {KpStepEnv BobBuildEnv : List AllocEvent → Prop}
    {G_cur : SessionGhost} {st_cur : SessionState (List (BitVec 8))}
    {CurTrialFailEnv : List AllocEvent → Prop}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop} {xs : List α}
    {g_arch : RecordGhost} {r_arch : SessionRecord (List (BitVec 8))}
    {hasOpk : Bool} {rd : ReadRule} {files : FsFiles}
    {spkId kpkId opkId : BitVec 32}
    {F : ShaCompress} {x_res : DoReserveCall} {x_spqr : InitialStateGhost}
    {evs : List AllocEvent}
    (h : dpx_W4BinaryStageP2PathAWideEnvAllFixedOf KpStepEnv BobBuildEnv
      hasOpk rd files spkId kpkId opkId F x_res x_spqr evs) :
    dpx_W4BinaryStageP2PathCWideEnvAllFixedOf KpStepEnv BobBuildEnv
      G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs g_arch r_arch
      hasOpk rd files spkId kpkId opkId F x_res x_spqr evs := by
  refine dpx_seqEnv_optStage_nil_left (dpx_seqEnv_optStage_nil_left ?_)
  exact dpx_seqEnv_mono (fun _ a => a)
    (fun _ x1 => dpx_seqEnv_mono (fun _ a => a)
      (fun _ x2 => dpx_seqEnv_mono (fun _ a => a)
        (fun _ x3 => dpx_seqEnv_mono (fun _ a => a)
          (fun _ x4 => dpx_seqEnv_mono (fun _ a => a)
            (fun _ x5 => dpx_seqEnv_mono (fun _ a => a)
              (fun _ x6 => dpx_seqEnv_mono (fun _ a => a)
                (fun _ x7 => dpx_seqEnv_mono (fun _ a => a)
                  (fun _ x8 => dpx_seqEnv_mono (fun _ a => a)
                    (fun _ xt => dpx_seqEnv_optStage_nil_left xt) x8) x7) x6) x5) x4) x3) x2) x1) h

private theorem dpx_arm4_to_pathA
    {BobBuildEnv : List AllocEvent → Prop}
    {rd : ReadRule} {files : FsFiles}
    {spkId kpkId : BitVec 32} {opkId? : Option (BitVec 32)}
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    {spkPoll kpkPoll kpPoll : List AllocEvent → Prop}
    {pkPoll : BitVec 32 → List AllocEvent → Prop}
    {KpStepEnv : List AllocEvent → Prop}
    (hspkEq : W4BoxedStoreStepEnv 16 spkPoll = W4BinarySpkGetStepEnvAllFixed rd files spkId)
    (hkpkEq : W4BoxedStoreStepEnv 16 kpkPoll = W4BinaryKpkGetStepEnvAllFixed rd files kpkId)
    (hpkEq : W4BoxedStoreStepEnv 16 (pkPoll (opkId?.getD 0#32)) =
      W4BinaryPkGetStepEnvAllFixed rd files (opkId?.getD 0#32))
    (hkpSub : ∀ e, dpx_W4OptBoxedStoreStepEnv 16 (SeqEnv kpPoll FreeOnlyEvs) e → KpStepEnv e)
    {evs : List AllocEvent}
    (h : P2V1Arm4Env 16 spkPoll 16 kpkPoll 16 pkPoll 16 opkId? kpPoll evs) :
    dpx_W4BinaryStageP2PathAWideEnvAllFixedOf KpStepEnv BobBuildEnv
      opkId?.isSome rd files spkId kpkId (opkId?.getD 0#32) F x_res x_spqr evs := by
  rcases h with h14 | ⟨e14, ekp_tail, rfl, h14, hkp_tail⟩
  · obtain ⟨e1, e2, e3, e4, e5, e6, ekp_box, rfl, he1, he2, he3, he4, he5, he6, hekp⟩ :=
      dpx_p2Sub1To4Ok_decomp h14
    rw [hspkEq] at he2; rw [hkpkEq] at he3; rw [hpkEq] at he6
    have hkp_step : OptStageEnv KpStepEnv ekp_box :=
      Or.inr (hkpSub ekp_box (Or.inl hekp))
    rw [List.append_assoc ((e1 ++ e2 ++ e3 ++ e4 ++ e5))]
    exact dpx_chain5_of_parts he1 he2 he3 he4 he5
      (Or.inr (dpx_seqEnv_opt_tail he6 (Or.inr (Or.inl hkp_step))))
  · obtain ⟨e1, e2, e3, e4, e5, e6, ekp_box, rfl, he1, he2, he3, he4, he5, he6, hekp⟩ :=
      dpx_p2Sub1To4Ok_decomp h14
    rw [hspkEq] at he2; rw [hkpkEq] at he3; rw [hpkEq] at he6
    have hkp_step : OptStageEnv KpStepEnv (ekp_box ++ ekp_tail) :=
      Or.inr (hkpSub _ (Or.inr ⟨ekp_box, ekp_tail, rfl, hekp, hkp_tail⟩))
    have hrew : ((e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ e6 ++ ekp_box) ++ ekp_tail =
        (e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ (e6 ++ (ekp_box ++ ekp_tail)) := by
      simp only [List.append_assoc]
    rw [hrew]
    exact dpx_chain5_of_parts he1 he2 he3 he4 he5
      (Or.inr (dpx_seqEnv_opt_tail he6 (Or.inr (Or.inl hkp_step))))

private theorem dpx_arm5_to_pathA
    {BobBuildEnv : List AllocEvent → Prop}
    {rd : ReadRule} {files : FsFiles}
    {spkId kpkId : BitVec 32} {opkId? : Option (BitVec 32)}
    {P : Primitives} {inp : AcceptKeysInput}
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    {spkPoll kpkPoll kpPoll : List AllocEvent → Prop}
    {pkPoll : BitVec 32 → List AllocEvent → Prop}
    {KpStepEnv : List AllocEvent → Prop}
    (hspkEq : W4BoxedStoreStepEnv 16 spkPoll = W4BinarySpkGetStepEnvAllFixed rd files spkId)
    (hkpkEq : W4BoxedStoreStepEnv 16 kpkPoll = W4BinaryKpkGetStepEnvAllFixed rd files kpkId)
    (hpkEq : W4BoxedStoreStepEnv 16 (pkPoll (opkId?.getD 0#32)) =
      W4BinaryPkGetStepEnvAllFixed rd files (opkId?.getD 0#32))
    (hkpSub : ∀ e, dpx_W4OptBoxedStoreStepEnv 16 (SeqEnv kpPoll FreeOnlyEvs) e → KpStepEnv e)
    {evs : List AllocEvent}
    (h : P2V1Arm5EnvOfAcceptErr 16 spkPoll 16 kpkPoll 16 pkPoll 16 opkId?
      kpPoll (AcceptOptFieldsEnv P inp) evs) :
    dpx_W4BinaryStageP2PathAWideEnvAllFixedOf KpStepEnv BobBuildEnv
      opkId?.isSome rd files spkId kpkId (opkId?.getD 0#32) F x_res x_spqr evs := by
  rcases h with h14 | ⟨e14, e_after, rfl, h14, hafter⟩
  · exact dpx_arm4_to_pathA F x_res x_spqr hspkEq hkpkEq hpkEq hkpSub (Or.inl h14)
  · rcases hafter with hkp | ⟨ekp, efr_acc, rfl, hkp, hfr_acc⟩
    · exact dpx_arm4_to_pathA F x_res x_spqr hspkEq hkpkEq hpkEq hkpSub
        (Or.inr ⟨e14, e_after, rfl, h14, Or.inl hkp⟩)
    · rcases hfr_acc with hfr | ⟨efr, eacc_all, rfl, hfr, hacc_all⟩
      · exact dpx_arm4_to_pathA F x_res x_spqr hspkEq hkpkEq hpkEq hkpSub
          (Or.inr ⟨e14, ekp ++ efr_acc, rfl, h14, Or.inr ⟨ekp, efr_acc, rfl, hkp, hfr⟩⟩)
      · obtain ⟨e1, e2, e3, e4, e5, e6, ekp_box, rfl, he1, he2, he3, he4, he5, he6, hekp⟩ :=
          dpx_p2Sub1To4Ok_decomp h14
        rw [hspkEq] at he2; rw [hkpkEq] at he3; rw [hpkEq] at he6
        have hkp_step : OptStageEnv KpStepEnv (ekp_box ++ (ekp ++ efr)) :=
          Or.inr (hkpSub _ (Or.inr ⟨ekp_box, ekp ++ efr, rfl, hekp,
            Or.inr ⟨ekp, efr, rfl, hkp, hfr⟩⟩))
        have hacc_bob :
            OptStageEnv (dpx_W4BinaryInitBobWideEnvOf BobBuildEnv F x_res opkId?.isSome x_spqr)
              eacc_all :=
          Or.inr (Or.inl (Or.inr (dpx_seqEnv_mono
            (fun _ ha => dpx_acceptOptFieldsEnv_sub_w4BoundedEvs ha)
            (fun _ hf => hf) hacc_all)))
        have hrew :
            ((e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ e6 ++ ekp_box) ++ (ekp ++ (efr ++ eacc_all)) =
              (e1 ++ e2 ++ e3 ++ e4 ++ e5) ++
                (e6 ++ ((ekp_box ++ (ekp ++ efr)) ++ eacc_all)) := by
          simp only [List.append_assoc]
        rw [hrew]
        exact dpx_chain5_of_parts he1 he2 he3 he4 he5
          (Or.inr (dpx_seqEnv_opt_tail he6
            (Or.inr (dpx_seqEnv_opt_tail hkp_step (Or.inr (Or.inl hacc_bob))))))

private theorem dpx_arm6OrOk_to_pathA
    {BobBuildEnv : List AllocEvent → Prop}
    {rd : ReadRule} {files : FsFiles}
    {spkId kpkId : BitVec 32} {opkId? : Option (BitVec 32)}
    {F : ShaCompress} (x_res : DoReserveCall) {x_spqr : InitialStateGhost}
    {spkPoll kpkPoll kpPoll regPoll BobForInp : List AllocEvent → Prop}
    {pkPoll : BitVec 32 → List AllocEvent → Prop}
    {KpStepEnv : List AllocEvent → Prop}
    (hspkEq : W4BoxedStoreStepEnv 16 spkPoll = W4BinarySpkGetStepEnvAllFixed rd files spkId)
    (hkpkEq : W4BoxedStoreStepEnv 16 kpkPoll = W4BinaryKpkGetStepEnvAllFixed rd files kpkId)
    (hpkEq : W4BoxedStoreStepEnv 16 (pkPoll (opkId?.getD 0#32)) =
      W4BinaryPkGetStepEnvAllFixed rd files (opkId?.getD 0#32))
    (hregEq : W4BoxedStoreStepEnv 16 regPoll = W4BinarySelfRegIdStepEnvAllFixed rd files)
    (hkpSub : ∀ e, dpx_W4OptBoxedStoreStepEnv 16 (SeqEnv kpPoll FreeOnlyEvs) e → KpStepEnv e)
    (hbobSub : ∀ e, BobForInp e →
      dpx_W4BinaryInitBobWideEnvOf BobBuildEnv F x_res opkId?.isSome x_spqr e)
    {evs : List AllocEvent}
    (h : P2V1OkEnvOfBob 16 spkPoll 16 kpkPoll 16 pkPoll 16 opkId? kpPoll BobForInp 16 regPoll evs) :
    dpx_W4BinaryStageP2PathAWideEnvAllFixedOf KpStepEnv BobBuildEnv
      opkId?.isSome rd files spkId kpkId (opkId?.getD 0#32) F x_res x_spqr evs := by
  rcases h with h14 | ⟨e14, e_after, rfl, h14, hafter⟩
  · exact dpx_arm4_to_pathA F x_res x_spqr hspkEq hkpkEq hpkEq hkpSub (Or.inl h14)
  · rcases hafter with hkp | ⟨ekp, efr_bob, rfl, hkp, hfr_bob⟩
    · exact dpx_arm4_to_pathA F x_res x_spqr hspkEq hkpkEq hpkEq hkpSub
        (Or.inr ⟨e14, e_after, rfl, h14, Or.inl hkp⟩)
    · rcases hfr_bob with hfr | ⟨efr, ebob_reg, rfl, hfr, hbob_reg⟩
      · exact dpx_arm4_to_pathA F x_res x_spqr hspkEq hkpkEq hpkEq hkpSub
          (Or.inr ⟨e14, ekp ++ efr_bob, rfl, h14, Or.inr ⟨ekp, efr_bob, rfl, hkp, hfr⟩⟩)
      · obtain ⟨e1, e2, e3, e4, e5, e6, ekp_box, rfl, he1, he2, he3, he4, he5, he6, hekp⟩ :=
          dpx_p2Sub1To4Ok_decomp h14
        rw [hspkEq] at he2; rw [hkpkEq] at he3; rw [hpkEq] at he6
        have hkp_step : OptStageEnv KpStepEnv (ekp_box ++ (ekp ++ efr)) :=
          Or.inr (hkpSub _ (Or.inr ⟨ekp_box, ekp ++ efr, rfl, hekp,
            Or.inr ⟨ekp, efr, rfl, hkp, hfr⟩⟩))
        rcases hbob_reg with hbob | ⟨ebob, ereg6, rfl, hbob, hreg6⟩
        · have hrew :
              ((e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ e6 ++ ekp_box) ++ (ekp ++ (efr ++ ebob_reg)) =
                (e1 ++ e2 ++ e3 ++ e4 ++ e5) ++
                  (e6 ++ ((ekp_box ++ (ekp ++ efr)) ++ ebob_reg)) := by
            simp only [List.append_assoc]
          rw [hrew]
          exact dpx_chain5_of_parts he1 he2 he3 he4 he5
            (Or.inr (dpx_seqEnv_opt_tail he6
              (Or.inr (dpx_seqEnv_opt_tail hkp_step
                (Or.inr (Or.inl (Or.inr (hbobSub _ hbob))))))))
        · have hreg_mem : W4BinarySelfRegIdStepEnvAllFixed rd files ereg6 := by
            rw [← hregEq]; exact hreg6
          have hrew :
              ((e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ e6 ++ ekp_box) ++
                  (ekp ++ (efr ++ (ebob ++ ereg6))) =
                (e1 ++ e2 ++ e3 ++ e4 ++ e5) ++
                  (e6 ++ ((ekp_box ++ (ekp ++ efr)) ++ (ebob ++ ereg6))) := by
            simp only [List.append_assoc]
          rw [hrew]
          exact dpx_chain5_of_parts he1 he2 he3 he4 he5
            (Or.inr (dpx_seqEnv_opt_tail he6
              (Or.inr (dpx_seqEnv_opt_tail hkp_step
                (Or.inr (dpx_seqEnv_opt_tail (Or.inr (hbobSub _ hbob))
                  (Or.inr (Or.inl (Or.inr hreg_mem)))))))))

/-- Stage P2 Path-A error-envelope (`dpx_p2PathAErrEnv`) inclusion into `dpx_W4BinaryStageP2PathAWideEnvAllFixedOf`. -/
theorem dpx_p2PathAErrEnv_sub_w4StageP2PathAOf [LibsignalPlacement]
    {A : RustAlloc} {X : UnreachedPqxdhPrimitives} {W : CliHooks} {g : DecPkGhost}
    {KpStepEnv BobBuildEnv : List AllocEvent → Prop}
    (hkpSub : ∀ e, dpx_W4BinarySelfKpStepOptEnvAllFixed cliIo.rd g.F e → KpStepEnv e)
    (hBuild : ∀ e, InitBobSessionBuildEnv e → BobBuildEnv e)
    (x_res : DoReserveCall) {evs : List AllocEvent}
    (h : dpx_p2PathAErrEnv A X W g evs) :
    ∃ (m : PreKeyMessageFields) (x_spqr : InitialStateGhost),
      pkToE? g.msg = some m ∧
      x_spqr.p.version = .v1 ∧
      x_spqr.p.authKey.length ≤ 32 ∧
      dpx_W4BinaryStageP2PathAWideEnvAllFixedOf KpStepEnv BobBuildEnv
        m.opkId.isSome cliIo.rd g.F m.spkId m.kpkId (m.opkId.getD 0#32)
        W.C.F x_res x_spqr evs := by
  have hkpSub' : ∀ e,
      dpx_W4OptBoxedStoreStepEnv 16
        (SeqEnv
          (SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd g.F
              StoresGhost.opened.identity.own (utf8 "identity-key-pair"))
            (SeqEnv
              (OptIkpTryFromEnv
                (StoresGhost.opened.identity.own.get cliIo.rd g.F (utf8 "identity-key-pair")))
              FreeOnlyEvs))
          FreeOnlyEvs) e → KpStepEnv e :=
    fun e hx => hkpSub e (dpx_cliSelfKpOptBoxed_sub_opt hx)
  unfold dpx_p2PathAErrEnv cliP2PathAOptFieldsErrEnv P2PathAErrEnvOf at h
  cases hm : pkToE? g.msg with
  | none => rw [hm] at h; exact False.elim h
  | some m =>
    rw [hm] at h
    dsimp only at h
    rw [hdrOpkIdBv?_mkPathAHdr] at h
    have h123_or : _ := h
    rcases h123_or with h1 | h2 | h3 | h4 | h56
    · exact ⟨m, dpx_dummySpqrGhost, rfl, rfl, by decide,
        dpx_arm1_to_pathA m.kpkId m.opkId W.C.F x_res dpx_dummySpqrGhost rfl h1⟩
    · exact ⟨m, dpx_dummySpqrGhost, rfl, rfl, by decide,
        dpx_arm2_to_pathA m.opkId W.C.F x_res dpx_dummySpqrGhost rfl rfl h2⟩
    · exact ⟨m, dpx_dummySpqrGhost, rfl, rfl, by decide,
        dpx_arm3_to_pathA W.C.F x_res dpx_dummySpqrGhost rfl rfl rfl h3⟩
    · exact ⟨m, dpx_dummySpqrGhost, rfl, rfl, by decide,
        dpx_arm4_to_pathA W.C.F x_res dpx_dummySpqrGhost rfl rfl rfl hkpSub' h4⟩
    · cases hk : pkStoreKeys g.F m with
      | none => rw [hk] at h56; exact False.elim h56
      | some k =>
        rw [hk] at h56
        cases hkp : StoresGhost.opened.identity.keyPair cliIo.rd g.F with
        | error _ => rw [hkp] at h56; exact False.elim h56
        | ok kp =>
          rw [hkp] at h56
          dsimp only at h56
          rcases h56 with h5 | h6
          · exact ⟨m, dpx_dummySpqrGhost, rfl, rfl, by decide,
              dpx_arm5_to_pathA W.C.F x_res dpx_dummySpqrGhost rfl rfl rfl hkpSub' h5⟩
          · cases hacc : acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
              (ofSignalPqxdhAcceptKeysInput
                (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)) with
            | none => rw [hacc] at h6; exact False.elim h6
            | some drKey =>
              rw [hacc] at h6
              dsimp only at h6
              have hlen32 : (bobSpqrGhost 0#64 drKey.pqrKey).p.authKey.length ≤ 32 := by
                have hsz :=
                  (acceptKeys_some_lengths
                    (structuralPrims_initiatorModelPrims X ⟨W.C, W.Q⟩) hacc).2.1
                dsimp only [bobSpqrGhost, bobSpqrParams, bytesToBv8]
                rw [List.length_map]
                omega
              exact ⟨m, bobSpqrGhost 0#64 drKey.pqrKey, rfl, rfl, hlen32,
                dpx_arm6OrOk_to_pathA x_res rfl rfl rfl rfl hkpSub'
                  (fun _ hb =>
                    dpx_initializeBobV1OptFieldsEnv_sub_w4InitBobWideOf hBuild x_res _ hb)
                  (show P2V1OkEnvOfBob _ _ _ _ _ _ _ _ _ _ _ _ _ from h6)⟩

theorem dpx_p2PathAErrEnv_sub_w4StageP2PathAFull9 [LibsignalPlacement]
    {A : RustAlloc} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    (x_res : DoReserveCall) {g : DecPkGhost} {evs : List AllocEvent}
    (h : dpx_p2PathAErrEnv A X W g evs) :
    ∃ (m : PreKeyMessageFields) (x_spqr : InitialStateGhost),
      pkToE? g.msg = some m ∧
      x_spqr.p.version = .v1 ∧
      x_spqr.p.authKey.length ≤ 32 ∧
      dpx_W4BinaryStageP2PathAWideEnvAllFixedOf
        (dpx_W4BinarySelfKpStepOptEnvAllFixed cliIo.rd g.F) dpx_W4BobSessionBuildEnv9
        m.opkId.isSome cliIo.rd g.F m.spkId m.kpkId (m.opkId.getD 0#32)
        W.C.F x_res x_spqr evs :=
  dpx_p2PathAErrEnv_sub_w4StageP2PathAOf (fun _ hx => hx)
    (fun _ hb => dpx_initBobSessionBuildEnv_sub_w4BobSessionBuildEnv9 hb) x_res h

/-- Stage P2 Path-A normal-exit (`dpx_p2PathAOkEnv`) inclusion into `dpx_W4BinaryStageP2PathAWideEnvAllFixedOf`. -/
theorem dpx_p2PathAOkEnv_sub_w4StageP2PathAOf [LibsignalPlacement]
    {A : RustAlloc} {X : UnreachedPqxdhPrimitives} {W : CliHooks} {g : DecPkGhost}
    {KpStepEnv BobBuildEnv : List AllocEvent → Prop}
    (hkpSub : ∀ e, dpx_W4BinarySelfKpStepOptEnvAllFixed cliIo.rd g.F e → KpStepEnv e)
    (hBuild : ∀ e, InitBobSessionBuildEnv e → BobBuildEnv e)
    (x_res : DoReserveCall) {evs : List AllocEvent}
    (h : dpx_p2PathAOkEnv A X W g evs) :
    ∃ (m : PreKeyMessageFields) (x_spqr : InitialStateGhost),
      pkToE? g.msg = some m ∧
      x_spqr.p.version = .v1 ∧
      x_spqr.p.authKey.length ≤ 32 ∧
      dpx_W4BinaryStageP2PathAWideEnvAllFixedOf KpStepEnv BobBuildEnv
        m.opkId.isSome cliIo.rd g.F m.spkId m.kpkId (m.opkId.getD 0#32)
        W.C.F x_res x_spqr evs := by
  have hkpSub' : ∀ e,
      dpx_W4OptBoxedStoreStepEnv 16
        (SeqEnv
          (SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd g.F
              StoresGhost.opened.identity.own (utf8 "identity-key-pair"))
            (SeqEnv
              (OptIkpTryFromEnv
                (StoresGhost.opened.identity.own.get cliIo.rd g.F (utf8 "identity-key-pair")))
              FreeOnlyEvs))
          FreeOnlyEvs) e → KpStepEnv e :=
    fun e hx => hkpSub e (dpx_cliSelfKpOptBoxed_sub_opt hx)
  unfold dpx_p2PathAOkEnv cliP2PathAOptFieldsOkEnv P2PathAOkEnvOf at h
  cases hm : pkToE? g.msg with
  | none => rw [hm] at h; exact False.elim h
  | some m =>
    rw [hm] at h
    dsimp only at h
    cases hk : pkStoreKeys g.F m with
    | none => rw [hk] at h; exact False.elim h
    | some k =>
      rw [hk] at h
      cases hkp : StoresGhost.opened.identity.keyPair cliIo.rd g.F with
      | error _ => rw [hkp] at h; exact False.elim h
      | ok kp =>
        rw [hkp] at h
        dsimp only at h
        cases hacc : acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
            (ofSignalPqxdhAcceptKeysInput
              (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)) with
        | none => rw [hacc] at h; exact False.elim h
        | some drKey =>
          rw [hacc] at h
          dsimp only at h
          rw [hdrOpkIdBv?_mkPathAHdr] at h
          have hlen32 : (bobSpqrGhost 0#64 drKey.pqrKey).p.authKey.length ≤ 32 := by
            have hsz :=
              (acceptKeys_some_lengths
                (structuralPrims_initiatorModelPrims X ⟨W.C, W.Q⟩) hacc).2.1
            dsimp only [bobSpqrGhost, bobSpqrParams, bytesToBv8]
            rw [List.length_map]
            omega
          exact ⟨m, bobSpqrGhost 0#64 drKey.pqrKey, rfl, rfl, hlen32,
            dpx_arm6OrOk_to_pathA x_res rfl rfl rfl rfl hkpSub'
              (fun _ hb =>
                dpx_initializeBobV1OptFieldsEnv_sub_w4InitBobWideOf hBuild x_res _ hb)
              h⟩

theorem dpx_p2PathAOkEnv_sub_w4StageP2PathAFull9 [LibsignalPlacement]
    {A : RustAlloc} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    (x_res : DoReserveCall) {g : DecPkGhost} {evs : List AllocEvent}
    (h : dpx_p2PathAOkEnv A X W g evs) :
    ∃ (m : PreKeyMessageFields) (x_spqr : InitialStateGhost),
      pkToE? g.msg = some m ∧
      x_spqr.p.version = .v1 ∧
      x_spqr.p.authKey.length ≤ 32 ∧
      dpx_W4BinaryStageP2PathAWideEnvAllFixedOf
        (dpx_W4BinarySelfKpStepOptEnvAllFixed cliIo.rd g.F) dpx_W4BobSessionBuildEnv9
        m.opkId.isSome cliIo.rd g.F m.spkId m.kpkId (m.opkId.getD 0#32)
        W.C.F x_res x_spqr evs :=
  dpx_p2PathAOkEnv_sub_w4StageP2PathAOf (fun _ hx => hx)
    (fun _ hb => dpx_initBobSessionBuildEnv_sub_w4BobSessionBuildEnv9 hb) x_res h

/-- Stage P2 Path-C (`Over`) error-envelope (`dpx_p2OverErrEnv`) inclusion into `dpx_W4BinaryStageP2PathCWideEnvAllFixedOf`. -/
theorem dpx_p2OverErrEnv_sub_w4StageP2PathCOf [LibsignalPlacement] {α : Type}
    {A : RustAlloc} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {g : DecPkGhost} {r : SessionRecord (List (BitVec 8))}
    {KpStepEnv BobBuildEnv : List AllocEvent → Prop}
    (hkpSub : ∀ e, dpx_W4BinarySelfKpStepOptEnvAllFixed cliIo.rd g.F e → KpStepEnv e)
    (hBuild : ∀ e, InitBobSessionBuildEnv e → BobBuildEnv e)
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    (CurTrialFailEnv : List AllocEvent → Prop)
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (x_res : DoReserveCall) {evs : List AllocEvent}
    (h : dpx_p2OverErrEnv A X W g r evs) :
    ∃ (m : PreKeyMessageFields) (x_spqr : InitialStateGhost),
      pkToE? g.msg = some m ∧
      x_spqr.p.version = .v1 ∧
      x_spqr.p.authKey.length ≤ 32 ∧
      dpx_W4BinaryStageP2PathCWideEnvAllFixedOf KpStepEnv BobBuildEnv
        G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs g_arch r_arch
        m.opkId.isSome cliIo.rd g.F m.spkId m.kpkId (m.opkId.getD 0#32)
        W.C.F x_res x_spqr evs := by
  have hA : dpx_p2PathAErrEnv A X W g evs := h
  obtain ⟨m, x_spqr, hm, hver, hlen, hpA⟩ :=
    dpx_p2PathAErrEnv_sub_w4StageP2PathAOf hkpSub hBuild x_res hA
  exact ⟨m, x_spqr, hm, hver, hlen, dpx_pathC_wrap_pathA hpA⟩

theorem dpx_p2OverErrEnv_sub_w4StageP2PathCFull9 [LibsignalPlacement] {α : Type}
    {A : RustAlloc} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    (CurTrialFailEnv : List AllocEvent → Prop)
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (x_res : DoReserveCall) {g : DecPkGhost} {r : SessionRecord (List (BitVec 8))}
    {evs : List AllocEvent}
    (h : dpx_p2OverErrEnv A X W g r evs) :
    ∃ (m : PreKeyMessageFields) (x_spqr : InitialStateGhost),
      pkToE? g.msg = some m ∧
      x_spqr.p.version = .v1 ∧
      x_spqr.p.authKey.length ≤ 32 ∧
      dpx_W4BinaryStageP2PathCWideEnvAllFixedOf
        (dpx_W4BinarySelfKpStepOptEnvAllFixed cliIo.rd g.F) dpx_W4BobSessionBuildEnv9
        G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs g_arch r_arch
        m.opkId.isSome cliIo.rd g.F m.spkId m.kpkId (m.opkId.getD 0#32)
        W.C.F x_res x_spqr evs :=
  dpx_p2OverErrEnv_sub_w4StageP2PathCOf (fun _ hx => hx)
    (fun _ hb => dpx_initBobSessionBuildEnv_sub_w4BobSessionBuildEnv9 hb)
    G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs g_arch r_arch x_res h

private theorem dpx_overEnd_dealloc_freeOnly :
    FreeOnlyEvs (rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1) := by
  intro ev hev
  simp only [rustDeallocEvents, List.mem_append, List.mem_singleton] at hev
  rcases hev with rfl | rfl
  · exact ⟨1, 1568, rfl⟩
  · exact ⟨1, 3168, rfl⟩

/-- Stage P2 Path-C (`Over`) normal-exit (`dpx_p2OverOkEnv`) inclusion into `dpx_W4BinaryStageP2PathCWideEnvAllFixedOf`. -/
theorem dpx_p2OverOkEnv_sub_w4StageP2PathCOf [LibsignalPlacement] {α : Type}
    {A : RustAlloc} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {g : DecPkGhost} {r : SessionRecord (List (BitVec 8))}
    {KpStepEnv BobBuildEnv : List AllocEvent → Prop}
    (hkpSub : ∀ e, dpx_W4BinarySelfKpStepOptEnvAllFixed cliIo.rd g.F e → KpStepEnv e)
    (hBuild : ∀ e, InitBobSessionBuildEnv e → BobBuildEnv e)
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    (CurTrialFailEnv : List AllocEvent → Prop)
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (x_res : DoReserveCall)
    {evs : List AllocEvent}
    (h : dpx_p2OverOkEnv A X W g r evs) :
    ∃ (m : PreKeyMessageFields) (sess : Session (List (BitVec 8))) (x_spqr : InitialStateGhost),
      pkToE? g.msg = some m ∧
      r.currentSession = some sess ∧
      x_spqr.p.version = .v1 ∧
      x_spqr.p.authKey.length ≤ 32 ∧
      ∀ r_arch : SessionRecord (List (BitVec 8)),
        r_arch.currentSession = some (clearPending sess) →
        dpx_W4BinaryStageP2PathCWideEnvAllFixedOf KpStepEnv BobBuildEnv
          G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs g_arch r_arch
          m.opkId.isSome cliIo.rd g.F m.spkId m.kpkId (m.opkId.getD 0#32)
          W.C.F x_res x_spqr evs := by
  have hkpSub' : ∀ e,
      dpx_W4OptBoxedStoreStepEnv 16
        (SeqEnv
          (SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd g.F
              StoresGhost.opened.identity.own (utf8 "identity-key-pair"))
            (SeqEnv
              (OptIkpTryFromEnv
                (StoresGhost.opened.identity.own.get cliIo.rd g.F (utf8 "identity-key-pair")))
              FreeOnlyEvs))
          FreeOnlyEvs) e → KpStepEnv e :=
    fun e hx => hkpSub e (dpx_cliSelfKpOptBoxed_sub_opt hx)
  unfold dpx_p2OverOkEnv P2OverPathCOkEnvOf at h
  cases hm : pkToE? g.msg with
  | none => rw [hm] at h; exact False.elim h
  | some m =>
    rw [hm] at h
    dsimp only at h
    cases hcur : r.currentSession with
    | none => rw [hcur] at h; exact False.elim h
    | some sess =>
      rw [hcur] at h
      dsimp only at h
      cases hk : pkStoreKeys g.F m with
      | none => rw [hk] at h; exact False.elim h
      | some k =>
        rw [hk] at h
        cases hkp : StoresGhost.opened.identity.keyPair cliIo.rd g.F with
        | error _ => rw [hkp] at h; exact False.elim h
        | ok kp =>
          rw [hkp] at h
          dsimp only at h
          cases hacc : acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
              (ofSignalPqxdhAcceptKeysInput
                (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)) with
          | none => rw [hacc] at h; exact False.elim h
          | some drKey =>
            rw [hacc] at h
            dsimp only at h
            rw [hdrOpkIdBv?_mkPathAHdr] at h
            have hlen32 : (bobSpqrGhost 0#64 drKey.pqrKey).p.authKey.length ≤ 32 := by
              have hsz :=
                (acceptKeys_some_lengths
                  (structuralPrims_initiatorModelPrims X ⟨W.C, W.Q⟩) hacc).2.1
              dsimp only [bobSpqrGhost, bobSpqrParams, bytesToBv8]
              rw [List.length_map]
              omega
            refine ⟨m, sess, bobSpqrGhost 0#64 drKey.pqrKey, rfl, rfl, rfl, hlen32, ?_⟩
            intro r_arch hr_arch
            rcases h with h14 | ⟨e14, e_after, rfl, h14, hafter⟩
            · exact dpx_pathC_wrap_pathA
                (dpx_arm4_to_pathA W.C.F x_res (bobSpqrGhost 0#64 drKey.pqrKey)
                  rfl rfl rfl hkpSub' (Or.inl h14))
            · rcases hafter with hkp' | ⟨ekp, efr_bob, rfl, hkp', hfr_bob⟩
              · exact dpx_pathC_wrap_pathA
                  (dpx_arm4_to_pathA W.C.F x_res (bobSpqrGhost 0#64 drKey.pqrKey)
                    rfl rfl rfl hkpSub' (Or.inr ⟨e14, e_after, rfl, h14, Or.inl hkp'⟩))
              · rcases hfr_bob with hfr | ⟨efr, ebob_reg, rfl, hfr, hbob_reg⟩
                · exact dpx_pathC_wrap_pathA
                    (dpx_arm4_to_pathA W.C.F x_res (bobSpqrGhost 0#64 drKey.pqrKey)
                      rfl rfl rfl hkpSub'
                      (Or.inr ⟨e14, ekp ++ efr_bob, rfl, h14, Or.inr ⟨ekp, efr_bob, rfl, hkp', hfr⟩⟩))
                · rcases hbob_reg with hbob | ⟨ebob, ereg_all, rfl, hbob, hreg_all⟩
                  · exact dpx_pathC_wrap_pathA
                      (dpx_arm6OrOk_to_pathA x_res rfl rfl rfl rfl hkpSub'
                        (fun _ hb =>
                          dpx_initializeBobV1OptFieldsEnv_sub_w4InitBobWideOf hBuild x_res _ hb)
                        (Or.inr ⟨e14, ekp ++ (efr ++ ebob_reg), rfl, h14,
                          Or.inr ⟨ekp, efr ++ ebob_reg, rfl, hkp',
                            Or.inr ⟨efr, ebob_reg, rfl, hfr, Or.inl hbob⟩⟩⟩))
                  · rcases hreg_all with hrbox | ⟨erbox, erpoll_tail, rfl, hrbox, hrpoll_tail⟩
                    · exact dpx_pathC_wrap_pathA
                        (dpx_arm6OrOk_to_pathA x_res rfl rfl rfl rfl hkpSub'
                          (fun _ hb =>
                            dpx_initializeBobV1OptFieldsEnv_sub_w4InitBobWideOf hBuild x_res _ hb)
                          (Or.inr ⟨e14, ekp ++ (efr ++ (ebob ++ ereg_all)), rfl, h14,
                            Or.inr ⟨ekp, efr ++ (ebob ++ ereg_all), rfl, hkp',
                              Or.inr ⟨efr, ebob ++ ereg_all, rfl, hfr,
                                Or.inr ⟨ebob, ereg_all, rfl, hbob, Or.inl hrbox⟩⟩⟩⟩))
                    · rcases hrpoll_tail with hrpoll | ⟨erpoll, eprom_tail, rfl, hrpoll, hprom_tail⟩
                      · exact dpx_pathC_wrap_pathA
                          (dpx_arm6OrOk_to_pathA x_res rfl rfl rfl rfl hkpSub'
                            (fun _ hb =>
                              dpx_initializeBobV1OptFieldsEnv_sub_w4InitBobWideOf hBuild x_res _ hb)
                            (Or.inr ⟨e14, ekp ++ (efr ++ (ebob ++ (erbox ++ erpoll_tail))), rfl, h14,
                              Or.inr ⟨ekp, efr ++ (ebob ++ (erbox ++ erpoll_tail)), rfl, hkp',
                                Or.inr ⟨efr, ebob ++ (erbox ++ erpoll_tail), rfl, hfr,
                                  Or.inr ⟨ebob, erbox ++ erpoll_tail, rfl, hbob,
                                    Or.inr ⟨erbox, erpoll_tail, rfl, hrbox, Or.inl hrpoll⟩⟩⟩⟩⟩))
                      · rcases hprom_tail with rfl | ⟨ed16, eprom_end, rfl, rfl, hprom_end⟩
                        · exact dpx_pathC_wrap_pathA
                            (dpx_arm6OrOk_to_pathA x_res rfl rfl rfl rfl hkpSub'
                              (fun _ hb =>
                                dpx_initializeBobV1OptFieldsEnv_sub_w4InitBobWideOf hBuild x_res _ hb)
                              (Or.inr ⟨e14,
                                ekp ++ (efr ++ (ebob ++ (erbox ++ (erpoll ++ rustDeallocEvents 16 8)))),
                                rfl, h14,
                                Or.inr ⟨ekp,
                                  efr ++ (ebob ++ (erbox ++ (erpoll ++ rustDeallocEvents 16 8))),
                                  rfl, hkp',
                                  Or.inr ⟨efr,
                                    ebob ++ (erbox ++ (erpoll ++ rustDeallocEvents 16 8)),
                                    rfl, hfr,
                                    Or.inr ⟨ebob,
                                      erbox ++ (erpoll ++ rustDeallocEvents 16 8),
                                      rfl, hbob,
                                      Or.inr ⟨erbox, erpoll ++ rustDeallocEvents 16 8, rfl, hrbox,
                                        Or.inr ⟨erpoll, rustDeallocEvents 16 8, rfl, hrpoll,
                                          rustDealloc8_freeOnly rfl⟩⟩⟩⟩⟩⟩))
                        · obtain ⟨e1, e2, e3, e4, e5, e6, ekp_box, rfl,
                            he1, he2, he3, he4, he5, he6, hekp⟩ := dpx_p2Sub1To4Ok_decomp h14
                          have hkp_step : OptStageEnv KpStepEnv (ekp_box ++ (ekp ++ efr)) :=
                            Or.inr (hkpSub' _ (Or.inr ⟨ekp_box, ekp ++ efr, rfl, hekp,
                              Or.inr ⟨ekp, efr, rfl, hkp', hfr⟩⟩))
                          have hbob_mem :
                              OptStageEnv (dpx_W4BinaryInitBobWideEnvOf BobBuildEnv W.C.F x_res
                                m.opkId.isSome (bobSpqrGhost 0#64 drKey.pqrKey)) ebob :=
                            Or.inr (dpx_initializeBobV1OptFieldsEnv_sub_w4InitBobWideOf hBuild
                              x_res _ hbob)
                          have hreg_mem :
                              OptStageEnv (W4BinarySelfRegIdStepEnvAllFixed cliIo.rd g.F)
                                (erbox ++ (erpoll ++ rustDeallocEvents 16 8)) :=
                            Or.inr (Or.inr ⟨erbox, erpoll ++ rustDeallocEvents 16 8, rfl, hrbox,
                              Or.inr ⟨erpoll, rustDeallocEvents 16 8, rfl, hrpoll,
                                rustDealloc8_freeOnly rfl⟩⟩)
                          have hprom_mem :
                              SeqEnv (OptStageEnv (W4BinaryPromoteArchiveEnv g_arch r_arch))
                                W4ErrTailWideEnv eprom_end := by
                            rcases hprom_end with hp | ⟨ep, ed_end, rfl, hp, rfl⟩
                            · exact Or.inl (Or.inr
                                (dpx_promoteOverArchiveCanonSessEnv_sub_w4PromoteArchive
                                  g_arch hr_arch hp))
                            · exact Or.inr ⟨ep, rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1,
                                rfl,
                                Or.inr (dpx_promoteOverArchiveCanonSessEnv_sub_w4PromoteArchive
                                  g_arch hr_arch hp),
                                w4ErrTailWideEnv_of_freeOnly dpx_overEnd_dealloc_freeOnly⟩
                          refine dpx_seqEnv_optStage_nil_left (dpx_seqEnv_optStage_nil_left ?_)
                          have hregSz :
                              (cliPollSelfKitPlaced A g.F g.peer
                                (cliKitStk cliRunBudgets)).regIdBoxSize = 16 := rfl
                          have hrew :
                              ((e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ e6 ++ ekp_box) ++
                                  (ekp ++ (efr ++ (ebob ++
                                    (erbox ++ (erpoll ++
                                      (rustDeallocEvents 16 8 ++ eprom_end)))))) =
                                (e1 ++ e2 ++ e3 ++ e4 ++ e5) ++
                                  (e6 ++ ((ekp_box ++ (ekp ++ efr)) ++
                                    (ebob ++ ((erbox ++ (erpoll ++ rustDeallocEvents 16 8)) ++
                                      eprom_end)))) := by
                            simp only [List.append_assoc]
                          rw [hregSz, hrew]
                          exact dpx_chain5_of_parts he1 he2 he3 he4 he5
                            (Or.inr (dpx_seqEnv_opt_tail he6
                              (Or.inr (dpx_seqEnv_opt_tail hkp_step
                                (Or.inr (dpx_seqEnv_opt_tail hbob_mem
                                  (Or.inr (dpx_seqEnv_opt_tail hreg_mem
                                    (Or.inr hprom_mem)))))))))

theorem dpx_p2OverOkEnv_sub_w4StageP2PathCFull9 [LibsignalPlacement] {α : Type}
    {A : RustAlloc} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    (CurTrialFailEnv : List AllocEvent → Prop)
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (x_res : DoReserveCall)
    {g : DecPkGhost} {r : SessionRecord (List (BitVec 8))}
    {evs : List AllocEvent}
    (h : dpx_p2OverOkEnv A X W g r evs) :
    ∃ (m : PreKeyMessageFields) (sess : Session (List (BitVec 8))) (x_spqr : InitialStateGhost),
      pkToE? g.msg = some m ∧
      r.currentSession = some sess ∧
      x_spqr.p.version = .v1 ∧
      x_spqr.p.authKey.length ≤ 32 ∧
      ∀ r_arch : SessionRecord (List (BitVec 8)),
        r_arch.currentSession = some (clearPending sess) →
        dpx_W4BinaryStageP2PathCWideEnvAllFixedOf
          (dpx_W4BinarySelfKpStepOptEnvAllFixed cliIo.rd g.F) dpx_W4BobSessionBuildEnv9
          G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs g_arch r_arch
          m.opkId.isSome cliIo.rd g.F m.spkId m.kpkId (m.opkId.getD 0#32)
          W.C.F x_res x_spqr evs :=
  dpx_p2OverOkEnv_sub_w4StageP2PathCOf (fun _ hx => hx)
    (fun _ hb => dpx_initBobSessionBuildEnv_sub_w4BobSessionBuildEnv9 hb)
    G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs g_arch x_res h

/-! ### Stage P3 non-`VerNe` (`prevEmpty` and `M3`) inclusions into `W4StageP3WideEnv` -/

/-- `StageP3OkPrefixEnv` inclusion into `W4StageP3WideEnv CloneEnv TryDecEnv`. -/
theorem dpx_stageP3OkPrefixEnv_sub_w4StageP3Wide
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {recG G₁ : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {rest : List (BitVec 8)}
    (hClone : ∀ e, SegCloneEnv recG st e → CloneEnv e)
    (hTd : ∀ e, tdEnv (stageP3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) e → TryDecEnv e)
    {evs : List AllocEvent}
    (h : StageP3OkPrefixEnv tdEnv recG G₁ st rem loc msgG msg rest evs) :
    W4StageP3WideEnv CloneEnv TryDecEnv evs :=
  w4StageP3WideEnv_of_okPrefix
    (dpx_seqEnv_mono hClone (fun _ ht => dpx_seqEnv_mono hTd (fun _ hf => hf) ht) h)

/-- `StageP3ErrEnv` inclusion into `W4StageP3WideEnv CloneEnv TryDecEnv`. -/
theorem dpx_stageP3ErrEnv_sub_w4StageP3Wide
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {recG G₁ : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {rest : List (BitVec 8)}
    (hClone : ∀ e, SegCloneEnv recG st e → CloneEnv e)
    (hTd : ∀ e, tdEnv (stageP3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) e → TryDecEnv e)
    {evs : List AllocEvent}
    (h : StageP3ErrEnv tdEnv recG G₁ st rem loc msgG msg rest evs) :
    W4StageP3WideEnv CloneEnv TryDecEnv evs :=
  w4StageP3WideEnv_of_err
    (dpx_seqEnv_mono hClone (fun _ ht => dpx_seqEnv_mono hTd (fun _ hv => hv) ht) h)

/-- `StageP3VerNeEnv` (`prevEmpty` `FromMEnv`) inclusion into `W4StageP3WideEnv CloneEnv TryDecEnv`. -/
theorem dpx_stageP3VerNeEnv_sub_w4StageP3Wide
    {CloneEnv : List AllocEvent → Prop} (TryDecEnv : List AllocEvent → Prop)
    {recG : SessionGhost} {st : SessionState (List (BitVec 8))}
    (hClone : ∀ e, SegCloneEnv recG st e → CloneEnv e)
    {evs : List AllocEvent}
    (h : StageP3VerNeEnv recG st evs) :
    W4StageP3WideEnv CloneEnv TryDecEnv evs :=
  w4StageP3WideEnv_of_verNe (dpx_seqEnv_mono hClone (fun _ hm => hm) h)

/-- Combined `StageP3Env` (`prevEmpty`) inclusion into `W4StageP3WideEnv CloneEnv TryDecEnv`. -/
theorem dpx_stageP3Env_sub_w4StageP3Wide
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {recG : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {msgVer : BitVec 32} {rest : List (BitVec 8)}
    (hClone : ∀ e, SegCloneEnv recG st e → CloneEnv e)
    (hTd : ∀ G₁, CloneRel recG G₁ →
      ∀ e, tdEnv (stageP3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) e → TryDecEnv e)
    {evs : List AllocEvent}
    (h : StageP3Env tdEnv recG st rem loc msgG msg msgVer rest evs) :
    W4StageP3WideEnv CloneEnv TryDecEnv evs := by
  unfold StageP3Env at h
  split at h
  · obtain ⟨G₁, hcl, herr⟩ := h
    exact dpx_stageP3ErrEnv_sub_w4StageP3Wide hClone (hTd G₁ hcl) herr
  · exact dpx_stageP3VerNeEnv_sub_w4StageP3Wide TryDecEnv hClone h

/-- `StageP3OkPrefixM3Env` (`Matched` `M3`) inclusion into `W4StageP3WideEnv CloneEnv TryDecEnv`. -/
theorem dpx_stageP3OkPrefixM3Env_sub_w4StageP3Wide
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {recG G₁ : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {rest : List (BitVec 8)}
    (hClone : ∀ e, SegCloneEnv recG st e → CloneEnv e)
    (hTd : ∀ e, tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) e → TryDecEnv e)
    {evs : List AllocEvent}
    (h : StageP3OkPrefixM3Env tdEnv recG G₁ st rem loc msgG msg rest evs) :
    W4StageP3WideEnv CloneEnv TryDecEnv evs :=
  w4StageP3WideEnv_of_okPrefix
    (dpx_seqEnv_mono hClone (fun _ ht => dpx_seqEnv_mono hTd (fun _ hf => hf) ht) h)

/-- `StageP3ErrM3Env` (`Matched` `M3`) inclusion into `W4StageP3WideEnv CloneEnv TryDecEnv`. -/
theorem dpx_stageP3ErrM3Env_sub_w4StageP3Wide
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {recG G₁ : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {rest : List (BitVec 8)}
    (hClone : ∀ e, SegCloneEnv recG st e → CloneEnv e)
    (hTd : ∀ e, tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) e → TryDecEnv e)
    {evs : List AllocEvent}
    (h : StageP3ErrM3Env tdEnv recG G₁ st rem loc msgG msg rest evs) :
    W4StageP3WideEnv CloneEnv TryDecEnv evs :=
  w4StageP3WideEnv_of_err
    (dpx_seqEnv_mono hClone (fun _ ht => dpx_seqEnv_mono hTd (fun _ hv => hv) ht) h)

/-- `StageP3VerNeM3Env` (`Matched` `M3` `FromMEnv`) inclusion into `W4StageP3WideEnv CloneEnv TryDecEnv`. -/
theorem dpx_stageP3VerNeM3Env_sub_w4StageP3Wide
    {CloneEnv : List AllocEvent → Prop} (TryDecEnv : List AllocEvent → Prop)
    {recG : SessionGhost} {st : SessionState (List (BitVec 8))}
    (hClone : ∀ e, SegCloneEnv recG st e → CloneEnv e)
    {evs : List AllocEvent}
    (h : StageP3VerNeM3Env recG st evs) :
    W4StageP3WideEnv CloneEnv TryDecEnv evs :=
  w4StageP3WideEnv_of_verNe (dpx_seqEnv_mono hClone (fun _ hm => hm) h)

/-- Combined `StageP3M3Env` (`Matched` `M3`) inclusion into `W4StageP3WideEnv CloneEnv TryDecEnv`. -/
theorem dpx_stageP3M3Env_sub_w4StageP3Wide
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {recG : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {msgVer : BitVec 32} {rest : List (BitVec 8)}
    (hClone : ∀ e, SegCloneEnv recG st e → CloneEnv e)
    (hTd : ∀ G₁, CloneRel recG G₁ →
      ∀ e, tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) e → TryDecEnv e)
    {evs : List AllocEvent}
    (h : StageP3M3Env tdEnv recG st rem loc msgG msg msgVer rest evs) :
    W4StageP3WideEnv CloneEnv TryDecEnv evs := by
  unfold StageP3M3Env at h
  split at h
  · obtain ⟨G₁, hcl, herr⟩ := h
    exact dpx_stageP3ErrM3Env_sub_w4StageP3Wide hClone (hTd G₁ hcl) herr
  · exact dpx_stageP3VerNeM3Env_sub_w4StageP3Wide TryDecEnv hClone h

end LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridgeX
