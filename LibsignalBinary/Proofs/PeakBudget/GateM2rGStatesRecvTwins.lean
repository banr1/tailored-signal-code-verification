/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridge
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak
public import LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
public import LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# `StatesRecvE`-Parametric Twins of `W4RecvPrekeyCmkSlot`

Parametric counterparts of `W4RecvPrekeyCmkSlot` and `CliDpPollTrustedWideBridge` replacing the
fixed `StatesRecvProtoEnv` across linked `spqr::recv`, Block-`507` `try_decrypt_with_state`, and
downstream `W4` (`decrypt_prekey`) slot envelopes so callers can instantiate at
`SpqrStatesRecvPeakSpecRepaired.StatesRecvProtoEnv' K` while retaining definitional equality
(`*_proto_eq`) at `StatesRecvProtoEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins

open Arm64 Arm64.Obj Arm64.Process
open CryptoGames.LibsignalSession
  (ChainKey Crypto IdentityKey MessageKeyGenerator MessageKeys Mut PublicKey RatchetState
   SessionState ShaCompress SignalMessage TripleRatchet)
open CryptoGames.LibsignalSessionApi (Direction Session SessionRecord)
open CryptoVerification
  (LibsignalFrozen LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives modelPrims)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Message MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB spqrAuthApi
   spqrPolyApi spqrV1)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall SpqrModel TrGhost TryDecryptGhost)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SessionGhost UuidParser coinsOf uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs cliExternsPlaced)
open CryptoVerification.SignalSession.Cli
  (CliGhostHooks ReadRule StoresGhost cliGhostExterns pathOf)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV cliIo cliRunBudgets parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOkD2c)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (cliKitStk)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (filesOk₀ scopeIn scopeKit)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
  (InitializeBobV1OptFieldsEnv)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (parseArgs_peer_name_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridge
  (CliDpPollD2cSeqFreeConcreteEnvOf CliDpPollD2cSeqFreeLinkedEnvOf CliDpPollD2cTiedLinkedEnvOf
   CliDpPollD2cTiedWideEnvOf CliDpPollPathCTiedEnvOf CliDpPollTrustedSeqFreeEnv
   cliPollStageP4Prev1SeqFreeEnvsAux decPkD2cSlotOkPlacedAtOf_targetGuarded_of_unguarded
   realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf
   realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf_of_guarded_cliPqInputs_recv
   realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf_of_guarded_tight
   realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf
   targetEnv_of_guarded_cliPqInputs_recv targetEnv_of_guarded_tight w4c_verNePrev1P3PathCEnv
   w4c_verNePrev1P3PathCEnvOf)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W4BinaryPkRemoveStepEnv W4BinaryStageP1OkEnv W4BinaryStageP1UntrustedEnv
   W4BinaryStageP2MatchedWideEnv W4BinaryStageP2PathAWideEnv W4BinaryStageP2PathCWideEnv
   W4BinaryStageP4MatchedWideEnv W4CloneACDomEnv W4CloneBDomEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (cliIo_rd_ok_length_le_sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
  (SpqrRecvC07C09aBytesEnv TryDecryptCliLinkedEnv)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase
  (DecPkD2cSlotOkFrozenPlaced DecPkD2cSlotOkFrozenPlacedAt DecPkD2cSlotOkPlacedAtOf)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W4BinaryIdSaveStepEnvAllFixed W4BinaryIdTrustStepEnvAllFixed W4BinaryKpkGetStepEnvAllFixed
   W4BinaryPkGetStepEnvAllFixed W4BinaryPkRemoveStepEnvAllFixed W4BinarySelfKpStepEnvAllFixed
   W4BinarySelfRegIdStepEnvAllFixed W4BinarySessLoadStepEnvAllFixed W4BinarySpkGetStepEnvAllFixed
   W4BinaryStageP1OkEnvAllFixed W4BinaryStageP1UntrustedEnvAllFixed
   W4BinaryStageP2PathAWideEnvAllFixed W4BinaryStageP2PathCWideEnvAllFixed
   W4BinaryStageP4MatchedWideEnvAllFixed W4BinaryStageP4PathAWideEnvAllFixed
   W4BinaryStageP4PathAWideEnvFixed W4BinaryStageP4PathCWideEnvAllFixed
   W4BinaryStageP4PathCWideEnvFixed dirGetEnv_fixed_eq_of_not_overCap
   not_overCapFile_runFiles_identities not_overCapFile_runFiles_kyberLastResort_keyName
   not_overCapFile_runFiles_kyberOneTime not_overCapFile_runFiles_oneTime
   not_overCapFile_runFiles_own_ikp not_overCapFile_runFiles_own_regId
   not_overCapFile_runFiles_sessions not_overCapFile_runFiles_signed)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv IterSeqEnv)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec (StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv (SpqrRecvC07C09aTightLinkedEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness (spqrRecvTightLinkedEnv_nil_exists)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (SpqrRecvEqualTightEnv SpqrRecvTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec (StatesRecvProtoEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (SessionCloneDom)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak (optDeallocListEvs)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak (ArchivedTrialIterEnv)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak (W4BoundedEvs)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4DecryptPrekeySlotParams W4StageP3WideEnv W4TryDecryptCloneFailWideEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec (W4DecryptPrekeyTightDom)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
  (VerNeTightTopEnv W4StageP3Prev1WideEnvOf w4StageP3Prev1WideEnvOf_of_wide)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4ArchivedTrialCmk W4ArchivedTrialDomCmkOf W4BinaryCallSiteDomCmk W4BinaryRecvPrekeyParamsCmk
   W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf W4BinaryRecvPrekeyPathBWideCmkEnvOf
   W4BinaryRecvPrekeyPathCWideCmkEnvFixedOf W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed
   W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf W4BinaryRecvPrekeyWideSlotEnvCmkFixedOf
   W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf
   W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf W4FailedTdCancelCmkEnvOf W4FailedTdDomCmkOf
   W4FailedTryDecryptCallCmk W4LoopAdvEnv W4LoopAdvSub W4RecvPrekeyRealParamsCmk
   W4RecvPrekeyTryDecACCmkEnvOf W4TrialDecCmkEnv W4TrialDropCmkEnv W4TrialRunWideCmkEnvOf
   W4TryDecryptCallCmk W4TryDecryptCallDomCmkOf W4TryDecryptPathACDomCmkOf
   mkW4RecvPrekeyWideCmkSlotParamsOf realCliDecPkBinaryWideSlotEnvCmkFixed
   realCliDecPkBinaryWideSlotEnvCmkFixedOf realCliDecPkBinaryWideSlotEnvCmkGuardedFixed
   realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf
   realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixed
   realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf w4c_DecodeStateTightEnvOf
   w4c_SpqrRecvC07C09aBytesEnvOf w4c_SpqrRecvC07C09aTightLinkedEnvOf w4c_SpqrRecvC07TightEnvOf
   w4c_SpqrRecvC07TightLinkedEnvOf w4c_TryDecryptCliEnvOfPure w4c_TryDecryptCliFailEnvOfPure
   w4c_TryDecryptCliLinkedEnvOf w4c_TryDecryptCliLinkedFailEnvOf w4c_decodeStateTightEnvOf_mono
   w4c_defaultDecodeMaxOps w4c_defaultP3PathCEnvOf w4c_loopAdvSub_refl
   w4c_spqrRecvC07TightLinkedEnvOf_mono w4c_tryDecryptCmkSeg4EnvOf w4c_tryDecryptCmkStepEnvOf)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSavePollEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitLoadPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
  (CliStageP4Prev1Envs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
  (P2OverPathCErrEnvOf P2OverPathCOkEnvOf PromoteOverArchiveCanonSessEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
  (cliPollSelfBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
  (cliP2PathAOptFieldsErrEnv cliP2PathAOptFieldsOkEnv cliStageP2KitEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget (CliKpkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget (CliPkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
  (CliPkRemovePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (CliSpkGetPollEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
  (FromS2GenEnv FromS3GenEnv FromS4GenEnv FromS5GenEnv seqEnv_mono)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv TryDecryptEnvArgs)

/-! ## 1. `StatesRecvE`-Parametric Linked `spqr::recv` Envelopes -/

/-- `(maxOps, StatesRecvE)`-parametric `SpqrRecvC07C09aTightLinkedEnvOf`, generalizing
`W4RecvPrekeyCmkSlot.w4c_SpqrRecvC07C09aTightLinkedEnvOf` over `StatesRecvE`. -/
def m2rg_SpqrRecvC07C09aTightLinkedEnvOf' (F : ShaCompress) (K : MlKem) (maxOps : Nat)
    (StatesRecvE : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  w4c_SpqrRecvC07TightLinkedEnvOf F K maxOps StatesRecvE
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

theorem m2rg_SpqrRecvC07C09aTightLinkedEnvOf'_proto_eq
    (F : ShaCompress) (K : MlKem) (maxOps : Nat) :
    m2rg_SpqrRecvC07C09aTightLinkedEnvOf' F K maxOps StatesRecvProtoEnv =
      w4c_SpqrRecvC07C09aTightLinkedEnvOf F K maxOps :=
  rfl

theorem m2rg_SpqrRecvC07C09aTightLinkedEnvOf'_83_proto_eq
    (F : ShaCompress) (K : MlKem) :
    m2rg_SpqrRecvC07C09aTightLinkedEnvOf' F K 83 StatesRecvProtoEnv =
      SpqrRecvC07C09aTightLinkedEnv F K :=
  rfl

/-- `(maxOps, StatesRecvE)`-parametric existentially lifted 12-ghost linked `spqr::recv`
byte-slice envelope. -/
def m2rg_SpqrRecvC07C09aBytesEnvOf' (F : ShaCompress) (K : MlKem) (maxOps : Nat)
    (StatesRecvE : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBs _msgBs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
    m2rg_SpqrRecvC07C09aTightLinkedEnvOf' F K maxOps StatesRecvE
      stBs pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

theorem m2rg_SpqrRecvC07C09aBytesEnvOf'_proto_eq
    (F : ShaCompress) (K : MlKem) (maxOps : Nat) :
    m2rg_SpqrRecvC07C09aBytesEnvOf' F K maxOps StatesRecvProtoEnv =
      w4c_SpqrRecvC07C09aBytesEnvOf F K maxOps :=
  rfl

theorem m2rg_SpqrRecvC07C09aBytesEnvOf'_83_proto_eq
    (F : ShaCompress) (K : MlKem) :
    m2rg_SpqrRecvC07C09aBytesEnvOf' F K 83 StatesRecvProtoEnv =
      SpqrRecvC07C09aBytesEnv F K :=
  rfl

/-- Non-emptiness (`[] ∈ m2rg_SpqrRecvC07C09aBytesEnvOf' F K maxOps StatesRecvE stBs msgBs`). -/
theorem m2rg_spqrRecvC07C09aBytesEnvOf'_nonempty
    (F : ShaCompress) (K : MlKem) (maxOps : Nat)
    (StatesRecvE : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBs msgBs : List (BitVec 8)) :
    ∃ evs, m2rg_SpqrRecvC07C09aBytesEnvOf' F K maxOps StatesRecvE stBs msgBs evs :=
  let _ := msgBs
  ⟨[], spqrRecvTightLinkedEnv_nil_exists F K
    (w4c_DecodeStateTightEnvOf maxOps)
    (fun _ => StatesFromPbTightEnv)
    (fun _ => StatesIntoPbTightEnv)
    StatesRecvE stBs⟩

theorem m2rg_spqrRecvC07C09aBytesEnvOf'_nonempty_of_le
    (F : ShaCompress) (K : MlKem) (maxOps : Nat) (_hm : 83 ≤ maxOps)
    (StatesRecvE : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBs msgBs : List (BitVec 8)) :
    ∃ evs, m2rg_SpqrRecvC07C09aBytesEnvOf' F K maxOps StatesRecvE stBs msgBs evs :=
  m2rg_spqrRecvC07C09aBytesEnvOf'_nonempty F K maxOps StatesRecvE stBs msgBs

theorem m2rg_spqrRecvC07C09aTightLinkedEnvOf'_mono
    {F : ShaCompress} {K : MlKem} {m₁ m₂ : Nat} (hm : m₁ ≤ m₂)
    {StatesRecvE : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {stBytes : Bytes}
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xInit : InitInnerGhost} {xNew : ChainNewGhost}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    {evs : List AllocEvent}
    (h : m2rg_SpqrRecvC07C09aTightLinkedEnvOf' F K m₁ StatesRecvE
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    m2rg_SpqrRecvC07C09aTightLinkedEnvOf' F K m₂ StatesRecvE
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs :=
  w4c_spqrRecvC07TightLinkedEnvOf_mono hm h

theorem m2rg_spqrRecvC07C09aTightLinkedEnvOf'_mono_env
    {F : ShaCompress} {K : MlKem} {m₁ m₂ : Nat} (hm : m₁ ≤ m₂)
    {R₁ R₂ : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (hR : ∀ st msg evs, R₁ st msg evs → R₂ st msg evs)
    {stBytes : Bytes}
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xInit : InitInnerGhost} {xNew : ChainNewGhost}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    {evs : List AllocEvent}
    (h : m2rg_SpqrRecvC07C09aTightLinkedEnvOf' F K m₁ R₁
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    m2rg_SpqrRecvC07C09aTightLinkedEnvOf' F K m₂ R₂
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs := by
  unfold m2rg_SpqrRecvC07C09aTightLinkedEnvOf' w4c_SpqrRecvC07TightLinkedEnvOf at h ⊢
  rcases h with ⟨h1, hlink⟩
  refine ⟨?_, hlink⟩
  unfold w4c_SpqrRecvC07TightEnvOf SpqrRecvTightEnv at h1 ⊢
  rcases h1 with hfree | hseq
  · exact Or.inl hfree
  · refine Or.inr (seqEnv_mono (fun _ hd => w4c_decodeStateTightEnvOf_mono hm stBytes hd)
      (fun _ ha => ?_) hseq)
    rcases ha with hfr2 | ⟨hdec, hbr⟩
    · exact Or.inl hfr2
    · refine Or.inr ⟨hdec, ?_⟩
      rcases hbr with hless | hgt | ⟨hin, heq⟩
      · exact Or.inl hless
      · exact Or.inr (Or.inl hgt)
      · refine Or.inr (Or.inr ⟨hin, ?_⟩)
        unfold SpqrRecvEqualTightEnv at heq ⊢
        exact seqEnv_mono (fun _ hf => hf)
          (fun _ hmd => hmd.elim Or.inl fun hfpb => Or.inr
            (seqEnv_mono (fun _ hfp => hfp)
              (fun _ haf => haf.elim Or.inl fun ⟨hpb, hsr⟩ => Or.inr ⟨hpb,
                seqEnv_mono (fun _ hr => hR st0 sckaMsg _ hr) (fun _ htail => htail) hsr⟩)
              hfpb))
          heq

theorem m2rg_spqrRecvC07C09aBytesEnvOf'_mono
    {F : ShaCompress} {K : MlKem} {m₁ m₂ : Nat} (hm : m₁ ≤ m₂)
    {StatesRecvE : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (stBs msgBs : List (BitVec 8)) {evs : List AllocEvent}
    (h : m2rg_SpqrRecvC07C09aBytesEnvOf' F K m₁ StatesRecvE stBs msgBs evs) :
    m2rg_SpqrRecvC07C09aBytesEnvOf' F K m₂ StatesRecvE stBs msgBs evs := by
  let _ := msgBs
  obtain ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto, h1⟩ := h
  exact ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto,
    m2rg_spqrRecvC07C09aTightLinkedEnvOf'_mono hm h1⟩

theorem m2rg_spqrRecvC07C09aBytesEnvOf'_mono_env
    {F : ShaCompress} {K : MlKem} {m₁ m₂ : Nat} (hm : m₁ ≤ m₂)
    {R₁ R₂ : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (hR : ∀ st msg evs, R₁ st msg evs → R₂ st msg evs)
    (stBs msgBs : List (BitVec 8)) {evs : List AllocEvent}
    (h : m2rg_SpqrRecvC07C09aBytesEnvOf' F K m₁ R₁ stBs msgBs evs) :
    m2rg_SpqrRecvC07C09aBytesEnvOf' F K m₂ R₂ stBs msgBs evs := by
  let _ := msgBs
  obtain ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto, h1⟩ := h
  exact ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto,
    m2rg_spqrRecvC07C09aTightLinkedEnvOf'_mono_env hm hR h1⟩

/-! ## 2. `StatesRecvE`-Parametric Block-`507` `TryDecrypt` and Failed-Trial Twins -/

/-- `(LoopAdvEnv, maxOps, StatesRecvE)`-parametric linked Block-`507` `try_decrypt_with_state` CLI
envelope (`rfl`-equal to `w4c_TryDecryptCliLinkedEnvOf` at `StatesRecvProtoEnv`). -/
abbrev m2rg_TryDecryptCliLinkedEnvOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem)
    (StatesRecvE : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop) :
    TryDecryptEnvArgs → List AllocEvent → Prop :=
  w4c_TryDecryptCliEnvOfPure LoopAdvEnv C (spqrV1 C.F K)
    FmtWriteEnv (m2rg_SpqrRecvC07C09aBytesEnvOf' C.F K maxOps StatesRecvE) FormatInnerEnv

theorem m2rg_TryDecryptCliLinkedEnvOf'_proto_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) (C : Crypto) (K : MlKem) :
    m2rg_TryDecryptCliLinkedEnvOf' LoopAdvEnv maxOps C K StatesRecvProtoEnv =
      w4c_TryDecryptCliLinkedEnvOf LoopAdvEnv maxOps C K :=
  rfl

theorem m2rg_TryDecryptCliLinkedEnvOf'_83_proto_eq (C : Crypto) (K : MlKem) :
    m2rg_TryDecryptCliLinkedEnvOf' CmkLoopAdvanceEvs 83 C K StatesRecvProtoEnv =
      TryDecryptCliLinkedEnv C K :=
  rfl

/-- `25000`-step `CmkLoopAdvanceEvs` specialization of `m2rg_TryDecryptCliLinkedEnvOf'`. -/
abbrev m2rg_TryDecryptCliLinkedCmkEnvOf' (maxOps : Nat) (C : Crypto) (K : MlKem)
    (StatesRecvE : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop) :
    TryDecryptEnvArgs → List AllocEvent → Prop :=
  m2rg_TryDecryptCliLinkedEnvOf' CmkLoopAdvanceEvs maxOps C K StatesRecvE

theorem m2rg_TryDecryptCliLinkedCmkEnvOf'_proto_eq
    (maxOps : Nat) (C : Crypto) (K : MlKem) :
    m2rg_TryDecryptCliLinkedCmkEnvOf' maxOps C K StatesRecvProtoEnv =
      w4c_TryDecryptCliLinkedEnvOf CmkLoopAdvanceEvs maxOps C K :=
  rfl

/-- `(LoopAdvEnv, maxOps, StatesRecvE)`-parametric failed-trial linked `try_decrypt_with_state`
envelope (`rfl`-equal to `w4c_TryDecryptCliLinkedFailEnvOf` at `StatesRecvProtoEnv`). -/
abbrev m2rg_TryDecryptCliLinkedFailEnvOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem)
    (StatesRecvE : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop) :
    TryDecryptEnvArgs → List AllocEvent → Prop :=
  w4c_TryDecryptCliFailEnvOfPure LoopAdvEnv C (spqrV1 C.F K)
    FmtWriteEnv (m2rg_SpqrRecvC07C09aBytesEnvOf' C.F K maxOps StatesRecvE) FormatInnerEnv

theorem m2rg_TryDecryptCliLinkedFailEnvOf'_proto_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) (C : Crypto) (K : MlKem) :
    m2rg_TryDecryptCliLinkedFailEnvOf' LoopAdvEnv maxOps C K StatesRecvProtoEnv =
      w4c_TryDecryptCliLinkedFailEnvOf LoopAdvEnv maxOps C K :=
  rfl

/-- `25000`-step `CmkLoopAdvanceEvs` specialization of `m2rg_TryDecryptCliLinkedFailEnvOf'`. -/
abbrev m2rg_TryDecryptCliLinkedFailCmkEnvOf' (maxOps : Nat) (C : Crypto) (K : MlKem)
    (StatesRecvE : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop) :
    TryDecryptEnvArgs → List AllocEvent → Prop :=
  m2rg_TryDecryptCliLinkedFailEnvOf' CmkLoopAdvanceEvs maxOps C K StatesRecvE

theorem m2rg_TryDecryptCliLinkedFailCmkEnvOf'_proto_eq
    (maxOps : Nat) (C : Crypto) (K : MlKem) :
    m2rg_TryDecryptCliLinkedFailCmkEnvOf' maxOps C K StatesRecvProtoEnv =
      w4c_TryDecryptCliLinkedFailEnvOf CmkLoopAdvanceEvs maxOps C K :=
  rfl

private theorem m2rg_tryDecryptCmkStepEnvOf_mono {L₁ L₂ : W4LoopAdvEnv}
    (hL : W4LoopAdvSub L₁ L₂)
    (msgCounter : BitVec 32) (senderRatchetKey : PublicKey)
    (trG : TrGhost) (r : RatchetState) (ck : ChainKey) {evs : List AllocEvent}
    (h : w4c_tryDecryptCmkStepEnvOf L₁ msgCounter senderRatchetKey trG r ck evs) :
    w4c_tryDecryptCmkStepEnvOf L₂ msgCounter senderRatchetKey trG r ck evs := by
  unfold w4c_tryDecryptCmkStepEnvOf at h ⊢
  by_cases hlt : msgCounter < ck.index
  · simp only [hlt, ↓reduceIte] at h ⊢
    exact h
  · simp only [hlt, ↓reduceIte] at h ⊢
    by_cases hj : (msgCounter - ck.index).toNat ≤ r.maxForwardJumps
    · simp only [hj, ↓reduceIte] at h ⊢
      revert h
      cases r.findReceiverChainIndex senderRatchetKey <;> intro h
      · exact h
      · exact hL _ _ _ _ _ h
    · simp only [hj, ↓reduceIte] at h ⊢
      exact h

private theorem m2rg_tryDecryptCmkSeg4EnvOf_mono {L₁ L₂ : W4LoopAdvEnv}
    (hL : W4LoopAdvSub L₁ L₂) (fmtWriteEnv : List AllocEvent → Prop)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (ck : ChainKey) {evs : List AllocEvent}
    (h : w4c_tryDecryptCmkSeg4EnvOf L₁ fmtWriteEnv x trG tr ck evs) :
    w4c_tryDecryptCmkSeg4EnvOf L₂ fmtWriteEnv x trG tr ck evs :=
  seqEnv_mono (fun _ hf => hf)
    (fun _ hs => seqEnv_mono
      (fun _ hc => m2rg_tryDecryptCmkStepEnvOf_mono hL _ _ _ _ _ hc)
      (fun _ hfr => hfr) hs) h

private theorem m2rg_pqRecvEnv_mono {S : SpqrModel}
    {R₁ R₂ : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    (hR : ∀ stBs msgBs evs, R₁ stBs msgBs evs → R₂ stBs msgBs evs)
    (fmtEnv : List AllocEvent → Prop)
    (x : TryDecryptGhost) (tr : TripleRatchet (List (BitVec 8))) {evs : List AllocEvent}
    (h : PqRecvEnv S R₁ fmtEnv x tr evs) :
    PqRecvEnv S R₂ fmtEnv x tr evs := by
  unfold PqRecvEnv at h ⊢
  revert h
  cases S.recv tr.pqrState x.msg.pqRatchet <;> intro h
  · exact seqEnv_mono
      (fun _ h1 => seqEnv_mono (fun _ hr => hR _ _ _ hr) (fun _ hf => hf) h1)
      (fun _ hfr => hfr) h
  · exact hR _ _ _ h

private theorem m2rg_fromS5GenEnv_mono {C : Crypto} {parse : UuidParser} {S : SpqrModel}
    {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
    {s5₁ s5₂ : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hs5 : ∀ x tr evs, s5₁ x tr evs → s5₂ x tr evs)
    {s6 : MessageKeyGenerator → List AllocEvent → Prop}
    {s7 : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop}
    {s8 : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9 : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) {evs : List AllocEvent}
    (h : FromS5GenEnv C parse S aesOpt s5₁ s6 s7 s8 s9 x trG tr st1 mkg evs) :
    FromS5GenEnv C parse S aesOpt s5₂ s6 s7 s8 s9 x trG tr st1 mkg evs := by
  unfold FromS5GenEnv at h ⊢
  revert h
  cases S.recv tr.pqrState x.msg.pqRatchet with
  | error _ =>
    intro h
    exact seqEnv_mono (fun _ h5 => hs5 x tr _ h5) (fun _ hfr => hfr) h
  | ok pair =>
    rcases pair with ⟨newPqrState, pqrKey⟩
    intro h
    exact seqEnv_mono (fun _ h5 => hs5 x tr _ h5) (fun _ h6 => h6) h

private theorem m2rg_fromS4GenEnv_mono {C : Crypto} {parse : UuidParser} {S : SpqrModel}
    {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
    {s4₁ s4₂ : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop}
    {s5₁ s5₂ : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hs4 : ∀ x trG tr ck evs, s4₁ x trG tr ck evs → s4₂ x trG tr ck evs)
    (hs5 : ∀ x tr evs, s5₁ x tr evs → s5₂ x tr evs)
    {s6 : MessageKeyGenerator → List AllocEvent → Prop}
    {s7 : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop}
    {s8 : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9 : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) {evs : List AllocEvent}
    (h : FromS4GenEnv C parse S aesOpt s4₁ s5₁ s6 s7 s8 s9 x trG tr st1 ck evs) :
    FromS4GenEnv C parse S aesOpt s4₂ s5₂ s6 s7 s8 s9 x trG tr st1 ck evs := by
  unfold FromS4GenEnv at h ⊢
  revert h
  cases Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) tr.ratchet with
  | mk res r2 =>
    cases res with
    | error _ =>
      intro h
      exact seqEnv_mono (fun _ h4 => hs4 x trG tr ck _ h4) (fun _ hfr => hfr) h
    | ok mkg =>
      intro h
      exact seqEnv_mono (fun _ h4 => hs4 x trG tr ck _ h4)
        (fun _ h5 => m2rg_fromS5GenEnv_mono hs5 x trG { tr with ratchet := r2 } st1 mkg h5) h

private theorem m2rg_fromS3GenEnv_mono {C : Crypto} {parse : UuidParser} {S : SpqrModel}
    {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
    {s3 : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    {s4₁ s4₂ : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop}
    {s5₁ s5₂ : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hs4 : ∀ x trG tr ck evs, s4₁ x trG tr ck evs → s4₂ x trG tr ck evs)
    (hs5 : ∀ x tr evs, s5₁ x tr evs → s5₂ x tr evs)
    {s6 : MessageKeyGenerator → List AllocEvent → Prop}
    {s7 : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop}
    {s8 : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9 : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) {evs : List AllocEvent}
    (h : FromS3GenEnv C parse S aesOpt s3 s4₁ s5₁ s6 s7 s8 s9 x trG tr st1 evs) :
    FromS3GenEnv C parse S aesOpt s3 s4₂ s5₂ s6 s7 s8 s9 x trG tr st1 evs := by
  unfold FromS3GenEnv at h ⊢
  revert h
  cases Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest)) tr.ratchet with
  | mk res _ =>
    cases res with
    | error _ =>
      intro h
      exact h
    | ok _ =>
      intro h
      exact seqEnv_mono (fun _ h3 => h3)
        (fun _ h4 => m2rg_fromS4GenEnv_mono hs4 hs5 _ _ _ _ _ h4) h

private theorem m2rg_fromS2GenEnv_mono {C : Crypto} {parse : UuidParser} {S : SpqrModel}
    {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
    {s3 : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    {s4₁ s4₂ : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop}
    {s5₁ s5₂ : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hs4 : ∀ x trG tr ck evs, s4₁ x trG tr ck evs → s4₂ x trG tr ck evs)
    (hs5 : ∀ x tr evs, s5₁ x tr evs → s5₂ x tr evs)
    {s6 : MessageKeyGenerator → List AllocEvent → Prop}
    {s7 : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop}
    {s8 : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9 : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) {evs : List AllocEvent}
    (h : FromS2GenEnv C parse S aesOpt s3 s4₁ s5₁ s6 s7 s8 s9 x trG tr st1 evs) :
    FromS2GenEnv C parse S aesOpt s3 s4₂ s5₂ s6 s7 s8 s9 x trG tr st1 evs := by
  unfold FromS2GenEnv at h ⊢
  revert h
  cases tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
  | error _ =>
    intro h
    exact h
  | ok ckOpt =>
    cases ckOpt with
    | some ck =>
      intro h
      exact m2rg_fromS4GenEnv_mono hs4 hs5 x trG tr st1 ck h
    | none =>
      intro h
      exact m2rg_fromS3GenEnv_mono hs4 hs5 x trG tr st1 h

theorem m2rg_tryDecryptCliLinkedEnvOf'_mono
    {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    {C : Crypto} {K : MlKem}
    {R₁ R₂ : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (hR : ∀ st msg evs, R₁ st msg evs → R₂ st msg evs)
    {a : TryDecryptEnvArgs} {evs : List AllocEvent}
    (h : m2rg_TryDecryptCliLinkedEnvOf' L₁ m₁ C K R₁ a evs) :
    m2rg_TryDecryptCliLinkedEnvOf' L₂ m₂ C K R₂ a evs := by
  unfold m2rg_TryDecryptCliLinkedEnvOf' w4c_TryDecryptCliEnvOfPure at h ⊢
  revert h
  cases Mut.exec TripleRatchet.fromSessionState a.st with
  | mk res st1 =>
    cases res with
    | error _ =>
      intro h
      exact h
    | ok tr0 =>
      intro h
      exact seqEnv_mono (fun _ hf => hf)
        (fun _ h2 => m2rg_fromS2GenEnv_mono
          (fun x trG tr ck _ hs4 => m2rg_tryDecryptCmkSeg4EnvOf_mono hL FmtWriteEnv x trG tr ck hs4)
          (fun x tr _ hs5 => m2rg_pqRecvEnv_mono
            (fun stBs msgBs _ hr => m2rg_spqrRecvC07C09aBytesEnvOf'_mono_env hm hR stBs msgBs hr)
            FormatInnerEnv x tr hs5)
          _ _ tr0 st1 h2) h

theorem m2rg_tryDecryptCliLinkedFailEnvOf'_mono
    {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    {C : Crypto} {K : MlKem}
    {R₁ R₂ : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (hR : ∀ st msg evs, R₁ st msg evs → R₂ st msg evs)
    {a : TryDecryptEnvArgs} {evs : List AllocEvent}
    (h : m2rg_TryDecryptCliLinkedFailEnvOf' L₁ m₁ C K R₁ a evs) :
    m2rg_TryDecryptCliLinkedFailEnvOf' L₂ m₂ C K R₂ a evs := by
  unfold m2rg_TryDecryptCliLinkedFailEnvOf' w4c_TryDecryptCliFailEnvOfPure at h ⊢
  revert h
  cases Mut.exec TripleRatchet.fromSessionState a.st with
  | mk res st1 =>
    cases res with
    | error _ =>
      intro h
      exact h
    | ok tr0 =>
      intro h
      exact seqEnv_mono (fun _ hf => hf)
        (fun _ h2 => m2rg_fromS2GenEnv_mono
          (fun x trG tr ck _ hs4 => m2rg_tryDecryptCmkSeg4EnvOf_mono hL FmtWriteEnv x trG tr ck hs4)
          (fun x tr _ hs5 => m2rg_pqRecvEnv_mono
            (fun stBs msgBs _ hr => m2rg_spqrRecvC07C09aBytesEnvOf'_mono_env hm hR stBs msgBs hr)
            FormatInnerEnv x tr hs5)
          _ _ tr0 st1 h2) h

/-! ## 3. `StatesRecvFK`-Parametric `W4` (`decrypt_prekey`) Slot Envelopes -/

/-- `(F, K)`-indexed `States.recv` protocol envelope family (`fun _ K => StatesRecvProtoEnv' K` on
repaired traces; `fun _ _ => StatesRecvProtoEnv` for `rfl` parity with `w4c_*`). -/
abbrev m2rg_StatesRecvEnvFam : Type :=
  ∀ (F : ShaCompress), MlKem →
    States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi → List AllocEvent → Prop

/-- Legacy `StatesRecvProtoEnv` family (`rfl`-matching all pre-existing `w4c_*` definitions). -/
abbrev m2rg_protoStatesRecvEnvFam : m2rg_StatesRecvEnvFam :=
  fun F _ => @StatesRecvProtoEnv F

/-- Pointwise inclusion on `m2rg_StatesRecvEnvFam`. -/
def m2rg_StatesRecvSub (E₁ E₂ : m2rg_StatesRecvEnvFam) : Prop :=
  ∀ F K st msg evs, E₁ F K st msg evs → E₂ F K st msg evs

theorem m2rg_statesRecvSub_refl (E : m2rg_StatesRecvEnvFam) : m2rg_StatesRecvSub E E :=
  fun _ _ _ _ _ h => h

/-- Failed-trial `try_decrypt` and drop-cancellation envelope twin. -/
def m2rg_W4FailedTdCancelCmkEnvOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem)
    (StatesRecvE : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (fc : W4FailedTryDecryptCallCmk) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    ConcatEnv (m2rg_TryDecryptCliLinkedFailEnvOf' LoopAdvEnv maxOps C K StatesRecvE fc.td.a)
      (· = optDeallocListEvs fc.failDropPairs) evs

theorem m2rg_W4FailedTdCancelCmkEnvOf'_proto_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) (C : Crypto) (K : MlKem) :
    m2rg_W4FailedTdCancelCmkEnvOf' LoopAdvEnv maxOps C K StatesRecvProtoEnv =
      W4FailedTdCancelCmkEnvOf LoopAdvEnv maxOps C K :=
  rfl

/-- Archived-trial version-mismatch or cloned-session failed `try_decrypt_pq` envelope twin. -/
def m2rg_W4TrialRunWideCmkEnvOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem)
    (StatesRecvE : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (x : W4ArchivedTrialCmk) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    W4TryDecryptCloneFailWideEnv (SegCloneEnv x.G_tr x.ses_tr.state)
      (m2rg_W4FailedTdCancelCmkEnvOf' LoopAdvEnv maxOps C K StatesRecvE x.fc_tr)
      (· = dropClonedSessionEvents x.G_tr x.ses_tr.state) evs

theorem m2rg_W4TrialRunWideCmkEnvOf'_proto_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) (C : Crypto) (K : MlKem) :
    m2rg_W4TrialRunWideCmkEnvOf' LoopAdvEnv maxOps C K StatesRecvProtoEnv =
      W4TrialRunWideCmkEnvOf LoopAdvEnv maxOps C K :=
  rfl

/-- `W4DecryptPrekeySlotParams` twin parameterized by `StatesRecvFK`. -/
def m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (R : W4RecvPrekeyRealParamsCmk) :
    W4DecryptPrekeySlotParams W4ArchivedTrialCmk where
  rd := R.rd
  DeserEnv := RecordDeserializeCancelEnv
  files := R.files
  ownDir := StoresGhost.opened.identity.own
  peersDir := StoresGhost.opened.identity.peers
  spkDir := StoresGhost.opened.signed
  kpkDir := R.kpkDir
  opkDir := StoresGhost.opened.oneTime
  sessDir := StoresGhost.opened.sessions
  peer := R.peer
  hasOpk := R.hasOpk
  spkId := R.spkId
  kpkId := R.kpkId
  opkId := R.opkId
  kpkMarkName := R.kpkMarkName
  ownKeyName := R.ownKeyName
  ownRegName := R.ownRegName
  F := R.C.F
  x_res := R.x_res
  x_spqr := R.x_spqr
  G_cur := R.G_cur
  st_cur := R.st_cur
  CurTrialFailEnv :=
    if R.hasCurSession then
      m2rg_W4FailedTdCancelCmkEnvOf' LoopAdvEnv maxOps R.C R.K (StatesRecvFK R.C.F R.K) R.fc_cur
    else fun _ => False
  DecEnv := W4TrialDecCmkEnv
  TrialEnv := m2rg_W4TrialRunWideCmkEnvOf' LoopAdvEnv maxOps R.C R.K (StatesRecvFK R.C.F R.K)
  DropEnv := W4TrialDropCmkEnv
  archivedTrials := R.archivedTrials
  g_arch := R.g_arch
  r_arch := R.r_arch
  VecPushEnv := W4BoundedEvs 1 192
  TryDecEnv :=
    if R.isPathB then
      m2rg_TryDecryptCliLinkedEnvOf' LoopAdvEnv maxOps R.C R.K (StatesRecvFK R.C.F R.K) R.td_B.a
    else fun _ => False
  g_out0 := R.g_out0
  r_out0 := R.r_out0
  G_out1 := R.G_out1
  sess_out1 := R.sess_out1
  enc_prev1 := R.enc_prev1

theorem m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf'_proto_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf' LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      mkW4RecvPrekeyWideCmkSlotParamsOf LoopAdvEnv maxOps :=
  rfl

/-- Path A / Path C Stage-P3 `try_decrypt` envelope twin. -/
def m2rg_W4RecvPrekeyTryDecACCmkEnvOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (R : W4RecvPrekeyRealParamsCmk) (evs : List AllocEvent) : Prop :=
  if R.isPathAC then
    m2rg_TryDecryptCliLinkedEnvOf' LoopAdvEnv maxOps R.C R.K (StatesRecvFK R.C.F R.K) R.td_AC.a evs
  else False

theorem m2rg_W4RecvPrekeyTryDecACCmkEnvOf'_proto_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_W4RecvPrekeyTryDecACCmkEnvOf' LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      W4RecvPrekeyTryDecACCmkEnvOf LoopAdvEnv maxOps :=
  rfl

/-- Binary-kit Path B (`Matched`) Stages P1 → P2 → P3 → P4 envelope twin. -/
def m2rg_W4BinaryRecvPrekeyPathBWideCmkEnvOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  let P := m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf' LoopAdvEnv maxOps StatesRecvFK w.base
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2MatchedWideEnv P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials
          w.base.g_arch w.base.r_arch))
      (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneBDomEnv P.TryDecEnv))
        (OptStageEnv
          (W4BinaryStageP4MatchedWideEnv w.base.rd w.base.files w.base.peer w.remoteIdKey
            w.base.g_out0 w.base.r_out0)))) evs

theorem m2rg_W4BinaryRecvPrekeyPathBWideCmkEnvOf'_proto_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_W4BinaryRecvPrekeyPathBWideCmkEnvOf' LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      W4BinaryRecvPrekeyPathBWideCmkEnvOf LoopAdvEnv maxOps :=
  rfl

/-- Binary-kit Path A (`0`-prev) Stages P1 → P2 → P3 → P4 envelope twin. -/
def m2rg_W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2PathAWideEnv w.base.hasOpk w.base.rd w.base.files
          w.base.spkId w.base.kpkId w.base.opkId w.base.C.F w.base.x_res w.base.x_spqr))
      (SeqEnv
        (OptStageEnv
          (W4StageP3WideEnv W4CloneACDomEnv
            (m2rg_W4RecvPrekeyTryDecACCmkEnvOf' LoopAdvEnv maxOps StatesRecvFK w.base)))
        (OptStageEnv
          (W4BinaryStageP4PathAWideEnvFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
            w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
            w.base.g_out0 w.base.r_out0)))) evs

theorem m2rg_W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf'_proto_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf' LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf LoopAdvEnv maxOps :=
  rfl

/-- Binary-kit Path C (`Over` / `prev1`) Stages P1 → P2 → P3 → P4 envelope twin. -/
def m2rg_W4BinaryRecvPrekeyPathCWideCmkEnvFixedOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  let P := m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf' LoopAdvEnv maxOps StatesRecvFK w.base
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2PathCWideEnv w.base.G_cur w.base.st_cur P.CurTrialFailEnv
          P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials w.base.g_arch w.base.r_arch
          w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
          w.base.C.F w.base.x_res w.base.x_spqr))
      (SeqEnv
        (OptStageEnv
          (W4StageP3WideEnv W4CloneACDomEnv
            (m2rg_W4RecvPrekeyTryDecACCmkEnvOf' LoopAdvEnv maxOps StatesRecvFK w.base)))
        (OptStageEnv
          (W4BinaryStageP4PathCWideEnvFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
            w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
            w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) evs

theorem m2rg_W4BinaryRecvPrekeyPathCWideCmkEnvFixedOf'_proto_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_W4BinaryRecvPrekeyPathCWideCmkEnvFixedOf' LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      W4BinaryRecvPrekeyPathCWideCmkEnvFixedOf LoopAdvEnv maxOps :=
  rfl

/-- Complete 4-arm binary-kit W4 (`recv-prekey`) slot envelope twin (`Fixed`). -/
def m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkFixedOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4BinaryStageP1UntrustedEnv w.base.rd w.base.files w.base.peer w.remoteIdKey e ∨
      m2rg_W4BinaryRecvPrekeyPathBWideCmkEnvOf' LoopAdvEnv maxOps StatesRecvFK w e ∨
      m2rg_W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf' LoopAdvEnv maxOps StatesRecvFK w e ∨
      m2rg_W4BinaryRecvPrekeyPathCWideCmkEnvFixedOf' LoopAdvEnv maxOps StatesRecvFK w e)
    FreeOnlyEvs evs

theorem m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkFixedOf'_proto_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkFixedOf' LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      W4BinaryRecvPrekeyWideSlotEnvCmkFixedOf LoopAdvEnv maxOps :=
  rfl

/-- Complete 4-arm binary-kit W4 (`recv-prekey`) slot envelope twin (`AllFixed`). -/
def m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  let P := m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf' LoopAdvEnv maxOps StatesRecvFK w.base
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4BinaryStageP1UntrustedEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2MatchedWideEnv P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials
              w.base.g_arch w.base.r_arch))
          (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneBDomEnv P.TryDecEnv))
            (OptStageEnv
              (W4BinaryStageP4MatchedWideEnvAllFixed w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.g_out0 w.base.r_out0)))) e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2PathAWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files
              w.base.spkId w.base.kpkId w.base.opkId w.base.C.F w.base.x_res w.base.x_spqr))
          (SeqEnv
            (OptStageEnv
              (W4StageP3WideEnv W4CloneACDomEnv
                (m2rg_W4RecvPrekeyTryDecACCmkEnvOf' LoopAdvEnv maxOps StatesRecvFK w.base)))
            (OptStageEnv
              (W4BinaryStageP4PathAWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                w.base.g_out0 w.base.r_out0)))) e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2PathCWideEnvAllFixed w.base.G_cur w.base.st_cur P.CurTrialFailEnv
              P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials w.base.g_arch w.base.r_arch
              w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
              w.base.C.F w.base.x_res w.base.x_spqr))
          (SeqEnv
            (OptStageEnv
              (W4StageP3WideEnv W4CloneACDomEnv
                (m2rg_W4RecvPrekeyTryDecACCmkEnvOf' LoopAdvEnv maxOps StatesRecvFK w.base)))
            (OptStageEnv
              (W4BinaryStageP4PathCWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) e)
    FreeOnlyEvs evs

theorem m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf'_proto_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf' LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf LoopAdvEnv maxOps :=
  rfl

/-- Default Path-C Stage-P3 step envelope twin. -/
def m2rg_defaultP3PathCEnvOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (w : W4BinaryRecvPrekeyParamsCmk) : List AllocEvent → Prop :=
  OptStageEnv
    (W4StageP3WideEnv W4CloneACDomEnv
      (m2rg_W4RecvPrekeyTryDecACCmkEnvOf' LoopAdvEnv maxOps StatesRecvFK w.base))

theorem m2rg_defaultP3PathCEnvOf'_proto_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_defaultP3PathCEnvOf' LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      w4c_defaultP3PathCEnvOf LoopAdvEnv maxOps :=
  rfl

/-- `P3PathCEnv`-parametric Path C Stages P1 → P2 → `P3PathCEnv` → P4 envelope twin. -/
def m2rg_W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed'
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  let P := m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf' LoopAdvEnv maxOps StatesRecvFK w.base
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2PathCWideEnv w.base.G_cur w.base.st_cur P.CurTrialFailEnv
          P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials w.base.g_arch w.base.r_arch
          w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
          w.base.C.F w.base.x_res w.base.x_spqr))
      (SeqEnv (P3PathCEnv w)
        (OptStageEnv
          (W4BinaryStageP4PathCWideEnvFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
            w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
            w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) evs

theorem m2rg_W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed'_proto_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed' LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed LoopAdvEnv maxOps :=
  rfl

/-- Complete 4-arm `P3PathCEnv`-parametric binary-kit W4 (`recv-prekey`) slot envelope twin (`Fixed`). -/
def m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf'
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4BinaryStageP1UntrustedEnv w.base.rd w.base.files w.base.peer w.remoteIdKey e ∨
      m2rg_W4BinaryRecvPrekeyPathBWideCmkEnvOf' LoopAdvEnv maxOps StatesRecvFK w e ∨
      m2rg_W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf' LoopAdvEnv maxOps StatesRecvFK w e ∨
      m2rg_W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed'
        LoopAdvEnv maxOps StatesRecvFK P3PathCEnv w e)
    FreeOnlyEvs evs

theorem m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf'_proto_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf'
        LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf LoopAdvEnv maxOps :=
  rfl

theorem m2rg_wideSlotEnvCmkWithP3CFixedOf'_default_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) (StatesRecvFK : m2rg_StatesRecvEnvFam) :
    m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf'
        LoopAdvEnv maxOps StatesRecvFK
        (m2rg_defaultP3PathCEnvOf' LoopAdvEnv maxOps StatesRecvFK) =
      m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkFixedOf' LoopAdvEnv maxOps StatesRecvFK :=
  rfl

/-- Complete 4-arm `P3PathCEnv`-parametric binary-kit W4 (`recv-prekey`) slot envelope twin (`AllFixed`). -/
def m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf'
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  let P := m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf' LoopAdvEnv maxOps StatesRecvFK w.base
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4BinaryStageP1UntrustedEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2MatchedWideEnv P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials
              w.base.g_arch w.base.r_arch))
          (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneBDomEnv P.TryDecEnv))
            (OptStageEnv
              (W4BinaryStageP4MatchedWideEnvAllFixed w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.g_out0 w.base.r_out0)))) e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2PathAWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files
              w.base.spkId w.base.kpkId w.base.opkId w.base.C.F w.base.x_res w.base.x_spqr))
          (SeqEnv
            (OptStageEnv
              (W4StageP3WideEnv W4CloneACDomEnv
                (m2rg_W4RecvPrekeyTryDecACCmkEnvOf' LoopAdvEnv maxOps StatesRecvFK w.base)))
            (OptStageEnv
              (W4BinaryStageP4PathAWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                w.base.g_out0 w.base.r_out0)))) e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2PathCWideEnvAllFixed w.base.G_cur w.base.st_cur P.CurTrialFailEnv
              P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials w.base.g_arch w.base.r_arch
              w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
              w.base.C.F w.base.x_res w.base.x_spqr))
          (SeqEnv (P3PathCEnv w)
            (OptStageEnv
              (W4BinaryStageP4PathCWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) e)
    FreeOnlyEvs evs

theorem m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf'_proto_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf'
        LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf LoopAdvEnv maxOps :=
  rfl

theorem m2rg_wideSlotEnvCmkWithP3CAllFixedOf'_default_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) (StatesRecvFK : m2rg_StatesRecvEnvFam) :
    m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf'
        LoopAdvEnv maxOps StatesRecvFK
        (m2rg_defaultP3PathCEnvOf' LoopAdvEnv maxOps StatesRecvFK) =
      m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf' LoopAdvEnv maxOps StatesRecvFK :=
  rfl

theorem m2rg_wideSlotEnvCmkWithP3CAllFixed'_eq_fixed {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {StatesRecvFK : m2rg_StatesRecvEnvFam}
    {P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop}
    {w : W4BinaryRecvPrekeyParamsCmk}
    (hfiles : w.base.files = runFiles i) (hrd : w.base.rd = cliIo.rd) :
    m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf'
        LoopAdvEnv maxOps StatesRecvFK P3PathCEnv w =
      m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf'
        LoopAdvEnv maxOps StatesRecvFK P3PathCEnv w := by
  have hsessLoad : ∀ a : AddrVal,
      cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
          (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          (ofBytesEnv RecordDeserializeCancelEnv) (runFiles i) StoresGhost.opened.sessions a =
        cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
          (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
          (ofBytesEnv RecordDeserializeCancelEnv) (runFiles i) StoresGhost.opened.sessions a := by
    intro a; unfold cliSessionKitLoadPollEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_sessions hi _)]
  have htrustPoll : ∀ (a : AddrVal) (k : IdentityKey) (d : Direction),
      cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          (runFiles i) StoresGhost.opened.identity a k d =
        cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
          (runFiles i) StoresGhost.opened.identity a k d := by
    intro a k d; unfold cliIdentityKitTrustPollEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_identities hi _)]
  have hsavePoll : ∀ (a : AddrVal) (k : IdentityKey),
      cliIdentityKitSavePollEnv cliIo.rd (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          DirPutStrEnv (runFiles i) StoresGhost.opened.identity a k =
        cliIdentityKitSavePollEnv cliIo.rd (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
          DirPutStrEnv (runFiles i) StoresGhost.opened.identity a k := by
    intro a k; unfold cliIdentityKitSavePollEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_identities hi _)]
  have hsess : ∀ peer,
      W4BinarySessLoadStepEnvAllFixed cliIo.rd (runFiles i) peer =
        CliRealBinaryKitEnvs.W4BinarySessLoadStepEnv cliIo.rd (runFiles i) peer := by
    intro peer; unfold W4BinarySessLoadStepEnvAllFixed CliRealBinaryKitEnvs.W4BinarySessLoadStepEnv
    rw [hsessLoad peer.val]
  have htrust : ∀ peer k,
      W4BinaryIdTrustStepEnvAllFixed cliIo.rd (runFiles i) peer k =
        CliRealBinaryKitEnvs.W4BinaryIdTrustStepEnv cliIo.rd (runFiles i) peer k := by
    intro peer k; unfold W4BinaryIdTrustStepEnvAllFixed CliRealBinaryKitEnvs.W4BinaryIdTrustStepEnv
    rw [htrustPoll peer.val k .receiving]
  have hsave : ∀ peer k,
      W4BinaryIdSaveStepEnvAllFixed cliIo.rd (runFiles i) peer k =
        CliRealBinaryKitEnvs.W4BinaryIdSaveStepEnv cliIo.rd (runFiles i) peer k := by
    intro peer k; unfold W4BinaryIdSaveStepEnvAllFixed CliRealBinaryKitEnvs.W4BinaryIdSaveStepEnv
    rw [hsavePoll peer.val k]
  have hspk : ∀ id,
      W4BinarySpkGetStepEnvAllFixed cliIo.rd (runFiles i) id =
        CliRealBinaryKitEnvs.W4BinarySpkGetStepEnv cliIo.rd (runFiles i) id := by
    intro id; unfold W4BinarySpkGetStepEnvAllFixed CliRealBinaryKitEnvs.W4BinarySpkGetStepEnv CliSpkGetPollEnv
    dsimp only
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_signed hi _)]
  have hkpk : ∀ id,
      W4BinaryKpkGetStepEnvAllFixed cliIo.rd (runFiles i) id =
        CliRealBinaryKitEnvs.W4BinaryKpkGetStepEnv cliIo.rd (runFiles i) id := by
    intro id; unfold W4BinaryKpkGetStepEnvAllFixed CliRealBinaryKitEnvs.W4BinaryKpkGetStepEnv CliKpkGetPollEnv
      LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.KpkPassEnv
    dsimp only
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_kyberOneTime hi _),
      dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_kyberLastResort_keyName hi id)]
  have hpk : ∀ id,
      W4BinaryPkGetStepEnvAllFixed cliIo.rd (runFiles i) id =
        CliRealBinaryKitEnvs.W4BinaryPkGetStepEnv cliIo.rd (runFiles i) id := by
    intro id; unfold W4BinaryPkGetStepEnvAllFixed CliRealBinaryKitEnvs.W4BinaryPkGetStepEnv CliPkGetPollEnv
    dsimp only
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_oneTime hi _)]
  have hselfKp :
      W4BinarySelfKpStepEnvAllFixed cliIo.rd (runFiles i) =
        CliRealBinaryKitEnvs.W4BinarySelfKpStepEnv cliIo.rd (runFiles i) := by
    unfold W4BinarySelfKpStepEnvAllFixed CliRealBinaryKitEnvs.W4BinarySelfKpStepEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_own_ikp hi)]
  have hselfReg :
      W4BinarySelfRegIdStepEnvAllFixed cliIo.rd (runFiles i) =
        CliRealBinaryKitEnvs.W4BinarySelfRegIdStepEnv cliIo.rd (runFiles i) := by
    unfold W4BinarySelfRegIdStepEnvAllFixed CliRealBinaryKitEnvs.W4BinarySelfRegIdStepEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_own_regId hi)]
  have hpkRem : ∀ id,
      W4BinaryPkRemoveStepEnvAllFixed cliIo.rd (runFiles i) id =
        W4BinaryPkRemoveStepEnv cliIo.rd (runFiles i) id := by
    intro id; unfold W4BinaryPkRemoveStepEnvAllFixed W4BinaryPkRemoveStepEnv CliPkRemovePollEnv
    dsimp only
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_oneTime hi _)]
  have hp1ok : ∀ peer k,
      W4BinaryStageP1OkEnvAllFixed cliIo.rd (runFiles i) peer k =
        W4BinaryStageP1OkEnv cliIo.rd (runFiles i) peer k := by
    intro peer k; funext evs; unfold W4BinaryStageP1OkEnvAllFixed W4BinaryStageP1OkEnv
    rw [hsess, htrust]
  have hp1un : ∀ peer k,
      W4BinaryStageP1UntrustedEnvAllFixed cliIo.rd (runFiles i) peer k =
        W4BinaryStageP1UntrustedEnv cliIo.rd (runFiles i) peer k := by
    intro peer k; funext evs; unfold W4BinaryStageP1UntrustedEnvAllFixed W4BinaryStageP1UntrustedEnv
    rw [hsess, htrust]
  have hp2a : ∀ hasOpk spkId kpkId opkId F x_res x_spqr,
      W4BinaryStageP2PathAWideEnvAllFixed hasOpk cliIo.rd (runFiles i) spkId kpkId opkId F x_res x_spqr =
        W4BinaryStageP2PathAWideEnv hasOpk cliIo.rd (runFiles i) spkId kpkId opkId F x_res x_spqr := by
    intro hasOpk spkId kpkId opkId F x_res x_spqr; funext evs
    unfold W4BinaryStageP2PathAWideEnvAllFixed W4BinaryStageP2PathAWideEnv
    rw [hspk, hkpk, hpk, hselfKp, hselfReg]
  have hp2c : ∀ {α : Type} G_cur st_cur CurTrialFailEnv
      (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) xs g_arch r_arch
      hasOpk spkId kpkId opkId F x_res x_spqr,
      W4BinaryStageP2PathCWideEnvAllFixed G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
          g_arch r_arch hasOpk cliIo.rd (runFiles i) spkId kpkId opkId F x_res x_spqr =
        W4BinaryStageP2PathCWideEnv G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
          g_arch r_arch hasOpk cliIo.rd (runFiles i) spkId kpkId opkId F x_res x_spqr := by
    intro α G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs g_arch r_arch
      hasOpk spkId kpkId opkId F x_res x_spqr; funext evs
    unfold W4BinaryStageP2PathCWideEnvAllFixed W4BinaryStageP2PathCWideEnv
    rw [hspk, hkpk, hpk, hselfKp, hselfReg]
  have hp4m : ∀ peer k g_out0 r_out0,
      W4BinaryStageP4MatchedWideEnvAllFixed cliIo.rd (runFiles i) peer k g_out0 r_out0 =
        W4BinaryStageP4MatchedWideEnv cliIo.rd (runFiles i) peer k g_out0 r_out0 := by
    intro peer k g_out0 r_out0; funext evs
    unfold W4BinaryStageP4MatchedWideEnvAllFixed W4BinaryStageP4MatchedWideEnv
    rw [hsave]
  have hp4a : ∀ hasOpk peer k kpkId spkId opkId bk g_out0 r_out0,
      W4BinaryStageP4PathAWideEnvAllFixed hasOpk cliIo.rd (runFiles i) peer k kpkId spkId opkId bk
          g_out0 r_out0 =
        W4BinaryStageP4PathAWideEnvFixed hasOpk cliIo.rd (runFiles i) peer k kpkId spkId opkId bk
          g_out0 r_out0 := by
    intro hasOpk peer k kpkId spkId opkId bk g_out0 r_out0; funext evs
    unfold W4BinaryStageP4PathAWideEnvAllFixed W4BinaryStageP4PathAWideEnvFixed
    rw [hsave, hpkRem]
  have hp4c : ∀ hasOpk peer k kpkId spkId opkId bk G_out1 sess_out1 enc_prev1,
      W4BinaryStageP4PathCWideEnvAllFixed hasOpk cliIo.rd (runFiles i) peer k kpkId spkId opkId bk
          G_out1 sess_out1 enc_prev1 =
        W4BinaryStageP4PathCWideEnvFixed hasOpk cliIo.rd (runFiles i) peer k kpkId spkId opkId bk
          G_out1 sess_out1 enc_prev1 := by
    intro hasOpk peer k kpkId spkId opkId bk G_out1 sess_out1 enc_prev1; funext evs
    unfold W4BinaryStageP4PathCWideEnvAllFixed W4BinaryStageP4PathCWideEnvFixed
    rw [hsave, hpkRem]
  funext evs
  unfold m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf'
    m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf'
    m2rg_W4BinaryRecvPrekeyPathBWideCmkEnvOf'
    m2rg_W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf'
    m2rg_W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed'
  dsimp only
  rw [hfiles, hrd, hp1un, hp1ok, hp2a, hp2c, hp4m, hp4a, hp4c]

theorem m2rg_wideSlotEnvCmkAllFixed'_eq_fixed {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {StatesRecvFK : m2rg_StatesRecvEnvFam}
    {w : W4BinaryRecvPrekeyParamsCmk}
    (hfiles : w.base.files = runFiles i) (hrd : w.base.rd = cliIo.rd) :
    m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf' LoopAdvEnv maxOps StatesRecvFK w =
      m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkFixedOf' LoopAdvEnv maxOps StatesRecvFK w :=
  m2rg_wideSlotEnvCmkWithP3CAllFixed'_eq_fixed hi
    (P3PathCEnv := m2rg_defaultP3PathCEnvOf' LoopAdvEnv maxOps StatesRecvFK) hfiles hrd

/-- Parametric `(smallFileCap, maxCt)` domain bundle twin for `W4RecvPrekeyRealParamsCmk`. -/
structure m2rg_W4RecvPrekeyRealDomCmkOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (smallFileCap maxCt : Nat) (R : W4RecvPrekeyRealParamsCmk) : Prop where
  kpk_dir : R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = StoresGhost.opened.kyber.lastResort
  outer_dom : W4DecryptPrekeyTightDom
    (m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf' LoopAdvEnv maxOps StatesRecvFK R)
    2097152 smallFileCap 286196 286196 2097152 286196 2097152 16384 2097152 2457152 4096
  cur_fail_dom : R.hasCurSession = true → W4FailedTdDomCmkOf R.C.F R.K maxCt R.fc_cur
  trials_dom : ∀ x ∈ R.archivedTrials, W4ArchivedTrialDomCmkOf R.C.F R.K maxCt x
  tdB_dom : R.isPathB = true → W4TryDecryptCallDomCmkOf R.C.F R.K maxCt R.td_B
  tdAC_dom : R.isPathAC = true → W4TryDecryptPathACDomCmkOf R.C.F R.K maxCt R.td_AC

private theorem m2rg_tryDecryptCallDomCmkOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {td : W4TryDecryptCallCmk}
    (h : W4TryDecryptCallDomCmkOf F K c₁ td) :
    W4TryDecryptCallDomCmkOf F K c₂ td :=
  { h with ct_le := Nat.le_trans h.ct_le hc }

private theorem m2rg_failedTdDomCmkOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {fc : W4FailedTryDecryptCallCmk}
    (h : W4FailedTdDomCmkOf F K c₁ fc) :
    W4FailedTdDomCmkOf F K c₂ fc :=
  ⟨m2rg_tryDecryptCallDomCmkOf_mono hc h.td_dom, h.align_le, h.cancel_live⟩

private theorem m2rg_archivedTrialDomCmkOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {tr : W4ArchivedTrialCmk}
    (h : W4ArchivedTrialDomCmkOf F K c₁ tr) :
    W4ArchivedTrialDomCmkOf F K c₂ tr :=
  ⟨h.enc_le, h.live_le_peak, h.live_le_drop, h.drop_caps, h.tr_gv, h.tr_dom,
    m2rg_failedTdDomCmkOf_mono hc h.tr_fail⟩

private theorem m2rg_tryDecryptPathACDomCmkOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {td : W4TryDecryptCallCmk}
    (h : W4TryDecryptPathACDomCmkOf F K c₁ td) :
    W4TryDecryptPathACDomCmkOf F K c₂ td :=
  ⟨m2rg_tryDecryptCallDomCmkOf_mono hc h.base, h.rc_nil⟩

theorem m2rg_toRealDomCmkOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    {C : Crypto} {K : MlKem} {maxCt : Nat}
    {i : Inputs} {peerV : AddrV} {files : FsFiles}
    {R : W4RecvPrekeyRealParamsCmk}
    (hcs : W4BinaryCallSiteDomCmk C K maxCt (addrValOf peerV) files R)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV))
    (hct : maxCt ≤ msgCapBytes) :
    m2rg_W4RecvPrekeyRealDomCmkOf' LoopAdvEnv maxOps StatesRecvFK
      sessionCapBytes msgCapBytes R where
  kpk_dir := hcs.kpk_dir
  outer_dom := by
    have hpeer40 : R.peer.name.bytes.length ≤ 40 := by
      have hp40 := parseArgs_peer_name_length_le hparse
      change R.peer.val.name.length ≤ 40
      rw [hcs.eq_peerVal]
      exact hp40
    have hsess2M : sessionCapBytes ≤ 2097152 := by
      unfold sessionCapBytes
      decide
    have hcur :
        (∀ evs, ¬ (m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf' LoopAdvEnv maxOps StatesRecvFK R).CurTrialFailEnv evs) ∨
        ∃ ses_cur : Session (List (BitVec 8)),
          ses_cur.state = R.st_cur ∧ SessionGhostValid R.G_cur ses_cur ∧
            SessionCloneDom 286196 ses_cur := by
      rcases hcs.cur_dom with hfalse | hses
      · refine Or.inl fun evs hev => ?_
        dsimp only [m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf'] at hev
        rw [hfalse] at hev
        exact nomatch hev
      · exact Or.inr hses
    refine
      { peer_len := hpeer40
        ownKey_len := hcs.ownKey_len
        ownReg_len := hcs.ownReg_len
        kpkMark_len := hcs.kpkMark_len
        res_old := hcs.res_old
        res_new := hcs.res_new
        ikm_small := by decide
        spqr_key := hcs.spqr_key
        sess_cap := fun bs hr => by
          dsimp only [m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf'] at hr
          rw [hcs.eq_rd] at hr
          exact Nat.le_trans (cliIo_rd_ok_length_le_sessionCapBytes R.files _ bs hr) hsess2M
        small_cap := fun d _ n bs hr => by
          dsimp only [m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf'] at hr
          rw [hcs.eq_rd] at hr
          exact cliIo_rd_ok_length_le_sessionCapBytes R.files (pathOf d.path n) bs hr
        cur_dom := hcur
        arch_valid := hcs.arch_valid
        arch_enc := hcs.arch_enc
        out0_valid := hcs.out0_valid
        out0_enc := hcs.out0_enc
        out1_freshBob := hcs.out1_freshBob
        trials_len4 := hcs.trials_len4 }
  cur_fail_dom hcur := m2rg_failedTdDomCmkOf_mono hct (hcs.cur_fail_dom hcur)
  trials_dom y hy := m2rg_archivedTrialDomCmkOf_mono hct (hcs.trials_dom y hy)
  tdB_dom hb := m2rg_tryDecryptCallDomCmkOf_mono hct (hcs.tdB_dom hb)
  tdAC_dom hac := m2rg_tryDecryptPathACDomCmkOf_mono hct (hcs.tdAC_dom hac)

private theorem m2rg_optStageEnv_mono {E₁ E₂ : List AllocEvent → Prop}
    (hE : ∀ evs, E₁ evs → E₂ evs) (evs : List AllocEvent)
    (h : OptStageEnv E₁ evs) : OptStageEnv E₂ evs :=
  h.elim Or.inl (fun h2 => Or.inr (hE evs h2))

private theorem m2rg_iterSeqEnv_mono {α : Type} {S₁ S₂ : α → List AllocEvent → Prop}
    (hS : ∀ x evs, S₁ x evs → S₂ x evs) :
    ∀ (xs : List α) (evs : List AllocEvent),
      IterSeqEnv S₁ xs evs → IterSeqEnv S₂ xs evs
  | [], _, h => h
  | x :: xs, _, h =>
    seqEnv_mono (fun e hx => hS x e hx) (fun e hxs => m2rg_iterSeqEnv_mono hS xs e hxs) h

private theorem m2rg_archivedTrialIterEnv_mono {α : Type}
    {DecEnv T₁ T₂ DropEnv : α → List AllocEvent → Prop}
    (hT : ∀ x evs, T₁ x evs → T₂ x evs) (x : α) (evs : List AllocEvent)
    (h : ArchivedTrialIterEnv DecEnv T₁ DropEnv x evs) :
    ArchivedTrialIterEnv DecEnv T₂ DropEnv x evs :=
  ConcatEnv.mono
    (fun _ h12 => ConcatEnv.mono (fun _ hd => hd) (fun e ht => hT x e ht) h12)
    (fun _ hdr => hdr) h

private theorem m2rg_cloneFailWideEnv_mono {CloneEnv F₁ F₂ DropCloneEnv : List AllocEvent → Prop}
    (hF : ∀ evs, F₁ evs → F₂ evs) (evs : List AllocEvent)
    (h : W4TryDecryptCloneFailWideEnv CloneEnv F₁ DropCloneEnv evs) :
    W4TryDecryptCloneFailWideEnv CloneEnv F₂ DropCloneEnv evs :=
  seqEnv_mono
    (fun _ hc => ConcatEnv.mono
      (fun _ h12 => ConcatEnv.mono (fun _ hcl => hcl) (fun e hf => hF e hf) h12)
      (fun _ hd => hd) hc)
    (fun _ ht => ht) h

private theorem m2rg_stageP3WideEnv_mono {CloneEnv T₁ T₂ : List AllocEvent → Prop}
    (hT : ∀ evs, T₁ evs → T₂ evs) (evs : List AllocEvent)
    (h : W4StageP3WideEnv CloneEnv T₁ evs) :
    W4StageP3WideEnv CloneEnv T₂ evs :=
  seqEnv_mono (fun _ hc => hc)
    (fun _ h2 => seqEnv_mono (fun e ho => m2rg_optStageEnv_mono hT e ho) (fun _ ht => ht) h2) h

private theorem m2rg_failedTdCancelCmkEnvOf'_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    {C : Crypto} {K : MlKem}
    {R₁ R₂ : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    (hR : ∀ st msg evs, R₁ st msg evs → R₂ st msg evs)
    {fc : W4FailedTryDecryptCallCmk} {evs : List AllocEvent}
    (h : m2rg_W4FailedTdCancelCmkEnvOf' L₁ m₁ C K R₁ fc evs) :
    m2rg_W4FailedTdCancelCmkEnvOf' L₂ m₂ C K R₂ fc evs :=
  h.elim Or.inl fun hc => Or.inr (ConcatEnv.mono
    (fun _ ht => m2rg_tryDecryptCliLinkedFailEnvOf'_mono hL hm hR ht)
    (fun _ hd => hd) hc)

private theorem m2rg_trialRunWideCmkEnvOf'_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    {C : Crypto} {K : MlKem}
    {R₁ R₂ : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    (hR : ∀ st msg evs, R₁ st msg evs → R₂ st msg evs)
    (x : W4ArchivedTrialCmk) {evs : List AllocEvent}
    (h : m2rg_W4TrialRunWideCmkEnvOf' L₁ m₁ C K R₁ x evs) :
    m2rg_W4TrialRunWideCmkEnvOf' L₂ m₂ C K R₂ x evs :=
  h.elim Or.inl fun hc => Or.inr (m2rg_cloneFailWideEnv_mono
    (fun _ hf => m2rg_failedTdCancelCmkEnvOf'_mono hL hm hR hf) evs hc)

private theorem m2rg_curTrialFailEnv'_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    {E₁ E₂ : m2rg_StatesRecvEnvFam}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂) (hE : m2rg_StatesRecvSub E₁ E₂)
    (R : W4RecvPrekeyRealParamsCmk) {evs : List AllocEvent}
    (h : (m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf' L₁ m₁ E₁ R).CurTrialFailEnv evs) :
    (m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf' L₂ m₂ E₂ R).CurTrialFailEnv evs := by
  dsimp only [m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf'] at h ⊢
  revert h
  cases R.hasCurSession <;> intro h
  · exact False.elim h
  · exact m2rg_failedTdCancelCmkEnvOf'_mono hL hm (hE R.C.F R.K) h

private theorem m2rg_tryDecBEnv'_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    {E₁ E₂ : m2rg_StatesRecvEnvFam}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂) (hE : m2rg_StatesRecvSub E₁ E₂)
    (R : W4RecvPrekeyRealParamsCmk) {evs : List AllocEvent}
    (h : (m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf' L₁ m₁ E₁ R).TryDecEnv evs) :
    (m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf' L₂ m₂ E₂ R).TryDecEnv evs := by
  dsimp only [m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf'] at h ⊢
  revert h
  cases R.isPathB <;> intro h
  · exact False.elim h
  · exact m2rg_tryDecryptCliLinkedEnvOf'_mono hL hm (hE R.C.F R.K) h

private theorem m2rg_tryDecACEnv'_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    {E₁ E₂ : m2rg_StatesRecvEnvFam}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂) (hE : m2rg_StatesRecvSub E₁ E₂)
    (R : W4RecvPrekeyRealParamsCmk) {evs : List AllocEvent}
    (h : m2rg_W4RecvPrekeyTryDecACCmkEnvOf' L₁ m₁ E₁ R evs) :
    m2rg_W4RecvPrekeyTryDecACCmkEnvOf' L₂ m₂ E₂ R evs := by
  unfold m2rg_W4RecvPrekeyTryDecACCmkEnvOf' at h ⊢
  revert h
  cases R.isPathAC <;> intro h
  · exact False.elim h
  · exact m2rg_tryDecryptCliLinkedEnvOf'_mono hL hm (hE R.C.F R.K) h

private theorem m2rg_stageP2MatchedWideEnv_mono {α : Type}
    {DecEnv T₁ T₂ DropEnv : α → List AllocEvent → Prop}
    (hT : ∀ x evs, T₁ x evs → T₂ x evs) (xs : List α)
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8))) (evs : List AllocEvent)
    (h : W4BinaryStageP2MatchedWideEnv DecEnv T₁ DropEnv xs g_arch r_arch evs) :
    W4BinaryStageP2MatchedWideEnv DecEnv T₂ DropEnv xs g_arch r_arch evs :=
  seqEnv_mono (fun _ hc => hc)
    (fun e ho => m2rg_optStageEnv_mono
      (fun _ h2 => h2.elim Or.inl fun hs => Or.inr (seqEnv_mono
        (fun e1 hi => m2rg_iterSeqEnv_mono (m2rg_archivedTrialIterEnv_mono hT) xs e1 hi)
        (fun _ hp => hp) hs)) e ho) h

private theorem m2rg_stageP2PathCWideEnvAllFixed_mono {α : Type}
    {G_cur : SessionGhost} {st_cur : SessionState (List (BitVec 8))}
    {C₁ C₂ : List AllocEvent → Prop}
    {DecEnv T₁ T₂ DropEnv : α → List AllocEvent → Prop}
    (hC : ∀ evs, C₁ evs → C₂ evs) (hT : ∀ x evs, T₁ x evs → T₂ x evs)
    (xs : List α) (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (spkId kpkId opkId : BitVec 32)
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    (evs : List AllocEvent)
    (h : W4BinaryStageP2PathCWideEnvAllFixed G_cur st_cur C₁ DecEnv T₁ DropEnv xs g_arch r_arch
      hasOpk rd files spkId kpkId opkId F x_res x_spqr evs) :
    W4BinaryStageP2PathCWideEnvAllFixed G_cur st_cur C₂ DecEnv T₂ DropEnv xs g_arch r_arch
      hasOpk rd files spkId kpkId opkId F x_res x_spqr evs :=
  seqEnv_mono
    (fun e hc => m2rg_optStageEnv_mono (m2rg_cloneFailWideEnv_mono hC) e hc)
    (fun _ h2 => seqEnv_mono
      (fun e hl => m2rg_optStageEnv_mono
        (m2rg_iterSeqEnv_mono (m2rg_archivedTrialIterEnv_mono hT) xs) e hl)
      (fun _ hrest => hrest) h2) h

theorem m2rg_wideSlotEnvCmkWithP3CAllFixed'_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    {E₁ E₂ : m2rg_StatesRecvEnvFam}
    {P3₁ P3₂ : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂) (hE : m2rg_StatesRecvSub E₁ E₂)
    (hP3 : ∀ w evs, P3₁ w evs → P3₂ w evs)
    {w : W4BinaryRecvPrekeyParamsCmk} {evs : List AllocEvent}
    (h : m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf' L₁ m₁ E₁ P3₁ w evs) :
    m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf' L₂ m₂ E₂ P3₂ w evs := by
  rcases h with hfr | hseq
  · exact Or.inl hfr
  · refine Or.inr (seqEnv_mono (fun e harm => ?_) (fun _ hfr => hfr) hseq)
    rcases harm with hun | hb | ha | hc
    · exact Or.inl hun
    · refine Or.inr (Or.inl ?_)
      exact seqEnv_mono (fun _ hp1 => hp1)
        (fun _ h2 => seqEnv_mono
          (fun e2 hp2 => m2rg_optStageEnv_mono
            (m2rg_stageP2MatchedWideEnv_mono
              (fun x _ ht => m2rg_trialRunWideCmkEnvOf'_mono hL hm (hE w.base.C.F w.base.K) x ht)
              w.base.archivedTrials w.base.g_arch w.base.r_arch) e2 hp2)
          (fun _ h3 => seqEnv_mono
            (fun e3 hp3 => m2rg_optStageEnv_mono
              (m2rg_stageP3WideEnv_mono (fun _ ht => m2rg_tryDecBEnv'_mono hL hm hE w.base ht))
              e3 hp3)
            (fun _ hp4 => hp4) h3) h2) hb
    · refine Or.inr (Or.inr (Or.inl ?_))
      exact seqEnv_mono (fun _ hp1 => hp1)
        (fun _ h2 => seqEnv_mono (fun _ hp2 => hp2)
          (fun _ h3 => seqEnv_mono
            (fun e3 hp3 => m2rg_optStageEnv_mono
              (m2rg_stageP3WideEnv_mono (fun _ ht => m2rg_tryDecACEnv'_mono hL hm hE w.base ht))
              e3 hp3)
            (fun _ hp4 => hp4) h3) h2) ha
    · refine Or.inr (Or.inr (Or.inr ?_))
      exact seqEnv_mono (fun _ hp1 => hp1)
        (fun _ h2 => seqEnv_mono
          (fun e2 hp2 => m2rg_optStageEnv_mono
            (m2rg_stageP2PathCWideEnvAllFixed_mono
              (fun _ hcf => m2rg_curTrialFailEnv'_mono hL hm hE w.base hcf)
              (fun x _ ht => m2rg_trialRunWideCmkEnvOf'_mono hL hm (hE w.base.C.F w.base.K) x ht)
              w.base.archivedTrials w.base.g_arch w.base.r_arch
              w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
              w.base.C.F w.base.x_res w.base.x_spqr) e2 hp2)
          (fun _ h3 => seqEnv_mono (fun e3 hp3 => hP3 w e3 hp3) (fun _ hp4 => hp4) h3) h2) hc

/-! ## 4. Top-Level `DecPkGhost → List AllocEvent → Prop` Slot Envelopes and Wrappers -/

/-- `(LoopAdvEnv, maxOps, StatesRecvFK)`-parametric unguarded binary-kit W4 (`decrypt_prekey`)
slot envelope twin. -/
abbrev m2rg_realCliDecPkBinaryWideSlotEnvCmkFixedOf' [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (_X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
    W4BinaryCallSiteDomCmk W.C W.Q.K x.msg.message.ciphertext.length x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf' LoopAdvEnv maxOps StatesRecvFK w4 evs

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkFixedOf'_proto_eq [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkFixedOf' LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      realCliDecPkBinaryWideSlotEnvCmkFixedOf LoopAdvEnv maxOps :=
  rfl

/-- Default `(CmkLoopAdvanceEvs, 109)` unguarded W4 slot envelope twin parametric in `StatesRecvFK`. -/
abbrev m2rg_realCliDecPkBinaryWideSlotEnvCmkFixed' [LibsignalPlacement]
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkFixedOf'
    CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps StatesRecvFK X W x evs

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkFixed'_proto_eq [LibsignalPlacement] :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkFixed' m2rg_protoStatesRecvEnvFam =
      realCliDecPkBinaryWideSlotEnvCmkFixed :=
  rfl

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkFixedOf'_ghost_congr [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val)
    (_hm : x.me.val = y.me.val)
    (_hs : x.stores = y.stores)
    (_hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F)
    (_hc : x.coins = y.coins)
    (hmsg : x.msg = y.msg) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkFixedOf' LoopAdvEnv maxOps StatesRecvFK X W x =
      m2rg_realCliDecPkBinaryWideSlotEnvCmkFixedOf' LoopAdvEnv maxOps StatesRecvFK X W y := by
  funext evs
  simp only [m2rg_realCliDecPkBinaryWideSlotEnvCmkFixedOf', hp, hf, hmsg]

/-- `(LoopAdvEnv, maxOps, StatesRecvFK)`-parametric `PeerSpqrStateTight640`-guarded binary-kit W4
(`decrypt_prekey`) slot envelope twin. -/
abbrev m2rg_realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf' [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
    m2rg_realCliDecPkBinaryWideSlotEnvCmkFixedOf' LoopAdvEnv maxOps StatesRecvFK X W x evs

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf'_proto_eq [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf'
        LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf LoopAdvEnv maxOps :=
  rfl

/-- Default `(CmkLoopAdvanceEvs, 109)` `PeerSpqrStateTight640`-guarded W4 slot envelope twin. -/
abbrev m2rg_realCliDecPkBinaryWideSlotEnvCmkGuardedFixed' [LibsignalPlacement]
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf'
    CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps StatesRecvFK X W x evs

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkGuardedFixed'_proto_eq [LibsignalPlacement] :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkGuardedFixed' m2rg_protoStatesRecvEnvFam =
      realCliDecPkBinaryWideSlotEnvCmkGuardedFixed :=
  rfl

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf'_ghost_congr [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf' LoopAdvEnv maxOps StatesRecvFK X W x =
      m2rg_realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf' LoopAdvEnv maxOps StatesRecvFK X W y := by
  funext evs
  dsimp [m2rg_realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf']
  rw [hf, hp,
    m2rg_realCliDecPkBinaryWideSlotEnvCmkFixedOf'_ghost_congr
      LoopAdvEnv maxOps StatesRecvFK X W x y hp hm hs hcp hf hc hmsg]

/-- `(LoopAdvEnv, maxOps, StatesRecvFK, P3PathCEnv)`-parametric unguarded W4 slot envelope twin. -/
abbrev m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf' [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (_X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
    W4BinaryCallSiteDomCmk W.C W.Q.K x.msg.message.ciphertext.length x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf'
        LoopAdvEnv maxOps StatesRecvFK P3PathCEnv w4 evs

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'_proto_eq [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'
        LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf LoopAdvEnv maxOps :=
  rfl

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'_ghost_congr [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val)
    (_hm : x.me.val = y.me.val)
    (_hs : x.stores = y.stores)
    (_hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F)
    (_hc : x.coins = y.coins)
    (hmsg : x.msg = y.msg) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'
        LoopAdvEnv maxOps StatesRecvFK P3PathCEnv X W x =
      m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'
        LoopAdvEnv maxOps StatesRecvFK P3PathCEnv X W y := by
  funext evs
  simp only [m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf', hp, hf, hmsg]

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'_mono [LibsignalPlacement]
    {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    {E₁ E₂ : m2rg_StatesRecvEnvFam}
    {P3₁ P3₂ : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂) (hE : m2rg_StatesRecvSub E₁ E₂)
    (hP3 : ∀ w evs, P3₁ w evs → P3₂ w evs)
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {x : DecPkGhost} {evs : List AllocEvent}
    (h : m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf' L₁ m₁ E₁ P3₁ X W x evs) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf' L₂ m₂ E₂ P3₂ X W x evs := by
  obtain ⟨w4, hcs, hik, hbk, henv⟩ := h
  exact ⟨w4, hcs, hik, hbk, m2rg_wideSlotEnvCmkWithP3CAllFixed'_mono hL hm hE hP3 henv⟩

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkFixedOf'_mono [LibsignalPlacement]
    {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    {E₁ E₂ : m2rg_StatesRecvEnvFam}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂) (hE : m2rg_StatesRecvSub E₁ E₂)
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {x : DecPkGhost} {evs : List AllocEvent}
    (h : m2rg_realCliDecPkBinaryWideSlotEnvCmkFixedOf' L₁ m₁ E₁ X W x evs) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkFixedOf' L₂ m₂ E₂ X W x evs :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'_mono (X := X) hL hm hE
    (fun w e hp3 => m2rg_optStageEnv_mono
      (m2rg_stageP3WideEnv_mono (fun _ ht => m2rg_tryDecACEnv'_mono hL hm hE w.base ht)) e hp3)
    h

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf'_mono [LibsignalPlacement]
    {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    {E₁ E₂ : m2rg_StatesRecvEnvFam}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂) (hE : m2rg_StatesRecvSub E₁ E₂)
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {x : DecPkGhost} {evs : List AllocEvent}
    (h : m2rg_realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf' L₁ m₁ E₁ X W x evs) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf' L₂ m₂ E₂ X W x evs :=
  fun hp => m2rg_realCliDecPkBinaryWideSlotEnvCmkFixedOf'_mono hL hm hE (h hp)

/-- `(LoopAdvEnv, maxOps, StatesRecvFK, P3PathCEnv)`-parametric `PeerSpqrStateTight640`-guarded
binary-kit W4 (`decrypt_prekey`) slot envelope twin. -/
abbrev m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf' [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
    m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'
      LoopAdvEnv maxOps StatesRecvFK P3PathCEnv X W x evs

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf'_proto_eq [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf'
        LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf LoopAdvEnv maxOps :=
  rfl

abbrev m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixed' [LibsignalPlacement]
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf'
    CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps StatesRecvFK P3PathCEnv X W x evs

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixed'_proto_eq [LibsignalPlacement] :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixed' m2rg_protoStatesRecvEnvFam =
      realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixed :=
  rfl

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf'_ghost_congr [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf'
        LoopAdvEnv maxOps StatesRecvFK P3PathCEnv X W x =
      m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf'
        LoopAdvEnv maxOps StatesRecvFK P3PathCEnv X W y := by
  funext evs
  dsimp [m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf']
  rw [hf, hp,
    m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'_ghost_congr
      LoopAdvEnv maxOps StatesRecvFK P3PathCEnv X W x y hp hm hs hcp hf hc hmsg]

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf'_mono [LibsignalPlacement]
    {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    {E₁ E₂ : m2rg_StatesRecvEnvFam}
    {P3₁ P3₂ : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂) (hE : m2rg_StatesRecvSub E₁ E₂)
    (hP3 : ∀ w evs, P3₁ w evs → P3₂ w evs)
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {x : DecPkGhost} {evs : List AllocEvent}
    (h : m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf' L₁ m₁ E₁ P3₁ X W x evs) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf' L₂ m₂ E₂ P3₂ X W x evs :=
  fun hp => m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'_mono hL hm hE hP3 (h hp)

/-- Path-C Stage-P3 step envelope twin with `W4StageP3Prev1WideEnvOf verNeEnv`. -/
def m2rg_verNePrev1P3PathCEnvOf'
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (w : W4BinaryRecvPrekeyParamsCmk) : List AllocEvent → Prop :=
  OptStageEnv
    (W4StageP3Prev1WideEnvOf verNeEnv W4CloneACDomEnv
      (m2rg_W4RecvPrekeyTryDecACCmkEnvOf' LoopAdvEnv maxOps StatesRecvFK w.base) w.base.enc_prev1)

theorem m2rg_verNePrev1P3PathCEnvOf'_proto_eq
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_verNePrev1P3PathCEnvOf' verNeEnv LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      w4c_verNePrev1P3PathCEnvOf verNeEnv LoopAdvEnv maxOps :=
  rfl

abbrev m2rg_verNePrev1P3PathCEnv'
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (w : W4BinaryRecvPrekeyParamsCmk) : List AllocEvent → Prop :=
  m2rg_verNePrev1P3PathCEnvOf' VerNeTightTopEnv LoopAdvEnv maxOps StatesRecvFK w

theorem m2rg_verNePrev1P3PathCEnv'_proto_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_verNePrev1P3PathCEnv' LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      w4c_verNePrev1P3PathCEnv LoopAdvEnv maxOps :=
  rfl

/-- `(verNeEnv, LoopAdvEnv, maxOps, StatesRecvFK)`-parametric unguarded `Cmk + VerNe-prev1`
binary-kit W4 slot envelope twin. -/
abbrev m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf' [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf' LoopAdvEnv maxOps StatesRecvFK
    (m2rg_verNePrev1P3PathCEnvOf' verNeEnv LoopAdvEnv maxOps StatesRecvFK) X W x evs

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf'_proto_eq [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf'
        verNeEnv LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf verNeEnv LoopAdvEnv maxOps :=
  rfl

/-- Default `(VerNeTightTopEnv, CmkLoopAdvanceEvs, 109)` unguarded `Cmk + VerNe-prev1` W4 slot
envelope twin parametric in `StatesRecvFK`. -/
abbrev m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed' [LibsignalPlacement]
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf'
    VerNeTightTopEnv CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps StatesRecvFK X W x evs

/-- `(verNeEnv, LoopAdvEnv, maxOps, StatesRecvFK)`-parametric `PeerSpqrStateTight640`-guarded
`Cmk + VerNe-prev1` binary-kit W4 (`decrypt_prekey`) slot envelope twin. -/
abbrev m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf' [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf' LoopAdvEnv maxOps StatesRecvFK
    (m2rg_verNePrev1P3PathCEnvOf' verNeEnv LoopAdvEnv maxOps StatesRecvFK) X W x evs

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'_proto_eq [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'
        verNeEnv LoopAdvEnv maxOps m2rg_protoStatesRecvEnvFam =
      realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf verNeEnv LoopAdvEnv maxOps :=
  rfl

/-- Default `(VerNeTightTopEnv, CmkLoopAdvanceEvs, 109)` `PeerSpqrStateTight640`-guarded
`Cmk + VerNe-prev1` W4 slot envelope twin parametric in `StatesRecvFK`. -/
abbrev m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed' [LibsignalPlacement]
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'
    VerNeTightTopEnv CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps StatesRecvFK X W x evs

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'_ghost_congr [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'
        verNeEnv LoopAdvEnv maxOps StatesRecvFK X W x =
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'
        verNeEnv LoopAdvEnv maxOps StatesRecvFK X W y :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf'_ghost_congr
    LoopAdvEnv maxOps StatesRecvFK
    (m2rg_verNePrev1P3PathCEnvOf' verNeEnv LoopAdvEnv maxOps StatesRecvFK)
    X W x y hp hm hs hcp hf hc hmsg

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'_ghost_congr [LibsignalPlacement]
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed' StatesRecvFK X W x =
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed' StatesRecvFK X W y :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'_ghost_congr
    VerNeTightTopEnv CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps StatesRecvFK
    X W x y hp hm hs hcp hf hc hmsg

theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkFixedOf'_sub_verNeOf' [LibsignalPlacement]
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {StatesRecvFK : m2rg_StatesRecvEnvFam}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {x : DecPkGhost} {evs : List AllocEvent}
    (h : m2rg_realCliDecPkBinaryWideSlotEnvCmkFixedOf' LoopAdvEnv maxOps StatesRecvFK X W x evs) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf'
      verNeEnv LoopAdvEnv maxOps StatesRecvFK X W x evs :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'_mono (X := X)
    (w4c_loopAdvSub_refl LoopAdvEnv) (Nat.le_refl maxOps)
    (m2rg_statesRecvSub_refl StatesRecvFK)
    (fun _ _ hp3 => hp3.elim Or.inl fun hw => Or.inr (w4StageP3Prev1WideEnvOf_of_wide hw))
    h

/-- Guarded-slot wrapper (`CodeOk`) for `m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'`. -/
theorem m2rg_decPkD2cSlotOkPlacedAtOf_cmkVerNeGuardedOf'_of_unguarded [LibsignalPlacement]
    (CodeOk : Memory → Prop) {M : AllocCostModel}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {StatesRecvFK : m2rg_StatesRecvEnvFam}
    {H : LibsignalHooks} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₀ DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'
        verNeEnv LoopAdvEnv maxOps StatesRecvFK X W g e)
    (hUnguarded : DecPkD2cSlotOkPlacedAtOf CodeOk H X W A lim DecPkEnv₀)
    (hBridge : ∀ g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ g evs →
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf'
        verNeEnv LoopAdvEnv maxOps StatesRecvFK X W g evs) :
    DecPkD2cSlotOkPlacedAtOf CodeOk H X W A lim DecPkEnv :=
  decPkD2cSlotOkPlacedAtOf_targetGuarded_of_unguarded CodeOk hSlot hUnguarded hBridge

/-- `LibsignalFrozen` fixed-`X` guarded-slot wrapper for `m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'`. -/
theorem m2rg_decPkD2cSlotOkFrozenPlacedAt_cmkVerNeGuardedOf'_of_unguarded [LibsignalPlacement]
    {M : AllocCostModel}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {StatesRecvFK : m2rg_StatesRecvEnvFam}
    {H : LibsignalHooks} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₀ DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'
        verNeEnv LoopAdvEnv maxOps StatesRecvFK X W g e)
    (hUnguarded : DecPkD2cSlotOkFrozenPlacedAt H X W A lim DecPkEnv₀)
    (hBridge : ∀ g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ g evs →
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf'
        verNeEnv LoopAdvEnv maxOps StatesRecvFK X W g evs) :
    DecPkD2cSlotOkFrozenPlacedAt H X W A lim DecPkEnv :=
  m2rg_decPkD2cSlotOkPlacedAtOf_cmkVerNeGuardedOf'_of_unguarded
    (LibsignalFrozen lsmpl) hSlot hUnguarded hBridge

/-- Universal-`X` (`DecPkD2cSlotOkFrozenPlaced`) guarded-slot wrapper for `m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'`. -/
theorem m2rg_decPkD2cSlotOkFrozenPlaced_cmkVerNeGuardedOf'_of_unguarded [LibsignalPlacement]
    {M : AllocCostModel}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {StatesRecvFK : m2rg_StatesRecvEnvFam}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₀ : UnreachedPqxdhPrimitives → DecPkGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives)
    (hSlot : ∀ g e, DecPkEnv g e ↔
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'
        verNeEnv LoopAdvEnv maxOps StatesRecvFK X W g e)
    (hUnguarded : ∀ X',
      DecPkD2cSlotOkFrozenPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W)) X' W A lim
        (DecPkEnv₀ X'))
    (hBridge : ∀ X' g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ X' g evs →
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf'
        verNeEnv LoopAdvEnv maxOps StatesRecvFK X' W g evs) :
    DecPkD2cSlotOkFrozenPlaced mmpl gh W A lim DecPkEnv := by
  intro X'
  have hSlot' : ∀ g e, DecPkEnv g e ↔
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'
        verNeEnv LoopAdvEnv maxOps StatesRecvFK X' W g e := by
    intro g e
    rw [hSlot g e]
  exact m2rg_decPkD2cSlotOkPlacedAtOf_cmkVerNeGuardedOf'_of_unguarded
    (LibsignalFrozen lsmpl) hSlot' (hUnguarded X') (hBridge X')

/-- `hRunSub` eliminator from `PeerSpqrStateTight640` via `targetEnv_of_guarded_tight`. -/
theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf'_of_guarded_tight [LibsignalPlacement]
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {StatesRecvFK : m2rg_StatesRecvEnvFam}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'
        verNeEnv LoopAdvEnv maxOps StatesRecvFK X W g e)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val)
    (hevs : DecPkEnv x evs) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf'
      verNeEnv LoopAdvEnv maxOps StatesRecvFK X W x evs :=
  targetEnv_of_guarded_tight hSlot hTight hevs

/-- `CmkLoopAdvanceEvs` / `VerNeTightTopEnv` / `109` `hRunSub` eliminator from `PeerSpqrStateTight640`. -/
theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed'_of_guarded_tight [LibsignalPlacement]
    {StatesRecvFK : m2rg_StatesRecvEnvFam}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed' StatesRecvFK X W g e)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val)
    (hevs : DecPkEnv x evs) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed' StatesRecvFK X W x evs :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf'_of_guarded_tight hSlot hTight hevs

/-- `hRunSub` eliminator at `.recv peer` under `CliPqxdhInputs ⟨W.C, W.Q⟩ i`. -/
theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf'_of_guarded_cliPqInputs_recv
    [LibsignalPlacement]
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {StatesRecvFK : m2rg_StatesRecvEnvFam}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {i : Inputs} {peer : AddrV}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'
        verNeEnv LoopAdvEnv maxOps StatesRecvFK X W g e)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hF : x.F = runFiles i) (hpeer : x.peer.val = addrValOf peer)
    (hevs : DecPkEnv x evs) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf'
      verNeEnv LoopAdvEnv maxOps StatesRecvFK X W x evs :=
  targetEnv_of_guarded_cliPqInputs_recv hSlot hi hparse hF hpeer hevs

/-- `CmkLoopAdvanceEvs` / `VerNeTightTopEnv` / `109` `hRunSub` eliminator at `.recv peer` under `CliPqxdhInputs ⟨W.C, W.Q⟩ i`. -/
theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed'_of_guarded_cliPqInputs_recv
    [LibsignalPlacement]
    {StatesRecvFK : m2rg_StatesRecvEnvFam}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {i : Inputs} {peer : AddrV}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed' StatesRecvFK X W g e)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hF : x.F = runFiles i) (hpeer : x.peer.val = addrValOf peer)
    (hevs : DecPkEnv x evs) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed' StatesRecvFK X W x evs :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf'_of_guarded_cliPqInputs_recv
    hSlot hi hparse hF hpeer hevs

/-- `CmkLoopAdvanceEvs` specialization of
`CliDpPollTrustedWideBridge.realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf_of_guarded_tight`. -/
theorem m2rg_cmk25000_verNeFixedOf_of_guarded_tight [LibsignalPlacement]
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop} {maxOps : Nat}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf
        verNeEnv CmkLoopAdvanceEvs maxOps X W g e)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val)
    (hevs : DecPkEnv x evs) :
    realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf
      verNeEnv CmkLoopAdvanceEvs maxOps X W x evs :=
  realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf_of_guarded_tight hSlot hTight hevs

/-- `CmkLoopAdvanceEvs` specialization of
`CliDpPollTrustedWideBridge.realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf_of_guarded_cliPqInputs_recv`. -/
theorem m2rg_cmk25000_verNeFixedOf_of_guarded_cliPqInputs_recv [LibsignalPlacement]
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop} {maxOps : Nat}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {i : Inputs} {peer : AddrV}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {x : DecPkGhost} {evs : List AllocEvent}
    (hSlot : ∀ g e, DecPkEnv g e ↔
      realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf
        verNeEnv CmkLoopAdvanceEvs maxOps X W g e)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hF : x.F = runFiles i) (hpeer : x.peer.val = addrValOf peer)
    (hevs : DecPkEnv x evs) :
    realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf
      verNeEnv CmkLoopAdvanceEvs maxOps X W x evs :=
  realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf_of_guarded_cliPqInputs_recv
    hSlot hi hparse hF hpeer hevs

/-- `(verNeEnv, LoopAdvEnv, maxOps, StatesRecvFK)`-parametric D2(c) tied linked poll envelope twin. -/
abbrev m2rg_CliDpPollD2cTiedLinkedEnvOf' [LibsignalPlacement] {A : RustAlloc}
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  CliDpPollD2cTiedWideEnvOf (A := A) verNeEnv W X B ReadEnv DeserEnv
    P2PathAErrEnv P2PathAOkEnv P2OverErrEnv P2OverOkEnv
    (fun W => m2rg_TryDecryptCliLinkedEnvOf' LoopAdvEnv maxOps W.C W.Q.K
      (StatesRecvFK W.C.F W.Q.K)) p4Envs g evs

theorem m2rg_CliDpPollD2cTiedLinkedEnvOf'_83_proto_eq [LibsignalPlacement] {A : RustAlloc}
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop) :
    m2rg_CliDpPollD2cTiedLinkedEnvOf' (A := A) verNeEnv CmkLoopAdvanceEvs 83
        m2rg_protoStatesRecvEnvFam =
      CliDpPollD2cTiedLinkedEnvOf (A := A) verNeEnv :=
  rfl

/-- `(verNeEnv, LoopAdvEnv, maxOps, StatesRecvFK)`-parametric `SeqFree` D2(c) linked poll envelope
twin. -/
def m2rg_CliDpPollD2cSeqFreeLinkedEnvOf' [LibsignalPlacement] {A : RustAlloc}
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let tdEnv := m2rg_TryDecryptCliLinkedEnvOf' LoopAdvEnv maxOps W.C W.Q.K
    (StatesRecvFK W.C.F W.Q.K)
  CliDpPollTrustedSeqFreeEnv (A := A) W X B ReadEnv DeserEnv
    P2PathAErrEnv P2PathAOkEnv tdEnv g evs ∨
  CliDpPollPathCTiedEnvOf (A := A) verNeEnv W X B ReadEnv DeserEnv
    P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs

theorem m2rg_CliDpPollD2cSeqFreeLinkedEnvOf'_83_proto_eq [LibsignalPlacement] {A : RustAlloc}
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop) :
    m2rg_CliDpPollD2cSeqFreeLinkedEnvOf' (A := A) verNeEnv CmkLoopAdvanceEvs 83
        m2rg_protoStatesRecvEnvFam =
      CliDpPollD2cSeqFreeLinkedEnvOf (A := A) verNeEnv :=
  rfl

/-- `(verNeEnv, LoopAdvEnv, maxOps, StatesRecvFK)`-parametric concrete CLI instantiation of
`m2rg_CliDpPollD2cSeqFreeLinkedEnvOf'`. -/
abbrev m2rg_CliDpPollD2cSeqFreeConcreteEnvOf' [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
  let selfEnv := fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk cliRunBudgets) ReadEnv
  let kitEnvs := cliStageP2KitEnvs (A := A) ReadEnv cliRunBudgets selfEnv
  m2rg_CliDpPollD2cSeqFreeLinkedEnvOf' (A := A) verNeEnv LoopAdvEnv maxOps StatesRecvFK W X
    cliRunBudgets ReadEnv
    (ofBytesEnv RecordDeserializeCancelEnv)
    (cliP2PathAOptFieldsErrEnv A ReadEnv X W cliRunBudgets selfEnv)
    (cliP2PathAOptFieldsOkEnv A ReadEnv X W cliRunBudgets selfEnv)
    (P2OverPathCErrEnvOf (A := A) X W cliRunBudgets
      (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
      (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
      kitEnvs)
    (P2OverPathCOkEnvOf (A := A) X W cliRunBudgets
      (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
      PromoteOverArchiveCanonSessEnv
      kitEnvs)
    (fun B F0 peer pid kpkId spkId kbk =>
      cliPollStageP4Prev1SeqFreeEnvsAux A B F0 peer pid kpkId spkId kbk ReadEnv)
    g evs

theorem m2rg_CliDpPollD2cSeqFreeConcreteEnvOf'_83_proto_eq [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop) :
    m2rg_CliDpPollD2cSeqFreeConcreteEnvOf' verNeEnv CmkLoopAdvanceEvs 83
        m2rg_protoStatesRecvEnvFam =
      CliDpPollD2cSeqFreeConcreteEnvOf verNeEnv :=
  rfl

end LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins
