/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOfEnvGlue
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollAuxPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.StageP3RawBodyPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBob
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobProducerAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobTightProducer
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage4OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
import ProofLib.SepLogic.WPp

/-!
# Fixed-Budget Raw-`VerNe` Slot-520 `OverD3` Producer

**Checked by Lean.**

Provides closed Slot-520 (`cliDecryptPrekey`) `OverD3` stage producers and slot wrappers specialized
to `cliRunBudgets` over `VerNeTightTopRawEnv`, `ReadFileRuleEnvFixed cliIo.rd`,
`PromoteOverArchiveCanonSessEnv`, `cliPollSessPrev1SeqFreeBudgetEnv`, and memory-extracted
`SessionGhostValid` witnesses.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAVerNeRawSlot520

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (IdentityKey PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (ApiError Session SessionRecord)
open CryptoVerification (
  IsLsBlockProg LibsignalFrozen LibsignalFullPlacement LibsignalPlacement
  libsignalFrozen_of_keepsFrozen lsProg_51 lsProg_75 lsmpl lsρ withLsCl
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  SessionExtraRel coroOpkIdAtP4 hdrOpkIdBv? mkP2AcceptKeysInput p1LoadedRecordAt stageP1ProgPlaced
  stageP4CallStack stageP4EnvOk stageP4Quiet
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  OverPrevEncOK StorePrev1Ops clearPending stageP3Sub5ExtraPrePrev1
)
open CryptoVerification.E2E (
  PreKeyMessageFields ResponderPreKeySecrets UnreachedPqxdhPrimitives acceptInput
  aesDecHookMallocng keyPairOf modelPrims toU8 vecU8
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  bytesToBv8 ofSignalPqxdhAcceptKeysInput ofSignalPqxdhDRKey
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys acceptKeys_ofSignalPqxdhPrimitives)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (ClosureCalleeSavedP4)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  bytesToBv8_vecU8 ls_subroutine_ok_withLsFrozen_of_block ofSignalPqxdhPrimitives vecU8_length
)
open CryptoVerification.E2E.Pqxdh.ResponderStore (clampBv8List_length)
open CryptoVerification.E2E.Record (encSession)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsAt FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost preKeyMsgAt)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall noAllocShimSpec rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost protocolAddressAt signalMessageAt uuidTryParse
)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli (
  StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym
  cliSignedPreKeyVtSym
)
open CryptoVerification.SignalSession.Cli.KitInst (
  cliKpk_getRel_error_iff cliPk_getRel_error_iff cliSpk_getRel_error_iff
)
open CryptoVerification.SignalSession.Cli.MainHops (
  cliIo cliRunBudgets cliRunNeeds cliWrOk coinsInstalledPlaced storesAt
)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem dpPollNeed)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other withPanics_cliGhostExterns
)
open CryptoVerification.SignalSession.Cli.RunProofs (
  SessMatchesPm cliDecryptPrekeyNeed dpWrapFrame pkStoreKeys pkToE? pmOfE
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit StageP1PostRegs cliKitStk cliModelPrims_matchCrypto cliModelPrims_structural
  cliPollIdKitPlaced cliPollId_vtablesPlacedOk cliPollKpkKitPlaced cliPollKpk_vtablesPlacedOk
  cliPollPkKitPlaced cliPollPk_vtablesPlacedOk cliPollSelfKitPlaced cliPollSelf_kpRel_err_placed
  cliPollSelf_kpRel_ok_placed cliPollSelf_regIdRel_err_placed cliPollSelf_regIdRel_ok_placed
  cliPollSelf_vtablesPlacedOk cliPollSessPrev1KitPlaced cliPollSpkKitPlaced
  cliPollSpk_vtablesPlacedOk cliPollStorePrev1OpsPlaced distinctSid_of_decPkOk₀ dpClosSubStack
  dpPollEntryPlaced dpPollProgPlaced entails_sepConj_anyHeap hdrOpkIdBv?_mkPathAHdr mkPathAHdr
  p2Over_cliPollKpk_getEvs_placed p2Over_cliPollPk_getEvs_placed p2Over_cliPollPk_opkOkEvs_placed
  p2Over_cliPollPk_opkOkUpdate_placed p2Over_cliPollSelf_kpEvs_placed
  p2Over_cliPollSelf_regIdEvs_placed p2Over_cliPollSpk_getEvs_placed pathAInitSession
  pathAInitState pkStoreKeys_eq_none_of_kpk_err pkStoreKeys_eq_none_of_opk_err
  pkStoreKeys_eq_none_of_spk_err pmOfE_fields pqxdhAcceptErr_entails_decResAt_anyHeap_ext
  preKeyMsgAt_eq_base_idKey_sep preKeyMsgRemBaseIdKeyAt scope_of_loadRec_some sepWPp_conseq_pre
  sp_sub_576_ne_zero stageP2PostP1At stageP3CoroFrameAt stageP3StackFrameAt x29_eq_sp0_sub_60
  x29_eq_sp_add_c70
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  FilesOkPeer blackBox_row_placed cliGhostExterns_sat_of_cliExternsPlaced
  encodeInjOn_deserializeScopeP_Q loadRec scopeIn scopeKit
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Heap.SpecBudget (
  FmtWriteEnv FormatInnerEnv aesDecBudgetSpec withVmPreserved
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  InitializeBobV1FrozenOkPlaced4KOfEnv StageP2BaseCalleesPlaced4K
  initializeBobSessionErrOwnedFrozen4KPlacedSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget (
  P2Sub1To4Arm3Env P2Sub1To4OkEnv P2Sub4OkEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv StageP2BaseCalleesPlaced4K.of_hooks
  initializeBobSession_ok_v1_of_env_4k_frozen_placed_on_stageP1 isSameAccount_4k_placed_ok_on_stageP1
  p2_errOwned_frozen_to_defs4K_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget (
  P2Sub6Env P2V1Arm4Env P2V1Arm5EnvOfAcceptErr P2V1Arm6EnvOfBob
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget (
  p2PromoteOverAtSpecWithEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget (
  PromoteMatchingMissAtPlacedProp PromoteOverAtPlacedWithEnvProp promoteMatchingMissAt_placed_of_gen
  promoteOverAt_placed_of_gen_withEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget (
  P2OverSub1To4Arm3Env P2OverSub1To4OkEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget (
  P2OverSub6EnvOf P2OverV1Arm4Env P2OverV1Arm5EnvOfAcceptErr P2OverV1Arm6EnvOfBob
  P2OverV1OkEnvOfBobAndProm stageP2OverV1KitsMemInvAtPlacedOfEnvProp
  stageP2_over_v1_kits_frozen_ext_defs_placed_ofEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget (
  OverVerNe1e04CliAtFrozenPlacedBody StageP3Prev1VRegsM3FrozenPlacedStmt
  stageP3Gen_prev1_vregs_at_full_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget (
  StageP4Prev1BranchPlaced StageP4Prev1ExitEnv stageP4Prev1PrePlaced
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (TryDecryptCliEnvOf)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget (
  initializeBobSession_err_owned_frozen_placed_ok_of_accept
)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs (VerNeTightTopRawEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (EncodeRawPreallocPlacedOkX)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  DecPkOkD3 DecPkOkOverV4 decPkOverDef decPkOverDef_pathCOver_stage2_rej_placed pm_fields_of_pkToE
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PollPlacedBudget (
  p2ErrFrame_fold_pathA_d3_placed_rep p2OverOkPost_fold_pathCOver_d3_placed
  p2Over_not_sessMatchesMsg_d3 stageP2_entry_unpack_pathCOver_d3_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOfEnvGlue (
  over_tryDecrypt_cli_of_tdEnv_placed_ok_at
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget (
  cliRunSemOverV4
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollAuxPlacedBudget (
  StageP4Prev1VRegsAtPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget (
  CliDpPollOkOverV4StateFrozenPlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage2PlacedBudget (
  StageP2OverErrD3Placed StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.StageP3RawBodyPlacedBudget (
  cliVerNe1e04_full_placed_ok_raw
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBob (
  DecPkD3ValidOverOfEnv' DecPkD3ValidOverTightConcreteEnv'
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobProducerAux (
  H7pbStageP4Prev1VRegsAtBPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobTightProducer (
  StageP4Prev1VRegsAtBPlacedStmt decPk_d3_validOver_tightRaw_at_b_poll_at_full_placedBudget'
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  RunSlotEnvs slotsOfSigPkFrozenPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget (
  CliStageP4Prev1Envs cliPollSessPrev1SeqFreeBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (
  overGenP3Pre_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget (
  overPollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  StageP2OverEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlacedBudget (
  encSessionMem_clearPending_lt_32 p2Over_serBytes_len stageP2OverV1CallStack4K_le_subStack_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  P2OverPathCErrEnvOf P2OverPathCOkEnvOf PromoteOverArchiveCanonSessEnv
  cliPromoteMatchingMissGen_placed_ok cliPromoteOverGen_archive_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux (
  cliStageP2ClosureHooksPlaced promoteOverArchiveEnv_eq_canon uuidTryParse_placed_vm_code_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage4OverInstPlacedBudget (
  stageP4Prev1_seqFree_placed_inst
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv cliPollSelf_kitPlacedOk_stagesHooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget (
  cliPqxdhAccept_err_owned_full_placed_ok cliPqxdhAccept_opt_fields_full_placed_ok
  pqxdhAccept_err_owned_responder_full_placed_ok_of_block
  pqxdhAccept_opt_fields_responder_full_placed_ok_of_block
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlacedBudget (
  cliPollKpk_wf_of_preKeysWf_placed cliPollPk_wf_of_preKeysWf_placed
  cliPollSpk_wf_of_preKeysWf_placed p2BobInitSessionV1_eq_pathAInitState
  pathA_acceptInput_agree_placed sepWPp_drop_steps sepWPp_with_steps
  sessionExtraRel_pathAInitSession
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget (
  cliPollKpk_getErr_entails_decResAt_anyHeap_placed cliPollPk_getErr_entails_decResAt_anyHeap_placed
  cliPollSelf_kpErr_entails_decResAt_err_placed cliPollSelf_regIdErr_entails_decResAt_err_placed
  cliPollSpk_getErr_entails_decResAt_anyHeap_placed cliPollStageP2_fsAt_stages_placed
  cliResponderPqxdhHookContractsPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliPollKpk_kitPlacedOk cliPollPk_kitPlacedOk cliPollSpk_kitPlacedOk cliStageP2KitEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget (
  dpSlotPollKStatePlaced_inv_vm dpSlotPollKStatePlaced_res_vm
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget (
  cliDecryptPrekey_ok_state_frozen_placed_at_block
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_framelessMemcpy_budget_sat
  cliExternsPlaced_sessionMemcpyRegion_budget_sat cliExternsPlaced_sessionMemcpy_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpSlotPollKStatePlaced dpSlot_ok_state_frozen_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  framelessMemcpyBudgetSpec framelessMemcpySpec noAllocShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## 1. `SeqFree` `Prev1` Stage-P4 Bundle & Raw-`VerNe` Stage-P3 Dischargers -/

def h7ra_cliStageP4Prev1SeqFreeEnvs [LibsignalPlacement] (A : RustAlloc)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) :
    CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk where
  opsEnv := cliPollSessPrev1SeqFreeBudgetEnv A F0 peer (cliKitStk B)
  ikitEnv := cliPollIdBudgetEnv A F0 peer (cliKitStk B) ReadEnv
  pkKitEnv := cliPollPkBudgetEnv A F0 pid (cliKitStk B) ReadEnv
  kpkKitEnv := cliPollKpkBudgetEnv A F0 kpkId spkId kbk (cliKitStk B) ReadEnv

/-- Frozen placed body at `+0x1e04` on `cliGhostExterns gh (cliExternsPlaced mmpl W)` at `OverPrevEncOK` and `VerNeTightTopRawEnv`. -/
theorem h7ra_overVerNe1e04_raw_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh) :
    OverVerNe1e04CliAtFrozenPlacedBody A lim OverPrevEncOK VerNeTightTopRawEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliVerNe1e04_full_placed_ok_raw mmpl gh W hG

/-- Stage-P3 `Prev1` frozen placed contract at `OverPrevEncOK` and `VerNeTightTopRawEnv`. -/
theorem h7ra_stageP3Prev1_rawEnv_frozen_placed [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop} :
    StageP3Prev1VRegsM3FrozenPlacedStmt A lim OverPrevEncOK tdEnv VerNeTightTopRawEnv :=
  stageP3Gen_prev1_vregs_at_full_placed_ok

/-! ## 2. Fixed-`B` (`AtB`) Stage-P2 & Stage-P4 Contracts and `cliRunBudgets` Producers -/

private theorem h7ra_dpPollProgPlaced_eq [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
    CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced H =
      dpPollProgPlaced H := by
  intro H
  dsimp only [CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced,
    dpPollProgPlaced, stageP1ProgPlaced]
  rw [withPanics_cliGhostExterns mmpl gh W]

/-- Fixed-`B` specialization of `StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt`. -/
def H7RAStageP2OverAtBStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (mmpl : MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (S : RunSem)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ)
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (g1 : StoresGhost)
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOkD3 ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → scopeIn r') →
    FilesOkPeer Scope y.g.F y.g.peer.val →
    loadRec Scope y.g.F y.g.peer.val = .ok (some r) →
    r.currentSession = some s_old →
    ¬ SessMatchesPm s_old y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 →
    LibsignalFrozen lsmpl s1.mem →
    s0.trace <+: s1.trace →
    s1.sp = sp →
    sp + 0xcd0#64 = s0.sp →
    dpClosSubStack B ≤ sp.toNat →
    s1.pc = dpPollEntryPlaced + 0x0868#64 →
    s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
    (herr : ∀ sf Pf,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf →
      sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      StageP2OverErrD3Placed A lim st_b P2OverErrEnv X W B S Scope y r s0 s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State) (evs_p2 : List AllocEvent)
      (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
      (kp : IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey) (recG : SessionGhost)
      (prevCap prevPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2OverOkEnv y.g r evs_p2 →
      prevCap ≠ 0#64 →
      pkToE? y.g.msg = some m →
      y.g.msg.message = i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 s2 →
      s2.trace = s1.trace →
      s2.pc = dpPollEntryPlaced + 0x1778#64 →
      s2.status = .Running →
      s2.sp = sp →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 →
      s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      LibsignalFrozen lsmpl s2.mem →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_b) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (encSession (clearPending s_old)) 0#8 ∗
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
         storesAt A.repAlloc y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q Qpan) →
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores g1 ∗
       LsTokenInit ∗
       lsLogOff ∗
       stackAt sp (dpClosSubStack B))
      Q Qpan

theorem h7ra_stageP2OverAtB_of_forall [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {X : UnreachedPqxdhPrimitives} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (B : RunBudgets)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (h : StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W P2OverErrEnv P2OverOkEnv) :
    H7RAStageP2OverAtBStmt A lim X mmpl gh W B P2OverErrEnv P2OverOkEnv :=
  h B

private theorem h7ra_hookSat_noAllocShimBudget_of_withVmPreserved
    {H : String → Option (State → State)}
    (hsat : HookSat H CryptoVerification.lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)) :
    HookSat H CryptoVerification.lsRustNoAllocShimSym noAllocShimBudgetSpec := by
  rcases hsat with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, noAllocShimSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

private theorem h7ra_hookSat_framelessMemcpy_of_vm
    {H : CryptoVerification.LibsignalHooks}
    (h : HookSat H "memcpy"
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    HookSat H CryptoVerification.lsMemcpySym framelessMemcpySpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    rcases x with ⟨dst, src, bs⟩
    dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      framelessMemcpySpec, framelessMemcpyBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact ⟨hkf, hsym, Or.inr hrest⟩

private theorem hookSat_sessionMemcpyRegionBudget_of_vm
    {H : CryptoVerification.LibsignalHooks}
    (h : HookSat H "memcpy"
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    HookSat H "memcpy"
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    rcases x with ⟨dst, src, bs⟩
    dsimp only [LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hpost.1, hpost.2.1, hpost.2.2⟩
  · exact ⟨hkf, hsym, Or.inr hrest⟩

private theorem hookSat_p2Memcpy4K_of_vm
    {H : CryptoVerification.LibsignalHooks}
    (h : HookSat H "memcpy"
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    HookSat H CryptoVerification.lsMemcpySym
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget.p2Memcpy4KSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases x with ⟨dst, src, bs⟩
  dsimp only [LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget.p2Memcpy4KSpec,
    LibsignalBinary.Heap.SpecBudget.withVmPreserved,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Memcpy4KSpec,
    ProofLib.libcMemcpySpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  have hpre' : s0.mem ⊨
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec).pre (dst, src, bs) s0 ∗
        (stackAt s0.sp CryptoVerification.RustHeap.allocHookStack ∗ R) := by
    dsimp only [LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by sep_ac_rfl)⟩
  rcases hok (dst, src, bs) (stackAt s0.sp CryptoVerification.RustHeap.allocHookStack ∗ R)
      s0 hrun hpre' hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget.p2Memcpy4KSpec,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Memcpy4KSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpost.1, hpost.2.1, Satisfies.of_eq hpost.2.2 (by sep_ac_rfl)⟩
  · exfalso
    rcases hrest with ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩ <;> {
      dsimp only [LibsignalBinary.Heap.SpecBudget.withVmPreserved,
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp
      exact hp.1
    }

private theorem h7ra_cliStageP2BaseCalleesPlaced4K [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2BaseCalleesPlaced4K A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  StageP2BaseCalleesPlaced4K.of_hooks
    (h7ra_hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim)
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    (hookSat_p2Memcpy4K_of_vm hh.codecHooks.memcpy)
    (isSameAccount_4k_placed_ok_on_stageP1
      ((cliGhostExterns_other gh (cliExternsPlaced mmpl W)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W)))
      (uuidTryParse_placed_vm_code_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))))

private theorem h7ra_cliInitBobV1FrozenOkPlaced4K [LibsignalFullPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives) (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W
      (InitialStateEnv W.C.F) (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv) :
    InitializeBobV1FrozenOkPlaced4KOfEnv
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      A lim W.C.F
      (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  initializeBobSession_ok_v1_of_env_4k_frozen_placed_on_stageP1
    (cliModelPrims_structural X W)
    (h7ra_hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim)
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    (hookSat_sessionMemcpyRegionBudget_of_vm hh.codecHooks.memcpy)
    (cliPqxdhAccept_opt_fields_full_placed_ok
      (callerProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 75)
      X mmpl gh W hG)
    hSpqr.initialStateMemInv_lsProg75
    (fun _ _ _ => Iff.rfl)

private theorem h7ra_cliInitBobErrOwnedFrozen4K_ok [LibsignalFullPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    (_hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok
      (stageP1ProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 75)
      (initializeBobSessionErrOwnedFrozen4KPlacedSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
        A lim
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))) := by
  have h75 :=
    initializeBobSession_err_owned_frozen_placed_ok_of_accept
      (cliPqxdhAccept_err_owned_full_placed_ok
        (callerProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 75)
        X mmpl gh W hG)
  have hbase :=
    ls_subroutine_ok_withLsFrozen_of_block
      (callerProg := stageP1ProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (calleeProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (i := 518) (j := 75) h75
  refine p2_errOwned_frozen_to_defs4K_placed ?_
  refine subroutine_ok_map hbase ?_
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun _ hpost => hpost⟩
  dsimp only [withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

private theorem h7ra_promoteOverAtPlacedWithEnv_of_eq [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    {coroPtr : BitVec 64} {g : RecordGhost} {recG : SessionGhost}
    {sess : Session (List (BitVec 8))}
    (hEq : Env₁ recG sess = Env₂ recG sess)
    (h : PromoteOverAtPlacedWithEnvProp M A lim Env₁ ext coroPtr g recG sess) :
    PromoteOverAtPlacedWithEnvProp M A lim Env₂ ext coroPtr g recG sess := by
  unfold PromoteOverAtPlacedWithEnvProp
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget.PromoteOverAtPlacedWithEnvProp
    p2PromoteOverAtSpecWithEnv at h ⊢
  rwa [← hEq]

private theorem h7ra_p2Sub1To4_opkWord_eq
    {spkBox : Nat} {spkPoll : List AllocEvent → Prop}
    {kpkBox : Nat} {kpkPoll : List AllocEvent → Prop}
    {pkBox1 pkBox2 : Nat}
    {pkPoll1 pkPoll2 : BitVec 32 → List AllocEvent → Prop}
    {kpBox : Nat} {m : PreKeyMessageFields} {opkWord : BitVec 32}
    (hopk : ∀ id : BitVec 32, m.opkId = some id → opkWord = id)
    (hbox : opkWord = m.opkId.getD 0#32 → pkBox1 = pkBox2)
    (hpoll : opkWord = m.opkId.getD 0#32 → pkPoll1 = pkPoll2) :
    P2Sub1To4Arm3Env spkBox spkPoll kpkBox kpkPoll pkBox1 pkPoll1 (hdrOpkIdBv? (mkPathAHdr m)) =
      P2Sub1To4Arm3Env spkBox spkPoll kpkBox kpkPoll pkBox2 pkPoll2 (hdrOpkIdBv? (mkPathAHdr m)) ∧
    P2Sub1To4OkEnv spkBox spkPoll kpkBox kpkPoll pkBox1 pkPoll1 kpBox (hdrOpkIdBv? (mkPathAHdr m)) =
      P2Sub1To4OkEnv spkBox spkPoll kpkBox kpkPoll pkBox2 pkPoll2 kpBox (hdrOpkIdBv? (mkPathAHdr m)) := by
  cases hid : hdrOpkIdBv? (mkPathAHdr m) with
  | none => exact ⟨rfl, rfl⟩
  | some id =>
    have hm : m.opkId = some id := (hdrOpkIdBv?_mkPathAHdr m).symm.trans hid
    have hw : opkWord = m.opkId.getD 0#32 := by rw [hopk id hm, hm]; rfl
    unfold P2Sub1To4Arm3Env P2Sub1To4OkEnv P2Sub4OkEnv
    rw [hbox hw, hpoll hw]; exact ⟨rfl, rfl⟩

private theorem h7ra_seqEnv_or_right {E1 A B : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv E1 (fun e => A e ∨ B e) evs) :
    SeqEnv E1 A evs ∨ SeqEnv E1 B evs := by
  rcases h with h1 | ⟨e1, e2, heq, h1, hA | hB⟩
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr ⟨e1, e2, heq, h1, hA⟩)
  · exact Or.inr (Or.inr ⟨e1, e2, heq, h1, hB⟩)

private theorem h7ra_p2OverSub6_or {Bob : List AllocEvent → Prop} {regBox : Nat}
    {regPoll PromTail : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv Bob (P2OverSub6EnvOf regBox regPoll PromTail) evs) :
    SeqEnv Bob (P2Sub6Env regBox regPoll) evs ∨
      SeqEnv Bob (SeqEnv (BoxAllocEnv regBox) (SeqEnv regPoll PromTail)) evs := by
  rcases h with hBob | ⟨eBob, eRest, heq1, hBob, hSub6⟩
  · exact Or.inl (Or.inl hBob)
  · unfold P2OverSub6EnvOf at hSub6
    rcases hSub6 with hBox | ⟨eBox, e2, heq2, hBox, h2⟩
    · exact Or.inl (Or.inr ⟨eBob, eRest, heq1, hBob, Or.inl hBox⟩)
    · rcases h7ra_seqEnv_or_right h2 with hFree | hProm
      · exact Or.inl (Or.inr ⟨eBob, eRest, heq1, hBob, Or.inr ⟨eBox, e2, heq2, hBox, hFree⟩⟩)
      · exact Or.inr (Or.inr ⟨eBob, eRest, heq1, hBob, Or.inr ⟨eBox, e2, heq2, hBox, hProm⟩⟩)

private theorem h7ra_fitsEnv_step3 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E1 E2 E3 E4 : List AllocEvent → Prop} {e1 e2 e3 : List AllocEvent}
    (h : FitsEnv M lim st (SeqEnv E1 (SeqEnv E2 (SeqEnv E3 E4))))
    (h1 : E1 e1) (h2 : E2 e2) (h3 : E3 e3) :
    FitsEnv M lim (M.stepEvents (e1 ++ e2 ++ e3) st) E4 := by
  rw [M.stepEvents_append, M.stepEvents_append]
  exact ((h.seq_right h1).seq_right h2).seq_right h3

set_option maxHeartbeats 1600000 in
/-- Fixed-`cliRunBudgets` Stage-P2 `Over` contract at `PromoteOverArchiveCanonSessEnv` and `InitialStateEnv W.C.F`. -/
theorem h7ra_stageP2Over_archive_at_cliRunBudgets_frozen_ok [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hRead : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile
        (ReadFileRuleEnvFixed cliIo.rd)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W
      (InitialStateEnv W.C.F) (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv) :
    let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
    let selfEnv := fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv
    let kitEnvs := cliStageP2KitEnvs (A := A.repAlloc) ReadEnv cliRunBudgets selfEnv
    H7RAStageP2OverAtBStmt A lim X mmpl gh W cliRunBudgets
      (P2OverPathCErrEnvOf (A := A.repAlloc) X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        kitEnvs)
      (P2OverPathCOkEnvOf (A := A.repAlloc) X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv
        kitEnvs) := by
  dsimp only
  let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
  let B := cliRunBudgets
  let selfEnv := fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv
  let kitEnvs := cliStageP2KitEnvs (A := A.repAlloc) ReadEnv B selfEnv
  have hReadD : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) := hRead
  intro S DecPkEnv Scope y st_b r sess g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hh0 hfits0 hcoins hdecOk hScope hFok hload hcur hnotMatch htrust hg1
    hfs1 hCode1 htr01 hsp1 hsp0 hsub hpc1 hrun1 halign1 hregs1 herr0 hok
  have hIn : scopeIn r := hScope r (scope_of_loadRec_some hFok hload)
  have hh :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    ⟨hh0.alloc, hh0.allocFs, hh0.panics, hh0.memcpyRO, hh0.bcmp, hh0.fs, hh0.utf8, hh0.memrchr,
      hh0.codecHooks, hh0.allocZeroed, hh0.stringClone, hh0.formatInner⟩
  have hPromMiss := cliPromoteMatchingMissGen_placed_ok A.repAlloc mmpl gh W
  have hPromOver := cliPromoteOverGen_archive_placed_ok mmpl gh W hh hGrow hRaw
  subst hg1
  rcases hregs1 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, _, hx29, hvregs1⟩
  obtain ⟨m, _, hi, hpkToE, hdec0⟩ := hdecOk
  let i : SignalMessage := y.g.msg.message
  have hmsg_i : y.g.msg.message = i := rfl
  have hbk_eq : y.g.msg.baseKey = (pmOfE m i).baseKey :=
    (pm_fields_of_pkToE hpkToE hmsg_i).2.2.2.2.1.trans (pmOfE_fields m i).2.2.2.2.1.symm
  have hfp_reg : s1.readReg64 .x29 = sp + 0xc70#64 := x29_eq_sp_add_c70 hsp0 hx29
  have hsp_align : (sp &&& 15#64 == 0#64) = true := by rw [← hsp1]; exact halign1
  refine sepWPp_with_steps ?_
  refine sepWPp_conseq_pre
    (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PollPlacedBudget.stageP2_entry_unpack_pathCOver_d3_placed
      (st_b := st_b) (s1 := s1)
      y r sess m i s0 sp (sp + 0xc70#64) rngPtr v_a8 v_b8 v_d0 hcur hpkToE hmsg_i rfl
      hdec0 hFok hScope) ?_
  refine SepWPp.exists_elim fun g => SepWPp.exists_elim fun recG =>
    SepWPp.exists_elim fun w => SepWPp.pure_left fun ⟨_hkit, _hgcur, hcanon, hctBuf_nz, hopkWord⟩ => ?_
  have hPromMissAt : PromoteMatchingMissAtPlacedProp A.repAlloc
      (cliGhostExterns gh (cliExternsPlaced mmpl W))
      y.fut g recG sess 4#8 (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk) :=
    promoteMatchingMissAt_placed_of_gen hPromMiss y.fut g recG sess 4#8
      (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk)
      (p2Over_not_sessMatchesMsg_d3 sess y.g.msg m i hpkToE hmsg_i hnotMatch)
      (p2Over_serBytes_len m)
  have hPromOverAt0 := promoteOverAt_placed_of_gen_withEnv hPromOver y.fut g recG sess
    (encSessionMem_clearPending_lt_32 hIn hcur hcanon)
  have hPromOverAt : PromoteOverAtPlacedWithEnvProp M A lim
      (fun _ s => PromoteOverArchiveCanonSessEnv s)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) y.fut g recG sess :=
    h7ra_promoteOverAtPlacedWithEnv_of_eq (promoteOverArchiveEnv_eq_canon hcanon) hPromOverAt0
  let opkWord0 : BitVec 32 := m.opkId.getD 0#32
  have ⟨hArm3_eq, hOk14_eq⟩ := h7ra_p2Sub1To4_opkWord_eq
    (spkBox := (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B)).getBoxSize)
    (spkPoll := (kitEnvs y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).spkEnv.getPollEnv
      StoresGhost.opened.signed m.spkId)
    (kpkBox := (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).getBoxSize)
    (kpkPoll := (kitEnvs y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).kpkEnv.getPollEnv
      StoresGhost.opened.kyber m.kpkId)
    (pkBox1 := (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B)).getBoxSize)
    (pkBox2 := (cliPollPkKitPlaced A.repAlloc y.g.F opkWord0 (cliKitStk B)).getBoxSize)
    (pkPoll1 := (kitEnvs y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey).pkEnv.getPollEnv
      StoresGhost.opened.oneTime)
    (pkPoll2 := (kitEnvs y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).pkEnv.getPollEnv
      StoresGhost.opened.oneTime)
    (kpBox := (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpBoxSize)
    (m := m) (opkWord := w.opkWord) hopkWord (fun hw => by rw [hw]) (fun hw => by rw [hw])
  let ikBSk : SignalPqxdh.Bytes :=
    match StoresGhost.opened.identity.keyPair cliIo.rd y.g.F with
    | .ok kp₀ => vecU8 kp₀.privateKey.bytes | .error _ => List.replicate 32 0
  let ikBPk : SignalPqxdh.Bytes :=
    match StoresGhost.opened.identity.keyPair cliIo.rd y.g.F with
    | .ok kp₀ => vecU8 kp₀.identityKey.publicKey.bytes | .error _ => List.replicate 32 0
  have hikBSk_len : ikBSk.length = 32 := by dsimp only [ikBSk]; split <;> [exact vecU8_length _; simp]
  have hikBPk_len : ikBPk.length = 32 := by dsimp only [ikBPk]; split <;> [exact vecU8_length _; simp]
  have hkp_sk : ∀ kp : IdentityKeyPair,
      (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp) → kp.privateKey.bytes.toList = bytesToBv8 ikBSk := by
    intro kp hrel; dsimp only [ikBSk]; rw [cliPollSelf_kpRel_ok_placed hrel, bytesToBv8_vecU8]
  have hkp_pk : ∀ kp : IdentityKeyPair,
      (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp) →
      kp.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk := by
    intro kp hrel; dsimp only [ikBPk]; rw [cliPollSelf_kpRel_ok_placed hrel, bytesToBv8_vecU8]
  let err0 : ApiError AddrVal Unit := .protocol .invalidKeyAgreement
  have herr0_p : err0 ≠ .panic := by nofun
  have herr0_s : err0 ≠ .store () := by nofun
  let P_m := ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)
  let ErrEnv := P2OverPathCErrEnvOf (A := A.repAlloc) X W B
    (InitializeBobV1OptFieldsEnv P_m W.C.F) (AcceptOptFieldsEnv P_m) kitEnvs
  let OkEnv := P2OverPathCOkEnvOf (A := A.repAlloc) X W B
    (InitializeBobV1OptFieldsEnv P_m W.C.F) PromoteOverArchiveCanonSessEnv kitEnvs
  have hStageP2 :
      stageP2OverV1KitsMemInvAtPlacedOfEnvProp
        (LibsignalFrozen lsmpl)
        P_m A lim W.C.F
        (InitializeBobV1OptFieldsEnv P_m W.C.F)
        (AcceptOptFieldsEnv P_m)
        (fun _ s => PromoteOverArchiveCanonSessEnv s)
        (cliGhostExterns gh (cliExternsPlaced mmpl W))
        (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
        (kitEnvs y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).selfEnv
        (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
        (kitEnvs y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).spkEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
        (kitEnvs y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).kpkEnv
        (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
        (kitEnvs y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey).pkEnv
        (dpClosSubStack B) :=
    stageP2_over_v1_kits_frozen_ext_defs_placed_ofEnv
      (M := M) (P := P_m) (A := A) (lim := lim) (F := W.C.F)
      (BobV1Env := InitializeBobV1OptFieldsEnv P_m W.C.F)
      (AcceptErrEnv := AcceptOptFieldsEnv P_m)
      (PromEnv := fun _ s => PromoteOverArchiveCanonSessEnv s)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) (cliModelPrims_structural X W)
      (cliStageP2ClosureHooksPlaced mmpl gh W hh)
      (h7ra_cliStageP2BaseCalleesPlaced4K mmpl gh W hh)
      (h7ra_cliInitBobErrOwnedFrozen4K_ok X mmpl gh W hG hh)
      (h7ra_cliInitBobV1FrozenOkPlaced4K X mmpl gh W hG hh hSpqr)
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (kitEnvs y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).selfEnv
      (cliPollSelf_vtablesPlacedOk y.g.F y.g.peer (cliKitStk B) h547)
      (cliPollSelf_kitPlacedOk_stagesHooks mmpl gh W B y.g.F y.g.peer h547 hh hReadD)
      (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
      (kitEnvs y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).spkEnv
      (cliPollSpk_vtablesPlacedOk y.g.F m.spkId (cliKitStk B) h547)
      (cliPollSpk_kitPlacedOk mmpl gh W B y.g.F m.spkId h547 hh hReadD)
      (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (kitEnvs y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).kpkEnv
      (cliPollKpk_vtablesPlacedOk y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) h547)
      (cliPollKpk_kitPlacedOk mmpl gh W B y.g.F m.kpkId m.spkId y.g.msg.baseKey h547 hh hReadD)
      (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
      (kitEnvs y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey).pkEnv
      (cliPollPk_vtablesPlacedOk y.g.F w.opkWord (cliKitStk B) h547)
      (cliPollPk_kitPlacedOk mmpl gh W B y.g.F w.opkWord h547 hh hReadD)
      (dpClosSubStack B) (stageP2OverV1CallStack4K_le_subStack_placed (A := A.repAlloc)
        y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B)
  exact hStageP2 (st := st_b)
    (Qp := fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Qpan sf Pf)
    s0 s1
    (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PollPlacedBudget.pathAInnerFrameD3Placed
      A.repAlloc y i rngPtr sp)
    (fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Q sf Pf)
    sp (sp + 0xc70#64) y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
    y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
    y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
    (mkPathAHdr m) ikBSk ikBPk i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
    w.opkWord m.kpkId m.regId m.spkId StoresGhost.opened.signed StoresGhost.opened.kyber
    StoresGhost.opened.oneTime StoresGhost.opened.identity y.g.me y.g.peer g recG sess
    hPromMissAt hPromOverAt
    (hfits0.mono fun evs hevs => by
      refine Or.inl ?_; unfold P2OverPathCErrEnvOf; rw [hpkToE]
      rcases hevs with h1 | h2 | h3 | hok4
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · rw [hArm3_eq] at h3; exact Or.inr (Or.inr (Or.inl h3))
      · rw [hOk14_eq] at hok4; exact Or.inr (Or.inr (Or.inr (Or.inl (SeqEnv.inl hok4)))))
    (fun evs14 hevs14 => by
      dsimp only [P2OverSub1To4OkEnv] at hevs14; rw [hOk14_eq] at hevs14
      have hArm4 : FitsEnv M lim st_b (P2OverV1Arm4Env
          (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B)).getBoxSize
          ((kitEnvs y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).spkEnv.getPollEnv
            StoresGhost.opened.signed m.spkId)
          (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).getBoxSize
          ((kitEnvs y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).kpkEnv.getPollEnv
            StoresGhost.opened.kyber m.kpkId)
          (cliPollPkKitPlaced A.repAlloc y.g.F opkWord0 (cliKitStk B)).getBoxSize
          ((kitEnvs y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).pkEnv.getPollEnv
            StoresGhost.opened.oneTime)
          (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpBoxSize
          (hdrOpkIdBv? (mkPathAHdr m))
          ((kitEnvs y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).selfEnv.kpPollEnv
            StoresGhost.opened.identity)) :=
        hfits0.mono fun evs h4 => by
          refine Or.inl ?_; unfold P2OverPathCErrEnvOf; rw [hpkToE]
          exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
      exact hArm4.seq_right hevs14)
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey evs14 evsKp
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccSome hevs14 hevsKp => by
      dsimp only [P2OverSub1To4OkEnv] at hevs14; rw [hOk14_eq] at hevs14
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hikBSk_ok : ikBSk = vecU8 kp.privateKey.bytes := by dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = vecU8 kp.identityKey.publicKey.bytes := by dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0 hspkRel hspkPubEq hspkPrivEq
        (hbk_eq ▸ hkpkRel) hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have hinp0 := hinp 0#32; rw [hinp0] at haccSome ⊢
      refine h7ra_fitsEnv_step3 (hfits0.mono fun evs hseq => ?_)
        hevs14 hevsKp (FreeOnlyEvs.singleton 8 _)
      rcases hseq with h14 | ⟨e14, er1, heq1, h14, hr1⟩
      · refine Or.inl ?_; unfold P2OverPathCErrEnvOf; rw [hpkToE]
        exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h14))))
      · rcases hr1 with hkp | ⟨eKp, er2, heq2, hkp, hr2⟩
        · refine Or.inl ?_; unfold P2OverPathCErrEnvOf; rw [hpkToE]
          exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨e14, er1, heq1, h14, Or.inl hkp⟩))))
        · rcases hr2 with hfr | ⟨eFr, er3, heq3, hfr, hr3⟩
          · refine Or.inl ?_; unfold P2OverPathCErrEnvOf; rw [hpkToE]
            exact Or.inr (Or.inr (Or.inr (Or.inl
              (Or.inr ⟨e14, er1, heq1, h14, Or.inr ⟨eKp, er2, heq2, hkp, hfr⟩⟩))))
          · rcases h7ra_p2OverSub6_or hr3 with hArm6 | hOk
            · refine Or.inl ?_; unfold P2OverPathCErrEnvOf; rw [hpkToE]; dsimp only
              rw [hk, hkpOk]; dsimp only; rw [haccSome]
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e14, er1, heq1, h14,
                Or.inr ⟨eKp, er2, heq2, hkp, Or.inr ⟨eFr, er3, heq3, hfr, hArm6⟩⟩⟩)))))
            · refine Or.inr ?_; unfold P2OverPathCOkEnvOf; rw [hpkToE, hcur]; dsimp only
              rw [hk, hkpOk]; dsimp only; rw [haccSome]
              exact Or.inr ⟨e14, er1, heq1, h14,
                Or.inr ⟨eKp, er2, heq2, hkp, Or.inr ⟨eFr, er3, heq3, hfr, hOk⟩⟩⟩)
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp evs14 evsKp
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel _haccNone hevs14 hevsKp => by
      dsimp only [P2OverSub1To4OkEnv] at hevs14; rw [hOk14_eq] at hevs14
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hikBSk_ok : ikBSk = vecU8 kp.privateKey.bytes := by dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = vecU8 kp.identityKey.publicKey.bytes := by dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0 hspkRel hspkPubEq hspkPrivEq
        (hbk_eq ▸ hkpkRel) hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      rw [hinp 0#32]
      refine h7ra_fitsEnv_step3 (hfits0.mono fun evs h5 => ?_) hevs14 hevsKp (FreeOnlyEvs.singleton 8 _)
      refine Or.inl ?_; unfold P2OverPathCErrEnvOf; rw [hpkToE]; dsimp only
      rw [hk, hkpOk]; dsimp only; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
    hctBuf_nz (sp_sub_576_ne_zero B hsub) hsub hikBSk_len hikBPk_len
    (vecU8_length m.idPub) (vecU8_length m.baseKey) (vecU8_length m.kyberCt) hCode1
    (cliPollStageP2_fsAt_stages_placed hh y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B hfs1)
    rfl (fun r' hrel _ => cliPollSpk_wf_of_preKeysWf_placed hdec0.preKeysWf r' hrel)
    rfl (fun r' hrel _ => cliPollKpk_wf_of_preKeysWf_placed hdec0.preKeysWf r' (hbk_eq ▸ hrel))
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid))
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid) |>.symm)
    (fun _id r' _ hrel _ => cliPollPk_wf_of_preKeysWf_placed hdec0.preKeysWf r' hrel)
    hkp_sk hkp_pk (Or.inr (distinctSid_of_decPkOk₀ hdec0))
    hpc1 hrun1 hsp1 hsp_align htr01 hvregs1
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hfp_reg
    (fun e sf Pf evs hspkErr hevs hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, List.append_nil] at htr_f
      have hspkNone : pkStoreKeys y.g.F m = none := pkStoreKeys_eq_none_of_spk_err
        ((cliSpk_getRel_error_iff (A := A.repAlloc) (b := 0#64) cliIo.rd y.g.F cliWrOk m.spkId
          (cliKitStk B).spkGetShim (cliKitStk B).spkGetPoll
          StoresGhost.opened.signed m.spkId).mp ⟨e, hspkErr⟩)
      have hevs' : ErrEnv y.g r evs := by
        dsimp only [ErrEnv]; unfold P2OverPathCErrEnvOf; rw [hpkToE]; exact Or.inl hevs
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F m.spkId (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr0 sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          decPkOverDef_pathCOver_stage2_rej_placed hload hcur htrust hnotMatch
            ⟨m, i, hpkToE, hi, hmsg_i, Or.inl (Or.inl hspkNone)⟩, hpost⟩)
    (fun _spkRec e sf Pf evs _ _ hkpkErr hevs hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          List.append_nil, List.append_nil] at htr_f
      have hkpkNone : pkStoreKeys y.g.F m = none := pkStoreKeys_eq_none_of_kpk_err
        ((cliKpk_getRel_error_iff (A := A.repAlloc) cliIo.rd y.g.F cliWrOk m.kpkId
          StoresGhost.opened.kyber m.kpkId).mp ⟨e, hkpkErr⟩)
      have hevs' : ErrEnv y.g r evs := by
        dsimp only [ErrEnv]; unfold P2OverPathCErrEnvOf; rw [hpkToE]; exact Or.inr (Or.inl hevs)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr0 sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          decPkOverDef_pathCOver_stage2_rej_placed hload hcur htrust hnotMatch
            ⟨m, i, hpkToE, hi, hmsg_i, Or.inl (Or.inl hkpkNone)⟩, hpost⟩)
    (fun _spkRec _kpkRec opkId e sf Pf evs _ _ _ _ hopkHdr hpkErr hevs hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          p2Over_cliPollPk_getEvs_placed, List.append_nil, List.append_nil, List.append_nil] at htr_f
      dsimp only [P2OverSub1To4Arm3Env] at hevs; rw [hArm3_eq] at hevs
      have hmOpk : m.opkId = some opkId := (hdrOpkIdBv?_mkPathAHdr m).symm.trans hopkHdr
      have hpkNone : pkStoreKeys y.g.F m = none := pkStoreKeys_eq_none_of_opk_err hmOpk
        ((cliPk_getRel_error_iff (A := A.repAlloc) (b := 0#64) cliIo.rd y.g.F cliWrOk w.opkWord
          (cliKitStk B).pkGetShim (cliKitStk B).pkGetPoll
          (cliKitStk B).pkRemoveShim (cliKitStk B).pkRemovePoll
          StoresGhost.opened.oneTime opkId).mp ⟨e, hpkErr⟩)
      have hevs' : ErrEnv y.g r evs := by
        dsimp only [ErrEnv]; unfold P2OverPathCErrEnvOf; rw [hpkToE]; exact Or.inr (Or.inr (Or.inl hevs))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F w.opkWord (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr0 sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          decPkOverDef_pathCOver_stage2_rej_placed hload hcur htrust hnotMatch
            ⟨m, i, hpkToE, hi, hmsg_i, Or.inl (Or.inl hpkNone)⟩, hpost⟩)
    (fun _spkRec _kpkRec wOpk e sf Pf evs _ _ _ _ _ hkpErr hevs hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          p2Over_cliPollPk_opkOkEvs_placed, p2Over_cliPollSelf_kpEvs_placed,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := p2Over_cliPollPk_opkOkUpdate_placed A.repAlloc y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      unfold P2OverV1Arm4Env P2V1Arm4Env at hevs; rw [hOk14_eq] at hevs
      have hkpNone := cliPollSelf_kpRel_err_placed hkpErr
      have hevs' : ErrEnv y.g r evs := by
        dsimp only [ErrEnv]; unfold P2OverPathCErrEnvOf; rw [hpkToE]
        exact Or.inr (Or.inr (Or.inr (Or.inl hevs)))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (Entails.trans
          (cliPollSelf_kpErr_entails_decResAt_err_placed A.repAlloc
            y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)))
        (p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr0 sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          decPkOverDef_pathCOver_stage2_rej_placed hload hcur htrust hnotMatch
            ⟨m, i, hpkToE, hi, hmsg_i, Or.inl (Or.inr (Or.inl hkpNone))⟩, hpost⟩)
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp errTag w2 w3 w4 w5 w6 sf Pf evs
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccNone hevs _ _
        hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          p2Over_cliPollPk_opkOkEvs_placed, p2Over_cliPollSelf_kpEvs_placed,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := p2Over_cliPollPk_opkOkUpdate_placed A.repAlloc y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hikBSk_ok : ikBSk = vecU8 kp.privateKey.bytes := by dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = vecU8 kp.identityKey.publicKey.bytes := by dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0 hspkRel hspkPubEq hspkPrivEq
        (hbk_eq ▸ hkpkRel) hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have haccNone0 : ∀ reg : BitVec 32, SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
          (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none := fun reg =>
        Option.map_eq_none_iff.mp (by
          rw [← acceptKeys_ofSignalPqxdhPrimitives, ← hinp reg]; exact haccNone)
      unfold P2OverV1Arm5EnvOfAcceptErr P2V1Arm5EnvOfAcceptErr at hevs
      rw [hOk14_eq, hinp 0#32] at hevs
      have hevs' : ErrEnv y.g r evs := by
        dsimp only [ErrEnv]; unfold P2OverPathCErrEnvOf; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hevs))))
      have hPf' := Entails.trans hPf (by rw [← sepConj_assoc]; exact Entails.refl _)
      have hpost := Entails.trans hPf' (Entails.trans
        (sepConj_mono_left (pqxdhAcceptErr_entails_decResAt_anyHeap_ext A.repAlloc
          y.out errTag w2 w3 w4 w5 w6 err0))
        (p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr0 sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          decPkOverDef_pathCOver_stage2_rej_placed hload hcur htrust hnotMatch
            ⟨m, i, hpkToE, hi, hmsg_i, Or.inr ⟨k, kp, hk, hkpOk, haccNone0⟩⟩, hpost⟩)
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey e sf Pf evs
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccSome hregErr hevs
        hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          p2Over_cliPollPk_opkOkEvs_placed, p2Over_cliPollSelf_kpEvs_placed,
          p2Over_cliPollSelf_regIdEvs_placed,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := p2Over_cliPollPk_opkOkUpdate_placed A.repAlloc y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hikBSk_ok : ikBSk = vecU8 kp.privateKey.bytes := by dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = vecU8 kp.identityKey.publicKey.bytes := by dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0 hspkRel hspkPubEq hspkPrivEq
        (hbk_eq ▸ hkpkRel) hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have hinp0 := hinp 0#32; rw [hinp0] at haccSome
      unfold P2OverV1Arm6EnvOfBob P2V1Arm6EnvOfBob at hevs; rw [hOk14_eq, hinp0] at hevs
      have hevs' : ErrEnv y.g r evs := by
        dsimp only [ErrEnv]; unfold P2OverPathCErrEnvOf; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        rw [haccSome]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hevs))))
      have hregNone := cliPollSelf_regIdRel_err_placed hregErr
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (Entails.trans
          (cliPollSelf_regIdErr_entails_decResAt_err_placed A.repAlloc
            y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)))
        (p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr0 sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          decPkOverDef_pathCOver_stage2_rej_placed hload hcur htrust hnotMatch
            ⟨m, i, hpkToE, hi, hmsg_i, Or.inl (Or.inr (Or.inr hregNone))⟩, hpost⟩)
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey localRegId G_bob s2 evs
        hspkRel _ hspkPub_len hspkPriv_len hspkPubEq hspkPrivEq
        hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccSome hregRel hevs
        hG_pend hG_kyb hG_alice hG_regs
        hSteps12 _ hpc2 hrun2 hsp2 htr2
        _ _ _ _ hx19_2 _ _ _ _ _ _ hx27_2 _ hx29_2 hvregs2 _hCode2 => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          p2Over_cliPollPk_opkOkEvs_placed, p2Over_cliPollSelf_kpEvs_placed,
          p2Over_cliPollSelf_regIdEvs_placed,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr2
      have hopkUpd := p2Over_cliPollPk_opkOkUpdate_placed A.repAlloc y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hregOk := cliPollSelf_regIdRel_ok_placed hregRel
      have hikBSk_ok : ikBSk = vecU8 kp.privateKey.bytes := by dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = vecU8 kp.identityKey.publicKey.bytes := by dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, hspkPub_eq, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0 hspkRel hspkPubEq
        hspkPrivEq (hbk_eq ▸ hkpkRel) hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have hinp0 := hinp 0#32
      have haccSome0 : acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
          (ofSignalPqxdhAcceptKeysInput (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)) =
          some drKey := by rw [← hinp0]; exact haccSome
      unfold P2OverV1OkEnvOfBobAndProm P2OverSub1To4OkEnv at hevs
      rw [hOk14_eq, hinp0] at hevs
      have hevs' : OkEnv y.g r evs := by
        dsimp only [OkEnv]; unfold P2OverPathCOkEnvOf; rw [hpkToE, hcur]; dsimp only; rw [hk, hkpOk]; dsimp only
        rw [haccSome0]; exact hevs
      obtain ⟨dk0, haccModel, hdk0⟩ := Option.map_eq_some_iff.mp (show
        (SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
          (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m)).map
            ofSignalPqxdhDRKey = some drKey by
          rw [← acceptKeys_ofSignalPqxdhPrimitives, ← hinp localRegId]; exact haccSome)
      have hikBPk_bv :
          bytesToBv8 ikBPk = (keyPairOf W.C kp.privateKey.bytes).publicKey.bytes.toList := by
        rw [hikBPk_ok, hdec0.idPairDerived kp hkpOk, bytesToBv8_vecU8]
      have hst_eq := p2BobInitSessionV1_eq_pathAInitState (cliModelPrims_structural X W)
        W kp localRegId k m drKey dk0 ikBPk spkPubBytes
        (mkP2AcceptKeysInput (mkPathAHdr m) ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes)
        hikBPk_len (vecU8_length m.idPub) (by simp [toU8, hspkPub_len])
        (by simp [mkP2AcceptKeysInput, toU8, clampBv8List_length hspkPriv_len])
        haccSome hdk0 (hinp localRegId) hikBPk_bv hspkPub_eq
      have hextra := sessionExtraRel_pathAInitSession W kp localRegId k m dk0 G_bob
        hG_pend hG_kyb hG_alice hG_regs
      have hmsg_reasm : signalMessageAt A.repAlloc y.g.msgG.msg y.g.msgA y.g.msg.message ∗
          ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ⊢
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg := by
        rw [preKeyMsgAt_eq_base_idKey_sep]; exact Entails.of_eq (by sep_ac_rfl)
      have halign2 : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
      have hx29_sp0 : s2.readReg64 .x29 = s0.sp - 0x60#64 := x29_eq_sp0_sub_60 hsp0 hx29_2
      rw [hst_eq, hopkUpd]
      refine sepWPp_drop_steps hSteps12 (sepWPp_conseq_pre
        (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PollPlacedBudget.p2OverOkPost_fold_pathCOver_d3_placed
          (st_b := M.stepEvents evs st_b)
          y m i w s0 s2 sp (sp + 0xc70#64) rngPtr
          recG G_bob sess (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m dk0)
          hcanon hpkToE hmsg_i hcoins hsub rfl hopkWord hsp2 hx19_2 hx27_2) ?_)
      refine SepWPp.exists_elim fun prevCap' => SepWPp.exists_elim fun prevPtr' =>
        SepWPp.pure_left fun hcap_ne => ?_
      exact hok s2 evs m i k kp localRegId dk0 G_bob prevCap' prevPtr' y.g.msgA y.g.msgG.msg
        (preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
        hevs' hcap_ne hpkToE hmsg_i hi hk hkpOk hregOk haccModel hextra hmsg_reasm
        hSteps12 htr2 hpc2 hrun2 hsp2 halign2 hx19_2 hx27_2 hx29_sp0 hvregs2
        (libsignalFrozen_of_keepsFrozen hCode1 hSteps12.keepsFrozen))

/-- Fixed-`B` specialization of `StageP4Prev1VRegsAtPlacedStmt`. -/
def H7RAStageP4Prev1AtBStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk) : Prop :=
  ∀ (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey) (st_b : M.σ),
    let σ := cliKitStk B
    let kit := cliPollSessPrev1KitPlaced A.repAlloc F0 peer σ
    let ops : StorePrev1Ops kit := cliPollStorePrev1OpsPlaced
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk σ
    let envs := p4Envs B F0 peer pid kpkId spkId kbk
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
      (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
      (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
      (remoteIk : IdentityKey) (baseKey : PublicKey)
      (sst0 : kit.StoreState) (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
      (G : SessionGhost) (ss : Session (List (BitVec 8))),
      FitsEnv M lim st_b
        (StageP4Prev1ExitEnv kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
          kpkKit envs.kpkKitEnv sst0 ist0 pst0 kst0 opkId? peer.val remoteIk
          kyberPreKeyId signedPreKeyId baseKey G ss enc) →
      SessionExtraRel G ss → ops.RecPrev1Ok G ss enc →
      kit.addrOk peer.val → ikit.addrOk peer.val →
      kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey →
      (∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId) →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64 →
      FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
        (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x34dc#64 →
      s.status = .Running → (s.sp &&& 15#64 == 0#64) = true → s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr → s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 → s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr → s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
        (stageP4Prev1PrePlaced A lim st_b kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevCap prevPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc
          peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss.state)
        (fun sf Pf =>
          Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧ ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          StageP4Prev1BranchPlaced A lim st_b kit ops envs.opsEnv ikit envs.ikitEnv
            pkKit envs.pkKitEnv kpkKit envs.kpkKitEnv s0 s coroPtr msgPtr outPtr
            remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
            ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
            baseKey sst0 ist0 pst0 kst0 G ss sf Pf)
        (fun _ _ => False)

theorem h7ra_stageP4Prev1AtB_of_forall [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (B : RunBudgets)
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (h : StageP4Prev1VRegsAtPlacedStmt A lim mmpl gh W p4Envs) :
    H7RAStageP4Prev1AtBStmt A lim mmpl gh W B p4Envs :=
  h B

/-- Fixed-`cliRunBudgets` `SeqFree` `Prev1` Stage-P4 discharger. -/
theorem h7ra_stageP4Prev1_seqFree_at_cliRunBudgets_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hRead : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile
        (ReadFileRuleEnvFixed cliIo.rd))) :
    H7RAStageP4Prev1AtBStmt A lim mmpl gh W cliRunBudgets
      (fun B F0 peer pid kpkId spkId kbk =>
        h7ra_cliStageP4Prev1SeqFreeEnvs A.repAlloc B F0 peer pid kpkId spkId kbk
          (ReadFileRuleEnvFixed cliIo.rd)) :=
  fun F0 peer pid kpkId spkId kbk st_b hhStages =>
    stageP4Prev1_seqFree_placed_inst h547 mmpl gh W cliRunBudgets F0 peer pid kpkId spkId kbk
      hhStages hRead st_b

theorem h7ra_tryDecrypt507_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {InitEnv : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (hG : CliGhostAllocHooks M A lim gh)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W
      InitEnv (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv W a evs) :
    subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))) :=
  over_tryDecrypt_cli_of_tdEnv_placed_ok_at mmpl gh W 0#64 hG hAesDec hSpqr hRecv_ne htd

/-! ## 3. Fixed-`cliRunBudgets` Slot-`520` Producer for the Primed `SessionGhostValid` Twin -/

/-- Envelope family for `OverD3` where arms 2–5 carry memory-extracted
`SessionGhostValid recG ses0` and arm 5 carries memory-extracted `SessionGhostValid G' ses'`. -/
abbrev H7RADecPkOverEnvTwinFam [LibsignalPlacement] : Type _ :=
  (A : RustAlloc) →
  (verNeEnv : List (BitVec 8) → List AllocEvent → Prop) →
  (W : CliHooks) → (X : UnreachedPqxdhPrimitives) → (B : RunBudgets) →
  (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) →
  (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) →
  (P2OverErrEnv P2OverOkEnv : DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) →
  (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop) →
  (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
    CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk) →
  DecPkGhost → List AllocEvent → Prop

/-- Specialization of `OverOfEnv'` to `VerNeTightTopRawEnv`, `ReadFileRuleEnvFixed cliIo.rd`,
`SessDeserializeCancelEnv`, `PromoteOverArchiveCanonSessEnv`, and `h7ra_cliStageP4Prev1SeqFreeEnvs` at `cliRunBudgets`. -/
def h7ra_decPkOverConcreteTwinOf [LibsignalPlacement]
    (OverOfEnv' : H7RADecPkOverEnvTwinFam)
    (A : RustAlloc) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
  let selfEnv := fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk cliRunBudgets) ReadEnv
  let kitEnvs := cliStageP2KitEnvs (A := A) ReadEnv cliRunBudgets selfEnv
  OverOfEnv' A VerNeTightTopRawEnv W X cliRunBudgets
    ReadEnv
    SessDeserializeCancelEnv
    (P2OverPathCErrEnvOf (A := A) X W cliRunBudgets
      (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
      (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
      kitEnvs)
    (P2OverPathCOkEnvOf (A := A) X W cliRunBudgets
      (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
      PromoteOverArchiveCanonSessEnv
      kitEnvs)
    tdEnv
    (fun B F0 peer pid kpkId spkId kbk =>
      h7ra_cliStageP4Prev1SeqFreeEnvs A B F0 peer pid kpkId spkId kbk ReadEnv)
    g evs

/-- Pointwise fixed-`cliRunBudgets` Block-518 poll producer obligation. -/
def H7RATightPollProducerAt [LibsignalFullPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (OverOfEnv' : H7RADecPkOverEnvTwinFam)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
  let selfEnv := fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv
  let kitEnvs := cliStageP2KitEnvs (A := A.repAlloc) ReadEnv cliRunBudgets selfEnv
  H7RAStageP2OverAtBStmt A lim X mmpl gh W cliRunBudgets
    (P2OverPathCErrEnvOf (A := A.repAlloc) X W cliRunBudgets
      (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
      (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
      kitEnvs)
    (P2OverPathCOkEnvOf (A := A.repAlloc) X W cliRunBudgets
      (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
      PromoteOverArchiveCanonSessEnv
      kitEnvs) →
  H7RAStageP4Prev1AtBStmt A lim mmpl gh W cliRunBudgets
    (fun B F0 peer pid kpkId spkId kbk =>
      h7ra_cliStageP4Prev1SeqFreeEnvs A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv) →
  subroutine_ok
    (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (lsmpl.base 508)
    (withLsCodeRoLoaded lsmpl
      (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
        (spqrV1 W.C.F W.Q.K) (tdEnv W))) →
  (∀ g evs, h7ra_decPkOverConcreteTwinOf OverOfEnv' A.repAlloc W X tdEnv g evs → DecPkEnv g evs) →
  CliDpPollOkOverV4StateFrozenPlacedAt A lim
    ReadEnv SessDeserializeCancelEnv DecPkEnv
    mmpl gh W X cliRunBudgets (cliRunSemOverV4 X W) scopeIn

/-- Proves `.decryptPrekey.OkPlaced` on `lsProg_579` at `lsmpl.base 520` for `OverOfEnv'` at `cliRunBudgets`. -/
theorem h7ra_decPkValidOverTwin_slot520_ok [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (OverOfEnv' : H7RADecPkOverEnvTwinFam)
    (sEnvs : RunSlotEnvs)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile
        (ReadFileRuleEnvFixed cliIo.rd)))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W
      (InitialStateEnv W.C.F) (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv W a evs)
    (hPollTwin :
      H7RATightPollProducerAt A lim mmpl gh W X OverOfEnv' tdEnv sEnvs.decryptPrekey)
    (hsEnv' : ∀ g evs,
      h7ra_decPkOverConcreteTwinOf OverOfEnv' A.repAlloc W X tdEnv g evs →
      sEnvs.decryptPrekey g evs) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hpan : Arm64.Rust.withPanics H = H := withPanics_cliGhostExterns mmpl gh W
  have hEq : CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced H =
      dpPollProgPlaced H :=
    h7ra_dpPollProgPlaced_eq mmpl gh W
  have hcaller : IsLsBlockProg (lsProg_579 H) 579 (Arm64.Rust.withPanics H) := by
    rw [hpan]; infer_instance
  have hpoll := hPollTwin
    (h7ra_stageP2Over_archive_at_cliRunBudgets_frozen_ok A lim mmpl gh W X h547 hG hRead hRaw hGrow hSpqr)
    (h7ra_stageP4Prev1_seqFree_at_cliRunBudgets_ok A lim mmpl gh W h547 hRead)
    (h7ra_tryDecrypt507_placed_ok A lim mmpl gh W hG hAesDec hSpqr hRecv_ne htd)
    hsEnv'
  intro stk hstk hstk64
  exact dpSlot_ok_state_frozen_placed cliRunBudgets (cliRunSemOverV4 X W) stk hstk hstk64
    (cliDecryptPrekey_ok_state_frozen_placed_at_block (ext := H)
      (dpSlotPollKStatePlaced A lim sEnvs.decryptPrekey cliRunBudgets (cliRunSemOverV4 X W))
      (dpSlotPollKStatePlaced_inv_vm A lim sEnvs.decryptPrekey cliRunBudgets (cliRunSemOverV4 X W))
      (dpSlotPollKStatePlaced_res_vm A lim sEnvs.decryptPrekey cliRunBudgets (cliRunSemOverV4 X W))
      (fun stk' hs1 hs2 => by
        rw [hpan]
        exact hpoll hG hh hRead (hEq ▸ hDeser)
          encodeInjOn_deserializeScopeP_Q (fun _ h => h) rfl
          (fun _F _peer _me _pm hf hd => ⟨hf.1, hd⟩) stk' hs1 hs2)
      stk
      (by
        dsimp only [slotsOfSigPkFrozenPlaced, cliRunNeeds,
          CryptoVerification.SignalSession.Cli.RunCompose.mkSlot] at hstk
        simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, dpSlotPollKStatePlaced] at hstk ⊢
        omega)
      hstk64 (by decide))

/-- Discharges `H7RATightPollProducerAt` at `DecPkD3ValidOverOfEnv'` via `decPk_d3_validOver_tightRaw_at_b_poll_at_full_placedBudget'`. -/
theorem h7ra_tightPollProducerAt_decPkD3ValidOver [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (h547 : lsmpl.base 547 ≠ 0#64) :
    H7RATightPollProducerAt A lim mmpl gh W X DecPkD3ValidOverOfEnv' tdEnv DecPkEnv :=
  fun hP2 hP4 hTry hEnv =>
    decPk_d3_validOver_tightRaw_at_b_poll_at_full_placedBudget'
      (p4Envs := fun B F0 peer pid kpkId spkId kbk =>
        h7ra_cliStageP4Prev1SeqFreeEnvs A.repAlloc B F0 peer pid kpkId spkId kbk
          (ReadFileRuleEnvFixed cliIo.rd))
      h547 mmpl gh W X cliRunBudgets (cliRunSemOverV4 X W) scopeIn
      hP2
      (fun F0 peer pid kpkId spkId kbk st_b => hP4 F0 peer pid kpkId spkId kbk st_b)
      hTry
      (fun g evs h => hEnv g evs h)

/-- Closed fixed-`cliRunBudgets` Slot-520 `OverD3` producer at `DecPkD3ValidOverOfEnv'`. -/
theorem h7ra_decPkValidOverTightRaw_slot520_ok [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (sEnvs : RunSlotEnvs)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile
        (ReadFileRuleEnvFixed cliIo.rd)))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W
      (InitialStateEnv W.C.F) (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv W a evs)
    (hsEnv' : ∀ g evs,
      DecPkD3ValidOverTightConcreteEnv' A.repAlloc W X tdEnv g evs →
      sEnvs.decryptPrekey g evs) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  h7ra_decPkValidOverTwin_slot520_ok A lim mmpl gh W X DecPkD3ValidOverOfEnv' sEnvs
    h547 hG hh hRead hDeser hRaw hGrow hAesDec hSpqr hRecv_ne htd
    (h7ra_tightPollProducerAt_decPkD3ValidOver A lim mmpl gh W X tdEnv sEnvs.decryptPrekey h547)
    hsEnv'

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAVerNeRawSlot520
