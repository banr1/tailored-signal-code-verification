/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchPathAContPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchSlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchAuxPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchUntrustedPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidMatchAuxPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidMatchPathAPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `LibsignalFrozen` Block-520 `decryptPrekey` Slot Contract for D3 `validMatch`

Proves `(slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced` on
`lsProg_579` for `cliRunSemD3ValidMatch X W` under `LibsignalFrozen`, polymorphic in
`ReadEnv`, `DeserEnv`, and `tdEnv`, with specializations to `TryDecryptCliLinkedEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ValidMatchDecPkSlot

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession (PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (ApiError Session SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalFrozen LibsignalFullPlacement LibsignalPlacement
   libsignalFrozen_of_keepsFrozen lsmpl lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5Model)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
  (SessionExtraRel coroOpkIdAtP4 hdrOpkIdBv? p1LoadedRecordAt sp_sub_cd0_align_std3
   stageP1CallStack stageP1ProgPlaced)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open CryptoVerification.E2E
  (LocalIdentity PreKeyMessageFields ResponderPreKeySecrets UnreachedPqxdhPrimitives
   acceptInput aesDecHookMallocng modelPrims)
open CryptoVerification.E2E.Pqxdh.Initiator (ofSignalPqxdhAcceptKeysInput)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (stageP3Sub5ExtraPre)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsAt FsFiles LibsignalCodeRoLoaded
   extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr
  (AddrVal RecordGhost apiDecResultAt preKeyMsgAt)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet
  (SendCall extract_withLsFrozen rootStack withLsFrozen)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SessionGhost SignalMessageGhost decryptDraws protocolAddressAt
   signalMessageAt uuidTryParse)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli
  (StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym
   cliSignedPreKeyVtSym dirAt)
open CryptoVerification.SignalSession.Cli.KitInst (cliIdentityStoreSpec cliSessionStoreSpec)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliRunBudgets cliRunNeeds cliWrOk coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost RunNeeds RunSem decResAt dpPollNeed
   dpSlotArgsPlaced mkSlot slotOutTr)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs
  (cliDecryptPrekeyNeed decPkDef dpFutDoneAt dpFutStartAt dpWrapFrame pkStoreKeys pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (LsTokenInit StageP1PostRegs apiDecResultAt_proto_entails_decResAt cliIdStoreSpecFull
   cliIdStoreSpecFullPlaced cliId_trustRel_eq_of_trusted cliKitStk cliPollIdKit
   cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSelfKitPlaced cliPollSessKit
   cliPollSessKitPlaced cliPollSpkKitPlaced cliPollStoresKitsAtPlaced
   cliPollStoresKitsAtPlaced_entails_storesAt cliSess_loadRel_isOk closStackUnusedP1OkAt
   clos_stack_3280_split_for_p1_ok closureCalleeSaved_toCalleeSavedPreserved coroUnusedP1At
   coroUnusedP1AtPlaced currentSession_some_of_cliPollSessPlaced_loadRel decPkDef_pathB_remId_ne
   decPkDef_pathB_ver_ne distinctSid_of_decPkOk₀ dpClosSubStack dpFutStartAt_split_for_p1_placed
   dpPollEntryPlaced dpPollNeed_eq_frame_add_subStack dpPollProgPlaced loadRec_of_cliPollSess_loadRel
   mkPathAHdr pathAInitSession pathAInitSession_scopeIn pathAInitState pmKyberId pmPreKeyId
   preKeyMsgAt_eq_idKey_sep preKeyMsgRemIdKeyAt rootStack_le_subStack
   sepWPp_conseq_pre sepWPp_sepExists_left slotOutTr_of_reject sp_frame_sub_add
   stackAt_poll_entry_split stackAt_subStack_split stackAt_subStack_sub_eq
   stageP1CallStack_le_subStack stageP2PostP1At stageP3CoroFrameAt stageP3StackFrameAt
   stageP3Sub5ExtraPrePrevEmpty subStack_le_sp_of_dpPollNeed
   subroutine_ok_of_sepWPp_steps trusted_ok_of_filesOkPeer)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (EncodeInjOn FilesOkPeer cliGhostExterns_sat_of_cliExternsPlaced
   encodeInjOn_deserializeScopeP_Q filesOk₀ loadRec scopeIn scopeKit)
open CryptoVerification.SignalSession.Coins (coinsAfterPlaced coinsAtPlaced)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.SpecBudget (aesDecBudgetSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
  (drop_session_structure4_placed_ok_at)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget
  (P2Sub1To3Arm1Env P2Sub1To3Arm2Env P2Sub1To4Arm3Env)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
  (InitializeBobV1OptFieldsEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget
  (P2V1Arm4Env P2V1Arm5EnvOfAcceptErr P2V1Arm6EnvOfBob)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudgetAux
  (StageP2MatchedBridgeEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
  (StageP2MatchedEnv StageP2MatchedMismatchEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
  (SpqrRecvC07C09aBytesEnv TryDecryptCliLinkedEnv)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux
  (overPollTryDecrypt_placed_at_linked)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase
  (cliDecryptPrekey_ok_state_frozen_placed_at_block)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
  (KyberPreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (PreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3
  (DecPkOkD3 decPkDef_pathA_err_d3 decPkDef_pathA_panic_d3 decPkDef_pathA_ver_ne_d3
   decPkDef_pathB_err_d3 decPkDef_pathB_panic_d3 pathB_scopeIn_and_match_d3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAPlacedBudget
  (P2PathAErrEnvD3Of P2PathAOkEnvD3Of StageP2PathAQpanCliD3AtFrozenPlacedBudgetStmt
   stageP2PathAQpan_cli_d3_at_frozen_placed_of_seams)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchAuxPlacedBudget
  (closure_pathB_p4_cont_d3_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchPathAContPlacedBudget
  (closure_pathA_p4_cont_d3_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchSlotPlacedBudget
  (CliStageP1OkEnv DecPkD3ValidMatchEnv DecPkD3ValidMatchPollEnv
   p1Ok_recombine_entails_stageP2_budget_d3_placed sepWPp_bind_p1_false_d3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchUntrustedPlacedBudget
  (closure_untrusted_d3_placed_ok dpPollPre_unpack_d3_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3
  (cliRunSemD3ValidMatch)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
  (cliPollSelfBudgetEnv cliPollSelf_kitPlacedOk_stagesHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget
  (dpPollEntrySpatialPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudget
  (stageP3_exit_pathA_to_pollPost_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
  (StageP2MatchedFramedCliPlacedStmt sepWPp_genP3_to_tailQpan_placed sepWPp_pollGoal_frame_placed
   stageP3_exit_prevEmpty_to_pollPost_placed storesAt_opened_entails_cliPollStoresKitsAtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget
  (cliFiles_eq_of_trace_eq_placed exit_entails_dpPollPost_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
  (StageP3Env StageP3ErrEnv StageP3OkPrefixEnv StageP3VerNeEnv genP3Pre_placed
   genP3S5PostFrame_placed pollTryDecryptPlacedSpecTPTight stageP3DispatchOkMidPrevEmpty_placed
   stageP3DispatchOkMid_placed stageP3ErrPostPrevEmpty_placed stageP3ErrPost_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (StageP2PathAEnv StageP4MatchedEnv StageP4MatchedStoreStepEnv StageP4PathAEnv
   StageP4PathAMarkErrEnv StageP4PathAStoreStepEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
  (cliPollStageP1_fsAt_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedInstPlacedBudget
  (stageP2Matched_framed_cli_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
  (stageP1OkPreAt stageP1_ok_placed_inst)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
  (cliPollKpk_kitPlacedOk cliPollPk_kitPlacedOk cliPollSpk_kitPlacedOk cliStageP2KitEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudget
  (stageP3GenStepsVRegs_of_base_full_placed_ok stageP3PrevEmptyVRegs_of_base_full_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudgetAux
  (StageP3CalleesM3BasePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
  (StageP4MatchedCliPlacedStmt StageP4PathACliPlacedStmt cliPollIdBudgetEnv cliPollKpkBudgetEnv
   cliPollPkBudgetEnv cliPollSessBudgetEnv stageP4Matched_placed_inst stageP4PathA_placed_inst)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
  (dpSlotPollKStatePlaced_inv_vm dpSlotPollKStatePlaced_res_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollGhostStateBudget decPkSlotSpecFrozenPlaced dpPollSpecStateBudget
   dpSlotPollKStatePlaced dpSlot_ok_state_frozen_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
  (SpqrV1PlacedSeams SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## `LibsignalFrozen` Path-A and Path-B Stage Closures -/

set_option maxHeartbeats 1200000 in
/-- `LibsignalFrozen` Path-A (`opt = none`) D3 Stage P2 → P3 → P4 closure. -/
theorem s2pv_closure_pathA_d3_frozen_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (hP2A : StageP2PathAQpanCliD3AtFrozenPlacedBudgetStmt A lim ReadEnv DeserEnv X mmpl gh W B
      P2PathAErrEnv P2PathAOkEnv)
    (hG : CliGhostAllocHooks M A lim gh)
    (hP4 : StageP4PathACliPlacedStmt) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r', Scope r' → scopeIn r')
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (kitEnv : SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B)))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)))
    (pkKitEnv : PreKeyStoreBudgetEnv
      (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)))
    (kpkKitEnv : ∀ kpkId spkId, KyberPreKeyStoreBudgetEnv
      (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey (cliKitStk B)))
    (hkitEnv : kitEnv = cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) DeserEnv ReadEnv)
    (hikitEnv : ikitEnv = cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
    (hpkKitEnv : pkKitEnv = cliPollPkBudgetEnv A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B) ReadEnv)
    (hkpkKitEnv : ∀ kpkId spkId,
      kpkKitEnv kpkId spkId =
        cliPollKpkBudgetEnv A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey (cliKitStk B) ReadEnv)
    (evs_p1 : List AllocEvent) (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hf0 : s0.fs.files = y.g.F) (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD3 ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok none))
    (hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv y.g))
    (hevs_p2_err : ∀ evs_p2, P2PathAErrEnv y.g evs_p2 → DecPkEnv y.g (evs_p1 ++ evs_p2))
    (hfits_p3 : ∀ evs_p2 m i k kp reg dk recG,
      P2PathAOkEnv y.g evs_p2 →
      pkToE? y.g.msg = some m → y.g.msg.message = i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
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
      pkToE? y.g.msg = some m → y.g.msg.message = i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
        y.g.msg.message.messageVersion.zeroExtend 32 →
      CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv tdEnv recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me y.g.msgG.msg y.g.msg.message y.g.coins evs_p3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      FitsEnv M lim (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st)
        (StageP4PathAEnv
          (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B)) kitEnv
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
      pkToE? y.g.msg = some m → y.g.msg.message = i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
        y.g.msg.message.messageVersion.zeroExtend 32 →
      CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv tdEnv recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me y.g.msgG.msg y.g.msg.message y.g.coins evs_p3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      StageP4PathAStoreStepEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B)) kitEnv
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
      pkToE? y.g.msg = some m → y.g.msg.message = i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
        y.g.msg.message.messageVersion.zeroExtend 32 →
      CloneRel recG G₁ →
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
      pkToE? y.g.msg = some m → y.g.msg.message = i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
        y.g.msg.message.messageVersion.zeroExtend 32 →
      CloneRel recG G₁ →
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
      pkToE? y.g.msg = some m → y.g.msg.message = i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
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
    (hfr1 : LibsignalFrozen lsmpl s1.mem)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x0868#64)
    (hrun1 : s1.status = .Running)
    (hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    SepWPp prog (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
  obtain ⟨_m0, _, _, _hpk0, hdec0⟩ := id hdecOk
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  dsimp only [cliPollSessKitPlaced] at hload_rel
  have hloadS : loadRec Scope y.g.F y.g.peer.val = .ok none :=
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
       p1LoadedRecordAt scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       lsLogOff ∗
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
          lsLogOff ∗
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
          lsLogOff ∗
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
      hevs_p2 hwg_eq hpkToE hmsg_i hi hk hkp hreg hacc hex hmsg_fold hsteps12 htr2 hpc2 hrun2
      hs2_sp hsp_align2 _ _ _ hvregs2 hfr2
    subst hwg_eq
    have hro2 : LibsignalCodeRoLoaded lsmpl s2.mem :=
      ⟨LibsignalCodeLoaded.of_codeLoaded hfr2.2, hfr2.1⟩
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
      exact decPkDef_pathA_panic_d3 X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS hcur htrusted hpkToE hmsg_i hi hk hkp hreg hacc hver hpan_s5
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
    let hc := StageP3CalleesM3BasePlaced.of_cliExternsPlaced mmpl gh W hG
    refine stageP3GenStepsVRegs_of_base_full_placed_ok
      (M.stepEvents (evs_p1 ++ evs_p2) y.st)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) W.C 0#64 W.Q.K
      hc hc.chainClone hc.senderChainClone hTryDec
      s0 s2 y.fut y.cx y.out 8#64 8#64 y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8 y.g.coins
      recG st0 y.g.peer y.g.me y.g.msgG.msg y.g.msg.message F_p3 _
      (hfits_p3 evs_p2 m i k kp reg dk recG hevs_p2 hpkToE hmsg_i hi hk hkp hreg hacc hex)
      (by decide) (Or.inr (distinctSid_of_decPkOk₀ hdec0)) hSeeds hRC hPqLt
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
        hsub hfPeer hdec0 (pid := pid) (sid := m.spkId) (kid := m.kpkId) (kbk := y.g.msg.baseKey)
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
            (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ).storeAt
              (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
            (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ).identityAt
              y.g.stores StoresGhost.opened.identity ∗
            (cliPollPkKitPlaced A.repAlloc y.g.F pid σ).storeAt
              (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
            (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ).storeAt
              (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
            (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt
              (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
            dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
            memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
              (dpClosSubStack B - rootStack)) := by
        dsimp only [F_p3]
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
        refine Entails.trans (sepConj_mono_left hstores_in) ?_
        dsimp only [cliPollStoresKitsAtPlaced]
        sep_frame
      exact sepWPp_conseq_pre hunpack_p3
        (closure_pathA_p4_cont_d3_placed hP4 B S hh hReadFile hDeser hS stk' hneed hstk63 y
          hfPeer hdecOk hloadS hcur htrusted m i k kp reg dk
          kitEnv ikitEnv pkKitEnv (kpkKitEnv m.kpkId m.spkId)
          hkitEnv hikitEnv hpkKitEnv (hkpkKitEnv m.kpkId m.spkId)
          ((evs_p1 ++ evs_p2) ++ evs_p3) recG G₁ G'
          rngPtr whisperMsgPtr ptCap ptPtr y.g.msgG.msg preKeyMsgRem P_s' R pt s0 s2 s'
          hpkToE hmsg_i hi hk hkp hreg hacc hex
          (hfits_p4 evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt
            hevs_p2 hpkToE hmsg_i hi hk hkp hreg hacc hex hver hcl hdec_rel hevs_p3 hok)
          (fun evs_p4 hevs_p4 =>
            hevs_ok evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4
              hevs_p2 hpkToE hmsg_i hi hk hkp hreg hacc hex hver hcl hdec_rel hevs_p3 hok hevs_p4)
          (fun evs_p4 hevs_p4 =>
            hevs_markErr evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4
              hevs_p2 hpkToE hmsg_i hi hk hkp hreg hacc hex hver hcl hdec_rel hevs_p3 hok hevs_p4)
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
          hevs_p2 hpkToE hmsg_i hi hk hkp hreg hacc hex hver hcl hdec_rel hevs_p3 herr hne_p)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathA_err_d3 X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS hcur htrusted hpkToE hmsg_i hi hk hkp hreg hacc hver herr hne_p)
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
          hevs_p2 hpkToE hmsg_i hi hk hkp hreg hacc hex hver_ne hevs_p3)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathA_ver_ne_d3 X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS hcur htrusted hpkToE hmsg_i hi hk hkp hreg hacc hver_ne)
        hent_f' hsf_sp htr_f hcs_f hvregs_f

set_option maxHeartbeats 1200000 in
/-- `LibsignalFrozen` Path-B (`opt = some r`, matched session) D3 Stage P2 → P3 → P4 closure. -/
theorem s2pv_closure_pathB_d3_frozen_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {gh : CliGhostHooks}
    (hP2 : StageP2MatchedFramedCliPlacedStmt)
    (hG : CliGhostAllocHooks M A lim gh)
    (hP4 : StageP4MatchedCliPlacedStmt)
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r', Scope r' → scopeIn r')
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (kitEnv : SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B)))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)))
    (hkitEnv : kitEnv = cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) DeserEnv ReadEnv)
    (hikitEnv : ikitEnv = cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
    (evs_p1 : List AllocEvent)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp) (hf0 : s0.fs.files = y.g.F)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD3 ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer
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
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv tdEnv recG G₁ sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          y.g.coins evs_p3 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .ok pt →
        FitsEnv M lim (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st)
          (StageP4MatchedEnv
            (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B)) kitEnv
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
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv tdEnv recG G₁ sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          y.g.coins evs_p3 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .ok pt →
        StageP4MatchedStoreStepEnv
          (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B)) kitEnv
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
        CloneRel recG G₁ →
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
    (hfroz1 : LibsignalFrozen lsmpl s1.mem)
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
       p1LoadedRecordAt scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
  have hro1 : LibsignalCodeRoLoaded lsmpl s1.mem :=
    ⟨LibsignalCodeLoaded.of_codeLoaded hfroz1.2, hfroz1.1⟩
  obtain ⟨_m0, _, _, _hpk0, hdec0⟩ := id hdecOk
  let sp := s0.sp - 0xcd0#64
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
  dsimp only [cliPollSessKitPlaced] at hload_rel
  obtain ⟨hloadS, hr_eq, hIn, hMatch, _, _, hSeeds, hRC, hPqLt⟩ :=
    pathB_scopeIn_and_match_d3 hinjK hsub hfPeer hdecOk hload_rel hcur
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
    hsub hfPeer hdec0 (pid := pid) (sid := sid) (kid := kid) (kbk := kbk)
  have hstk_split := stackAt_subStack_sub_eq sp B (rootStack_le_subStack B) hsp_sub
  have hpre_split :
      stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut (some ⟨some sess⟩) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      ((stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
          y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
        p1LoadedRecordAt scopeKit A.repAlloc y.fut (some ⟨some sess⟩) ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        lsLogOff ∗
        stackAt sp rootStack) ∗ F_p2) ∗ Fr_tail := by
    rw [hstk_split]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores_in))))))) ?_
    unfold cliPollStoresKitsAtPlaced F_p2 Fr_tail
    sep_frame
  refine sepWPp_conseq_pre hpre_split (sepWPp_pollGoal_frame_placed A lim DecPkEnv B S stk' y ?_)
  refine hP2 mmpl gh W B S scopeKit y sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 F_p2 _ _
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
          lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          stackAt sp rootStack := by
      rw [M.stepEvents_append evs_p1 evs_p2 y.st]
      exact hent_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_f')) hm_f
    have hdec_at := apiDecResultAt_proto_entails_decResAt A.repAlloc y.out
      (.invalidMessage .preKey .badCiphertext) err
    have hstores_out := cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc)
      (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    have hm2 : sf.mem ⊨
        apiDecResultAt A.repAlloc y.out (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer pid sid kid kbk σ
          y.g.stores StoresGhost.opened ∗
        (protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          lsLogOff ∗
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
          lsLogOff ∗
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
    subst hwg_eq
    have hfroz2 : LibsignalFrozen lsmpl s2.mem :=
      libsignalFrozen_of_keepsFrozen hfroz1 hsteps12.keepsFrozen
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
      exact decPkDef_pathB_panic_d3 X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
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
    let hc := StageP3CalleesM3BasePlaced.of_cliExternsPlaced mmpl gh W hG
    refine stageP3PrevEmptyVRegs_of_base_full_placed_ok
      (M.stepEvents (evs_p1 ++ evs_p2) y.st)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) W.C 0#64 W.Q.K
      hc hc.chainClone hc.senderChainClone hTryDec
      (drop_session_structure4_placed_ok_at (i := 518) hh.codecHooks.dealloc (by decide))
      s0 s2 y.fut y.cx y.out 8#64 y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8 y.g.coins
      g recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message F_p3 _
      (hfits_p3 hrem_eq evs_p2 recG hevs_p2 hex)
      (by decide) (Or.inr (distinctSid_of_decPkOk₀ hdec0)) hSeeds hRC hPqLt
      hfroz2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot) htr20 hvregs2 ?_ ?_ ?_
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
      exact closure_pathB_p4_cont_d3_placed hP4 mmpl gh W X B S Scope hh hReadFile hDeser hS stk'
        hneed hstk63 y kitEnv ikitEnv hkitEnv hikitEnv sess ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 s'
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
        (decPkDef_pathB_err_d3 X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
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

/-! ## Block-518 Poll and Block-520 Slot Lift -/

/-- `withLsFrozen`-guarded block-518 poll specification for D3 `validMatch` (`DecPkOkD3`). -/
def s2pv_CliDpPollOkD3StateFrozenPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
    A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
  subroutine_ok
    (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (lsρ lsReadFileSym)
    (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
  subroutine_ok
    (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (lsmpl.base 46)
    (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
  EncodeInjOn scopeKit →
  (∀ r, Scope r → scopeIn r) →
  S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope →
  (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
    FilesOkPeer Scope F peer ∧ DecPkOkD3 ⟨W.C, W.Q⟩ Scope F peer me pm) →
  ∀ stk' : Nat, (dpSlotPollKStatePlaced A lim DecPkEnv B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
    subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      dpPollEntryPlaced
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk'))

set_option maxHeartbeats 1200000 in
/-- Block-518 `withLsFrozen` poll proof for D3 `validMatch`. -/
theorem s2pv_decPk_d3_validMatch_poll_frozen_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hP2A : StageP2PathAQpanCliD3AtFrozenPlacedBudgetStmt A lim ReadEnv DeserEnv X mmpl gh W B
      P2PathAErrEnv P2PathAOkEnv)
    (hG : CliGhostAllocHooks M A lim gh)
    (hTryDec : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hEnv : ∀ g evs,
      DecPkD3ValidMatchPollEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv tdEnv g evs →
      DecPkEnv g evs) :
    s2pv_CliDpPollOkD3StateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope := by
  intro hh hRead hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hfroz0, hpre0⟩ :=
    extract_withLsFrozen
      (spec := dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk') hpre
  have hro0 : LibsignalCodeRoLoaded lsmpl s0.mem :=
    ⟨LibsignalCodeLoaded.of_codeLoaded hfroz0.2, hfroz0.1⟩
  have hpre_ro : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre y s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hro0, hpre0⟩
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_d3_placed (X := X) (W := W) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre_ro
  obtain ⟨_m0, _, _, _hpk0, hdec0⟩ := hpure.decPkOk
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  have hEqP :
      CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
    dsimp only [
      CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced,
      dpPollProgPlaced, stageP1ProgPlaced
    ]
    rw [withPanics_cliGhostExterns mmpl gh W]
  have hRead' := hEqP ▸ hRead
  have hDeser' := hEqP ▸ hDeser
  cases b with
  | false =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    rw [hEqP]
    exact closure_untrusted_d3_placed_ok A lim hDropNz mmpl gh W X B S Scope
      hh hRead' hDeser' hinjK hsub hS stk' hneed' hstk63 y
      (fun evs hevs => hpure.fits evs (hEnv y.g evs (Or.inl hevs)))
      (fun evs hevs => hEnv y.g evs (Or.inl hevs))
      R s0 hpc hrun hsp hpure.ro hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer
      hpure.decPkOk htrusted hm_base
  | true =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    have hhSt :
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
          A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
      ⟨hh.alloc, hh.allocFs, hh.panics, hh.memcpyRO, hh.bcmp, hh.fs,
       hh.utf8, hh.memrchr, hh.codecHooks, hh.allocZeroed, hh.stringClone, hh.formatInner⟩
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
      cliPollKpkBudgetEnv A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey σ ReadEnv
    let sp := s0.sp - 0xcd0#64
    have hsp_align0 : (s0.sp &&& 15#64 == 0#64) = true := by
      simpa [State.spAligned] using hsp
    have hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat :=
      (subStack_le_sp_of_dpPollNeed hneed' hpure.stk_le_sp).1
    have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced A.repAlloc σ y.g.stores
      hsub hpure.filesOkPeer hdec0 (pid := pid) (sid := sid) (kid := kid) (kbk := kbk)
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
      Satisfies.mono (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left hent_stores)))) hm_base
    have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
      have := dpPollNeed_eq_frame_add_subStack B; omega
    have hp1_le : stageP1CallStack kit ikit ≤ dpClosSubStack B :=
      stageP1CallStack_le_subStack (A := A.repAlloc) 0#64 y.g.F scopeKit y.g.peer B
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
    dsimp only [cliPollStoresKitsAtPlaced, coroUnusedP1AtPlaced] at hm_flat
    let P_p1 : SepProp :=
      stageP1OkPreAt A lim y.st kit ikit StoresGhost.opened.sessions StoresGhost.opened.identity
        y.g.peer y.g.msg.identityKey s0 sp y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) y.g.stores
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
        v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390 b_4f2
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
      Satisfies.mono (by
        dsimp only [P_p1, Fr_inner, stageP1OkPreAt, kit, ikit, pkKit, spkKit, kpkKit,
          cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
          cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced,
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSignedPreKeyStoreSpecPlaced,
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKpkStoreSpecFullPlaced,
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced]
        sep_frame) hm_flat
    rw [hEqP]
    refine ⟨P_p1 ∗ Fr_inner, R, hm_split, ?_⟩
    have hfits_all :
        FitsEnv M lim y.st
          (DecPkD3ValidMatchPollEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
            P2PathAErrEnv P2PathAOkEnv tdEnv y.g) :=
      fun evs hevs => hpure.fits evs (hEnv y.g evs hevs)
    have hfits_p1 : FitsEnv M lim y.st (CliStageP1OkEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g) :=
      fun evs hevs => hfits_all evs (Or.inr (Or.inl hevs))
    have hwp := stageP1_ok_placed_inst hDropNz mmpl gh W B y.g.F y.g.peer y.g.msg.identityKey
      hhSt hRead' hDeser' y.st StoresGhost.opened.sessions StoresGhost.opened.identity
      (Nat.le_trans hp1_le hsub64) rfl rfl
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
      (cliPollStageP1_fsAt_placed hh y.g.F scopeKit y.g.peer B hpure.files_eq)
      hpc hrun hsp_align0 rfl hpure.x0 hpure.x1 hpure.x2
    refine sepWPp_bind_p1_false_d3 hwp ?_
    intro s1 P_1 hsteps01 hpc1 hrun1 hq1
    rcases hq1 with ⟨⟨opt, evs_p1, hP1_raw, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
      hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
      hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, hro1⟩
    have hfroz1 : LibsignalFrozen lsmpl s1.mem :=
      libsignalFrozen_of_keepsFrozen hfroz0 hsteps01.keepsFrozen
    have hevs_p1 : CliStageP1OkEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs_p1 := hP1_raw
    have htr1 : s1.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollSessKit,
        cliSessionStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
        cliIdentityStoreSpec] using htr_evs
    have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true :=
      hs1_sp ▸ sp_sub_cd0_align_std3 hsp_align0
    have hregs1 : StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) :=
      ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
       hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1⟩
    refine sepWPp_conseq_pre (sepConj_mono_left hent_1) ?_
    simp only [sepExists_sepConj_left]
    refine sepWPp_sepExists_left fun v_a8 =>
      sepWPp_sepExists_left fun v_b8 =>
      sepWPp_sepExists_left fun v_d0 => ?_
    have hrecomb := p1Ok_recombine_entails_stageP2_budget_d3_placed stk' hneed' hstk63 y
      (M.stepEvents evs_p1 y.st) s0 s1 coins v_a8 v_b8 v_d0 opt
    dsimp only at hrecomb
    refine sepWPp_conseq_pre hrecomb ?_
    cases opt with
    | none =>
      have hfits_p2 :
          FitsEnv M lim (M.stepEvents evs_p1 y.st)
            (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv y.g) :=
        (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inl h⟩))).seq_right hevs_p1
      have hevs_p2_err : ∀ evs_p2, P2PathAErrEnv y.g evs_p2 → DecPkEnv y.g (evs_p1 ++ evs_p2) :=
        fun evs_p2 he2 =>
          hEnv y.g _ (Or.inr (Or.inr (Or.inl
            ⟨hload_rel, Or.inl (SeqEnv.append hevs_p1 (Or.inl he2))⟩)))
      refine s2pv_closure_pathA_d3_frozen_placed_ok mmpl gh W X B S hP2A hG
        (stageP4PathA_placed_inst hDropNz) Scope hhSt hRead' hDeser' hTryDec
        hinjK hsub hS stk' hneed' hstk63 y kitEnv ikitEnv pkKitEnv kpkKitEnv
        rfl rfl rfl (fun _ _ => rfl)
        evs_p1 s0 s1 coins v_a8 v_b8 v_d0 R
        hpure.files_eq hpure.filesOkPeer hpure.decPkOk hpure.coins_lt htrusted hload_rel
        hfits_p2 hevs_p2_err ?_ ?_ ?_ ?_ ?_ ?_
        hsteps01 htr1 hfroz1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
      · intro evs_p2 m i k kp reg dk recG he2 hpk hmsg_i hi hk hkp hreg hacc hex
        exact (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
            hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, Or.inl h⟩⟩))).seq_right
          (SeqEnv.append hevs_p1 he2)
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt he2 hpk hmsg_i hi hk hkp hreg hacc hex
          hver hcl hdec he3 hok
        exact (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
            hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex,
            Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok, h⟩⟩⟩))).seq_right
          (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4 he2 hpk hmsg_i hi hk hkp hreg hacc hex
          hver hcl hdec he3 hok he4
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
          hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex,
          Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok,
            SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
              (Or.inr (Or.inr (Or.inr he4)))⟩⟩⟩)))
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4 he2 hpk hmsg_i hi hk hkp hreg hacc hex
          hver hcl hdec he3 hok he4
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
          hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex,
          Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok,
            SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
              (Or.inr (Or.inl he4))⟩⟩⟩)))
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 e he2 hpk hmsg_i hi hk hkp hreg hacc hex
          hver hcl _hdec he3 _herr _hne
        have he3_env : StageP3Env tdEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
          unfold StageP3Env
          simp only [hver, ↓reduceIte]
          exact ⟨G₁, hcl, he3⟩
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
          hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex,
          Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩)))
      · intro evs_p2 m i k kp reg dk recG evs_p3 he2 hpk hmsg_i hi hk hkp hreg hacc hex hver_ne he3
        have he3_env : StageP3Env tdEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
          unfold StageP3Env
          simp only [hver_ne, ↓reduceIte]
          exact he3
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
          hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex,
          Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩)))
    | some r =>
      obtain ⟨sess, hcur⟩ := currentSession_some_of_cliPollSessPlaced_loadRel hload_rel
      have hfits_p2 :
          FitsEnv M lim (M.stepEvents evs_p1 y.st)
            (StageP2MatchedEnv sess y.g.msg.identityKey) :=
        (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur, Or.inl h⟩))).seq_right hevs_p1
      refine s2pv_closure_pathB_d3_frozen_placed_ok stageP2Matched_framed_cli_placed_ok hG
        (stageP4Matched_placed_inst hDropNz) mmpl W X B S Scope
        hhSt hRead' hDeser' hTryDec hinjK hsub hS stk' hneed' hstk63
        y kitEnv ikitEnv rfl rfl evs_p1 r sess s0 s1 coins v_a8 v_b8 v_d0 R
        hpure.files_eq hpure.filesOkPeer hpure.decPkOk hpure.coins_lt htrusted hload_rel hcur hfits_p2
        ?_ ?_ ?_ ?_ ?_ ?_
        hsteps01 htr1 hfroz1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
      · intro hne evs_p2 he2
        have he2_env : StageP2MatchedEnv sess y.g.msg.identityKey evs_p2 := by
          unfold StageP2MatchedEnv
          simp only [hne, ↓reduceIte]
          exact he2
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inr
          ⟨r, sess, hload_rel, hcur, Or.inl (SeqEnv.append hevs_p1 he2_env)⟩)))
      · intro hrem evs_p2 recG he2 hex
        exact (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
            Or.inr ⟨hrem, recG, hex, Or.inl h⟩⟩))).seq_right (SeqEnv.append hevs_p1 he2)
      · intro hrem hver evs_p2 recG G₁ G' evs_p3 pt he2 hex hcl hdec he3 hok
        exact (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
            Or.inr ⟨hrem, recG, hex, Or.inr ⟨hver, G₁, G', pt, hcl, hdec, hok, h⟩⟩⟩))).seq_right
          (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
      · intro hrem hver evs_p2 recG G₁ G' evs_p3 pt evs_p4 he2 hex hcl hdec he3 hok he4
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
          Or.inr ⟨hrem, recG, hex, Or.inr ⟨hver, G₁, G', pt, hcl, hdec, hok,
            SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3) (Or.inr he4)⟩⟩⟩)))
      · intro hrem hver evs_p2 recG G₁ G' evs_p3 e he2 hex hcl _hdec he3 _herr _hne
        have he3_env : StageP3Env tdEnv recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
          unfold StageP3Env
          simp only [hver, ↓reduceIte]
          exact ⟨G₁, hcl, he3⟩
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
          Or.inr ⟨hrem, recG, hex,
            Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩)))
      · intro hrem hver_ne evs_p2 recG evs_p3 he2 hex he3
        have he3_env : StageP3Env tdEnv recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
          unfold StageP3Env
          simp only [hver_ne, ↓reduceIte]
          exact he3
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
          Or.inr ⟨hrem, recG, hex,
            Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩)))

/-- Caller-block (`i < 619`) `decPkSlotSpecFrozenPlaced` reduction at `lsmpl.base 520` for D3 `validMatch`. -/
theorem s2pv_cliDecryptPrekey_slot_d3_match_frozen_placedBudget_at_block [LibsignalFullPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W))] (_hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2A : StageP2PathAQpanCliD3AtFrozenPlacedBudgetStmt A lim ReadEnv DeserEnv X mmpl gh W B
      P2PathAErrEnv P2PathAOkEnv)
    (hG : CliGhostAllocHooks M A lim gh)
    (hTryDec : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkD3 ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hevs_sub : ∀ g evs,
      DecPkD3ValidMatchEnv A.repAlloc W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv tdEnv g evs →
      DecPkEnv g evs)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok prog (lsmpl.base 520) (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hpan : Rust.withPanics H = H := withPanics_cliGhostExterns mmpl gh W
  have : IsLsBlockProg prog i (Rust.withPanics H) := by
    rw [hpan]; exact hcaller
  have hEq518 :
      lsProg_518 (Rust.withPanics H) =
      CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced H := rfl
  have hpoll := s2pv_decPk_d3_validMatch_poll_frozen_placedBudget hDropNz mmpl gh W X B S Scope
    hP2A hG hTryDec hevs_sub
  exact dpSlot_ok_state_frozen_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_frozen_placed_at_block (ext := H)
      (dpSlotPollKStatePlaced A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_inv_vm A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_res_vm A lim DecPkEnv B S)
      (fun stk' hs1 hs2 => by
        rw [hEq518]
        exact hpoll hh hRead hDeser hinjK hsub hS hok stk' hs1 hs2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, dpSlotPollKStatePlaced] at hstk ⊢
          omega)
      hstk64)

/-- `OkPlaced` slot wrapper on caller blocks `i < 619` for D3 `validMatch`. -/
theorem s2pv_cliDecryptPrekey_slotOk_d3_match_frozen_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2A : StageP2PathAQpanCliD3AtFrozenPlacedBudgetStmt A lim ReadEnv DeserEnv X mmpl gh W B
      P2PathAErrEnv P2PathAOkEnv)
    (hG : CliGhostAllocHooks M A lim gh)
    (hTryDec : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkD3 ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hevs_sub : ∀ g evs,
      DecPkD3ValidMatchEnv A.repAlloc W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv tdEnv g evs →
      DecPkEnv g evs)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecFrozenPlaced A lim DecPkEnv S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) :=
  fun stk h1 h2 =>
    s2pv_cliDecryptPrekey_slot_d3_match_frozen_placedBudget_at_block A lim B mmpl gh W hi X S Scope
      hDropNz hh hRead hDeser hP2A hG hTryDec hinjK hsub hS hok hevs_sub
      stk (hneed ▸ h1) h2

/-- Polymorphic block-520 `decryptPrekey.OkPlaced` producer on `lsProg_579` under `LibsignalFrozen`. -/
theorem s2pv_decPkValidMatchSlotOk_frozen_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2A : StageP2PathAQpanCliD3AtFrozenPlacedBudgetStmt A lim ReadEnv DeserEnv X mmpl gh W
      cliRunBudgets P2PathAErrEnv P2PathAOkEnv)
    (hTryDec : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) tdEnv)))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3ValidMatchEnv A.repAlloc W X cliRunBudgets ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv tdEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkD3 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  s2pv_cliDecryptPrekey_slotOk_d3_match_frozen_placedBudget
    (prog := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
    A lim cliRunBudgets mmpl gh W (by decide) X S scopeIn needs
    h547 hh hRead hDeser hP2A hG hTryDec
    encodeInjOn_deserializeScopeP_Q (fun _ h => h) hdecPk
    (fun F peer me pm hf hd => ⟨(hfiles ▸ hf).1, hdecPkOk F peer me pm hd⟩)
    hsEnv hneed

/-! ## Canonical Stage-P2 and Linked `tryDecrypt` Specializations -/

/-- CLI Path-A D3 Stage-P2 error allocator envelope. -/
abbrev s2pv_P2PathAErrEnvD3CliOf [LibsignalPlacement] (A : RustAlloc)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets) :
    DecPkGhost → List AllocEvent → Prop :=
  P2PathAErrEnvD3Of (A := A) X W B
    (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
    (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
    (cliStageP2KitEnvs (A := A) ReadEnv B
      (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B) ReadEnv))

/-- CLI Path-A D3 Stage-P2 normal-exit (`+0x1778`) allocator envelope. -/
abbrev s2pv_P2PathAOkEnvD3CliOf [LibsignalPlacement] (A : RustAlloc)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets) :
    DecPkGhost → List AllocEvent → Prop :=
  P2PathAOkEnvD3Of (A := A) X W B
    (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
    (cliStageP2KitEnvs (A := A) ReadEnv B
      (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B) ReadEnv))

private theorem s2pv_congr10 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 β : Sort _}
    (f : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → β)
    {a1 b1 : α1} {a2 b2 : α2} {a3 b3 : α3} {a4 b4 : α4} {a5 b5 : α5}
    {a6 b6 : α6} {a7 b7 : α7} {a8 b8 : α8} {a9 b9 : α9} {a10 b10 : α10}
    (h1 : a1 = b1) (h2 : a2 = b2) (h3 : a3 = b3) (h4 : a4 = b4) (h5 : a5 = b5)
    (h6 : a6 = b6) (h7 : a7 = b7) (h8 : a8 = b8) (h9 : a9 = b9) (h10 : a10 = b10) :
    f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = f b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 := by
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10; rfl

private theorem s2pv_p2PathAErrEnvD3Of_cli_eq [LibsignalPlacement] {A : RustAlloc}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {BobV1Env AcceptErrEnv}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B' B : RunBudgets) :
    P2PathAErrEnvD3Of (A := A) X W B' BobV1Env AcceptErrEnv
      (cliStageP2KitEnvs (A := A) ReadEnv B'
        (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B') ReadEnv)) =
    P2PathAErrEnvD3Of (A := A) X W B BobV1Env AcceptErrEnv
      (cliStageP2KitEnvs (A := A) ReadEnv B
        (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B) ReadEnv)) := by
  funext g evs
  unfold P2PathAErrEnvD3Of
  cases pkToE? g.msg with
  | none => rfl
  | some m =>
    dsimp only
    exact s2pv_congr10
      (fun (spkBox : Nat) (spkPoll : List AllocEvent → Prop)
           (kpkBox : Nat) (kpkPoll : List AllocEvent → Prop)
           (pkBox : Nat) (pkPoll : BitVec 32 → List AllocEvent → Prop)
           (kpBox : Nat) (kpPoll : List AllocEvent → Prop)
           (regBox : Nat) (regPoll : List AllocEvent → Prop) =>
        let opkId? := hdrOpkIdBv? (mkPathAHdr m)
        P2Sub1To3Arm1Env spkBox spkPoll evs ∨
        P2Sub1To3Arm2Env spkBox spkPoll kpkBox kpkPoll evs ∨
        P2Sub1To4Arm3Env spkBox spkPoll kpkBox kpkPoll pkBox pkPoll opkId? evs ∨
        P2V1Arm4Env spkBox spkPoll kpkBox kpkPoll pkBox pkPoll kpBox opkId? kpPoll evs ∨
        (match pkStoreKeys g.F m, StoresGhost.opened.identity.keyPair cliIo.rd g.F with
         | some k, .ok kp =>
             let inp := ofSignalPqxdhAcceptKeysInput
               (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)
             P2V1Arm5EnvOfAcceptErr spkBox spkPoll kpkBox kpkPoll pkBox pkPoll kpBox opkId?
               kpPoll (AcceptErrEnv inp) evs ∨
             (match acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) inp with
              | none => False
              | some drKey =>
                  P2V1Arm6EnvOfBob spkBox spkPoll kpkBox kpkPoll pkBox pkPoll kpBox opkId?
                    kpPoll (BobV1Env inp drKey) regBox regPoll evs)
         | _, _ => False))
      (a1 := (cliPollSpkKitPlaced A g.F m.spkId (cliKitStk B')).getBoxSize)
      (b1 := (cliPollSpkKitPlaced A g.F m.spkId (cliKitStk B)).getBoxSize)
      (a2 := (cliStageP2KitEnvs (A := A) ReadEnv B'
        (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B') ReadEnv)
        g.F g.peer m.spkId m.kpkId (m.opkId.getD 0#32) g.msg.baseKey).spkEnv.getPollEnv
        StoresGhost.opened.signed m.spkId)
      (b2 := (cliStageP2KitEnvs (A := A) ReadEnv B
        (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B) ReadEnv)
        g.F g.peer m.spkId m.kpkId (m.opkId.getD 0#32) g.msg.baseKey).spkEnv.getPollEnv
        StoresGhost.opened.signed m.spkId)
      (a3 := (cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey (cliKitStk B')).getBoxSize)
      (b3 := (cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey (cliKitStk B)).getBoxSize)
      (a4 := (cliStageP2KitEnvs (A := A) ReadEnv B'
        (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B') ReadEnv)
        g.F g.peer m.spkId m.kpkId (m.opkId.getD 0#32) g.msg.baseKey).kpkEnv.getPollEnv
        StoresGhost.opened.kyber m.kpkId)
      (b4 := (cliStageP2KitEnvs (A := A) ReadEnv B
        (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B) ReadEnv)
        g.F g.peer m.spkId m.kpkId (m.opkId.getD 0#32) g.msg.baseKey).kpkEnv.getPollEnv
        StoresGhost.opened.kyber m.kpkId)
      (a5 := (cliPollPkKitPlaced A g.F (m.opkId.getD 0#32) (cliKitStk B')).getBoxSize)
      (b5 := (cliPollPkKitPlaced A g.F (m.opkId.getD 0#32) (cliKitStk B)).getBoxSize)
      (a6 := (cliStageP2KitEnvs (A := A) ReadEnv B'
        (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B') ReadEnv)
        g.F g.peer m.spkId m.kpkId (m.opkId.getD 0#32) g.msg.baseKey).pkEnv.getPollEnv
        StoresGhost.opened.oneTime)
      (b6 := (cliStageP2KitEnvs (A := A) ReadEnv B
        (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B) ReadEnv)
        g.F g.peer m.spkId m.kpkId (m.opkId.getD 0#32) g.msg.baseKey).pkEnv.getPollEnv
        StoresGhost.opened.oneTime)
      (a7 := (cliPollSelfKitPlaced A g.F g.peer (cliKitStk B')).kpBoxSize)
      (b7 := (cliPollSelfKitPlaced A g.F g.peer (cliKitStk B)).kpBoxSize)
      (a8 := (cliStageP2KitEnvs (A := A) ReadEnv B'
        (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B') ReadEnv)
        g.F g.peer m.spkId m.kpkId (m.opkId.getD 0#32) g.msg.baseKey).selfEnv.kpPollEnv
        StoresGhost.opened.identity)
      (b8 := (cliStageP2KitEnvs (A := A) ReadEnv B
        (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B) ReadEnv)
        g.F g.peer m.spkId m.kpkId (m.opkId.getD 0#32) g.msg.baseKey).selfEnv.kpPollEnv
        StoresGhost.opened.identity)
      (a9 := (cliPollSelfKitPlaced A g.F g.peer (cliKitStk B')).regIdBoxSize)
      (b9 := (cliPollSelfKitPlaced A g.F g.peer (cliKitStk B)).regIdBoxSize)
      (a10 := (cliStageP2KitEnvs (A := A) ReadEnv B'
        (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B') ReadEnv)
        g.F g.peer m.spkId m.kpkId (m.opkId.getD 0#32) g.msg.baseKey).selfEnv.regIdPollEnv
        StoresGhost.opened.identity)
      (b10 := (cliStageP2KitEnvs (A := A) ReadEnv B
        (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B) ReadEnv)
        g.F g.peer m.spkId m.kpkId (m.opkId.getD 0#32) g.msg.baseKey).selfEnv.regIdPollEnv
        StoresGhost.opened.identity)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

private theorem s2pv_p2PathAOkEnvD3Of_cli_eq [LibsignalPlacement] {A : RustAlloc}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {BobV1Env}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B' B : RunBudgets) :
    P2PathAOkEnvD3Of (A := A) X W B' BobV1Env
      (cliStageP2KitEnvs (A := A) ReadEnv B'
        (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B') ReadEnv)) =
    P2PathAOkEnvD3Of (A := A) X W B BobV1Env
      (cliStageP2KitEnvs (A := A) ReadEnv B
        (fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk B) ReadEnv)) := by
  funext g evs
  unfold P2PathAOkEnvD3Of
  cases pkToE? g.msg with
  | none => rfl
  | some m =>
    cases pkStoreKeys g.F m with
    | none => rfl
    | some k =>
      cases StoresGhost.opened.identity.keyPair cliIo.rd g.F with
      | error _ => rfl
      | ok kp =>
        dsimp only
        generalize acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
          (ofSignalPqxdhAcceptKeysInput
            (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)) = ak
        cases ak <;> rfl

private theorem s2pv_p2PathAErrEnvD3CliOf_eq [LibsignalPlacement] (A : RustAlloc)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B' B : RunBudgets) :
    s2pv_P2PathAErrEnvD3CliOf A ReadEnv X W B' =
    s2pv_P2PathAErrEnvD3CliOf A ReadEnv X W B :=
  s2pv_p2PathAErrEnvD3Of_cli_eq X W B' B

private theorem s2pv_p2PathAOkEnvD3CliOf_eq [LibsignalPlacement] (A : RustAlloc)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B' B : RunBudgets) :
    s2pv_P2PathAOkEnvD3CliOf A ReadEnv X W B' =
    s2pv_P2PathAOkEnvD3CliOf A ReadEnv X W B :=
  s2pv_p2PathAOkEnvD3Of_cli_eq X W B' B

/-- D3 `validMatch` poll allocator envelope at `(ReadEnv, DeserEnv, tdEnv)`. -/
abbrev s2pv_DecPkD3ValidMatchOfReadEnv [LibsignalPlacement] (A : RustAlloc)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    DecPkGhost → List AllocEvent → Prop :=
  DecPkD3ValidMatchEnv A W X B ReadEnv DeserEnv
    (s2pv_P2PathAErrEnvD3CliOf A ReadEnv X W B)
    (s2pv_P2PathAOkEnvD3CliOf A ReadEnv X W B)
    tdEnv

/-- Instantiates `StageP2PathAQpanCliD3AtFrozenPlacedBudgetStmt` across the four CLI store kits (`self`, `spk`, `kpk`, `pk`). -/
theorem s2pv_stageP2PathA_cli_d3_at_frozen_of_readEnv [LibsignalFullPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hRead : ∀ (B' : RunBudgets),
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile ReadEnv)) :
    StageP2PathAQpanCliD3AtFrozenPlacedBudgetStmt A lim ReadEnv DeserEnv X mmpl gh W B
      (s2pv_P2PathAErrEnvD3CliOf A.repAlloc ReadEnv X W B)
      (s2pv_P2PathAOkEnvD3CliOf A.repAlloc ReadEnv X W B) :=
  stageP2PathAQpan_cli_d3_at_frozen_placed_of_seams A lim X mmpl gh W B
    (kitEnvs := fun B' =>
      cliStageP2KitEnvs (A := A.repAlloc) ReadEnv B'
        (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B') ReadEnv))
    (fun B' g evs h =>
      Eq.mp (congrFun (congrFun (s2pv_p2PathAErrEnvD3CliOf_eq A.repAlloc ReadEnv X W B' B) g) evs) h)
    (fun B' g evs h =>
      Eq.mp (congrFun (congrFun (s2pv_p2PathAOkEnvD3CliOf_eq A.repAlloc ReadEnv X W B' B) g) evs) h)
    (fun B' st_b g h => by
      change FitsEnv M lim st_b
        (StageP2PathAEnv
          (s2pv_P2PathAErrEnvD3CliOf A.repAlloc ReadEnv X W B')
          (s2pv_P2PathAOkEnvD3CliOf A.repAlloc ReadEnv X W B') g)
      rw [s2pv_p2PathAErrEnvD3CliOf_eq A.repAlloc ReadEnv X W B' B,
          s2pv_p2PathAOkEnvD3CliOf_eq A.repAlloc ReadEnv X W B' B]
      exact h)
    hDropNz hG hSpqr
    (fun B' F0 peer _ _ _ _ hh =>
      cliPollSelf_kitPlacedOk_stagesHooks mmpl gh W B' F0 peer hDropNz hh (hRead B'))
    (fun B' F0 _ spkId _ _ _ hh =>
      cliPollSpk_kitPlacedOk mmpl gh W B' F0 spkId hDropNz hh (hRead B'))
    (fun B' F0 _ spkId kpkId _ kbk hh =>
      cliPollKpk_kitPlacedOk mmpl gh W B' F0 kpkId spkId kbk hDropNz hh (hRead B'))
    (fun B' F0 _ _ _ opkWord _ hh =>
      cliPollPk_kitPlacedOk mmpl gh W B' F0 opkWord hDropNz hh (hRead B'))

/-- Seam-discharged block-520 `decryptPrekey.OkPlaced` producer for D3 `validMatch`. -/
theorem s2pv_decPkValidMatchSlotOk_of_seams_frozen_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ (B' : RunBudgets),
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile ReadEnv))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hTryDec : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) tdEnv)))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      s2pv_DecPkD3ValidMatchOfReadEnv A.repAlloc W X cliRunBudgets ReadEnv DeserEnv tdEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkD3 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hEqP : dpPollProgPlaced H =
      CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced H := by
    dsimp only [
      CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced,
      dpPollProgPlaced, stageP1ProgPlaced
    ]
    rw [withPanics_cliGhostExterns mmpl gh W]
  exact s2pv_decPkValidMatchSlotOk_frozen_placedBudget mmpl gh W X h547 hG hh
    (hEqP ▸ hRead cliRunBudgets)
    hDeser
    (s2pv_stageP2PathA_cli_d3_at_frozen_of_readEnv A lim X mmpl gh W cliRunBudgets h547 hG hSpqr hRead)
    hTryDec S sEnvs needs hsEnv hfiles hdecPk hdecPkOk hneed

/-- Specializes `s2pv_decPkValidMatchSlotOk_of_seams_frozen_placedBudget` to `TryDecryptCliLinkedEnv W.C W.Q.K`. -/
theorem s2pv_decPkValidMatchSlotOk_linked_frozen_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ (B' : RunBudgets),
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile ReadEnv))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hSpqrLinked : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv)
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      s2pv_DecPkD3ValidMatchOfReadEnv A.repAlloc W X cliRunBudgets ReadEnv DeserEnv
        (TryDecryptCliLinkedEnv W.C W.Q.K) g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkD3 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  s2pv_decPkValidMatchSlotOk_of_seams_frozen_placedBudget mmpl gh W X h547 hG hh hRead hDeser hSpqr
    (overPollTryDecrypt_placed_at_linked mmpl gh W 0#64 hG hAesDec hSpqrLinked)
    S sEnvs needs hsEnv hfiles hdecPk hdecPkOk hneed

/-- Specializes `s2pv_decPkValidMatchSlotOk_linked_frozen_placedBudget` to `cliRunSemD3ValidMatch X W`. -/
theorem s2pv_decPkValidMatchSlotOk_cliRunSemD3ValidMatch_linked_frozen_placedBudget
    [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ (B' : RunBudgets),
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile ReadEnv))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hSpqrLinked : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv)
    (sEnvs : RunSlotEnvs)
    (hsEnv : ∀ g evs,
      s2pv_DecPkD3ValidMatchOfReadEnv A.repAlloc W X cliRunBudgets ReadEnv DeserEnv
        (TryDecryptCliLinkedEnv W.C W.Q.K) g evs →
      sEnvs.decryptPrekey g evs) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemD3ValidMatch X W)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  s2pv_decPkValidMatchSlotOk_linked_frozen_placedBudget mmpl gh W X h547 hG hh hRead hDeser
    hAesDec hSpqr hSpqrLinked (cliRunSemD3ValidMatch X W) sEnvs
    (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) hsEnv
    rfl rfl (fun _ _ _ _ h => h) rfl

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ValidMatchDecPkSlot
