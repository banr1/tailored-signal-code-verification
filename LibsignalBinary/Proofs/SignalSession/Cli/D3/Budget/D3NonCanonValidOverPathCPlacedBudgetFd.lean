/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollAuxPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPathCP4PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobProducerAux -- proof-setup: allow-public-import
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import ProofLib.SepLogic.WPp

/-!
# `hRead`-Free `Path C Over` Branch for Non-Matching Overwrite (`OverD3`)

Proves the `hRead`-free `Path C Over` branch `closure_pathCOver_d3_ofVerNe_at_b_full_placedBudget_ok`
extracting `SessionGhostValid recG ses0` from `overGenP3Pre_placed`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPathCPlacedBudgetFd

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (
  IdentityKey PublicKey SessionState SignalMessage SignalProtocolError
)
open CryptoGames.LibsignalSessionApi (ApiError Session SessionRecord)
open CryptoVerification (
  LibsignalFrozen LibsignalPlacement libsignalFrozen_of_keepsFrozen lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.E2E (
  LocalIdentity PreKeyMessageFields ResponderPreKeySecrets UnreachedPqxdhPrimitives acceptInput
  modelPrims
)
open CryptoVerification.E2E.Record (encSession)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (ClosureCalleeSavedP4)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5Model genP3S5ModelPanicProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  SessionExtraRel coroOpkIdAtP4 p1LoadedRecordAt sp_sub_cd0_align_std3 stageP1CallStack
  stageP4CallStack stageP4EnvOk stageP4Quiet
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  OverPrevEncOK StorePrev1Ops clearPending encodeRecordPrev1
  overPrevEncOK_clearPending_of_scopeIn_placed overScratch prevVecAt
  stageP3DispatchOkMidPrev1Placed stageP3Sub5ExtraPrePrev1
)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SeedsLen32 rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost decryptDraws protocolAddressAt sessionStateAt
  signalMessageAt uuidTryParse vecResultAt
)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal preKeyMsgAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsAt FsFiles LibsignalCodeRoLoaded speErrAt withLsCodeRoLoaded
)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (
  StoresGhost addressText cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym
  cliSignedPreKeyVtSym dirAt kpkMarkOf removePreKey
)
open CryptoVerification.SignalSession.Cli.KitInst (
  cliIdentityStoreSpec cliPreKeyStoreSpec cliSessionStoreSpec
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost RunSem decResAt dpPollNeed dpSlotArgsPlaced slotOutTr
)
open CryptoVerification.SignalSession.Cli.RunProofs (
  DecPkOk₀ SessMatchesPm dpFutDoneAt dpFutStartAt pkStoreKeys pkToE? pmOfE
)
open CryptoVerification.SignalSession.Cli.Slots (EncodeInjOn FilesOkPeer loadRec scopeIn scopeKit)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit StageP1PostRegs canonSession_of_sessionStateAt_extraRel cliIdStoreSpecFull
  cliIdStoreSpecFullPlaced cliId_saveRel_not_err cliId_trustRel_eq_of_trusted cliKitStk
  cliKpkStoreSpecFullPlaced cliKpk_markRel_error_to_mark cliKpk_markRel_ok_to_mark
  cliKyberPreKeyStoreSpecPlaced cliPk_removeRel_not_err_of_pkStoreKeys cliPollIdKit
  cliPollIdKitPlaced cliPollKpkKitPlaced cliPollKpk_markErr_entails_decResAt_anyHeap
  cliPollPkKitPlaced cliPollSessKit cliPollSessKitPlaced cliPollSessPrev1KitPlaced
  cliPollSpkKitPlaced cliPollStorePrev1OpsPlaced cliPollStoresKitsAtPlaced cliPreKeyStoreSpecPlaced
  cliSess_loadRel_isOk cliSignedPreKeyStoreSpecPlaced closStackUnusedP1OkAt
  clos_stack_3280_split_for_p1_ok closureCalleeSaved_toCalleeSavedPreserved coroUnusedP1At
  coroUnusedP1AtPlaced decResultAt_ok_entails_decResAt_anyHeap distinctSid_of_decPkOk dpClosSubStack
  dpFutStartAt_split_for_p1_placed dpPollEntryPlaced dpPollNeed_eq_frame_add_subStack
  dpPollProgPlaced loadRec_of_cliPollSessPlaced_loadRel pathAInitSession pathAInitSession_scopeIn
  pathAInitState pmKyberId pmPreKeyId preKeyMsgAt_eq_idKey_sep preKeyMsgRemIdKeyAt
  rootStack_le_subStack sepWPp_conseq_pre sepWPp_sepExists_left sessionExtraRel_of_clone_decRel
  sp_frame_sub_add stackAt_poll_entry_split stackAt_subStack_split stageP1CallStack_le_subStack
  stageP2PostP1At stageP3CoroFrameAt stageP3OverStackFrameAt stageP3StackFrameAt
  stageP3StackFrameAt_eq_over subStack_le_sp_of_dpPollNeed subroutine_ok_of_sepWPp_steps
  trusted_ok_of_filesOkPeer
)
open CryptoVerification.SignalSession.Coins (coinsAfterPlaced coinsAtPlaced)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget (
  ChainClone3OkPlaced SenderChainClone3OkPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  StageP3ErrM3Env StageP3OkPrefixM3Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget (
  StageP4Prev1BranchPlaced StageP4Prev1ExitEnv StageP4Prev1NoneExitEnv StageP4Prev1StoreBranchEnv
  stageP4Prev1ExitAtPlaced stageP4Prev1PrePlaced stageP4Prev1RawPrePlaced stageP4Prev1SharedPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux (VerNeTopEnv)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  DecPkOkD3 ScopeOverIn decPkOk0_of_d3_pkToE decPkOverDef decPkOverDef_pathCOver_err
  decPkOverDef_pathCOver_mark_err decPkOverDef_pathCOver_ok decPkOverDef_pathCOver_panic
  decPkOverDef_pathCOver_ver_ne encodeRecordPrev1_pathCOver_lt_32 pm_fields_of_pkToE
  slotOutTr_over_of_accept slotOutTr_over_of_reject x29_eq_sp_add_c70_over_d3_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollAuxPlacedBudget (
  StageP4Prev1VRegsAtPlacedStmt closure_untrusted_over_d3_full_placedBudget_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget (
  CliDpPollOkOverV4StateFrozenPlacedAt CliStageP1OkEnv dpPollPre_unpack_over_d3_frozen_placed
  fitsEnv_after_d3 p1Ok_recombine_entails_stageP2_budget_d3_placed sepWPp_bind_p1_false_d3
  seqEnv_append_d3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage2PlacedBudget (
  StageP2OverErrD3Placed StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage4PlacedBudget (
  cliPollKpk_markOk_d3_placedBudget cliPollPk_removeIdOk_of_pkToE_placedBudget
  stageP3_exit_pathCOver_to_pollPost_d3_placedBudget storesAt_opened_entails_cliPollStoresKitsAtPlaced_d3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget (
  StageP3Prev1D3FrozenPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget (
  CliStageP4Prev1Envs p4_finish_dpPollPost_placed stageP4Prev1CallStack_le_subStack_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (
  overExit_entails_dpPollPost_placed overGenP3Pre_placed overGenP3S5PostFrame_placed
  overPathAP4RemAtPlaced stageP3MidPathC_entails_p4_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget (
  overPollTryDecryptPlacedSpecTPTight overSepWPp_genP3_to_tailQpan_placed
  overSepWPp_pollGoal_frame_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  StageP2OverEnv cliChainClone3_placed_ok cliDropSessionStructure4_placed_ok_at
  cliFiles_eq_of_trace_eq_placed cliFsAt_of_files_eq_placed cliPollStageP4Prev1_fsAt_placed
  cliSenderChainClone3_placed_ok overStageP3ErrPostPrevEmptyAt_placed
  stageP3DispatchOkMidPrev1At_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget (
  dpPollEntrySpatialPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  CliDpPollUntrustedEnv cliPollStageP1_fsAt_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget (
  stageP1OkPreAt stageP1_ok_placed_inst
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPathCP4PlacedBudgetFd (
  closure_pathCOver_p4_d3_cont_at_b_placedBudget h7pb_sepWPp_peek_mem
  h7pb_sessionGhostValid_of_overGenP3Pre
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobProducerAux (
  H7pbStageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt
  H7pbStageP3Prev1D3OfVerNeAtFrozenPlacedStmt H7pbStageP4Prev1VRegsAtBPlacedStmt
)

/-! ## `Path C Over` Branch Extracting `SessionGhostValid recG ses0` from `overGenP3Pre_placed` -/

set_option maxHeartbeats 1200000 in
theorem closure_pathCOver_d3_ofVerNe_at_b_full_placedBudget_ok [LibsignalPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {X : UnreachedPqxdhPrimitives} {mmpl : Obj.MultiPlacement}
    {gh : CliGhostHooks} {W : CliHooks}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hP2O : H7pbStageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt A lim X mmpl gh W B
      P2OverErrEnv P2OverOkEnv)
    (hP3O : H7pbStageP3Prev1D3OfVerNeAtFrozenPlacedStmt A lim tdEnv verNeEnv mmpl gh W)
    (hP4O : H7pbStageP4Prev1VRegsAtBPlacedStmt A lim mmpl gh W B p4Envs)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hTry : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r', Scope r' → scopeIn r')
    (hS : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (evs_p1 : List AllocEvent)
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hFits2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r))
    (hEnvErr2 : ∀ evs2, P2OverErrEnv y.g r evs2 → DecPkEnv y.g (evs_p1 ++ evs2))
    (hFits3 : ∀ evs2 m i k kp reg dk recG whisperG,
      P2OverOkEnv y.g r evs2 → pkToE? y.g.msg = some m → y.g.msg.message = i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      SessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      FitsEnv M lim (M.stepEvents (evs_p1 ++ evs2) y.st)
        (StageP3Prev1Env (tdEnv W) verNeEnv recG
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
          y.g.peer y.g.me whisperG y.g.msg.message
          (y.g.msg.message.messageVersion.zeroExtend 32)
          (encSession (clearPending s_old)) y.g.coins))
    (hEnvErr3 : ∀ evs2 evs3 m i k (kp : IdentityKeyPair) reg dk recG G₁ whisperG,
      P2OverOkEnv y.g r evs2 → pkToE? y.g.msg = some m → y.g.msg.message = i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      SessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      CloneRel recG G₁ →
      StageP3ErrM3Env (tdEnv W) recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me whisperG y.g.msg.message y.g.coins evs3 →
      DecPkEnv y.g (evs_p1 ++ evs2 ++ evs3))
    (hEnvVerNe3 : ∀ evs2 evs3 m i k (kp : IdentityKeyPair) reg dk recG,
      P2OverOkEnv y.g r evs2 → pkToE? y.g.msg = some m → y.g.msg.message = i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      SessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      StageP3VerNePrev1Env verNeEnv recG
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        (encSession (clearPending s_old)) evs3 →
      DecPkEnv y.g (evs_p1 ++ evs2 ++ evs3))
    (hFits4 : ∀ evs2 evs3 m i k kp reg dk recG G₁ G' pt whisperG,
      P2OverOkEnv y.g r evs2 → pkToE? y.g.msg = some m → y.g.msg.message = i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      SessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      CloneRel recG G₁ → G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixM3Env (tdEnv W) recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me whisperG y.g.msg.message y.g.coins evs3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
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
          pendingPreKey := none, pendingKyberPreKey := none }
      SessionGhostValid G' ses' →
      FitsEnv M lim (M.stepEvents (evs_p1 ++ evs2 ++ evs3) y.st)
        (StageP4Prev1ExitEnv prev1Kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
          kpkKit envs.kpkKitEnv StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber m.opkId y.g.peer.val
          y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey G' ses'
          (encSession (clearPending s_old))))
    (hEnv4 : ∀ evs2 evs3 evs4 m i k kp reg dk recG G₁ G' pt whisperG,
      P2OverOkEnv y.g r evs2 → pkToE? y.g.msg = some m → y.g.msg.message = i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      SessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      CloneRel recG G₁ → G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixM3Env (tdEnv W) recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me whisperG y.g.msg.message y.g.coins evs3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
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
          pendingPreKey := none, pendingKyberPreKey := none }
      SessionGhostValid G' ses' →
      StageP4Prev1ExitEnv prev1Kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
        kpkKit envs.kpkKitEnv StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber m.opkId y.g.peer.val
        y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey G' ses'
        (encSession (clearPending s_old)) evs4 →
      DecPkEnv y.g (evs_p1 ++ evs2 ++ evs3 ++ evs4))
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hd3False : DecPkOkD3 ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hScopeOver : ScopeOverIn r)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok (some r)))
    (hcur : r.currentSession = some s_old)
    (hnot_match : ¬ SessMatchesPm s_old y.g.msg)
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
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    let st_p1 := M.stepEvents evs_p1 y.st
    SepWPp prog (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim st_p1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗ lsLogOff ∗ stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
            (dpPollSpecStateBudget K stk')).post
            y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
            (dpPollSpecStateBudget K stk')).onPanic
            y s0 sf ∗ R)) := by
  dsimp only
  let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
  let sp := s0.sp - 0xcd0#64
  let st_p1 := M.stepEvents evs_p1 y.st
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  have hloadS : loadRec Scope y.g.F y.g.peer.val = .ok (some r) :=
    loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload_rel
  have hr_eq : r = ⟨some s_old⟩ := by cases r; simpa using hcur
  have hs_old : scopeIn ⟨some s_old⟩ := hr_eq ▸ hScopeOver.1
  have hver_old : s_old.state.sessionVersion = 4#32 := hScopeOver.2 s_old hcur
  have hprevOK : OverPrevEncOK (encSession (clearPending s_old)) :=
    overPrevEncOK_clearPending_of_scopeIn_placed hs_old hver_old
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  have hs1_files : s1.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed hh hsteps01 htr1).trans hf0
  have hfiles1 : FsAt (fun f => f = y.g.F) True prog s1 :=
    cliFsAt_of_files_eq_placed hh trivial rfl hs1_files
  let Fr_tail : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  have hpre_split :
      stageP2PostP1At (A.atState lim st_p1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗ lsLogOff ∗ stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      (stageP2PostP1At (A.atState lim st_p1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗ lsLogOff ∗ stackAt sp (dpClosSubStack B)) ∗ Fr_tail := by
    dsimp only [Fr_tail]
    sep_frame
  refine sepWPp_conseq_pre hpre_split
    (overSepWPp_pollGoal_frame_placed (mmpl := mmpl) (g := gh) (W := W) A lim DecPkEnv B S stk' y ?_)
  refine hP2O S Scope y st_p1 r s_old StoresGhost.opened s0 s1 sp rngPtr v_a8 v_b8 v_d0 _ _
    hh hFits2 hcoins hd3False hsub hfPeer hloadS hcur hnot_match htrusted rfl
    hfiles1 hfroz1 (htr1 ▸ List.prefix_refl _)
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
          lsLogOff ∗ A.pool lim (M.stepEvents (evs_p1 ++ evs2) y.st) sf ∗
          anyHeap ∗ dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by dsimp only [Fr_tail]; sep_frame) hm1
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_over_of_reject StoresGhost.opened hS hne_p hne_s hmodel
    have hpost_goal := overExit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y
      s0 sf (evs_p1 ++ evs2) StoresGhost.opened (.error err) anyHeap (hEnvErr2 evs2 hevs2)
      (hh.fs prog 518) hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm2
  · intro s2 evs_p2 m i k kp reg dk recG prevCap prevPtr whisperMsgPtr whisperG preKeyMsgRem
      hevs2 hcap_nz hpk hmsg_i hi hk hkp hreg hacc hex hmsg_fold hsteps12 htr2 hpc2 hrun2
      hs2_sp hsp_align2 _ _ hx29_2 hvregs2 hfroz2
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st0 := pathAInitState ⟨W.C, W.Q⟩ meE k m dk
    let st_p2 := M.stepEvents (evs_p1 ++ evs_p2) y.st
    have hst_p2_eq : M.stepEvents evs_p2 st_p1 = st_p2 :=
      (M.stepEvents_append evs_p1 evs_p2 y.st).symm
    have hd0 : DecPkOk₀ ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val
        (pmOfE m y.g.msg.message) :=
      decPkOk0_of_d3_pkToE hd3False hpk
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
      exact decPkOverDef_pathCOver_panic X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hd0 hloadS hcur htrusted hnot_match hpk hmsg_i hi hk hkp hreg hacc hver hpan_s5
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
         storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ⊢
        LsTokenInit ∗
         overGenP3Pre_placed A lim st_p2 s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
           whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG st0 y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (encSession (clearPending s_old)) 0#8 ∗
         overScratch s2.sp ∗ F_p3 := by
      have heq1 := congrArg (fun st =>
        overGenP3Pre_placed A lim st s2.sp (s2.readReg64 .x29) y.fut
          y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
          (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
          recG st0 y.g.peer y.g.me whisperG y.g.msg.message s2) hst_p2_eq
      have heq2 := (stageP3StackFrameAt_eq_over sp (y.g.msgA + 0xc8#64) y.g.peerA).trans
        (congrArg (stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗ overScratch ·)
          hs2_sp.symm)
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono (Entails.of_eq heq1)
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (Entails.of_eq heq2)))))) ?_
      dsimp only [F_p3, sp]
      sep_frame
    refine sepWPp_conseq_pre hpre_p3
      (overSepWPp_genP3_to_tailQpan_placed (mmpl := mmpl) (g := gh) (W := W)
        A lim DecPkEnv B S stk' y hpan_model ?_)
    refine h7pb_sepWPp_peek_mem fun hm_s2 => ?_
    have hsgv0 : SessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ meE k m dk) :=
      h7pb_sessionGhostValid_of_overGenP3Pre hex hm_s2
    refine hP3O st_p2 hG hh.alloc
      (cliChainClone3_placed_ok mmpl gh W hh)
      (cliSenderChainClone3_placed_ok mmpl gh W hh)
      hTry
      (cliDropSessionStructure4_placed_ok_at mmpl gh W hh (callerProg := prog) (i := 518))
      s0 s2 y.fut y.cx y.out 8#64 prevCap prevPtr y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8
      (encSession (clearPending s_old)) y.g.coins
      recG st0 y.g.peer y.g.me whisperG y.g.msg.message F_p3 _
      (hFits3 evs_p2 m i k kp reg dk recG whisperG hevs2 hpk hmsg_i hi hk hkp hreg hacc hex hsgv0)
      (by decide) hcap_nz hprevOK hver4
      (Or.inr (distinctSid_of_decPkOk hd0)) hSeeds hRC hPqLt
      hfroz2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot)
      (x29_eq_sp_add_c70_over_d3_placed hx29_2 hs2_sp) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' evs_p3 pt ptCap ptPtr s' P_s' hver hcl hdec_rel hevs3 hok
        hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
        hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s'
      have hstep_p3_eq : M.stepEvents evs_p3 st_p2 = M.stepEvents (evs_p1 ++ evs_p2 ++ evs_p3) y.st :=
        (M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st).symm
      rw [hstep_p3_eq] at hent_s'
      have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d3 A.repAlloc σ
        y.g.stores hsub hfPeer hd3False pid m.spkId m.kpkId y.g.msg.baseKey
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
        (closure_pathCOver_p4_d3_cont_at_b_placedBudget A lim DecPkEnv B hP4O S hh hS stk' hneed
          hstk63 y (evs_p1 ++ evs_p2 ++ evs_p3)
          hfPeer hScopeOver.1 hd3False hloadS hcur htrusted hnot_match m i k kp reg dk recG G₁ G'
          rngPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem P_s' R pt s0 s2 s'
          (fun hsgv' =>
            hFits4 evs_p2 evs_p3 m i k kp reg dk recG G₁ G' pt whisperG
              hevs2 hpk hmsg_i hi hk hkp hreg hacc hex hsgv0 hcl hdec_rel hevs3 hok hsgv')
          (fun hsgv' evs4 hevs4 =>
            hEnv4 evs_p2 evs_p3 evs4 m i k kp reg dk recG G₁ G' pt whisperG
              hevs2 hpk hmsg_i hi hk hkp hreg hacc hex hsgv0 hcl hdec_rel hevs3 hok hsgv' hevs4)
          hpk hmsg_i hi hk hkp hreg hacc hex hmsg_fold hs2_files htr20 hs2_sp hsp_align2 hsp_sub
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
            (coinsAfterPlaced y.g.coinsP y.g.coins
              (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins)) ∗
          overScratch s2.sp ∗ anyHeap := by
        refine Entails.trans hent_f ?_
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right
            (Entails.trans (Entails.of_eq (sepConj_emp (overScratch s2.sp)).symm)
              (sepConj_mono_right (entails_anyHeap emp))))))
      exact stageP3_exit_pathCOver_to_pollPost_d3_placedBudget A lim DecPkEnv B S hh hS stk' hneed
        hstk63 y s0 s2 sf (evs_p1 ++ evs_p2 ++ evs_p3) rngPtr whisperMsgPtr whisperG preKeyMsgRem
        (coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins))
        P_f R m.opkId m.kpkId m.spkId e
        (hEnvErr3 evs_p2 evs_p3 m i k kp reg dk recG G₁ whisperG
          hevs2 hpk hmsg_i hi hk hkp hreg hacc hex hsgv0 hcl hevs3)
        hs2_sp hsp_sub hmsg_fold
        (decPkOverDef_pathCOver_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hd0 hloadS hcur htrusted hnot_match hpk hmsg_i hi hk hkp hreg hacc hver herr hne_p)
        hent_any hsf_sp htr_f hcs_f hvregs_f
    · intro evs_p3 sf P_f hver_ne hevs3 hent_f hsf_sp htr_f hcs_f hvregs_f _hro_f
      have hstep_p3_eq : M.stepEvents evs_p3 st_p2 = M.stepEvents (evs_p1 ++ evs_p2 ++ evs_p3) y.st :=
        (M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st).symm
      rw [hstep_p3_eq] at hent_f
      exact stageP3_exit_pathCOver_to_pollPost_d3_placedBudget A lim DecPkEnv B S hh hS stk' hneed
        hstk63 y s0 s2 sf (evs_p1 ++ evs_p2 ++ evs_p3) rngPtr whisperMsgPtr whisperG preKeyMsgRem
        (coinsAtPlaced y.g.coinsP y.g.coins) P_f R m.opkId m.kpkId m.spkId
        (.invalidMessage .preKey .decryptionFailed)
        (hEnvVerNe3 evs_p2 evs_p3 m i k kp reg dk recG
          hevs2 hpk hmsg_i hi hk hkp hreg hacc hex hsgv0 hevs3)
        hs2_sp hsp_sub hmsg_fold
        (decPkOverDef_pathCOver_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg
          y.g.coins hloadS hcur htrusted hnot_match hpk hmsg_i hi hk hkp hreg hacc hver_ne)
        hent_f hsf_sp htr_f hcs_f hvregs_f

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPathCPlacedBudgetFd
