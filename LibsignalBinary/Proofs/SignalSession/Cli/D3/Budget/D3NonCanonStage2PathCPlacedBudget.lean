/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidOverAuxPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Stage P2 Overwrite-Path (`Path C`) Instantiation for Non-Canonical Wire Encodings

Defines `StageP2PathCOverErrD3Placed` and `StageP2PathCOverQpanCliD3PlacedBudgetStmt` (and their
`LibsignalFrozen` variants) and proves `stageP2PathCOverQpan_cli_d3_placed_of_seams` for arbitrary
`pm : PreKeySignalMessage` with `pkToE? pm = some m` on non-matching sessions.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathCPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSession (PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (ApiError Session SessionRecord)
open CryptoVerification (
  LibsignalFrozen LibsignalFullPlacement LibsignalPlacement lsProg_75 lsmpl lsρ
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  SessionExtraRel coroOpkIdAtP4 hdrOpkIdBv? mkP2AcceptKeysInput p1LoadedRecordAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  clearPending stageP3Sub5ExtraPrePrev1
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2 (clearPendingGhost)
open CryptoVerification.E2E (
  PreKeyMessageFields ResponderPreKeySecrets UnreachedPqxdhPrimitives acceptInput keyPairOf
  modelPrims toU8 vecU8
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput bytesToBv8 ofSignalPqxdhAcceptKeysInput ofSignalPqxdhDRKey
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys acceptKeys_ofSignalPqxdhPrimitives)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  bytesToBv8_vecU8 ofSignalPqxdhPrimitives vecU8_length
)
open CryptoVerification.E2E.Pqxdh.ResponderStore (clampBv8List_length)
open CryptoVerification.E2E.Record (encSession)
open CryptoVerification.E2E.Record.Serialization (CanonSession encSessionMem)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsAt FsFiles LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost preKeyMsgAt)
open CryptoVerification.LibsignalTripleRatchet (rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost protocolAddressAt signalMessageAt
)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (
  CliGhostHooks StoresGhost cliGhostExterns cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym
  cliSignedPreKeyVtSym
)
open CryptoVerification.SignalSession.Cli.KitInst (
  cliKpk_getRel_error_iff cliPk_getRel_error_iff cliSpk_getRel_error_iff
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem decResAt)
open CryptoVerification.SignalSession.Cli.RunProofs (dpFutDoneAt pkStoreKeys pkToE? pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0 (SessMatchesPm)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit StageP1PostRegs cliKitStk cliModelPrims_structural cliPollIdKitPlaced
  cliPollKpkKitPlaced cliPollKpk_vtablesPlacedOk cliPollPkKitPlaced cliPollPk_vtablesPlacedOk
  cliPollSelfKitPlaced cliPollSelf_kpRel_err_placed cliPollSelf_kpRel_ok_placed
  cliPollSelf_regIdRel_err_placed cliPollSelf_regIdRel_ok_placed cliPollSelf_vtablesPlacedOk
  cliPollSpkKitPlaced cliPollSpk_vtablesPlacedOk distinctSid_of_decPkOk₀ dpClosSubStack
  dpPollEntryPlaced dpPollProgPlaced entails_sepConj_anyHeap hdrOpkIdBv?_mkPathAHdr mkPathAHdr
  p2Over_cliPollKpk_getEvs_placed p2Over_cliPollPk_getEvs_placed p2Over_cliPollPk_opkOkEvs_placed
  p2Over_cliPollPk_opkOkUpdate_placed p2Over_cliPollSelf_kpEvs_placed
  p2Over_cliPollSelf_regIdEvs_placed p2Over_cliPollSpk_getEvs_placed pathAInitSession
  pathAInitState pkStoreKeys_eq_none_of_kpk_err pkStoreKeys_eq_none_of_opk_err
  pkStoreKeys_eq_none_of_spk_err pmOfE_fields pqxdhAcceptErr_entails_decResAt_anyHeap_ext
  preKeyMsgAt_eq_base_idKey_sep preKeyMsgRemBaseIdKeyAt sepWPp_conseq_pre sp_sub_576_ne_zero
  stageP2PostP1At stageP3CoroFrameAt stageP3StackFrameAt x29_eq_sp0_sub_60 x29_eq_sp_add_c70
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (FilesOkPeer scopeIn scopeKit)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  InitializeBobV1Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget (
  P2Sub1To4Arm3Env P2Sub1To4OkEnv P2Sub4OkEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv initializeBobSession_err_owned_4k_placed_ok_on_stageP1
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget (
  P2Sub6Env P2V1Arm4Env P2V1Arm5EnvOfAcceptErr P2V1Arm6EnvOfBob
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget (
  PromoteOverAllocMidEnv PromoteOverEnv p2PromoteOverAtSpecWithEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget (
  PromoteMatchingMissAtPlacedProp PromoteMatchingMissGenPlacedProp PromoteOverAtPlacedWithEnvProp
  PromoteOverGenPlacedWithEnvProp promoteMatchingMissAt_placed_of_gen promoteOverAt_placed_of_gen
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget (
  P2OverSub1To4Arm3Env P2OverSub1To4OkEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget (
  P2OverSub6EnvOf P2OverV1Arm4Env P2OverV1Arm5EnvOfAcceptErr P2OverV1Arm6EnvOfBob
  P2OverV1OkEnvOfBobAndProm stageP2_over_v1_kits_ext_placed_ofEnv
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (pqxdhAcceptOptFieldsPlacedSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget (AcceptSuccessEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget (
  pqxdhAcceptErrOwnedPlacedSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk PreKeyStoreKitPlacedOk
  SignedPreKeyStoreKitPlacedOk
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  DecPkOkD3 StageP2PathCOverModelRejD3Placed pm_fields_of_pkToE
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PollPlacedBudget (
  p2ErrFrame_fold_pathA_d3_placed_rep p2OverOkPost_fold_pathCOver_d3_placed
  p2Over_not_sessMatchesMsg_d3 pathAInnerFrameD3Placed stageP2_entry_unpack_pathCOver_d3_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (
  overGenP3Pre_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  StageP2OverEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlacedBudget (
  encSessionMem_clearPending_eq encSessionMem_clearPending_lt_32 p2Over_serBytes_len
  stageP2OverV1CallStack4K_le_subStack_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  CliPollStageP2Envs P2OverPathCErrEnvOf P2OverPathCOkEnvOf PromoteOverCanonSessEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux (
  PromoteOverCanonSessEnvLocal cliStageP2ClosureHooksPlaced cliStageP2PureCalleesPlaced4K
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
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeams)

export LibsignalBinary.Proofs.SignalSession.Cli.D3 (StageP2PathCOverModelRejD3Placed)

/-! ## 1. Budget-Threaded Stage P2 Path C (`Over`) Error Postcondition & Contract Statement -/

/-- Budget-threaded exit postcondition of all 6 Stage P2 store-error and PQXDH-rejection arms on
Path C (`Over`) for arbitrary `pm.serialized` under `[LibsignalPlacement]`. -/
def StageP2PathCOverErrD3Placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (P2OverErrEnv : DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (r : SessionRecord (List (BitVec 8)))
    (s1 sf : State) (sp : BitVec 64) (Pf : SepProp) : Prop :=
  ∃ (err : ApiError AddrVal Unit) (evs : List AllocEvent),
    P2OverErrEnv y.g r evs ∧
    err ≠ .panic ∧
    err ≠ .store () ∧
    sf.trace = s1.trace ∧
    StageP2PathCOverModelRejD3Placed X W y.g.F y.g.msg ∧
    (Pf ⊢
      dpFutDoneAt y.fut ∗
      memRegion sp 3280 ∗
      decResAt A.repAlloc y.out (.error err) ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      lsLogOff ∗
      A.pool lim (M.stepEvents evs st_b) sf ∗
      stackAt sp (dpClosSubStack B) ∗
      anyHeap)

/-- Budget-threaded Placed Stage P2 Path C (`Over`) CPS contract statement at
`dpPollEntryPlaced + 0x0868#64` for non-canonical D3 `PreKeySignalMessage`s (`DecPkOkD3`). -/
def StageP2PathCOverQpanCliD3PlacedBudgetStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets) (S : RunSem)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ)
    (g1 : StoresGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    PromoteMatchingMissGenPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    PromoteOverGenPlacedWithEnvProp M A lim PromEnv (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOkD3 ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → scopeIn r') →
    FilesOkPeer Scope y.g.F y.g.peer.val →
    r.currentSession = some sess →
    scopeIn r →
    ¬ SessMatchesPm sess y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 →
    LibsignalCodeRoLoaded lsmpl s1.mem →
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
      StageP2PathCOverErrD3Placed A lim st_b P2OverErrEnv X W B S y r s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State) (evs_p2 : List AllocEvent)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (G_bob : SessionGhost)
      (prevCap' prevPtr' : BitVec 64)
      (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2OverOkEnv y.g r evs_p2 →
      prevCap' ≠ 0#64 →
      pkToE? y.g.msg = some m →
      y.g.msg.message = i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel G_bob
        (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
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
      LibsignalCodeRoLoaded lsmpl s2.mem →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_b) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           G_bob (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
           (encSession (clearPending sess)) 0#8 ∗
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
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
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

/-! ## 2. Stage P2 Path C (`Over`) V1 CPS Instantiation (`stageP2PathCOverQpan_cli_d3_placed_of_seams`) -/

private theorem promoteOverEnv_eq_canon {recG : SessionGhost} {sess : Session (List (BitVec 8))}
    (hcanon : CanonSession recG sess) :
    PromoteOverEnv recG sess = PromoteOverCanonSessEnvLocal sess := by
  unfold PromoteOverEnv PromoteOverAllocMidEnv PromoteOverCanonSessEnvLocal
  rw [encSessionMem_clearPending_eq hcanon]; rfl

private theorem promoteOverAtPlacedWithEnv_of_eq [LibsignalPlacement]
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

private theorem p2Sub1To4_opkWord_eq
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

private theorem seqEnv_or_right {E1 A B : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv E1 (fun e => A e ∨ B e) evs) :
    SeqEnv E1 A evs ∨ SeqEnv E1 B evs := by
  rcases h with h1 | ⟨e1, e2, heq, h1, hA | hB⟩
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr ⟨e1, e2, heq, h1, hA⟩)
  · exact Or.inr (Or.inr ⟨e1, e2, heq, h1, hB⟩)

private theorem p2OverSub6_or {Bob : List AllocEvent → Prop} {regBox : Nat}
    {regPoll PromTail : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv Bob (P2OverSub6EnvOf regBox regPoll PromTail) evs) :
    SeqEnv Bob (P2Sub6Env regBox regPoll) evs ∨
      SeqEnv Bob (SeqEnv (BoxAllocEnv regBox) (SeqEnv regPoll PromTail)) evs := by
  rcases h with hBob | ⟨eBob, eRest, heq1, hBob, hSub6⟩
  · exact Or.inl (Or.inl hBob)
  · unfold P2OverSub6EnvOf at hSub6
    rcases hSub6 with hBox | ⟨eBox, e2, heq2, hBox, h2⟩
    · exact Or.inl (Or.inr ⟨eBob, eRest, heq1, hBob, Or.inl hBox⟩)
    · rcases seqEnv_or_right h2 with hFree | hProm
      · exact Or.inl (Or.inr ⟨eBob, eRest, heq1, hBob, Or.inr ⟨eBox, e2, heq2, hBox, hFree⟩⟩)
      · exact Or.inr (Or.inr ⟨eBob, eRest, heq1, hBob, Or.inr ⟨eBox, e2, heq2, hBox, hProm⟩⟩)

private theorem fitsEnv_step3 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E1 E2 E3 E4 : List AllocEvent → Prop} {e1 e2 e3 : List AllocEvent}
    (h : FitsEnv M lim st (SeqEnv E1 (SeqEnv E2 (SeqEnv E3 E4))))
    (h1 : E1 e1) (h2 : E2 e2) (h3 : E3 e3) :
    FitsEnv M lim (M.stepEvents (e1 ++ e2 ++ e3) st) E4 := by
  rw [M.stepEvents_append, M.stepEvents_append]
  exact ((h.seq_right h1).seq_right h2).seq_right h3

set_option maxHeartbeats 1600000 in
/-- Budget-threaded Path-C overwrite Stage P2 instantiation
(`StageP2PathCOverQpanCliD3PlacedBudgetStmt`) under `[LibsignalPlacement]` for arbitrary `pm` with
`pkToE? pm = some m`. -/
theorem stageP2PathCOverQpan_cli_d3_placed_of_seams [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {AcceptErrEnv : UnreachedPqxdhPrimitives → CliHooks → AcceptKeysInput → List AllocEvent → Prop}
    {kitEnvs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ X W B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B (InitializeBobV1Env W.C.F)
        (AcceptErrEnv X W) (kitEnvs B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X W B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B (InitializeBobV1Env W.C.F)
        PromoteOverCanonSessEnv (kitEnvs B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X W B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B (InitializeBobV1Env W.C.F)
            (AcceptErrEnv X W) (kitEnvs B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B (InitializeBobV1Env W.C.F)
            PromoteOverCanonSessEnv (kitEnvs B))
          g r))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hSpqr : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      SpqrV1PlacedSeams M A lim mmpl gh W)
    (h_accept_ok : ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement)
      (gh : CliGhostHooks) (W : CliHooks),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim AcceptSuccessEnv))
    (h_accept_err : ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement)
      (gh : CliGhostHooks) (W : CliHooks),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim (AcceptErrEnv X W)))
    (h_accept_err_owned : ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement)
      (gh : CliGhostHooks) (W : CliHooks),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptErrOwnedPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim (AcceptErrEnv X W)))
    (hSelfKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).selfEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).spkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).kpkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).pkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PathCOverQpanCliD3PlacedBudgetStmt A lim PromoteOverEnv P2OverErrEnv P2OverOkEnv := by
  intro X mmpl gh W B S DecPkEnv Scope y st_b g1 r sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hPromMiss hPromOver hh0 hfits hcoins hdecOk hScope hFok hcur hIn hnotMatch _htrust hg1
    hfs1 hCode1 htr01 hsp1 hsp0 hsub hpc1 hrun1 halign1 hregs1 herr hok
  subst hg1
  have hh :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    ⟨hh0.alloc, hh0.allocFs, hh0.panics, hh0.memcpyRO, hh0.bcmp, hh0.fs, hh0.utf8, hh0.memrchr,
      hh0.codecHooks, hh0.allocZeroed, hh0.stringClone, hh0.formatInner⟩
  rcases hregs1 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, _, hx29, hvregs1⟩
  obtain ⟨m, _, hi, hpkToE, hdec0⟩ := hdecOk
  let i : SignalMessage := y.g.msg.message
  have hmsg_i : y.g.msg.message = i := rfl
  have hbk_eq : y.g.msg.baseKey = (pmOfE m i).baseKey :=
    (pm_fields_of_pkToE hpkToE hmsg_i).2.2.2.2.1.trans (pmOfE_fields m i).2.2.2.2.1.symm
  have hfp_reg : s1.readReg64 .x29 = sp + 0xc70#64 := x29_eq_sp_add_c70 hsp0 hx29
  have hsp_align : (sp &&& 15#64 == 0#64) = true := by rw [← hsp1]; exact halign1
  have hfits0 := hFitsSplit X W B st_b y.g r hfits
  refine sepWPp_with_steps ?_
  refine sepWPp_conseq_pre
    (D3NonCanonStage2PollPlacedBudget.stageP2_entry_unpack_pathCOver_d3_placed (st_b := st_b) (s1 := s1)
      y r sess m i s0 sp (sp + 0xc70#64) rngPtr v_a8 v_b8 v_d0 hcur hpkToE hmsg_i rfl
      hdec0 hFok hScope) ?_
  refine SepWPp.exists_elim fun g => SepWPp.exists_elim fun recG =>
    SepWPp.exists_elim fun w => SepWPp.pure_left fun ⟨_hkit, _hgcur, hcanon, hctBuf_nz, hopkWord⟩ => ?_
  have hPromMissAt : PromoteMatchingMissAtPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W))
      y.fut g recG sess 4#8 (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk) :=
    promoteMatchingMissAt_placed_of_gen hPromMiss y.fut g recG sess 4#8
      (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk)
      (D3NonCanonStage2PollPlacedBudget.p2Over_not_sessMatchesMsg_d3 sess y.g.msg m i hpkToE hmsg_i hnotMatch)
      (p2Over_serBytes_len m)
  have hPromOverAt0 := promoteOverAt_placed_of_gen hPromOver y.fut g recG sess
    (encSessionMem_clearPending_lt_32 hIn hcur hcanon)
  have hPromOverAt : PromoteOverAtPlacedWithEnvProp M A lim
      (fun _ s => PromoteOverCanonSessEnv s) (cliGhostExterns gh (cliExternsPlaced mmpl W)) y.fut g recG sess :=
    promoteOverAtPlacedWithEnv_of_eq (promoteOverEnv_eq_canon hcanon) hPromOverAt0
  let opkWord0 : BitVec 32 := m.opkId.getD 0#32
  have ⟨hArm3_eq, hOk14_eq⟩ := p2Sub1To4_opkWord_eq
    (spkBox := (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B)).getBoxSize)
    (spkPoll := (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).spkEnv.getPollEnv
      StoresGhost.opened.signed m.spkId)
    (kpkBox := (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).getBoxSize)
    (kpkPoll := (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).kpkEnv.getPollEnv
      StoresGhost.opened.kyber m.kpkId)
    (pkBox1 := (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B)).getBoxSize)
    (pkBox2 := (cliPollPkKitPlaced A.repAlloc y.g.F opkWord0 (cliKitStk B)).getBoxSize)
    (pkPoll1 := (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey).pkEnv.getPollEnv
      StoresGhost.opened.oneTime)
    (pkPoll2 := (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).pkEnv.getPollEnv
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
  exact stageP2_over_v1_kits_ext_placed_ofEnv (M := M)
    (P := ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) (A := A) (lim := lim) (F := W.C.F)
    (BobV1Env := InitializeBobV1Env W.C.F) (AcceptErrEnv := AcceptErrEnv X W)
    (PromEnv := fun _ s => PromoteOverCanonSessEnv s) (st := st_b)
    (Qp := fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Qpan sf Pf)
    (cliGhostExterns gh (cliExternsPlaced mmpl W)) (cliModelPrims_structural X W)
    (cliStageP2ClosureHooksPlaced mmpl gh W hh)
    (cliStageP2PureCalleesPlaced4K X mmpl gh W hh (hSpqr mmpl gh W)
      (h_accept_ok X mmpl gh W) (h_accept_err X mmpl gh W))
    (initializeBobSession_err_owned_4k_placed_ok_on_stageP1 (h_accept_err_owned X mmpl gh W))
    (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
    (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
    (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).selfEnv
    (cliPollSelf_vtablesPlacedOk y.g.F y.g.peer (cliKitStk B) hDropNz)
    (hSelfKit mmpl gh W B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
    (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
    (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).spkEnv
    (cliPollSpk_vtablesPlacedOk y.g.F m.spkId (cliKitStk B) hDropNz)
    (hSpkKit mmpl gh W B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
    (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
    (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).kpkEnv
    (cliPollKpk_vtablesPlacedOk y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) hDropNz)
    (hKpkKit mmpl gh W B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
    (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
    (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey).pkEnv
    (cliPollPk_vtablesPlacedOk y.g.F w.opkWord (cliKitStk B) hDropNz)
    (hPkKit mmpl gh W B y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey hh)
    (dpClosSubStack B) (stageP2OverV1CallStack4K_le_subStack_placed (A := A.repAlloc)
      y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B)
    s0 s1 (D3NonCanonStage2PollPlacedBudget.pathAInnerFrameD3Placed A.repAlloc y i rngPtr sp)
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
          ((kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).spkEnv.getPollEnv
            StoresGhost.opened.signed m.spkId)
          (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).getBoxSize
          ((kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).kpkEnv.getPollEnv
            StoresGhost.opened.kyber m.kpkId)
          (cliPollPkKitPlaced A.repAlloc y.g.F opkWord0 (cliKitStk B)).getBoxSize
          ((kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).pkEnv.getPollEnv
            StoresGhost.opened.oneTime)
          (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpBoxSize
          (hdrOpkIdBv? (mkPathAHdr m))
          ((kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).selfEnv.kpPollEnv
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
      refine fitsEnv_step3 (hfits0.mono fun evs hseq => ?_)
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
          · rcases p2OverSub6_or hr3 with hArm6 | hOk
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
      refine fitsEnv_step3 (hfits0.mono fun evs h5 => ?_) hevs14 hevsKp (FreeOnlyEvs.singleton 8 _)
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
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv X W B y.g r evs (by
        unfold P2OverPathCErrEnvOf; rw [hpkToE]; exact Or.inl hevs)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F m.spkId (cliKitStk B) y.out e err0))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hmsg_i, Or.inl (Or.inl hspkNone)⟩, hpost⟩)
    (fun _spkRec e sf Pf evs _ _ hkpkErr hevs hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          List.append_nil, List.append_nil] at htr_f
      have hkpkNone : pkStoreKeys y.g.F m = none := pkStoreKeys_eq_none_of_kpk_err
        ((cliKpk_getRel_error_iff (A := A.repAlloc) cliIo.rd y.g.F cliWrOk m.kpkId
          StoresGhost.opened.kyber m.kpkId).mp ⟨e, hkpkErr⟩)
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv X W B y.g r evs (by
        unfold P2OverPathCErrEnvOf; rw [hpkToE]; exact Or.inr (Or.inl hevs))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) y.out e err0))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
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
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv X W B y.g r evs (by
        unfold P2OverPathCErrEnvOf; rw [hpkToE]; exact Or.inr (Or.inr (Or.inl hevs)))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F w.opkWord (cliKitStk B) y.out e err0))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
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
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv X W B y.g r evs (by
        unfold P2OverPathCErrEnvOf; rw [hpkToE]; exact Or.inr (Or.inr (Or.inr (Or.inl hevs))))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (Entails.trans
          (cliPollSelf_kpErr_entails_decResAt_err_placed A.repAlloc
            y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
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
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv X W B y.g r evs (by
        unfold P2OverPathCErrEnvOf; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hevs)))))
      have hPf' := Entails.trans hPf (by rw [← sepConj_assoc]; exact Entails.refl _)
      have hpost := Entails.trans hPf' (Entails.trans
        (sepConj_mono_left (pqxdhAcceptErr_entails_decResAt_anyHeap_ext A.repAlloc
          y.out errTag w2 w3 w4 w5 w6 err0))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
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
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv X W B y.g r evs (by
        unfold P2OverPathCErrEnvOf; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        rw [haccSome]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hevs)))))
      have hregNone := cliPollSelf_regIdRel_err_placed hregErr
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (Entails.trans
          (cliPollSelf_regIdErr_entails_decResAt_err_placed A.repAlloc
            y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hmsg_i, Or.inl (Or.inr (Or.inr hregNone))⟩, hpost⟩)
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey localRegId G_bob s2 evs
        hspkRel _ hspkPub_len hspkPriv_len hspkPubEq hspkPrivEq
        hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccSome hregRel hevs
        hG_pend hG_kyb hG_alice hG_regs
        hSteps12 _ hpc2 hrun2 hsp2 htr2
        _ _ _ _ hx19_2 _ _ _ _ _ _ hx27_2 _ hx29_2 hvregs2 hCode2 => by
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
      have hevs' : P2OverOkEnv y.g r evs := hOkEnv X W B y.g r evs (by
        unfold P2OverPathCOkEnvOf; rw [hpkToE, hcur]; dsimp only; rw [hk, hkpOk]; dsimp only
        rw [haccSome0]; exact hevs)
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
        (D3NonCanonStage2PollPlacedBudget.p2OverOkPost_fold_pathCOver_d3_placed (st_b := M.stepEvents evs st_b)
          y m i w s0 s2 sp (sp + 0xc70#64) rngPtr
          recG G_bob sess (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m dk0)
          hcanon hpkToE hmsg_i hcoins hsub rfl hopkWord hsp2 hx19_2 hx27_2) ?_)
      refine SepWPp.exists_elim fun prevCap' => SepWPp.exists_elim fun prevPtr' =>
        SepWPp.pure_left fun hcap_ne => ?_
      exact hok s2 evs m i k kp localRegId dk0 G_bob prevCap' prevPtr' y.g.msgA y.g.msgG.msg
        (preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
        hevs' hcap_ne hpkToE hmsg_i hi hk hkpOk hregOk haccModel hextra hmsg_reasm
        hSteps12 htr2 hpc2 hrun2 hsp2 halign2 hx19_2 hx27_2 hx29_sp0 hvregs2 hCode2)

/-! ## 3. `[LibsignalFullPlacement]` / `LibsignalFrozen` Twins -/

/-- `LibsignalFrozen`-guarded Stage P2 Path C (`Over`) CPS contract statement at
`dpPollEntryPlaced + 0x0868#64` for non-canonical D3 `PreKeySignalMessage`s (`DecPkOkD3`). -/
def StageP2PathCOverQpanCliD3FrozenPlacedBudgetStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets) (S : RunSem)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ)
    (g1 : StoresGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    PromoteMatchingMissGenPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    PromoteOverGenPlacedWithEnvProp M A lim PromEnv (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOkD3 ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → scopeIn r') →
    FilesOkPeer Scope y.g.F y.g.peer.val →
    r.currentSession = some sess →
    scopeIn r →
    ¬ SessMatchesPm sess y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 →
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
      StageP2PathCOverErrD3Placed A lim st_b P2OverErrEnv X W B S y r s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State) (evs_p2 : List AllocEvent)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (G_bob : SessionGhost)
      (prevCap' prevPtr' : BitVec 64)
      (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2OverOkEnv y.g r evs_p2 →
      prevCap' ≠ 0#64 →
      pkToE? y.g.msg = some m →
      y.g.msg.message = i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel G_bob
        (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
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
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_b) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           G_bob (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
           (encSession (clearPending sess)) 0#8 ∗
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
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
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

/-- Pointwise `(X, mmpl, gh, W)` `LibsignalFrozen`-guarded general-`Qpan` CPS Stage P2 contract
for Path C Over (`r.currentSession = some sess`, `¬ SessMatchesPm sess y.g.msg`, `DecPkOkD3`). -/
def StageP2PathCOverQpanCliD3FrozenAtPlacedBudgetStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks)
    (PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (B : RunBudgets) (S : RunSem)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ)
    (g1 : StoresGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    PromoteMatchingMissGenPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    PromoteOverGenPlacedWithEnvProp M A lim PromEnv (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOkD3 ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → scopeIn r') →
    FilesOkPeer Scope y.g.F y.g.peer.val →
    r.currentSession = some sess →
    scopeIn r →
    ¬ SessMatchesPm sess y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 →
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
      StageP2PathCOverErrD3Placed A lim st_b P2OverErrEnv X W B S y r s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State) (evs_p2 : List AllocEvent)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (G_bob : SessionGhost)
      (prevCap' prevPtr' : BitVec 64)
      (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2OverOkEnv y.g r evs_p2 →
      prevCap' ≠ 0#64 →
      pkToE? y.g.msg = some m →
      y.g.msg.message = i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel G_bob
        (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
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
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_b) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           G_bob (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
           (encSession (clearPending sess)) 0#8 ∗
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
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
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

private theorem hookSat_noAllocShimBudget_of_withVmPreserved
    {H : String → Option (State → State)}
    (hsat : Arm64.HookSat H CryptoVerification.lsRustNoAllocShimSym
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec)) :
    Arm64.HookSat H CryptoVerification.lsRustNoAllocShimSym
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimBudgetSpec := by
  rcases hsat with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

private theorem hookSat_framelessMemcpy_of_vm
    {H : CryptoVerification.LibsignalHooks}
    (h : Arm64.HookSat H "memcpy"
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    Arm64.HookSat H CryptoVerification.lsMemcpySym
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpySpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    rcases x with ⟨dst, src, bs⟩
    dsimp only [LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpySpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact ⟨hkf, hsym, Or.inr hrest⟩

private theorem hookSat_sessionMemcpyRegionBudget_of_codec
    {H : CryptoVerification.LibsignalHooks}
    (h : Arm64.HookSat H "memcpy"
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    Arm64.HookSat H CryptoVerification.lsMemcpySym
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  rcases hok (dst, src, bs) R s0 hrun hpre hsp with ⟨hkeep, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · exact ⟨hkeep, hsym, Or.inl ⟨hret, hcc, hpost⟩⟩
  · exact ⟨hkeep, hsym, Or.inr hrest⟩

private theorem hookSat_sessionMemcpyBudget_of_codec
    {H : CryptoVerification.LibsignalHooks} (hookStack : Nat)
    (h : Arm64.HookSat H "memcpy"
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    Arm64.HookSat H CryptoVerification.lsMemcpySym
      (LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyBudgetSpec hookStack) := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  have hpre' : s0.mem ⊨ (LibsignalBinary.Heap.SpecBudget.withVmPreserved
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec).pre (dst, src, bs) s0 ∗
      (stackAt s0.sp hookStack ∗ R) := by
    dsimp only [LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec, libcMemcpySpec] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  rcases hok (dst, src, bs) (stackAt s0.sp hookStack ∗ R) s0 hrun hpre' hsp with
    ⟨hkeep, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩⟩
  · refine ⟨hkeep, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact False.elim (((satisfies_pure_sepConj ..).mp hp).1)
  · exact False.elim (((satisfies_pure_sepConj ..).mp he).1)
  · exact False.elim (((satisfies_pure_sepConj ..).mp ho).1)

private theorem cliStageP2BaseCalleesPlaced4K [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.StageP2BaseCalleesPlaced4K
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget.StageP2BaseCalleesPlaced4K.of_hooks
    (hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim)
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    (hookSat_sessionMemcpyBudget_of_codec CryptoVerification.RustHeap.allocHookStack hh.codecHooks.memcpy)
    (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget.isSameAccount_4k_placed_ok_on_stageP1
      ((CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_other gh
          (cliExternsPlaced mmpl W)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (CryptoVerification.SignalSession.Cli.RunGlue.cliExternsPlaced_row mmpl W
          (CryptoVerification.SignalSession.Cli.Slots.blackBox_row_placed mmpl W)))
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux.uuidTryParse_placed_vm_code_ok
        (cliGhostExterns gh (cliExternsPlaced mmpl W))))

private theorem cliInitBobV1FrozenOkPlaced4K [LibsignalFullPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W) :
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.InitializeBobV1FrozenOkPlaced4KOfEnv
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      A lim W.C.F
      (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget.initializeBobSession_ok_v1_of_env_4k_frozen_placed_on_stageP1
    (cliModelPrims_structural X W)
    (hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim)
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    (hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget.pqxdhAccept_opt_fields_responder_full_placed_ok_of_block
      (callerProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 75)
      (cliModelPrims_structural X W)
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliModelPrims_matchCrypto X W)
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget.cliResponderPqxdhHookContractsPlaced_of_hookSat
        X mmpl gh W hG hh.codecHooks.alloc hh.codecHooks.dealloc
        (hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim))
      (hookSat_framelessMemcpy_of_vm hh.codecHooks.memcpy))
    hSpqr.initialStateMemInv_lsProg75
    (fun _ _ _ => Iff.rfl)

private theorem cliInitBobErrOwnedFrozen4K_ok [LibsignalFullPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP1ProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 75)
      (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
        A lim
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))) := by
  have h75 :=
    LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget.initializeBobSession_err_owned_frozen_placed_ok_of_accept
      (LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptErrOwnedPlacedBudget.pqxdhAccept_err_owned_placed_ok_of_block
        (callerProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 75)
        (cliModelPrims_structural X W)
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget.ecPubKeyIsCanonical_responder_placed_ok_cl
          (cliModelPrims_structural X W)
          (CryptoVerification.SignalSession.Cli.Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
            (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget.cliExternsPlaced_toEdwards_budget_sat mmpl W X))
          (CryptoVerification.SignalSession.Cli.Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
            (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget.cliExternsPlaced_torsionFree_budget_sat mmpl W X)))
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget.cliPqxdhCalculateAgreement_placed_ok_of_hookSat
          X mmpl gh W hh.codecHooks.alloc hh.codecHooks.dealloc
          (hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim))
        (hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim)
        hh.codecHooks.alloc
        hh.codecHooks.dealloc
        (hookSat_framelessMemcpy_of_vm hh.codecHooks.memcpy))
  have hbase :=
    CryptoVerification.E2E.Pqxdh.ResponderCore.ls_subroutine_ok_withLsFrozen_of_block
      (callerProg := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP1ProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (calleeProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (i := 518) (j := 75) h75
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget.p2_errOwned_frozen_to_defs4K_placed ?_
  refine subroutine_ok_map hbase ?_
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun _ hpost => hpost⟩
  dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

set_option maxHeartbeats 1600000 in
/-- Pointwise `(X, mmpl, gh, W)` `[LibsignalFullPlacement]` Path-C overwrite Stage P2
instantiation (`StageP2PathCOverQpanCliD3FrozenAtPlacedBudgetStmt`), discharging block `79`
internally. -/
theorem stageP2PathCOverQpan_cli_d3_at_full_placed_of_seams [LibsignalFullPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks)
    {kitEnvs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (kitEnvs B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverCanonSessEnv (kitEnvs B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (kitEnvs B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverCanonSessEnv (kitEnvs B))
          g r))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.CliGhostAllocHooks M A lim gh)
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hSelfKit : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).selfEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).spkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).kpkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).pkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PathCOverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W PromoteOverEnv
      P2OverErrEnv P2OverOkEnv := by
  unfold StageP2PathCOverQpanCliD3FrozenAtPlacedBudgetStmt
  intro B S DecPkEnv Scope y st_b g1 r sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hPromMiss hPromOver hh0 hfits hcoins hdecOk hScope hFok hcur hIn hnotMatch _htrust hg1
    hfs1 hCode1 htr01 hsp1 hsp0 hsub hpc1 hrun1 halign1 hregs1 herr hok
  subst hg1
  have hh :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    ⟨hh0.alloc, hh0.allocFs, hh0.panics, hh0.memcpyRO, hh0.bcmp, hh0.fs, hh0.utf8, hh0.memrchr,
      hh0.codecHooks, hh0.allocZeroed, hh0.stringClone, hh0.formatInner⟩
  rcases hregs1 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, _, hx29, hvregs1⟩
  obtain ⟨m, _, hi, hpkToE, hdec0⟩ := hdecOk
  let i : SignalMessage := y.g.msg.message
  have hmsg_i : y.g.msg.message = i := rfl
  have hbk_eq : y.g.msg.baseKey = (pmOfE m i).baseKey :=
    (pm_fields_of_pkToE hpkToE hmsg_i).2.2.2.2.1.trans (pmOfE_fields m i).2.2.2.2.1.symm
  have hfp_reg : s1.readReg64 .x29 = sp + 0xc70#64 := x29_eq_sp_add_c70 hsp0 hx29
  have hsp_align : (sp &&& 15#64 == 0#64) = true := by rw [← hsp1]; exact halign1
  have hfits0 := hFitsSplit B st_b y.g r hfits
  refine sepWPp_with_steps ?_
  refine sepWPp_conseq_pre
    (D3NonCanonStage2PollPlacedBudget.stageP2_entry_unpack_pathCOver_d3_placed (st_b := st_b) (s1 := s1)
      y r sess m i s0 sp (sp + 0xc70#64) rngPtr v_a8 v_b8 v_d0 hcur hpkToE hmsg_i rfl
      hdec0 hFok hScope) ?_
  refine SepWPp.exists_elim fun g => SepWPp.exists_elim fun recG =>
    SepWPp.exists_elim fun w => SepWPp.pure_left fun ⟨_hkit, _hgcur, hcanon, hctBuf_nz, hopkWord⟩ => ?_
  have hPromMissAt : PromoteMatchingMissAtPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W))
      y.fut g recG sess 4#8 (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk) :=
    promoteMatchingMissAt_placed_of_gen hPromMiss y.fut g recG sess 4#8
      (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk)
      (D3NonCanonStage2PollPlacedBudget.p2Over_not_sessMatchesMsg_d3 sess y.g.msg m i hpkToE hmsg_i hnotMatch)
      (p2Over_serBytes_len m)
  have hPromOverAt0 := promoteOverAt_placed_of_gen hPromOver y.fut g recG sess
    (encSessionMem_clearPending_lt_32 hIn hcur hcanon)
  have hPromOverAt : PromoteOverAtPlacedWithEnvProp M A lim
      (fun _ s => PromoteOverCanonSessEnv s) (cliGhostExterns gh (cliExternsPlaced mmpl W)) y.fut g recG sess :=
    promoteOverAtPlacedWithEnv_of_eq (promoteOverEnv_eq_canon hcanon) hPromOverAt0
  let opkWord0 : BitVec 32 := m.opkId.getD 0#32
  have ⟨hArm3_eq, hOk14_eq⟩ := p2Sub1To4_opkWord_eq
    (spkBox := (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B)).getBoxSize)
    (spkPoll := (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).spkEnv.getPollEnv
      StoresGhost.opened.signed m.spkId)
    (kpkBox := (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).getBoxSize)
    (kpkPoll := (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).kpkEnv.getPollEnv
      StoresGhost.opened.kyber m.kpkId)
    (pkBox1 := (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B)).getBoxSize)
    (pkBox2 := (cliPollPkKitPlaced A.repAlloc y.g.F opkWord0 (cliKitStk B)).getBoxSize)
    (pkPoll1 := (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey).pkEnv.getPollEnv
      StoresGhost.opened.oneTime)
    (pkPoll2 := (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).pkEnv.getPollEnv
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
  have hStageP2 :
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget.stageP2OverV1KitsMemInvAtPlacedOfEnvProp
        (LibsignalFrozen lsmpl)
        P_m A lim W.C.F
        (InitializeBobV1OptFieldsEnv P_m W.C.F)
        (AcceptOptFieldsEnv P_m)
        (fun _ s => PromoteOverCanonSessEnv s)
        (cliGhostExterns gh (cliExternsPlaced mmpl W))
        (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
        (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).selfEnv
        (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
        (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).spkEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
        (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).kpkEnv
        (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
        (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey).pkEnv
        (dpClosSubStack B) :=
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget.stageP2_over_v1_kits_frozen_ext_defs_placed_ofEnv
      (M := M) (P := P_m) (A := A) (lim := lim) (F := W.C.F)
      (BobV1Env := InitializeBobV1OptFieldsEnv P_m W.C.F)
      (AcceptErrEnv := AcceptOptFieldsEnv P_m)
      (PromEnv := fun _ s => PromoteOverCanonSessEnv s)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) (cliModelPrims_structural X W)
      (cliStageP2ClosureHooksPlaced mmpl gh W hh)
      (cliStageP2BaseCalleesPlaced4K mmpl gh W hh)
      (cliInitBobErrOwnedFrozen4K_ok X mmpl gh W hh)
      (cliInitBobV1FrozenOkPlaced4K X mmpl gh W hG hh hSpqr)
    (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
    (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
    (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).selfEnv
    (cliPollSelf_vtablesPlacedOk y.g.F y.g.peer (cliKitStk B) hDropNz)
    (hSelfKit B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
    (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
    (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).spkEnv
    (cliPollSpk_vtablesPlacedOk y.g.F m.spkId (cliKitStk B) hDropNz)
    (hSpkKit B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
    (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
    (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).kpkEnv
    (cliPollKpk_vtablesPlacedOk y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) hDropNz)
    (hKpkKit B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
    (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
    (kitEnvs B y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey).pkEnv
    (cliPollPk_vtablesPlacedOk y.g.F w.opkWord (cliKitStk B) hDropNz)
    (hPkKit B y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey hh)
    (dpClosSubStack B) (stageP2OverV1CallStack4K_le_subStack_placed (A := A.repAlloc)
      y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B)
  exact hStageP2 (st := st_b)
    (Qp := fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Qpan sf Pf)
    s0 s1 (D3NonCanonStage2PollPlacedBudget.pathAInnerFrameD3Placed A.repAlloc y i rngPtr sp)
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
          ((kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).spkEnv.getPollEnv
            StoresGhost.opened.signed m.spkId)
          (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).getBoxSize
          ((kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).kpkEnv.getPollEnv
            StoresGhost.opened.kyber m.kpkId)
          (cliPollPkKitPlaced A.repAlloc y.g.F opkWord0 (cliKitStk B)).getBoxSize
          ((kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).pkEnv.getPollEnv
            StoresGhost.opened.oneTime)
          (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpBoxSize
          (hdrOpkIdBv? (mkPathAHdr m))
          ((kitEnvs B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).selfEnv.kpPollEnv
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
      refine fitsEnv_step3 (hfits0.mono fun evs hseq => ?_)
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
          · rcases p2OverSub6_or hr3 with hArm6 | hOk
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
      refine fitsEnv_step3 (hfits0.mono fun evs h5 => ?_) hevs14 hevsKp (FreeOnlyEvs.singleton 8 _)
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
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv B y.g r evs (by
        unfold P2OverPathCErrEnvOf; rw [hpkToE]; exact Or.inl hevs)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F m.spkId (cliKitStk B) y.out e err0))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hmsg_i, Or.inl (Or.inl hspkNone)⟩, hpost⟩)
    (fun _spkRec e sf Pf evs _ _ hkpkErr hevs hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          List.append_nil, List.append_nil] at htr_f
      have hkpkNone : pkStoreKeys y.g.F m = none := pkStoreKeys_eq_none_of_kpk_err
        ((cliKpk_getRel_error_iff (A := A.repAlloc) cliIo.rd y.g.F cliWrOk m.kpkId
          StoresGhost.opened.kyber m.kpkId).mp ⟨e, hkpkErr⟩)
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv B y.g r evs (by
        unfold P2OverPathCErrEnvOf; rw [hpkToE]; exact Or.inr (Or.inl hevs))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) y.out e err0))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
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
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv B y.g r evs (by
        unfold P2OverPathCErrEnvOf; rw [hpkToE]; exact Or.inr (Or.inr (Or.inl hevs)))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F w.opkWord (cliKitStk B) y.out e err0))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
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
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv B y.g r evs (by
        unfold P2OverPathCErrEnvOf; rw [hpkToE]; exact Or.inr (Or.inr (Or.inr (Or.inl hevs))))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (Entails.trans
          (cliPollSelf_kpErr_entails_decResAt_err_placed A.repAlloc
            y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
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
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv B y.g r evs (by
        unfold P2OverPathCErrEnvOf; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hevs)))))
      have hPf' := Entails.trans hPf (by rw [← sepConj_assoc]; exact Entails.refl _)
      have hpost := Entails.trans hPf' (Entails.trans
        (sepConj_mono_left (pqxdhAcceptErr_entails_decResAt_anyHeap_ext A.repAlloc
          y.out errTag w2 w3 w4 w5 w6 err0))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
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
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv B y.g r evs (by
        unfold P2OverPathCErrEnvOf; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        rw [haccSome]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hevs)))))
      have hregNone := cliPollSelf_regIdRel_err_placed hregErr
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (Entails.trans
          (cliPollSelf_regIdErr_entails_decResAt_err_placed A.repAlloc
            y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
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
      have hevs' : P2OverOkEnv y.g r evs := hOkEnv B y.g r evs (by
        unfold P2OverPathCOkEnvOf; rw [hpkToE, hcur]; dsimp only; rw [hk, hkpOk]; dsimp only
        rw [haccSome0]; exact hevs)
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
        (D3NonCanonStage2PollPlacedBudget.p2OverOkPost_fold_pathCOver_d3_placed (st_b := M.stepEvents evs st_b)
          y m i w s0 s2 sp (sp + 0xc70#64) rngPtr
          recG G_bob sess (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m dk0)
          hcanon hpkToE hmsg_i hcoins hsub rfl hopkWord hsp2 hx19_2 hx27_2) ?_)
      refine SepWPp.exists_elim fun prevCap' => SepWPp.exists_elim fun prevPtr' =>
        SepWPp.pure_left fun hcap_ne => ?_
      exact hok s2 evs m i k kp localRegId dk0 G_bob prevCap' prevPtr' y.g.msgA y.g.msgG.msg
        (preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
        hevs' hcap_ne hpkToE hmsg_i hi hk hkpOk hregOk haccModel hextra hmsg_reasm
        hSteps12 htr2 hpc2 hrun2 hsp2 halign2 hx19_2 hx27_2 hx29_sp0 hvregs2 (CryptoVerification.libsignalFrozen_of_keepsFrozen hCode1 hSteps12.keepsFrozen))

/-- `[LibsignalFullPlacement]` Path-C overwrite Stage P2 instantiation
(`StageP2PathCOverQpanCliD3FrozenPlacedBudgetStmt`) for arbitrary `pm` with `pkToE? pm = some m`. -/
theorem stageP2PathCOverQpan_cli_d3_full_placed_of_seams [LibsignalFullPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {kitEnvs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ X W B g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (kitEnvs B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X W B g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverCanonSessEnv (kitEnvs B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X W B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (kitEnvs B))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverCanonSessEnv (kitEnvs B))
          g r))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : ∀ (gh : CliGhostHooks),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.CliGhostAllocHooks M A lim gh)
    (hSpqr : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      SpqrV1PlacedSeams M A lim mmpl gh W)
    (hSelfKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).selfEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).spkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).kpkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (kitEnvs B F0 peer spkId kpkId opkWord kbk).pkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PathCOverQpanCliD3FrozenPlacedBudgetStmt A lim PromoteOverEnv P2OverErrEnv P2OverOkEnv :=
  fun X mmpl gh W =>
    stageP2PathCOverQpan_cli_d3_at_full_placed_of_seams A lim X mmpl gh W
      (hErrEnv X W) (hOkEnv X W) (hFitsSplit X W) hDropNz (hG gh) (hSpqr mmpl gh W)
      (hSelfKit mmpl gh W) (hSpkKit mmpl gh W) (hKpkKit mmpl gh W) (hPkKit mmpl gh W)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathCPlacedBudget
