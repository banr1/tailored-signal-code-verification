/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.BodyPlaced
public import LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1InstPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFoldPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget
import ProofLib
import ProofLib.SepLogic.WPp

/-!
# Kit-Parametric D2(c) Stage-P2 Path A Producer

Provides shared Stage-P2 callee adapters from `InitialStateMemInvPlacedOkOfEnv`, defines
`StageP2PathAQpanCliNoReadMemInvPlacedAtStmt` / `StageP2PathAQpanCliNoReadFrozenPlacedAtStmt`, and
proves `stageP2PathA_qpan_cli_noRead_frozen_of_init75_and_kits` from the four Stage-P2 store kits.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2PathAPlacedBudgetFd

open Arm64 Arm64.Process ProofLib
open Arm64.Obj (MultiPlacement)
open CryptoGames.LibsignalSession (PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (ApiError SessionRecord)
open CryptoVerification (
  LibsignalFrozen LibsignalFullPlacement LibsignalHooks LibsignalPlacement
  lsMemcpySym lsProg_75 lsRustNoAllocShimSym lsmpl lsρ
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  SessionExtraRel coroOpkIdAtP4 hdrOpkIdBv? mkP2AcceptKeysInput p1LoadedRecordAt stageP1ProgPlaced
)
open CryptoVerification.E2E (
  PreKeyMessageFields ResponderPreKeySecrets UnreachedPqxdhPrimitives
  acceptInput keyPairOf modelPrims toU8 vecU8
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  bytesToBv8 ofSignalPqxdhAcceptKeysInput ofSignalPqxdhDRKey
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys acceptKeys_ofSignalPqxdhPrimitives)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (stageP3Sub5ExtraPre)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  bytesToBv8_vecU8 ls_subroutine_ok_withLsFrozen_of_block ofSignalPqxdhPrimitives vecU8_length
)
open CryptoVerification.E2E.Pqxdh.ResponderStore (clampBv8List_length)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsAt FsFiles LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal preKeyMsgAt)
open CryptoVerification.LibsignalTripleRatchet (framelessMemcpySpec noAllocShimSpec rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost protocolAddressAt signalMessageAt
)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (
  CliGhostHooks StoresGhost cliGhostExterns cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym
  cliSessionVtSym cliSignedPreKeyVtSym
)
open CryptoVerification.SignalSession.Cli.KitInst (
  cliKpk_getRel_error_iff cliPk_getRel_error_iff cliSpk_getRel_error_iff
)
open CryptoVerification.SignalSession.Cli.MainHops (
  cliIo cliWrOk coinsInstalledPlaced storesAt
)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunGlue (cliExternsPlaced_row cliGhostExterns_other)
open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOk₀ pkStoreKeys pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit StageP1PostRegs cliKitStk cliModelPrims_matchCrypto cliModelPrims_structural
  cliPollIdKitPlaced cliPollKpkKitPlaced cliPollKpk_vtablesPlacedOk cliPollPkKitPlaced
  cliPollPk_vtablesPlacedOk cliPollSelfKitPlaced cliPollSelf_kpRel_err_placed
  cliPollSelf_kpRel_ok_placed cliPollSelf_regIdRel_err_placed cliPollSelf_regIdRel_ok_placed
  cliPollSelf_vtablesPlacedOk cliPollSpkKitPlaced cliPollSpk_vtablesPlacedOk
  decPkDef_pathA_accept_none_anyReg decPkDef_pathA_lookup_err distinctSid_of_decPkOk₀
  dpClosSubStack dpPollEntryPlaced dpPollProgPlaced entails_sepConj_anyHeap hdrOpkIdBv?_mkPathAHdr
  mkPathAHdr p2Over_cliPollKpk_getEvs_placed p2Over_cliPollPk_getEvs_placed
  p2Over_cliPollPk_opkOkEvs_placed p2Over_cliPollPk_opkOkUpdate_placed
  p2Over_cliPollSelf_kpEvs_placed p2Over_cliPollSelf_regIdEvs_placed
  p2Over_cliPollSpk_getEvs_placed pathAInitSession pathAInitState pathA_pm_typed
  pkStoreKeys_eq_none_of_kpk_err pkStoreKeys_eq_none_of_opk_err pkStoreKeys_eq_none_of_spk_err
  pqxdhAcceptErr_entails_decResAt_anyHeap_ext preKeyMsgAt_eq_base_idKey_sep
  preKeyMsgRemBaseIdKeyAt sepWPp_conseq_pre sp_sub_576_ne_zero stageP2PostP1At
  stageP3CoroFrameAt stageP3StackFrameAt x29_eq_sp0_sub_60 x29_eq_sp_add_c70
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  FilesOkPeer blackBox_row_placed cliGhostExterns_sat_of_cliExternsPlaced loadRec scopeIn scopeKit
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  InitializeBobV1FrozenOkPlaced4KOfEnv StageP2BaseCalleesPlaced4K
  initializeBobSessionErrOwnedFrozen4KPlacedSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget (
  P2Sub1To4Arm3Env P2Sub1To4OkEnv P2Sub4OkEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv initializeBobSession_ok_v1_of_env_4k_frozen_placed_on_stageP1
  isSameAccount_4k_placed_ok_on_stageP1 p2_errOwned_frozen_to_defs4K_placed
  stageP2BaseCalleesPlaced4K_of_hooks
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget (
  P2V1Arm4Env P2V1Arm5EnvOfAcceptErr P2V1Arm6EnvOfBob P2V1OkEnvOfBob
  stageP2_v1_kits_frozen_ext_defs_placed_ofEnv
)
open LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget (InitialStateMemInvPlacedOkOfEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget (
  initializeBobSession_err_owned_frozen_placed_ok_of_accept
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk PreKeyStoreKitPlacedOk
  SignedPreKeyStoreKitPlacedOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  CliPollStageP2Envs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux (
  cliStageP2ClosureHooksPlaced uuidTryParse_placed_vm_code_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  genP3Pre_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced StageP2PathAEnv StageP2PathAErrPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget (
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
  cliPollKpk_getErr_entails_decResAt_anyHeap_placed
  cliPollPk_getErr_entails_decResAt_anyHeap_placed cliPollSelf_kpErr_entails_decResAt_err_placed
  cliPollSelf_regIdErr_entails_decResAt_err_placed
  cliPollSpk_getErr_entails_decResAt_anyHeap_placed cliPollStageP2_fsAt_stages_placed
  cliResponderPqxdhHookContractsPlaced_of_hookSat
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget (
  p2ErrFrame_fold_pathA_placed_rep pathAInnerFramePlaced stageP2PreAt_dup_kyberPtr_placed
  stageP2_entry_unpack_pathA_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1InstPlacedBudgetAux (
  P2PathAErrEnvOf P2PathAOkEnvOf stageP2V1CallStack4K_le_subStack_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliP2PathAOptFieldsErrEnv cliP2PathAOptFieldsOkEnv cliPollKpkFullBudgetEnv
  cliPollPkFullBudgetEnv cliPollSpkFullBudgetEnv cliStageP2KitEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFoldPlacedBudget (
  p2OkPost_fold_pathA_placed_at
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_framelessMemcpy_budget_sat
  cliExternsPlaced_sessionMemcpyRegion_budget_sat cliExternsPlaced_sessionMemcpy_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  framelessMemcpyBudgetSpec noAllocShimBudgetSpec
)

/-! ## 1. `0`-`hRead` Stage-P2 Path A Statement (`DecPkOk₀`) -/

/-- `0`-`hRead` / `0`-`hDeser` counterpart of `StageP2PathAQpanCliMemInvPlacedAtStmt`. -/
def StageP2PathAQpanCliNoReadMemInvPlacedAtStmt (Φ : Memory → Prop) [LibsignalPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (mmpl : MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {st_b : M.σ}
    (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (g1 : StoresGhost)
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    FitsEnv M lim st_b (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv y.g) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → scopeIn r') →
    FilesOkPeer Scope y.g.F y.g.peer.val →
    loadRec Scope y.g.F y.g.peer.val = .ok none →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 →
    Φ s1.mem →
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
      StageP2PathAErrPlaced A lim st_b P2PathAErrEnv X W B S Scope y s0 s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (evs : List AllocEvent) (s2 : State)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (recG : SessionGhost)
      (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2PathAOkEnv y.g evs →
      whisperG = y.g.msgG.msg →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG
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
      Φ s2.mem →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         genP3Pre_placed A lim (M.stepEvents evs st_b) s2.sp (s2.readReg64 .x29) y.fut y.cx
           y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
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
       p1LoadedRecordAt scopeKit A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores g1 ∗
       LsTokenInit ∗
       lsLogOff ∗
       stackAt sp (dpClosSubStack B))
      Q Qpan

/-- `LibsignalFrozen`-guarded `0`-`hRead` Stage P2 Path A statement. -/
abbrev StageP2PathAQpanCliNoReadFrozenPlacedAtStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (mmpl : MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  StageP2PathAQpanCliNoReadMemInvPlacedAtStmt (LibsignalFrozen lsmpl) A lim X mmpl gh W B
    P2PathAErrEnv P2PathAOkEnv

/-! ## 2. Shared `{M} {A}`-Generic Stage-P2 Callee Helpers -/

theorem hookSat_noAllocShimBudget_of_withVmPreserved
    {H : LibsignalHooks}
    (hsat : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)) :
    HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec := by
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

theorem hookSat_framelessMemcpy_of_vm
    {H : LibsignalHooks}
    (h : HookSat H "memcpy" (withVmPreserved framelessMemcpySpec)) :
    HookSat H lsMemcpySym LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpySpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    rcases x with ⟨_dst, _src, _bs⟩
    dsimp only [withVmPreserved, framelessMemcpySpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpySpec,
      framelessMemcpyBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact ⟨hkf, hsym, Or.inr hrest⟩

private theorem hookSat_sessionMemcpyBudget_of_vm {H : String → Option (State → State)}
    {sym : String} (hookStack : Nat)
    (h : HookSat H sym (withVmPreserved framelessMemcpySpec)) :
    HookSat H sym (LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyBudgetSpec hookStack) := by
  have hreg : HookSat H sym
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec :=
    (show withVmPreserved framelessMemcpySpec =
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec from rfl) ▸ h
  refine ProofLib.HookSat.mono hreg fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyBudgetSpec,
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec, ProofLib.libcMemcpySpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, ProofLib.memcpyRegionSpec] at hpre ⊢
    ac_nf at hpre ⊢
  · dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyBudgetSpec,
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec] at hpost ⊢
    ac_nf at hpost ⊢

theorem cliStageP2BaseCalleesPlaced4K [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2BaseCalleesPlaced4K A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  stageP2BaseCalleesPlaced4K_of_hooks
    (hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim)
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    (hookSat_sessionMemcpyBudget_of_vm allocHookStack hh.codecHooks.memcpy)
    (isSameAccount_4k_placed_ok_on_stageP1
      ((cliGhostExterns_other gh _
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W)))
      (uuidTryParse_placed_vm_code_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))))

theorem cliInitBobV1FrozenOkPlaced4K_of_init75 [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hInit75 : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim W.C.F
      (InitialStateEnv W.C.F) (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    InitializeBobV1FrozenOkPlaced4KOfEnv
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      A lim W.C.F
      (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  initializeBobSession_ok_v1_of_env_4k_frozen_placed_on_stageP1
    (cliModelPrims_structural X W)
    (hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim)
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG)
    (pqxdhAccept_opt_fields_responder_full_placed_ok_of_block
      (callerProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 75)
      (cliModelPrims_structural X W)
      (cliModelPrims_matchCrypto X W)
      (cliResponderPqxdhHookContractsPlaced_of_hookSat
        X mmpl gh W hG hh.codecHooks.alloc hh.codecHooks.dealloc
        (hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim))
      (hookSat_framelessMemcpy_of_vm
        (cliExternsPlaced_framelessMemcpy_budget_sat mmpl gh W hG)))
    hInit75
    (fun _ _ _ => Iff.rfl)

theorem cliInitBobErrOwnedFrozen4K_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok
      (stageP1ProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 75)
      (initializeBobSessionErrOwnedFrozen4KPlacedSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
        A lim
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))) := by
  have h75 :=
    initializeBobSession_err_owned_frozen_placed_ok_of_accept
      (pqxdhAccept_err_owned_responder_full_placed_ok_of_block
        (callerProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 75)
        (cliModelPrims_structural X W)
        (cliModelPrims_matchCrypto X W)
        (cliResponderPqxdhHookContractsPlaced_of_hookSat
          X mmpl gh W hG hh.codecHooks.alloc hh.codecHooks.dealloc
          (hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim))
        (hookSat_framelessMemcpy_of_vm
          (cliExternsPlaced_framelessMemcpy_budget_sat mmpl gh W hG)))
  have hbase :=
    ls_subroutine_ok_withLsFrozen_of_block
      (callerProg := stageP1ProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (calleeProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (i := 518) (j := 75) h75
  refine p2_errOwned_frozen_to_defs4K_placed ?_
  refine subroutine_ok_map hbase ?_
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun _ hpost => hpost⟩
  dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

theorem p2Sub1To4_opkWord_eq
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
    rw [hbox hw, hpoll hw]
    exact ⟨rfl, rfl⟩

theorem fitsEnv_step3 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E1 E2 E3 E4 : List AllocEvent → Prop} {e1 e2 e3 : List AllocEvent}
    (h : FitsEnv M lim st (SeqEnv E1 (SeqEnv E2 (SeqEnv E3 E4))))
    (h1 : E1 e1) (h2 : E2 e2) (h3 : E3 e3) :
    FitsEnv M lim (M.stepEvents (e1 ++ e2 ++ e3) st) E4 := by
  rw [M.stepEvents_append, M.stepEvents_append]
  exact ((h.seq_right h1).seq_right h2).seq_right h3

/-! ## 3. Kit-Parametric `0`-`hRead` Stage-P2 Path A Frozen Producer -/

set_option maxHeartbeats 1600000 in
theorem stageP2PathA_qpan_cli_noRead_full_placed_at_of_init75 [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (mmpl : MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    {kitEnvs : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hInit75 : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim W.C.F
      (InitialStateEnv W.C.F) (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSelfKit : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (kitEnvs F0 peer spkId kpkId opkWord kbk).selfEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (kitEnvs F0 peer spkId kpkId opkWord kbk).spkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kitEnvs F0 peer spkId kpkId opkWord kbk).kpkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (kitEnvs F0 peer spkId kpkId opkWord kbk).pkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PathAQpanCliNoReadFrozenPlacedAtStmt A lim X mmpl gh W B
      (P2PathAErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        kitEnvs)
      (P2PathAOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        kitEnvs) := by
  intro DecPkEnv st_b S Scope y g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hh hfits0 hcoins hdecOk hScope hFok hloadNone htrust hg1
    hfs1 hCode1 htr01 hsp1 hsp0 hsub hpc1 hrun1 halign1 hregs1 herr hok
  subst hg1
  rcases hregs1 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, _, hx29, hvregs1⟩
  obtain ⟨m, i, _, hi, hpm, hpkToE⟩ := pathA_pm_typed hdecOk
  have hfp_reg : s1.readReg64 .x29 = sp + 0xc70#64 := x29_eq_sp_add_c70 hsp0 hx29
  have hsp_align : (sp &&& 15#64 == 0#64) = true := by rw [← hsp1]; exact halign1
  refine sepWPp_with_steps ?_
  refine sepWPp_conseq_pre
    (stageP2_entry_unpack_pathA_placed (Scope_p1 := scopeKit) (Scope := Scope)
      y m i s0 sp (sp + 0xc70#64) rngPtr v_a8 v_b8 v_d0 hpm rfl hdecOk hFok hScope) ?_
  refine SepWPp.exists_elim fun w => SepWPp.pure_left fun hopkWord => ?_
  refine sepWPp_conseq_pre
    (stageP2PreAt_dup_kyberPtr_placed
      (A_s := A.atState lim st_b s1) (A_r := A.repAlloc)
      (spkKit := cliPollSpkKitPlaced (A.atState lim st_b s1) y.g.F m.spkId (cliKitStk B))
      (kpkKit := cliPollKpkKitPlaced (A.atState lim st_b s1) y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (pkKit := cliPollPkKitPlaced (A.atState lim st_b s1) y.g.F w.opkWord (cliKitStk B))
      (ikit := cliPollIdKitPlaced (A.atState lim st_b s1) y.g.F y.g.peer (cliKitStk B))
      y m i w s0 sp (sp + 0xc70#64) rngPtr v_a8 v_b8 v_d0
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity) ?_
  refine SepWPp.pure_left fun hctBuf_nz => ?_
  let opkWord0 : BitVec 32 := m.opkId.getD 0#32
  have ⟨hArm3_eq, hOk14_eq⟩ := p2Sub1To4_opkWord_eq
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
  exact stageP2_v1_kits_frozen_ext_defs_placed_ofEnv
    (M := M) (P := P_m) (A := A) (lim := lim) (F := W.C.F)
    (BobV1Env := InitializeBobV1OptFieldsEnv P_m W.C.F)
    (AcceptErrEnv := AcceptOptFieldsEnv P_m)
    (st := st_b)
    (Qp := fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Qpan sf Pf)
    (cliGhostExterns gh (cliExternsPlaced mmpl W)) (cliModelPrims_structural X W)
    (cliStageP2ClosureHooksPlaced mmpl gh W hh)
    (cliStageP2BaseCalleesPlaced4K mmpl gh W hh)
    (cliInitBobErrOwnedFrozen4K_ok X mmpl gh W hG hh)
    (cliInitBobV1FrozenOkPlaced4K_of_init75 X mmpl gh W hG hh hInit75)
    (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
    (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
    (kitEnvs y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).selfEnv
    (cliPollSelf_vtablesPlacedOk y.g.F y.g.peer (cliKitStk B) hDropNz)
    (hSelfKit y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
    (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
    (kitEnvs y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).spkEnv
    (cliPollSpk_vtablesPlacedOk y.g.F m.spkId (cliKitStk B) hDropNz)
    (hSpkKit y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
    (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
    (kitEnvs y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).kpkEnv
    (cliPollKpk_vtablesPlacedOk y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) hDropNz)
    (hKpkKit y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
    (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
    (kitEnvs y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey).pkEnv
    (cliPollPk_vtablesPlacedOk y.g.F w.opkWord (cliKitStk B) hDropNz)
    (hPkKit y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey hh)
    (dpClosSubStack B) (stageP2V1CallStack4K_le_subStack_placed (A := A.repAlloc)
      y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B)
    s0 s1 (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp)
    (fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Q sf Pf)
    sp (sp + 0xc70#64) y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
    y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
    y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
    (mkPathAHdr m) ikBSk ikBPk i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
    w.opkWord m.kpkId m.regId m.spkId StoresGhost.opened.signed StoresGhost.opened.kyber
    StoresGhost.opened.oneTime StoresGhost.opened.identity y.g.me y.g.peer
    (hfits0.mono fun evs hevs => by
      refine Or.inl ?_; unfold P2PathAErrEnvOf; rw [hpkToE]
      rcases hevs with h1 | h2 | h3 | hok4
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · rw [hArm3_eq] at h3; exact Or.inr (Or.inr (Or.inl h3))
      · rw [hOk14_eq] at hok4; exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl hok4)))))
    (fun evs14 hevs14 => by
      rw [hOk14_eq] at hevs14
      have hArm4 : FitsEnv M lim st_b (P2V1Arm4Env
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
          refine Or.inl ?_; unfold P2PathAErrEnvOf; rw [hpkToE]
          exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
      exact hArm4.seq_right hevs14)
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey evs14 evsKp
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccSome hevs14 hevsKp => by
      rw [hOk14_eq] at hevs14
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hikBSk_ok : ikBSk = vecU8 kp.privateKey.bytes := by dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = vecU8 kp.identityKey.publicKey.bytes := by dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdecOk hspkRel hspkPubEq hspkPrivEq
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have hinp0 := hinp 0#32; rw [hinp0] at haccSome ⊢
      refine fitsEnv_step3 (hfits0.mono fun evs h6 => ?_)
        hevs14 hevsKp (FreeOnlyEvs.singleton 8 _)
      refine Or.inl ?_; unfold P2PathAErrEnvOf; rw [hpkToE]; dsimp only
      rw [hk, hkpOk]; dsimp only; rw [haccSome]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6)))))
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp evs14 evsKp
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel _haccNone hevs14 hevsKp => by
      rw [hOk14_eq] at hevs14
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hikBSk_ok : ikBSk = vecU8 kp.privateKey.bytes := by dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = vecU8 kp.identityKey.publicKey.bytes := by dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdecOk hspkRel hspkPubEq hspkPrivEq
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      rw [hinp 0#32]
      refine fitsEnv_step3 (hfits0.mono fun evs h5 => ?_) hevs14 hevsKp (FreeOnlyEvs.singleton 8 _)
      refine Or.inl ?_; unfold P2PathAErrEnvOf; rw [hpkToE]; dsimp only
      rw [hk, hkpOk]; dsimp only; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
    hctBuf_nz (sp_sub_576_ne_zero B hsub) hsub hikBSk_len hikBPk_len
    (vecU8_length m.idPub) (vecU8_length m.baseKey) (vecU8_length m.kyberCt) hCode1
    (cliPollStageP2_fsAt_stages_placed hh y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B hfs1)
    rfl (fun r' hrel _ => cliPollSpk_wf_of_preKeysWf_placed hdecOk.preKeysWf r' hrel)
    rfl (fun r' hrel _ => cliPollKpk_wf_of_preKeysWf_placed hdecOk.preKeysWf r' hrel)
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid))
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid) |>.symm)
    (fun _id r' _ hrel _ => cliPollPk_wf_of_preKeysWf_placed hdecOk.preKeysWf r' hrel)
    hkp_sk hkp_pk (Or.inr (distinctSid_of_decPkOk₀ hdecOk))
    hpc1 hrun1 hsp1 hsp_align htr01 hvregs1
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hfp_reg
    (fun e evs sf Pf hspkErr hevs hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, List.append_nil] at htr_f
      have hspkNone : pkStoreKeys y.g.F m = none := pkStoreKeys_eq_none_of_spk_err
        ((cliSpk_getRel_error_iff (A := A.repAlloc) (b := 0#64) cliIo.rd y.g.F cliWrOk m.spkId
          (cliKitStk B).spkGetShim (cliKitStk B).spkGetPoll
          StoresGhost.opened.signed m.spkId).mp ⟨e, hspkErr⟩)
      have hevs' : P2PathAErrEnvOf (A := A.repAlloc) X W B
          (InitializeBobV1OptFieldsEnv P_m W.C.F) (AcceptOptFieldsEnv P_m) kitEnvs y.g evs := by
        unfold P2PathAErrEnvOf; rw [hpkToE]; exact Or.inl hevs
      have hmod := decPkDef_pathA_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inl hspkNone)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F m.spkId (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    (fun _spkRec e evs sf Pf _ _ hkpkErr hevs hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          List.append_nil, List.append_nil] at htr_f
      have hkpkNone : pkStoreKeys y.g.F m = none := pkStoreKeys_eq_none_of_kpk_err
        ((cliKpk_getRel_error_iff (A := A.repAlloc) cliIo.rd y.g.F cliWrOk m.kpkId
          StoresGhost.opened.kyber m.kpkId).mp ⟨e, hkpkErr⟩)
      have hevs' : P2PathAErrEnvOf (A := A.repAlloc) X W B
          (InitializeBobV1OptFieldsEnv P_m W.C.F) (AcceptOptFieldsEnv P_m) kitEnvs y.g evs := by
        unfold P2PathAErrEnvOf; rw [hpkToE]; exact Or.inr (Or.inl hevs)
      have hmod := decPkDef_pathA_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inl hkpkNone)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    (fun _spkRec _kpkRec opkId e evs sf Pf _ _ _ _ hopkHdr hpkErr hevs hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          p2Over_cliPollPk_getEvs_placed, List.append_nil, List.append_nil, List.append_nil] at htr_f
      rw [hArm3_eq] at hevs
      have hmOpk : m.opkId = some opkId := (hdrOpkIdBv?_mkPathAHdr m).symm.trans hopkHdr
      have hpkNone : pkStoreKeys y.g.F m = none := pkStoreKeys_eq_none_of_opk_err hmOpk
        ((cliPk_getRel_error_iff (A := A.repAlloc) (b := 0#64) cliIo.rd y.g.F cliWrOk w.opkWord
          (cliKitStk B).pkGetShim (cliKitStk B).pkGetPoll
          (cliKitStk B).pkRemoveShim (cliKitStk B).pkRemovePoll
          StoresGhost.opened.oneTime opkId).mp ⟨e, hpkErr⟩)
      have hevs' : P2PathAErrEnvOf (A := A.repAlloc) X W B
          (InitializeBobV1OptFieldsEnv P_m W.C.F) (AcceptOptFieldsEnv P_m) kitEnvs y.g evs := by
        unfold P2PathAErrEnvOf; rw [hpkToE]; exact Or.inr (Or.inr (Or.inl hevs))
      have hmod := decPkDef_pathA_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inl hpkNone)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F w.opkWord (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    (fun _spkRec _kpkRec wOpk e evs sf Pf _ _ _ _ _ hkpErr hevs hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          p2Over_cliPollPk_opkOkEvs_placed, p2Over_cliPollSelf_kpEvs_placed,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := p2Over_cliPollPk_opkOkUpdate_placed A.repAlloc y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      unfold P2V1Arm4Env at hevs; rw [hOk14_eq] at hevs
      have hkpNone := cliPollSelf_kpRel_err_placed hkpErr
      have hevs' : P2PathAErrEnvOf (A := A.repAlloc) X W B
          (InitializeBobV1OptFieldsEnv P_m W.C.F) (AcceptOptFieldsEnv P_m) kitEnvs y.g evs := by
        unfold P2PathAErrEnvOf; rw [hpkToE]; exact Or.inr (Or.inr (Or.inr (Or.inl hevs)))
      have hmod := decPkDef_pathA_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inr (Or.inl hkpNone))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (Entails.trans
          (cliPollSelf_kpErr_entails_decResAt_err_placed A.repAlloc
            y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp errTag w2 w3 w4 w5 w6 evs sf Pf
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
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdecOk hspkRel hspkPubEq hspkPrivEq
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have haccNone0 : ∀ reg : BitVec 32, SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
          (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none := fun reg =>
        Option.map_eq_none_iff.mp (by
          rw [← acceptKeys_ofSignalPqxdhPrimitives, ← hinp reg]; exact haccNone)
      unfold P2V1Arm5EnvOfAcceptErr at hevs
      rw [hOk14_eq, hinp 0#32] at hevs
      have hevs' : P2PathAErrEnvOf (A := A.repAlloc) X W B
          (InitializeBobV1OptFieldsEnv P_m W.C.F) (AcceptOptFieldsEnv P_m) kitEnvs y.g evs := by
        unfold P2PathAErrEnvOf; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hevs))))
      have hmod := decPkDef_pathA_accept_none_anyReg X ⟨W.C, W.Q⟩ Scope y.g.F
        y.g.peer.val y.g.me.val y.g.msg y.g.coins hloadNone htrust hpkToE hi hk hkpOk haccNone0
      have hPf' := Entails.trans hPf (by rw [← sepConj_assoc]; exact Entails.refl _)
      have hpost := Entails.trans hPf' (Entails.trans
        (sepConj_mono_left (pqxdhAcceptErr_entails_decResAt_anyHeap_ext A.repAlloc
          y.out errTag w2 w3 w4 w5 w6 err0))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey e evs sf Pf
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
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdecOk hspkRel hspkPubEq hspkPrivEq
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have hinp0 := hinp 0#32; rw [hinp0] at haccSome
      unfold P2V1Arm6EnvOfBob at hevs; rw [hOk14_eq, hinp0] at hevs
      have hevs' : P2PathAErrEnvOf (A := A.repAlloc) X W B
          (InitializeBobV1OptFieldsEnv P_m W.C.F) (AcceptOptFieldsEnv P_m) kitEnvs y.g evs := by
        unfold P2PathAErrEnvOf; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        rw [haccSome]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hevs))))
      have hregNone := cliPollSelf_regIdRel_err_placed hregErr
      have hmod := decPkDef_pathA_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inr (Or.inr hregNone))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (Entails.trans
          (cliPollSelf_regIdErr_entails_decResAt_err_placed A.repAlloc
            y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey localRegId G_bob evs s2
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
      obtain ⟨k, hk, hspkPub_eq, _, hinp⟩ := pathA_acceptInput_agree_placed hdecOk hspkRel hspkPubEq
        hspkPrivEq hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have hinp0 := hinp 0#32
      have haccSome0 : acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
          (ofSignalPqxdhAcceptKeysInput (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)) =
          some drKey := by rw [← hinp0]; exact haccSome
      unfold P2V1OkEnvOfBob at hevs
      rw [hOk14_eq, hinp0] at hevs
      have hevs' : P2PathAOkEnvOf (A := A.repAlloc) X W B
          (InitializeBobV1OptFieldsEnv P_m W.C.F) kitEnvs y.g evs := by
        unfold P2PathAOkEnvOf; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        rw [haccSome0]; exact hevs
      obtain ⟨dk0, haccModel, hdk0⟩ := Option.map_eq_some_iff.mp (show
        (SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
          (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m)).map
            ofSignalPqxdhDRKey = some drKey by
          rw [← acceptKeys_ofSignalPqxdhPrimitives, ← hinp localRegId]; exact haccSome)
      have hikBPk_bv :
          bytesToBv8 ikBPk = (keyPairOf W.C kp.privateKey.bytes).publicKey.bytes.toList := by
        rw [hikBPk_ok, hdecOk.idPairDerived kp hkpOk, bytesToBv8_vecU8]
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
        (p2OkPost_fold_pathA_placed_at (M.stepEvents evs st_b)
          y m i w s0 s2 sp (sp + 0xc70#64) rngPtr
          G_bob (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m dk0)
          hpm hcoins hsub rfl hopkWord hsp2 hx19_2 hx27_2) ?_)
      exact hok evs s2 m i k kp localRegId dk0 G_bob y.g.msgA y.g.msgG.msg
        (preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
        hevs' rfl hpm hi hk hkpOk hregOk haccModel hextra hmsg_reasm
        hSteps12 htr2 hpc2 hrun2 hsp2 halign2 hx19_2 hx27_2 hx29_sp0 hvregs2
        (CryptoVerification.libsignalFrozen_of_keepsFrozen hCode1 hSteps12.keepsFrozen))

/-- Closed 4-kit `0`-`hRead` D2(c) Path A Stage P2 frozen producer at `B`. -/
theorem stageP2PathA_qpan_cli_noRead_frozen_of_init75_and_kits [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (mmpl : MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hInit75 : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim W.C.F
      (InitialStateEnv W.C.F) (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSelf : ∀ F0 peer,
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpk : ∀ F0 spkId,
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (cliPollSpkFullBudgetEnv A.repAlloc F0 spkId (cliKitStk B) ReadEnv)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpk : ∀ F0 kpkId spkId kbk,
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (cliPollKpkFullBudgetEnv A.repAlloc F0 kpkId spkId kbk (cliKitStk B) ReadEnv)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPk : ∀ F0 opkWord,
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (cliPollPkFullBudgetEnv A.repAlloc F0 opkWord (cliKitStk B) ReadEnv)
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PathAQpanCliNoReadFrozenPlacedAtStmt A lim X mmpl gh W B
      (cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W B
        (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv))
      (cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W B
        (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv)) :=
  stageP2PathA_qpan_cli_noRead_full_placed_at_of_init75 A lim X mmpl gh W B
    (kitEnvs := cliStageP2KitEnvs (A := A.repAlloc) ReadEnv B
      (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv))
    hDropNz hG hInit75
    (fun F0 peer _ _ _ _ _hh => hSelf F0 peer)
    (fun F0 _ spkId _ _ _ _hh => hSpk F0 spkId)
    (fun F0 _ spkId kpkId _ kbk _hh => hKpk F0 kpkId spkId kbk)
    (fun F0 _ _ _ opkWord _ _hh => hPk F0 opkWord)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2PathAPlacedBudgetFd
