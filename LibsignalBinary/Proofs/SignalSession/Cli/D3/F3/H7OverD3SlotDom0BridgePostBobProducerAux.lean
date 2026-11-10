/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollAuxPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
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
# `OverD3` Poll Producer Extracting `SessionGhostValid` from Memory

Extracts `SessionGhostValid` on the initial recipient session `pathAInitSession` from
`overGenP3Pre_placed` (at `+0x1778`) and on the post-decryption session `(G', ses')` from
`sessionStateAt` (at `+0x34dc`), closing `h7pb_decPk_d3_validOver_poll_at_full_placedBudget'`
without external `SessionGhostValid` hypotheses.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobProducerAux

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

/-! ## 1. `SessionGhostValid` Extraction Helpers -/

private theorem h7pb_sepWPp_peek_mem {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hk : (∃ R', s.mem ⊨ P ∗ R') → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R' hm hL => hk ⟨R', hm⟩ R' hm hL

private theorem h7pb_ex_frame_drop_left {m : Memory} {P Q : SepProp}
    (h : ∃ R, m ⊨ (P ∗ Q) ∗ R) : ∃ R, m ⊨ Q ∗ R :=
  let ⟨R, hR⟩ := h
  ⟨P ∗ R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hR⟩

private theorem h7pb_ex_frame_drop_right {m : Memory} {P Q : SepProp}
    (h : ∃ R, m ⊨ (P ∗ Q) ∗ R) : ∃ R, m ⊨ P ∗ R :=
  let ⟨R, hR⟩ := h
  ⟨Q ∗ R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hR⟩

private theorem h7pb_sessionGhostValid_of_overGenP3Pre [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st_b : M.σ}
    {sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64}
    {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {recG : SessionGhost} {ses : Session (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {s2 : State} {PreL Rest : SepProp}
    (hex : SessionExtraRel recG ses)
    (hm : ∃ R', s2.mem ⊨
      (PreL ∗
        overGenP3Pre_placed A lim st_b sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG ses.state rem loc msgG msg s2 ∗
        Rest) ∗ R') :
    SessionGhostValid recG ses := by
  have h1 := h7pb_ex_frame_drop_right (h7pb_ex_frame_drop_left hm)
  dsimp only [overGenP3Pre_placed,
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.overGenP3Pre_placed] at h1
  obtain ⟨R'', hm_ss⟩ := h7pb_ex_frame_drop_right (h7pb_ex_frame_drop_left h1)
  exact ⟨hex, A.atState lim st_b s2, coroPtr + 0xf8#64, s2.mem, R'', hm_ss⟩

/-! ## 1b. Fixed-`B` and `verNeEnv`-Parametric Stage Specializations -/

/-- `StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt` specialized to a single `(B : RunBudgets)`. -/
def H7pbStageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
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

theorem h7pb_stageP2OverQpanCliD3FrozenAtB_of_forall [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {X : UnreachedPqxdhPrimitives} {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    {W : CliHooks} (B : RunBudgets)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (h : StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W P2OverErrEnv P2OverOkEnv) :
    H7pbStageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt A lim X mmpl gh W B
      P2OverErrEnv P2OverOkEnv :=
  fun S {_DecPkEnv} Scope y st_b r s_old g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan =>
    h B S Scope y st_b r s_old g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan

/-- `StageP3Prev1D3AtFrozenPlacedStmt` at `OverPrevEncOK`, generalized from `VerNeTopEnv` to
`verNeEnv` and specialized to `(mmpl, gh, W)`. -/
def H7pbStageP3Prev1D3OfVerNeAtFrozenPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop :=
  ∀ (st_b : M.σ),
    CliGhostAllocHooks M A lim gh →
    AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    ChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    SenderChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (enc rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      FitsEnv M lim st_b
        (StageP3Prev1Env (tdEnv W) verNeEnv recG st rem loc msgG msg msgVer enc rest) →
      initErrsPtr ≠ 0#64 →
      prevCap ≠ 0#64 →
      OverPrevEncOK enc →
      st.version = 4#32 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      LibsignalFrozen lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.readReg64 .x29 = s.sp + 0xc70#64 →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s s' →
        s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrev1At_placed A lim (M.stepEvents evs_p3 st_b) s0 s s'
            coroPtr outPtr initErrsPtr prevCap prevPtr ptCap ptPtr enc pt b_2c0 G'
            (genP3S5Model W.C W.Q.K rem loc msg rest st).2 ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws W.C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
          (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5ModelPanicProp W.C W.Q.K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        StageP3ErrM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          overStageP3ErrPostPrevEmptyAt_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf
            coroPtr outPtr e ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws W.C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (evs_p3 : List AllocEvent) (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        StageP3VerNePrev1Env verNeEnv recG st enc evs_p3 →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          overStageP3ErrPostPrevEmptyAt_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf coroPtr
            outPtr (.invalidMessage .preKey .decryptionFailed) ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg (coinsAtPlaced cur rest) ∗
          overScratch s.sp ∗
          anyHeap) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (s0.readReg64 .x30) s
        (LsTokenInit ∗
          overGenP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr
            locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
            enc b_2c0 ∗
          overScratch s.sp ∗
          F_frame)
        Q
        (genP3S5ModelPanicProp W.C W.Q.K rem loc st msg msgVer rest s0)

/-- `StageP3Prev1D3FrozenPlacedStmt` with `VerNeTopEnv` generalized to `verNeEnv`. -/
def H7pbStageP3Prev1D3OfVerNeFrozenPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop) : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
    H7pbStageP3Prev1D3OfVerNeAtFrozenPlacedStmt A lim tdEnv verNeEnv mmpl gh W

theorem h7pb_stageP3Prev1D3OfVerNe_top_iff [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop} :
    H7pbStageP3Prev1D3OfVerNeFrozenPlacedStmt A lim tdEnv VerNeTopEnv ↔
      StageP3Prev1D3FrozenPlacedStmt A lim tdEnv :=
  Iff.rfl

/-- `StageP4Prev1VRegsAtPlacedStmt` specialized to a single `(B : RunBudgets)`. -/
def H7pbStageP4Prev1VRegsAtBPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
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

theorem h7pb_stageP4Prev1VRegsAtB_of_forall [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (B : RunBudgets)
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (h : StageP4Prev1VRegsAtPlacedStmt A lim mmpl gh W p4Envs) :
    H7pbStageP4Prev1VRegsAtBPlacedStmt A lim mmpl gh W B p4Envs :=
  fun F0 peer pid kpkId spkId kbk st_b =>
    h B F0 peer pid kpkId spkId kbk st_b

/-! ## 2. Stage P4 Continuation Extracting `SessionGhostValid G' ses'` from Memory -/

set_option maxHeartbeats 1200000 in
private theorem h7pb_closure_pathCOver_p4_d3_cont_at_b_placedBudget [LibsignalPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (B : RunBudgets)
    (hP4 : H7pbStageP4Prev1VRegsAtBPlacedStmt A lim mmpl gh W B p4Envs)
    {X : UnreachedPqxdhPrimitives}
    (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hS : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))}
    (evs_pre : List AllocEvent)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hr_in : scopeIn r)
    (hd3False : DecPkOkD3 ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hloadS : loadRec Scope y.g.F y.g.peer.val = .ok (some r))
    (hcur : r.currentSession = some s_old)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hnot_match : ¬ SessMatchesPm s_old y.g.msg)
    (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
    (kp : IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
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
      SessionGhostValid G' ses' →
      FitsEnv M lim (M.stepEvents evs_pre y.st)
        (StageP4Prev1ExitEnv prev1Kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
          kpkKit envs.kpkKitEnv StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber m.opkId y.g.peer.val
          y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey G' ses'
          (encSession (clearPending s_old))))
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
      SessionGhostValid G' ses' →
      ∀ evs4,
        StageP4Prev1ExitEnv prev1Kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
          kpkKit envs.kpkKitEnv StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber m.opkId y.g.peer.val
          y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey G' ses'
          (encSession (clearPending s_old)) evs4 →
        DecPkEnv y.g (evs_pre ++ evs4))
    (hpk : pkToE? y.g.msg = some m)
    (hmsg_i : y.g.msg.message = i)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
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
    (hcl : CloneRel recG G₁)
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
    (hro' : LibsignalCodeRoLoaded lsmpl s'.mem)
    (hent_s' : P_s' ⊢
      stageP3DispatchOkMidPrev1At_placed A lim (M.stepEvents evs_pre y.st) s0 s2 s'
        y.fut y.out 8#64 prevCap prevPtr ptCap ptPtr
        (encSession (clearPending s_old)) pt 0#8 G'
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2 ∗
      overGenP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.msg.message.senderRatchetKey y.g.coins)) ∗
      overScratch s2.sp) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
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
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post
            y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5ModelPanicProp W.C W.Q.K y.g.peer y.g.me st0 y.g.msg.message
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins s0) := by
  dsimp only
  let st_pre := M.stepEvents evs_pre y.st
  let A_s : RustAlloc := A.atState lim st_pre s'
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
  let prev1Kit := cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ
  let ops : StorePrev1Ops prev1Kit := cliPollStorePrev1OpsPlaced
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
  let envs := p4Envs B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
  let enc := encSession (clearPending s_old)
  let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
  let st0 := pathAInitState ⟨W.C, W.Q⟩ meE k m dk
  have hd0 : DecPkOk₀ ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val
      (pmOfE m y.g.msg.message) :=
    decPkOk0_of_d3_pkToE hd3False hpk
  dsimp only at hFits4 hEnv4
  generalize hst'_eq :
    (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2 = st' at hent_s'
  generalize hcoins_eq :
    coinsAfterPlaced y.g.coinsP y.g.coins
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
  have hh_p4 :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    ⟨hh.alloc, hh.allocFs, hh.panics, hh.memcpyRO, hh.bcmp, hh.fs, hh.utf8, hh.memrchr,
      hh.codecHooks, hh.allocZeroed, hh.stringClone, hh.formatInner⟩
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
  have hk1 : kit.storeAt = (cliPollSessKitPlaced A_s y.g.F scopeKit y.g.peer σ).storeAt := rfl
  have hk2 : ikit.identityAt = (cliPollIdKitPlaced A_s y.g.F y.g.peer σ).identityAt := rfl
  have hk3 : pkKit.storeAt = (cliPollPkKitPlaced A_s y.g.F pid σ).storeAt := rfl
  have hk4 : spkKit.storeAt = (cliPollSpkKitPlaced A_s y.g.F m.spkId σ).storeAt := rfl
  have hk5 : kpkKit.storeAt =
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt := rfl
  have hk6 : dirAt A.repAlloc = dirAt A_s := rfl
  have hm1' : s'.mem ⊨
      (stageP3DispatchOkMidPrev1Placed A_s s0 s2 y.fut y.out 8#64
          prevCap prevPtr ptCap ptPtr enc pt 0#8 G' st' ∗
        overGenP3S5PostFrame_placed A_s sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
          (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
          coinsPost ∗
        overScratch s2.sp) ∗
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
      (cliPollSessKitPlaced A_s y.g.F scopeKit y.g.peer σ).storeAt
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
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP4Prev1PrePlaced 0#64
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
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP4Prev1PrePlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP4Prev1RawPrePlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP4Prev1SharedPlaced
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
      Entails.trans (Entails.of_eq (by sep_ac_rfl : (A1 ∗ A2 ∗ S ∗ A3) ∗ A4 = S ∗ (A1 ∗ A2 ∗ A3 ∗ A4)))
        (sepConj_mono_right (entails_anyHeap _))
    exact hcomm _ _ _ _ _
  have hsgv' : SessionGhostValid G' ses' :=
    ⟨hex', A.repAlloc, y.fut + 0xf8#64, s'.mem, anyHeap, hm_sess⟩
  have hrecOk : ops.RecPrev1Ok G' ses' enc := by
    refine ⟨canonSession_of_sessionStateAt_extraRel hex' hm_sess, ?_⟩
    have hlen := encodeRecordPrev1_pathCOver_lt_32 hd0 hr_in hcur hver hok
    dsimp only at hlen
    rwa [hst'_eq] at hlen
  have hwp4 := hP4 y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey st_pre hh_p4
    s0 s'
    y.fut y.cx y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
    (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
    prevCap prevPtr ptCap ptPtr 8#64
    m.opkId m.kpkId m.spkId 0#8 pt enc
    y.g.msg.identityKey y.g.msg.baseKey
    StoresGhost.opened.sessions StoresGhost.opened.identity
    StoresGhost.opened.oneTime StoresGhost.opened.kyber
    G' ses'
    (hFits4 hsgv') hex' hrecOk rfl rfl
    (cliPollKpk_markOk_d3_placedBudget y.g.F m y.g.msg.baseKey σ)
    (cliPollPk_removeIdOk_of_pkToE_placedBudget y.g.F m i σ hpk hmsg_i)
    hpt_le hpt_lt hpt_ne hp4_64
    (cliPollStageP4Prev1_fsAt_placed A.repAlloc hh y.g.F y.g.peer pid m.kpkId m.spkId
      y.g.msg.baseKey σ hf')
    hro' hpc' hrun'
    (hs'_sp ▸ hsp_align2) (htr' ▸ List.prefix_refl _)
    hx19' (hs'_sp ▸ hx24') (hs'_sp ▸ hx25') hx26' hx27' hx28' hvregs'
  obtain ⟨sf, hsteps_p4, hBranch⟩ := hwp4 _ hm2 hL
  refine ⟨sf, hsteps_p4, ?_⟩
  have hpre_id : y.g.msg.preKeyId = m.opkId := (pm_fields_of_pkToE hpk hmsg_i).2.2.1
  have hspk_id : y.g.msg.signedPreKeyId = m.spkId := (pm_fields_of_pkToE hpk hmsg_i).2.2.2.1
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
      have hevs_tot : DecPkEnv y.g (evs_pre ++ evs4) := hEnv4 hsgv' evs4 hevs_exit
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
      obtain ⟨_hLen, hDec, hWr⟩ :=
        decPkOverDef_pathCOver_ok X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hfPeer hd0 hr_in hloadS hcur htrusted hnot_match hpk hmsg_i hi hk hkp hreg hacc hver
          hok_pair hmark_eq
      let oneTime' := match y.g.msg.preKeyId with
        | none => StoresGhost.opened.oneTime
        | some j => (removePreKey cliIo.rd y.g.F StoresGhost.opened.oneTime j).2
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := StoresGhost.opened.identity.saveUpd cliIo.rd y.g.F y.g.peer.val
            y.g.msg.identityKey
          kyber := kyber'
          oneTime := oneTime'
          sessions := StoresGhost.opened.sessions.put (addressText y.g.peer.val)
            (encodeRecordPrev1 ses' enc) }
      have hot_eq : g'.oneTime =
          (match m.opkId with
           | none => StoresGhost.opened.oneTime
           | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ())) := by
        dsimp only [g', oneTime', pkKit, cliPollPkKitPlaced, cliPreKeyStoreSpecPlaced,
          cliPreKeyStoreSpec]
        rw [hpre_id]
      exact p4_finish_dpPollPost_placed A lim DecPkEnv B S hh_p4 stk' hneed hstk63 y s0 s' sf
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
        (slotOutTr_over_of_accept hS hDec hWr) hm_f
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
      have hevs_tot : DecPkEnv y.g (evs_pre ++ evs4) := hEnv4 hsgv' evs4 hevs_exit
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
      have hDec := decPkOverDef_pathCOver_mark_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg
        y.g.coins hd0 hloadS hcur htrusted hnot_match hpk hmsg_i hi hk hkp hreg hacc hver hok_pair
        hmark_err
      let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val
            y.g.msg.identityKey (.ok c)
          kyber := kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId
            y.g.msg.baseKey (.error e) }
      exact p4_finish_dpPollPost_placed A lim DecPkEnv B S hh_p4 stk' hneed hstk63 y s0 s' sf
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
        (slotOutTr_over_of_reject g' hS nofun nofun hDec) hm_f
    · exact False.elim (cliPk_removeRel_not_err_of_pkStoreKeys (A := A.repAlloc) (b := 0#64)
        (pid := pid) (σ := σ) (e := e) hk hopk hrem)
    · exact False.elim (by cases hstore)
  · exact hpan_false.elim
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem h7pb_closure_pathCOver_p4_d3_cont_at_placedBudget [LibsignalPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hP4 : StageP4Prev1VRegsAtPlacedStmt A lim mmpl gh W p4Envs)
    {X : UnreachedPqxdhPrimitives}
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hS : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))}
    (evs_pre : List AllocEvent)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hr_in : scopeIn r)
    (hd3False : DecPkOkD3 ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hloadS : loadRec Scope y.g.F y.g.peer.val = .ok (some r))
    (hcur : r.currentSession = some s_old)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hnot_match : ¬ SessMatchesPm s_old y.g.msg)
    (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
    (kp : IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
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
      SessionGhostValid G' ses' →
      FitsEnv M lim (M.stepEvents evs_pre y.st)
        (StageP4Prev1ExitEnv prev1Kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
          kpkKit envs.kpkKitEnv StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber m.opkId y.g.peer.val
          y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey G' ses'
          (encSession (clearPending s_old))))
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
      SessionGhostValid G' ses' →
      ∀ evs4,
        StageP4Prev1ExitEnv prev1Kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
          kpkKit envs.kpkKitEnv StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber m.opkId y.g.peer.val
          y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey G' ses'
          (encSession (clearPending s_old)) evs4 →
        DecPkEnv y.g (evs_pre ++ evs4))
    (hpk : pkToE? y.g.msg = some m)
    (hmsg_i : y.g.msg.message = i)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
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
    (hcl : CloneRel recG G₁)
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
    (hro' : LibsignalCodeRoLoaded lsmpl s'.mem)
    (hent_s' : P_s' ⊢
      stageP3DispatchOkMidPrev1At_placed A lim (M.stepEvents evs_pre y.st) s0 s2 s'
        y.fut y.out 8#64 prevCap prevPtr ptCap ptPtr
        (encSession (clearPending s_old)) pt 0#8 G'
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2 ∗
      overGenP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.msg.message.senderRatchetKey y.g.coins)) ∗
      overScratch s2.sp) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
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
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post
            y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5ModelPanicProp W.C W.Q.K y.g.peer y.g.me st0 y.g.msg.message
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins s0) :=
  h7pb_closure_pathCOver_p4_d3_cont_at_b_placedBudget A lim DecPkEnv B
    (h7pb_stageP4Prev1VRegsAtB_of_forall B hP4) S hh hS stk' hneed hstk63 y evs_pre
    hfPeer hr_in hd3False hloadS hcur htrusted hnot_match m i k kp reg dk recG G₁ G'
    rngPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem P_s' R pt s0 s2 s'
    hFits4 hEnv4 hpk hmsg_i hi hk hkp hreg hacc hex hmsg_fold hfiles2 htr2 hs2_sp hsp_align2
    hsp_sub hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
    hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s'

/-! ## 3. `Path C Over` Branch Extracting `SessionGhostValid recG ses0` from `overGenP3Pre_placed` -/

set_option maxHeartbeats 1200000 in
private theorem h7pb_closure_pathCOver_d3_ofVerNe_at_b_full_placedBudget_ok [LibsignalPlacement]
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
        (h7pb_closure_pathCOver_p4_d3_cont_at_b_placedBudget A lim DecPkEnv B hP4O S hh hS stk' hneed
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

private theorem h7pb_closure_pathCOver_d3_at_full_placedBudget_ok [LibsignalPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    {X : UnreachedPqxdhPrimitives} {mmpl : Obj.MultiPlacement}
    {gh : CliGhostHooks} {W : CliHooks}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hP2O : StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W
      P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1D3FrozenPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsAtPlacedStmt A lim mmpl gh W p4Envs)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
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
        (StageP3Prev1Env (tdEnv W) VerNeTopEnv recG
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
      StageP3VerNePrev1Env VerNeTopEnv recG
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
            y s0 sf ∗ R)) :=
  h7pb_closure_pathCOver_d3_ofVerNe_at_b_full_placedBudget_ok A lim DecPkEnv B S Scope
    (h7pb_stageP2OverQpanCliD3FrozenAtB_of_forall B hP2O)
    (hP3O mmpl gh W)
    (h7pb_stageP4Prev1VRegsAtB_of_forall B hP4O)
    hG hh hTry hinjK hsub hS stk' hneed hstk63 y evs_p1 r s_old s0 s1 rngPtr v_a8 v_b8 v_d0 R
    hFits2 hEnvErr2 hFits3 hEnvErr3 hEnvVerNe3 hFits4 hEnv4
    hf0 hfPeer hd3False hScopeOver hcoins htrusted hload_rel hcur hnot_match
    hsteps01 htr1 hfroz1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1

/-! ## 4. Full Block-518 Poll Producer (`h7pb_decPk_d3_validOver_poll_at_full_placedBudget'`) -/

/-- Local copy of `DecPkD3ValidOverOfEnv'` (definitionally equal to
`H7OverD3SlotDom0BridgePostBob.DecPkD3ValidOverOfEnv'`), avoiding a circular import. -/
def H7pbDecPkD3ValidOverOfEnv' [LibsignalPlacement] (A : RustAlloc)
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let σ := cliKitStk B
  let P1 := CliStageP1OkEnv (A := A) B ReadEnv DeserEnv g
  CliDpPollUntrustedEnv (A := A) B ReadEnv DeserEnv g evs ∨
  P1 evs ∨
  ∃ (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8))),
    (cliPollSessKitPlaced A g.F scopeKit g.peer σ).loadRel
      StoresGhost.opened.sessions g.peer.val (.ok (some r)) ∧
    r.currentSession = some s_old ∧
    ScopeOverIn r ∧
    ¬ SessMatchesPm s_old g.msg ∧
    (SeqEnv P1 (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) evs ∨
     (∃ m i k kp reg dk recG whisperG,
       pkToE? g.msg = some m ∧
       g.msg.message = i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       SessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
         (StageP3Prev1Env (tdEnv W) verNeEnv recG
           (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           g.peer g.me whisperG g.msg.message
           (g.msg.message.messageVersion.zeroExtend 32)
           (encSession (clearPending s_old)) g.coins) evs) ∨
     (∃ m i k, ∃ kp : IdentityKeyPair, ∃ reg dk recG G₁ whisperG,
       pkToE? g.msg = some m ∧
       g.msg.message = i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       SessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       CloneRel recG G₁ ∧
       SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
         (StageP3ErrM3Env (tdEnv W) recG G₁
           (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           g.peer g.me whisperG g.msg.message g.coins) evs) ∨
     (∃ m i k, ∃ kp : IdentityKeyPair, ∃ reg dk recG,
       pkToE? g.msg = some m ∧
       g.msg.message = i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       SessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
         (StageP3VerNePrev1Env verNeEnv recG
           (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           (encSession (clearPending s_old))) evs) ∨
     (∃ m i k kp reg dk recG G₁ G' pt whisperG,
       pkToE? g.msg = some m ∧
       g.msg.message = i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       SessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       CloneRel recG G₁ ∧
       G₁.AfterTryDecrypt true G' ∧
       (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins
         (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt ∧
       let pid := pmPreKeyId g.msg
       let envs := p4Envs B g.F g.peer pid m.kpkId m.spkId g.msg.baseKey
       let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
       let ses' : Session (List (BitVec 8)) :=
         { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
           state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins st0).2
           pendingPreKey := none
           pendingKyberPreKey := none }
       SessionGhostValid G' ses' ∧
       SeqEnv
         (SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
           (StageP3OkPrefixM3Env (tdEnv W) recG G₁ st0
             g.peer g.me whisperG g.msg.message g.coins))
         (StageP4Prev1ExitEnv
           (cliPollSessPrev1KitPlaced A g.F g.peer σ) envs.opsEnv
           (cliPollIdKitPlaced A g.F g.peer σ) envs.ikitEnv
           (cliPollPkKitPlaced A g.F pid σ) envs.pkKitEnv
           (cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey σ) envs.kpkKitEnv
           StoresGhost.opened.sessions StoresGhost.opened.identity
           StoresGhost.opened.oneTime StoresGhost.opened.kyber
           m.opkId g.peer.val g.msg.identityKey m.kpkId m.spkId g.msg.baseKey G' ses'
           (encSession (clearPending s_old))) evs))

set_option maxHeartbeats 1200000 in
/-- Pointwise `(X, mmpl, gh, W, B)` `verNeEnv`-parametric `withLsFrozen` poll composition
extracting `SessionGhostValid` on both `pathAInitSession` and `(G', ses')` from memory. -/
theorem h7pb_decPk_d3_validOver_poll_ofVerNe_at_b_at_full_placedBudget' [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hP2O : H7pbStageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt A lim X mmpl gh W B
      P2OverErrEnv P2OverOkEnv)
    (hP3O : H7pbStageP3Prev1D3OfVerNeAtFrozenPlacedStmt A lim tdEnv verNeEnv mmpl gh W)
    (hP4O : H7pbStageP4Prev1VRegsAtBPlacedStmt A lim mmpl gh W B p4Envs)
    (hTry : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hEnv : ∀ g evs,
      H7pbDecPkD3ValidOverOfEnv' A.repAlloc verNeEnv W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs) :
    CliDpPollOkOverV4StateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope := by
  intro hG hh hRead hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_over_d3_frozen_placed (W := W) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre
  obtain ⟨⟨hd3False, _hd3Scope⟩, r0, s_old0, hload0, hcur0, hScopeOver0, hnot_match0⟩ :=
    hpure.decPkOk
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    exact closure_untrusted_over_d3_full_placedBudget_ok A lim hDropNz mmpl gh W X B S Scope
      hh hRead hDeser hinjK hsub hS stk' hneed' hstk63 y
      (fun evs hevs => hpure.fits evs (hEnv y.g evs (Or.inl hevs)))
      (fun evs hevs => hEnv y.g evs (Or.inl hevs))
      R s0 hpc hrun hsp hpure.froz hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer
      hd3False htrusted hm_base
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
    let sp := s0.sp - 0xcd0#64
    have hsp_align0 : (s0.sp &&& 15#64 == 0#64) = true := by
      simpa [State.spAligned] using hsp
    have hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat :=
      (subStack_le_sp_of_dpPollNeed hneed' hpure.stk_le_sp).1
    have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d3 A.repAlloc
      σ y.g.stores hsub hpure.filesOkPeer hd3False pid sid kid kbk
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
          cliPreKeyStoreSpecPlaced, cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
          cliKyberPreKeyStoreSpecPlaced]
        sep_frame) hm_flat
    refine ⟨P_p1 ∗ Fr_inner, R, hm_split, ?_⟩
    have hfits_p1 : FitsEnv M lim y.st (CliStageP1OkEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g) :=
      fun evs hevs => hpure.fits evs (hEnv y.g evs (Or.inr (Or.inl hevs)))
    have hwp := stageP1_ok_placed_inst hDropNz mmpl gh W B y.g.F y.g.peer y.g.msg.identityKey
      hhSt hRead hDeser y.st StoresGhost.opened.sessions StoresGhost.opened.identity
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
      (CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded.of_libsignalFrozen
        hpure.froz)
      (cliPollStageP1_fsAt_placed hh y.g.F scopeKit y.g.peer B hpure.files_eq)
      hpc hrun hsp_align0 rfl hpure.x0 hpure.x1 hpure.x2
    refine sepWPp_bind_p1_false_d3 hwp ?_
    intro s1 P_1 hsteps01 hpc1 hrun1 hq1
    rcases hq1 with ⟨⟨opt, evs_p1, hP1_raw, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
      hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
      hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, _hro1⟩
    have hfroz1 : LibsignalFrozen lsmpl s1.mem :=
      libsignalFrozen_of_keepsFrozen hpure.froz hsteps01.keepsFrozen
    have hP1 : CliStageP1OkEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs_p1 := hP1_raw
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
    have hload_opt : loadRec Scope y.g.F y.g.peer.val = .ok opt :=
      loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hpure.filesOkPeer hload_rel
    cases opt with
    | none =>
      cases hload0.symm.trans hload_opt
    | some r =>
      have hr_eq0 : r = r0 := Option.some.inj (Except.ok.inj (hload_opt.symm.trans hload0))
      subst hr_eq0
      exact h7pb_closure_pathCOver_d3_ofVerNe_at_b_full_placedBudget_ok A lim DecPkEnv B S Scope
        hP2O hP3O hP4O hG hh hTry hinjK hsub hS stk' hneed' hstk63
        y evs_p1 r s_old0 s0 s1 coins v_a8 v_b8 v_d0 R
        (fitsEnv_after_d3 hpure.fits fun evs2 h2 =>
          hEnv y.g (evs_p1 ++ evs2)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inl (seqEnv_append_d3 hP1 h2)⟩)))
        (fun evs2 h2 =>
          hEnv y.g (evs_p1 ++ evs2)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inl (seqEnv_append_d3 hP1 (Or.inl h2))⟩)))
        (fun evs2 m i k kp reg dk recG whisperG h2 hpk hmsg_i hi hk hkp hreg hacc hex hsgv0 =>
          fitsEnv_after_d3 hpure.fits fun evs3 h3 =>
            hEnv y.g ((evs_p1 ++ evs2) ++ evs3)
              (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
                Or.inr (Or.inl ⟨m, i, k, kp, reg, dk, recG, whisperG,
                  hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hsgv0,
                  seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3⟩)⟩)))
        (fun evs2 evs3 m i k kp reg dk recG G₁ whisperG
            h2 hpk hmsg_i hi hk hkp hreg hacc hex hsgv0 hcl h3 =>
          hEnv y.g (evs_p1 ++ evs2 ++ evs3)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inr (Or.inr (Or.inl ⟨m, i, k, kp, reg, dk, recG, G₁, whisperG,
                hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hsgv0, hcl,
                seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3⟩))⟩)))
        (fun evs2 evs3 m i k kp reg dk recG
            h2 hpk hmsg_i hi hk hkp hreg hacc hex hsgv0 h3 =>
          hEnv y.g (evs_p1 ++ evs2 ++ evs3)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inr (Or.inr (Or.inr (Or.inl ⟨m, i, k, kp, reg, dk, recG,
                hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hsgv0,
                seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3⟩)))⟩)))
        (fun evs2 evs3 m i k kp reg dk recG G₁ G' pt whisperG
            h2 hpk hmsg_i hi hk hkp hreg hacc hex hsgv0 hcl htd h3 hok hsgv' =>
          fitsEnv_after_d3 hpure.fits fun evs4 h4 =>
            hEnv y.g (evs_p1 ++ evs2 ++ evs3 ++ evs4)
              (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
                Or.inr (Or.inr (Or.inr (Or.inr ⟨m, i, k, kp, reg, dk, recG, G₁, G', pt, whisperG,
                  hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hsgv0, hcl, htd, hok, hsgv',
                  seqEnv_append_d3 (seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3) h4⟩)))⟩)))
        (fun evs2 evs3 evs4 m i k kp reg dk recG G₁ G' pt whisperG
            h2 hpk hmsg_i hi hk hkp hreg hacc hex hsgv0 hcl htd h3 hok hsgv' h4 =>
          hEnv y.g (evs_p1 ++ evs2 ++ evs3 ++ evs4)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inr (Or.inr (Or.inr (Or.inr ⟨m, i, k, kp, reg, dk, recG, G₁, G', pt, whisperG,
                hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hsgv0, hcl, htd, hok, hsgv',
                seqEnv_append_d3 (seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3) h4⟩)))⟩)))
        hpure.files_eq hpure.filesOkPeer hd3False hScopeOver0 hpure.coins_lt htrusted
        hload_rel hcur0 hnot_match0
        hsteps01 htr1 hfroz1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1

/-- `verNeEnv`-parametric, fixed-`B` poll producer over `H7pbStageP3Prev1D3OfVerNeFrozenPlacedStmt`. -/
theorem h7pb_decPk_d3_validOver_poll_ofVerNe_at_b_full_placedBudget' [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hP2O : H7pbStageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt A lim X mmpl gh W B
      P2OverErrEnv P2OverOkEnv)
    (hP3O : H7pbStageP3Prev1D3OfVerNeFrozenPlacedStmt A lim tdEnv verNeEnv)
    (hP4O : H7pbStageP4Prev1VRegsAtBPlacedStmt A lim mmpl gh W B p4Envs)
    (hTry : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hEnv : ∀ g evs,
      H7pbDecPkD3ValidOverOfEnv' A.repAlloc verNeEnv W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs) :
    CliDpPollOkOverV4StateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope :=
  h7pb_decPk_d3_validOver_poll_ofVerNe_at_b_at_full_placedBudget'
    hDropNz mmpl gh W X B S Scope hP2O (hP3O mmpl gh W) hP4O hTry hEnv

/-- Pointwise `(X, mmpl, gh, W)` `withLsFrozen` poll composition extracting `SessionGhostValid`
on both `pathAInitSession` and `(G', ses')` from memory. -/
theorem h7pb_decPk_d3_validOver_poll_at_full_placedBudget' [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hP2O : StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W
      P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1D3FrozenPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsAtPlacedStmt A lim mmpl gh W p4Envs)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hTry : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hEnv : ∀ g evs,
      H7pbDecPkD3ValidOverOfEnv' A.repAlloc VerNeTopEnv W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs) :
    CliDpPollOkOverV4StateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope :=
  h7pb_decPk_d3_validOver_poll_ofVerNe_at_b_full_placedBudget'
    hDropNz mmpl gh W X B S Scope
    (h7pb_stageP2OverQpanCliD3FrozenAtB_of_forall B hP2O)
    hP3O
    (h7pb_stageP4Prev1VRegsAtB_of_forall B hP4O)
    hTry hEnv

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobProducerAux
