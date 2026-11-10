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
# `hRead`-Free Stage-P4 Continuation for Non-Matching Overwrite (`OverD3`)

Extracts `SessionGhostValid` from memory and proves the `hRead`-free Stage-P4 continuation
`closure_pathCOver_p4_d3_cont_at_b_placedBudget` for `Path C Over`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPathCP4PlacedBudgetFd

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

open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobProducerAux (
  H7pbStageP4Prev1VRegsAtBPlacedStmt
)

/-! ## 1. `SessionGhostValid` Extraction Helpers -/

theorem h7pb_sepWPp_peek_mem {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hk : (∃ R', s.mem ⊨ P ∗ R') → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R' hm hL => hk ⟨R', hm⟩ R' hm hL

theorem h7pb_ex_frame_drop_left {m : Memory} {P Q : SepProp}
    (h : ∃ R, m ⊨ (P ∗ Q) ∗ R) : ∃ R, m ⊨ Q ∗ R :=
  let ⟨R, hR⟩ := h
  ⟨P ∗ R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hR⟩

theorem h7pb_ex_frame_drop_right {m : Memory} {P Q : SepProp}
    (h : ∃ R, m ⊨ (P ∗ Q) ∗ R) : ∃ R, m ⊨ P ∗ R :=
  let ⟨R, hR⟩ := h
  ⟨Q ∗ R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hR⟩

theorem h7pb_sessionGhostValid_of_overGenP3Pre [LibsignalPlacement]
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

/-! ## 2. Stage P4 Continuation Extracting `SessionGhostValid G' ses'` from Memory -/

set_option maxHeartbeats 1200000 in
theorem closure_pathCOver_p4_d3_cont_at_b_placedBudget [LibsignalPlacement]
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
        dsimp only [g', oneTime', pkKit, cliPollPkKitPlaced,
          CryptoVerification.SignalSession.Cli.KitInst.cliPreKeyStoreSpecPlaced,
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
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

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPathCP4PlacedBudgetFd
