/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBMainPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3MatchingPathBAuxPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefs
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.NonVacProofs.StateWitnessPlaced
import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
import LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
import ProofLib.SepLogic.WPp

/-!
# `SeqFree` and `SessionGhostValid`-Strengthened Matching-Session Path-B Slot Closure

Proves `decPkPathBSlotOk_seqFree_of_readEnv_placedBudget` and its `SessionGhostValid`-strengthened
counterpart `decPkPathBSlotOk_gvSeqFree_of_readEnv_placedBudget` on Path-B slot `520`, and embeds
`DecPkD3MatchingPathBGvSeqFreeOfReadEnv` into `realCliDecPkBinaryWideSlotEnvCmkDom0FixedOf`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.D3MatchingPathBSeqFreeR

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoGames.LibsignalSessionApi (ApiError Session SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsRustNoAllocShimSym lsmpl lsρ
   withLsCodeLoaded)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5ModelPanicProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
  (SessionExtraRel loadCallStack p1LoadedRecordAt sp_sub_cd0_align_std3 stageP1CallStack
   stageP1UntrustedCallStack)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.E2E.Pqxdh.ResponderClosure
  (decryptPrekeyCoroCopyAt decryptPrekeyCoroInitAt decryptPrekeySavedRegsAt
   processPrekeyInnerInitAt processPrekeyPostTrustAt)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr
  (AddrVal RecordGhost apiDecResultAt preKeyMsgAt)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (extHookStack noAllocShimSpec rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SessionGhost SignalMessageGhost decryptDraws protocolAddressAt signalMessageAt
   uuidTryParse vecResultAt)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced isCliPanicSymbolPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli
  (StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym
   cliSignedPreKeyVtSym dirAt)
open CryptoVerification.SignalSession.Cli.KitInst
  (cliIdentityStoreSpec cliKyberPreKeyStoreSpecPlaced cliPreKeyStoreSpecPlaced
   cliSessionStoreSpec cliSignedPreKeyStoreSpecPlaced)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliRunBudgets_placed cliWrOk coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost RunNeeds RunSem decResAt dpPollNeed dpSlotArgsPlaced mkSlot slotOutTr)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns cliGhostExterns_other)
open CryptoVerification.SignalSession.Cli.RunProofs
  (SessMatchesPm cliDecryptPrekeyNeed decPkDef dpCxAt dpFutDoneAt dpFutStartAt dpWrapFrame)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (LsTokenInit StageP1PostRegs apiDecResultAt_proto_entails_decResAt
   apiDecResultAt_untrusted_entails_decResAt cliIdStoreSpecFull cliIdStoreSpecFullPlaced
   cliId_saveRel_not_err cliId_trustRel_eq_of_trusted cliKitStk cliKpkStoreSpecFullPlaced
   cliPollIdKit cliPollIdKitPlaced cliPollId_trustUpdate_eq_placed cliPollId_vtablesPlacedOk
   cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessKit cliPollSessKitPlaced
   cliPollSess_vtablesPlacedOk cliPollSpkKitPlaced cliPollStoresKitsAtPlaced
   cliPollStoresKitsAtPlaced_entails_storesAt cliSess_loadRel_isOk cliSess_storeRel_not_err
   closStackUnusedP1OkAt closStackUnusedUntrustedAt clos_stack_3280_of_p1_untrusted
   clos_stack_3280_split_for_p1_ok clos_stack_3280_split_for_p1_untrusted
   closureCalleeSaved_toCalleeSavedPreserved coroUnusedP1At
   coro_of_p1_untrusted_entails_dpFutDoneAt decPkDef_of_trust_err decPkDef_pathB_remId_ne
   decPkDef_pathB_ver_ne dpClosSubStack dpCxAt_entails_memRegion32
   dpFutStartAt_split_for_p1_placed dpPollEntryPlaced dpPollNeed_eq_frame_add_subStack
   dpPollProgPlaced loadRec_of_cliPollSessPlaced_loadRel pmKyberId pmPreKeyId
   preKeyMsgAt_eq_idKey_sep preKeyMsgRemIdKeyAt rootStack_le_subStack sepWPp_conseq_pre
   sepWPp_sepExists_left sessionExtraRel_of_clone_decRel slotOutTr_of_err slotOutTr_of_ok
   slotOutTr_of_reject sp_frame_sub_add stackAt_poll_entry_split stackAt_subStack_split
   stackAt_subStack_sub_eq stageP1CallStack_le_subStack stageP1UntrustedCallStack_le_subStack
   stageP2PostP1At stageP3CoroFrameAt stageP3StackFrameAt stageP3Sub5ExtraPrePrevEmpty
   stageP4MatchedCallStack subStack_le_sp_of_dpPollNeed subroutine_ok_of_sepWPp_steps
   trusted_ok_of_filesOkPeer)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (EncodeInjOn FilesOkPeer encodeInjOn_deserializeScopeP_Q filesOk₀ loadRec scopeIn scopeKit)
open CryptoVerification.SignalSession.Coins (coinsAfterPlaced coinsAtPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
  (chainClone3_placed_ok_of_hooks senderChainClone3_placed_ok_of_hooks)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
  (drop_session_structure4_placed_ok_at)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudgetAux
  (StageP2MatchedBridgeEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
  (StageP2MatchedEnv StageP2MatchedMismatchEnv)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
  (realCliDecPkBinaryWideSlotEnvCmkDom0Fixed' realCliDecPkBinaryWideSlotEnvCmkDom0FixedOf)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
  (W4StatesRecvEnv w4c_TryDecryptCliLinkedSrEnvOf w4c_repairedStatesRecvEnvFam)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot (w4c_defaultDecodeMaxOps)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3
  (DecPkOkPathB decPkDef_pathB_err_pathB decPkDef_pathB_ok_pathB decPkDef_pathB_panic_pathB
   distinctSid_of_decPkOkPathB genP3S5Model pathB_scopeIn_and_match_of_decPkOkPathB
   storesAt_opened_entails_cliPollStoresKitsAtPlaced_pathB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPlacedBudget
  (DecPkD3MatchingPathBEnv decPkPathBSlotOk_full_placedBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs decPkSlotSpecPlaced slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
  (StageP2MatchedFramedCliPlacedStmt sepWPp_genP3_to_tailQpan_placed sepWPp_pollGoal_frame_placed
   stageP3_exit_prevEmpty_to_pollPost_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBPlacedBudget
  (pathBP4RemAtPlaced stageP3MidPrevEmpty_eq_p4_placed stageP4MatchedExit_entails_exit_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget
  (cliFiles_eq_of_trace_eq_placed cliPollStageP1_fsAt_placed exit_entails_dpPollPost_placed
   stageP4MatchedStack_placed_le_pow64)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget
  (StageP1OkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
  (ChainClone3OkPlaced SenderChainClone3OkPlaced StageP3Env StageP3ErrEnv StageP3OkPrefixEnv
   StageP3PrevEmptyVRegsPlacedStmt StageP3VerNeEnv genP3Pre_placed genP3S5PostFrame_placed
   pollTryDecryptPlacedSpecTPTight stageP3DispatchOkMidPrevEmpty_placed
   stageP3ErrPostPrevEmpty_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (RunHooksPlaced StageP4MatchedEnv StageP4MatchedStoreStepEnv stageP4MatchedExitAtPlaced
   stageP4MatchedPrePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
  (CliDpPollUntrustedEnv StageP1UntrustedMangledPlacedStmt dpPollPost_of_decResAt_placed
   runHooks_to_stages stageP1_untrusted_mangled_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedInstPlacedBudget
  (stageP2Matched_framed_cli_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
  (stageP1_ok_placed_inst)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
  (cliPollIdBudgetEnv cliPollId_kitPlacedOkI cliPollSessBudgetEnv cliPollSessSeqFreeBudgetEnv
   cliPollSess_seqFreeKitPlacedOkSE stageP4Matched_placed_of_kits)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget
  (K₀_statePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
  (dpSlotPollKStatePlaced_inv_vm dpSlotPollKStatePlaced_res_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
  (cliDecryptPrekey_ok_state_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced dpSlot_ok_state_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## 1. `SeqFree` `ReadEnv`-Parametric Path-B Envelope and Slot `520` Theorem -/

/-- `SeqFree` `ReadEnv`-parametric CLI specialization of `DecPkD3MatchingPathBEnv` wired to
`SessDeserializeCancelEnv` and `cliPollSessSeqFreeBudgetEnv`. -/
abbrev DecPkD3MatchingPathBSeqFreeOfReadEnv [LibsignalPlacement] (A : RustAlloc)
    (W : CliHooks) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (g : DecPkGhost) : List AllocEvent → Prop :=
  DecPkD3MatchingPathBEnv A W B ReadEnv SessDeserializeCancelEnv
    (fun F0 peer =>
      cliPollSessSeqFreeBudgetEnv A F0 peer (cliKitStk B) SessDeserializeCancelEnv ReadEnv)
    tdEnv g

/-- `SeqFree` `ReadEnv`-parametric CLI slot `520` theorem over
`DecPkD3MatchingPathBSeqFreeOfReadEnv`, discharging `hSkit` via `cliPollSess_seqFreeKitPlacedOkSE`. -/
theorem decPkPathBSlotOk_seqFree_of_readEnv_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets_placed.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hStageP3 : StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3MatchingPathBSeqFreeOfReadEnv A.repAlloc W cliRunBudgets_placed ReadEnv tdEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets_placed) :
    (slotsOfPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  decPkPathBSlotOk_full_placedBudget X mmpl gh W h547 hh hRead hDeser
    (fun F0 peer => cliPollSess_seqFreeKitPlacedOkSE mmpl gh W cliRunBudgets_placed F0 peer h547 hh hRead hDeser)
    hStageP3 hTryDec S sEnvs needs hsEnv hfiles hdecPk hdecPkOk hneed

/-! ## 2. `SessionGhostValid`-Strengthened (`Gv`) `SeqFree` Path-B Envelopes and Slot `520` Theorem -/

/-- `SessionGhostValid`-strengthened counterpart of `MatchingPathBMainEnv`, recording
`SessionGhostValid recG sess` alongside `SessionExtraRel recG sess` at the `recG` binder. -/
def MatchingPathBGvMainEnv [LibsignalPlacement] (A_r : RustAlloc)
    (W : CliHooks) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (kitEnv4 : ∀ F0 peer, SessionStoreBudgetEnv
      (cliPollSessKitPlaced A_r F0 CryptoVerification.SignalSession.Cli.Slots.scopeKit peer (cliKitStk B)))
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (g : DecPkGhost) (sess : Session (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  let σ := cliKitStk B
  let kit := cliPollSessKitPlaced A_r g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit g.peer σ
  let ikit := cliPollIdKitPlaced A_r g.F g.peer σ
  let kitEnv := kitEnv4 g.F g.peer
  let ikitEnv := cliPollIdBudgetEnv A_r g.F g.peer σ ReadEnv
  StageP2MatchedEnv sess g.msg.identityKey evs ∨
  (sess.state.remoteIdentity = some g.msg.identityKey ∧
    ∃ recG : SessionGhost, SessionExtraRel recG sess ∧ SessionGhostValid recG sess ∧
      SeqEnv StageP2MatchedBridgeEnv
        (fun evs34 =>
          StageP3Env tdEnv recG sess.state g.peer g.me g.msgG.msg
            g.msg.message (g.msg.message.messageVersion.zeroExtend 32) g.coins evs34 ∨
          (sess.state.version = g.msg.message.messageVersion.zeroExtend 32 ∧
            ∃ G₁ G' pt,
              CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ ∧
              G₁.AfterTryDecrypt true G' ∧
              (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state).1 = .ok pt ∧
              SeqEnv
                (StageP3OkPrefixEnv tdEnv recG G₁ sess.state g.peer g.me g.msgG.msg
                  g.msg.message g.coins)
                (StageP4MatchedEnv kit kitEnv ikit ikitEnv
                  CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
                  g.peer.val g.msg.identityKey
                  { sess with
                    state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state).2
                    pendingPreKey := none
                    pendingKyberPreKey := none })
                evs34))
        evs)

private theorem e2c_sessionGhostValid_of_genP3Pre [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    {recG : SessionGhost} {sess : Session (List (BitVec 8))}
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) (F_rem : SepProp)
    (hex : SessionExtraRel recG sess)
    (hm : s.mem ⊨ genP3Pre_placed A lim st_b sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG sess.state rem loc msgG msg s ∗ F_rem) :
    SessionGhostValid recG sess := by
  refine ⟨hex, A.atState lim st_b s, coroPtr + 0xf8#64, s.mem, ?w, ?_⟩
  rotate_left
  refine Arm64.Satisfies.mono ?_ hm
  dsimp only [
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.genP3Pre_placed,
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3Pre_placed]
  sep_frame

set_option maxHeartbeats 800000 in
private theorem e2c_closure_pathB_p4_cont_pathB_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    {kitEnv4 : SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer (cliKitStk B))}
    (hSkit : SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer (cliKitStk B))
      kitEnv4 CryptoVerification.SignalSession.Cli.Slots.scopeKit encodeRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (sess : Session (List (BitVec 8)))
    (evs_pre : List AllocEvent)
    (s0 s2 s' : State)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem P_s' R : SepProp)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (g : RecordGhost) (recG G₁ G' : SessionGhost)
    (pt : List (BitVec 8))
    (hfPeer : CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkPathB ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hIn : CryptoVerification.SignalSession.Cli.Slots.scopeIn ⟨some sess⟩)
    (hloadS : CryptoVerification.SignalSession.Cli.Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some ⟨some sess⟩))
    (htrusted : CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hMatch : SessMatchesPm sess y.g.msg)
    (hrem : sess.state.remoteIdentity = some y.g.msg.identityKey)
    (hex : SessionExtraRel recG sess)
    (hfits_p4 : FitsEnv M lim (M.stepEvents evs_pre y.st)
      (StageP4MatchedEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv4
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
        y.g.peer.val y.g.msg.identityKey
        { sess with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
          pendingPreKey := none
          pendingKyberPreKey := none }))
    (hevs_ok : ∀ evs_p4,
      StageP4MatchedStoreStepEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv4
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
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
    (hro' : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem)
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
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
    let Fr_tail : SepProp :=
      pkKit.storeAt (y.g.stores + 0xc8#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.pub ∗
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
        ikit.identityAt y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity ∗
        kit.storeAt (y.g.stores + 0xf0#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions ∗
        memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5ModelPanicProp W.C W.Q.K y.g.peer y.g.me sess.state y.g.msg.message
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins s0) := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer σ
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
    decPkDef_pathB_ok_pathB X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
      hfPeer hdecOk hIn hloadS htrusted hMatch hrem hver hok
  have hex' : SessionExtraRel G' ses' := sessionExtraRel_of_clone_decRel hex hcl hdec_rel
  have hs'_sp0 : s'.sp = sp := hs'_sp.trans hs2_sp
  have hsp_ret : sp + 0xcd0#64 = s0.sp := BitVec.sub_add_cancel s0.sp 0xcd0#64
  have hs'_files : s'.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps2' (htr'.trans htr20.symm)).trans hs2_files
  have hfs_p4 := cliPollStageP1_fsAt_placed hh y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer B hs'_files
  have hp4_64 : stageP4MatchedCallStack kit ikit ≤ 2 ^ 64 :=
    stageP4MatchedStack_placed_le_pow64 A.repAlloc B hneed hstk63
  have hwp4 := stageP4Matched_placed_of_kits mmpl gh W B y.g.F y.g.peer hDropNz hh hSkit
    (cliPollId_kitPlacedOkI mmpl gh W B y.g.F y.g.peer hDropNz hh hReadFile)
    (M.stepEvents evs_pre y.st) s0 s'
    y.fut y.g.msgA y.cx y.out y.g.peerA (y.g.msgA + 0xc8#64)
    (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
    y.g.msg.identityKey CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
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
        y.g.peer y.g.msg.identityKey CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
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
          ikit.identityAt y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity ∗
          kit.storeAt (y.g.stores + 0xf0#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions ∗
          memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) ∗ R' =
        stageP4MatchedPrePlaced A lim (M.stepEvents evs_pre y.st) kit ikit s0 s'
          y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
          (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
          y.g.peer y.g.msg.identityKey CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
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
        CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4.ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
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
        { CryptoVerification.SignalSession.Cli.StoresGhost.opened with
          identity := CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.saveUpd cliIo.rd y.g.F y.g.peer.val
            y.g.msg.identityKey
          sessions := CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions.put (CryptoVerification.SignalSession.Cli.addressText y.g.peer.val)
            (CryptoVerification.E2E.Record.encodeRecord ⟨some ses'⟩) }
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
            (kit.storeUpdate CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
            (ikit.saveUpdate CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c)) := by
        rw [M.stepEvents_append evs_pre evs_p4 y.st]
        exact hpost_f
      have hm_f1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hpost_f')) hm_f
      have hexit := stageP4MatchedExit_entails_exit_placed A lim (M.stepEvents (evs_pre ++ evs_p4) y.st)
        B y s0 s' sf rngPtr whisperMsgPtr ptCap ptPtr whisperG
        preKeyMsgRem coinsPost (y.g.msg.message.messageVersion.zeroExtend 32)
        opkHi kyberPreKeyId signedPreKeyId pid kid pt
        (kit.storeUpdate CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
        (ikit.saveUpdate CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        g' hs'_sp0 hsp_sub hmsg_fold rfl rfl rfl rfl rfl rfl
      dsimp only at hexit
      have hm_f2 : sf.mem ⊨
          (stageP4MatchedExitAtPlaced A lim (M.stepEvents (evs_pre ++ evs_p4) y.st) kit ikit
              s0 s' sf y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
              (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
              ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId
              (vecResultAt A.repAlloc y.out (.ok pt)) pt
              y.g.peer y.g.msg.identityKey
              (kit.storeUpdate CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
              (ikit.saveUpdate CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c)) ∗
            pathBP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
              (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost ∗
            pkKit.storeAt (y.g.stores + 0xc8#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime ∗
            spkKit.storeAt (y.g.stores + 0x50#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed ∗
            kpkKit.storeAt (y.g.stores + 0x78#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber ∗
            dirAt A.repAlloc (y.g.stores + 0x118#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.pub) ∗
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
            CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
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

private theorem e2c_hookSat_sessionShimBudget_of_codec {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec)) :
    HookSat H lsRustNoAllocShimSym
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionShimBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · exact ⟨hkeep, hsym, Or.inl ⟨hret, hcc, hpost⟩⟩
  · exact ⟨hkeep, hsym, Or.inr hrest⟩

private theorem e2c_hookSat_sessionMemcpyRegionBudget_of_codec {H : LibsignalHooks}
    (h : HookSat H CryptoVerification.LibsignalTripleRatchet.lsMemcpySym
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    HookSat H CryptoVerification.LibsignalTripleRatchet.lsMemcpySym
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · exact ⟨hkeep, hsym, Or.inl ⟨hret, hcc, hpost⟩⟩
  · exact ⟨hkeep, hsym, Or.inr hrest⟩

private theorem e2c_cliChainClone3_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    ChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  chainClone3_placed_ok_of_hooks
    (e2c_hookSat_sessionShimBudget_of_codec hh.codecHooks.shim)
    hh.codecHooks.alloc
    (e2c_hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)

private theorem e2c_cliSenderChainClone3_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    SenderChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  senderChainClone3_placed_ok_of_hooks
    (e2c_hookSat_sessionShimBudget_of_codec hh.codecHooks.shim)
    hh.codecHooks.alloc
    (e2c_hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)

private theorem e2c_cliDropSessionStructure4_budget_placed_ok_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec M A lim)) :=
  drop_session_structure4_placed_ok_at (i := 518) hh.codecHooks.dealloc (by decide)

set_option maxHeartbeats 800000 in
private theorem e2c_decPk_matchingPathB_main_gv_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hP3 : StageP3PrevEmptyVRegsPlacedStmt)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    {kitEnv4 : ∀ F0 peer, SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc F0 CryptoVerification.SignalSession.Cli.Slots.scopeKit peer (cliKitStk B))}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced CryptoVerification.SignalSession.Cli.Slots.scopeKit A lim DeserEnv))
    (hSkit : ∀ F0 peer, SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 CryptoVerification.SignalSession.Cli.Slots.scopeKit peer (cliKitStk B))
      (kitEnv4 F0 peer) CryptoVerification.SignalSession.Cli.Slots.scopeKit encodeRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : CryptoVerification.SignalSession.Cli.Slots.EncodeInjOn CryptoVerification.SignalSession.Cli.Slots.scopeKit)
    (hsub : ∀ r', Scope r' → CryptoVerification.SignalSession.Cli.Slots.scopeIn r')
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (evs_p1 : List AllocEvent)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkPathB ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer
      (cliKitStk B)).loadRel CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions y.g.peer.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hfits_main : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess))
    (hevs_main : ∀ evs234,
      MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess evs234 →
      DecPkEnv y.g (evs_p1 ++ evs234))
    (hsteps01 : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s1)
    (htr1 : s1.trace = s0.trace)
    (hro1 : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
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
       p1LoadedRecordAt CryptoVerification.SignalSession.Cli.Slots.scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
       LsTokenInit ∗
       CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  let hP2 : StageP2MatchedFramedCliPlacedStmt :=
    stageP2Matched_framed_cli_placed_ok
  have hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2MatchedEnv sess y.g.msg.identityKey) :=
    hfits_main.mono (fun _ h => Or.inl h)
  have hevs_mismatch : sess.state.remoteIdentity ≠ some y.g.msg.identityKey →
      ∀ evs_p2, StageP2MatchedMismatchEnv evs_p2 → DecPkEnv y.g (evs_p1 ++ evs_p2) := by
    intro hrem_ne evs_p2 hevs_p2
    exact hevs_main _ (Or.inl (by simp [StageP2MatchedEnv, hrem_ne, hevs_p2]))
  have hfits_p3 : sess.state.remoteIdentity = some y.g.msg.identityKey →
      ∀ evs_p2 recG, StageP2MatchedBridgeEnv evs_p2 → SessionExtraRel recG sess →
        SessionGhostValid recG sess →
        FitsEnv M lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
          (StageP3Env tdEnv recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins) := by
    intro hrem_eq evs_p2 recG hevs_p2 hex hgv evs_p3 hevs_p3
    rw [M.stepEvents_append]
    exact ((LibsignalBinary.Heap.fitsEvents_append M lim evs_p2 evs_p3 (M.stepEvents evs_p1 y.st)).mp
      (hfits_main (evs_p2 ++ evs_p3)
        (Or.inr ⟨hrem_eq, recG, hex, hgv,
          LibsignalBinary.Heap.SeqEnv.append hevs_p2 (Or.inl hevs_p3)⟩))).2
  have hfits_p4 : sess.state.remoteIdentity = some y.g.msg.identityKey →
      sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
      ∀ evs_p2 recG G₁ G' evs_p3 pt,
        StageP2MatchedBridgeEnv evs_p2 → SessionExtraRel recG sess →
        SessionGhostValid recG sess →
        CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv tdEnv recG G₁ sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          y.g.coins evs_p3 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .ok pt →
        FitsEnv M lim (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st)
          (StageP4MatchedEnv
            (cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer (cliKitStk B))
            (kitEnv4 y.g.F y.g.peer)
            (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
            (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
            CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
            y.g.peer.val y.g.msg.identityKey
            { sess with
              state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
              pendingPreKey := none
              pendingKyberPreKey := none }) := by
    intro hrem_eq hver evs_p2 recG G₁ G' evs_p3 pt hevs_p2 hex hgv hcl hdec_rel hevs_p3 hok evs_p4 hevs_p4
    have hstep_eq : M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st =
        M.stepEvents (evs_p2 ++ evs_p3) (M.stepEvents evs_p1 y.st) := by
      rw [List.append_assoc, M.stepEvents_append]
    rw [hstep_eq]
    have hmem : MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess
        ((evs_p2 ++ evs_p3) ++ evs_p4) := by
      rw [List.append_assoc]
      exact Or.inr ⟨hrem_eq, recG, hex, hgv,
        LibsignalBinary.Heap.SeqEnv.append hevs_p2 (Or.inr ⟨hver, G₁, G', pt, hcl, hdec_rel, hok,
          LibsignalBinary.Heap.SeqEnv.append hevs_p3 hevs_p4⟩)⟩
    exact ((LibsignalBinary.Heap.fitsEvents_append M lim (evs_p2 ++ evs_p3) evs_p4
      (M.stepEvents evs_p1 y.st)).mp (hfits_main _ hmem)).2
  have hevs_ok : sess.state.remoteIdentity = some y.g.msg.identityKey →
      sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
      ∀ evs_p2 recG G₁ G' evs_p3 pt evs_p4,
        StageP2MatchedBridgeEnv evs_p2 → SessionExtraRel recG sess →
        SessionGhostValid recG sess →
        CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv tdEnv recG G₁ sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          y.g.coins evs_p3 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .ok pt →
        StageP4MatchedStoreStepEnv
          (cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer (cliKitStk B))
          (kitEnv4 y.g.F y.g.peer)
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
          (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
          y.g.peer.val y.g.msg.identityKey
          { sess with
            state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
            pendingPreKey := none
            pendingKyberPreKey := none } evs_p4 →
        DecPkEnv y.g (((evs_p1 ++ evs_p2) ++ evs_p3) ++ evs_p4) := by
    intro hrem_eq hver evs_p2 recG G₁ G' evs_p3 pt evs_p4 hevs_p2 hex hgv hcl hdec_rel hevs_p3 hok hevs_p4
    have hmem : MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess
        (evs_p2 ++ (evs_p3 ++ evs_p4)) :=
      Or.inr ⟨hrem_eq, recG, hex, hgv,
        LibsignalBinary.Heap.SeqEnv.append hevs_p2 (Or.inr ⟨hver, G₁, G', pt, hcl, hdec_rel, hok,
          LibsignalBinary.Heap.SeqEnv.append hevs_p3 (Or.inr hevs_p4)⟩)⟩
    have happ : ((evs_p1 ++ evs_p2) ++ evs_p3) ++ evs_p4 = evs_p1 ++ (evs_p2 ++ (evs_p3 ++ evs_p4)) := by
      simp [List.append_assoc]
    rw [happ]; exact hevs_main _ hmem
  have hevs_err : sess.state.remoteIdentity = some y.g.msg.identityKey →
      sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
      ∀ evs_p2 recG G₁ G' evs_p3 e,
        StageP2MatchedBridgeEnv evs_p2 → SessionExtraRel recG sess →
        SessionGhostValid recG sess →
        CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        StageP3ErrEnv tdEnv recG G₁ sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          y.g.coins evs_p3 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .error e →
        e ≠ .panic → DecPkEnv y.g ((evs_p1 ++ evs_p2) ++ evs_p3) := by
    intro hrem_eq hver evs_p2 recG G₁ G' evs_p3 e hevs_p2 hex hgv hcl hdec_rel hevs_p3 _herr _hne_p
    have hmem : MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess (evs_p2 ++ evs_p3) :=
      Or.inr ⟨hrem_eq, recG, hex, hgv,
        LibsignalBinary.Heap.SeqEnv.append hevs_p2 (Or.inl (by simp [StageP3Env, hver]; exact ⟨G₁, hcl, hevs_p3⟩))⟩
    rw [List.append_assoc]; exact hevs_main _ hmem
  have hevs_verNe : sess.state.remoteIdentity = some y.g.msg.identityKey →
      sess.state.version ≠ y.g.msg.message.messageVersion.zeroExtend 32 →
      ∀ evs_p2 recG evs_p3, StageP2MatchedBridgeEnv evs_p2 → SessionExtraRel recG sess →
        SessionGhostValid recG sess →
        StageP3VerNeEnv recG sess.state evs_p3 → DecPkEnv y.g ((evs_p1 ++ evs_p2) ++ evs_p3) := by
    intro hrem_eq hver_ne evs_p2 recG evs_p3 hevs_p2 hex hgv hevs_p3
    have hmem : MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess (evs_p2 ++ evs_p3) :=
      Or.inr ⟨hrem_eq, recG, hex, hgv,
        LibsignalBinary.Heap.SeqEnv.append hevs_p2 (Or.inl (by simp [StageP3Env, hver_ne]; exact hevs_p3))⟩
    rw [List.append_assoc]; exact hevs_main _ hmem
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
  dsimp only [cliPollSessKitPlaced] at hload_rel
  obtain ⟨hloadS, hr_eq, hIn, hMatch, hSeeds, hRC, hPqLt⟩ :=
    pathB_scopeIn_and_match_of_decPkOkPathB hinjK hsub hfPeer hdecOk hload_rel hcur
  subst hr_eq
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  let F_p2 : SepProp :=
    ikit.identityAt y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity ∗
    kit.storeAt (y.g.stores + 0xf0#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
  let Fr_tail : SepProp :=
    pkKit.storeAt (y.g.stores + 0xc8#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.pub ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced_pathB (A := A.repAlloc) σ y.g.stores
    hsub hfPeer hdecOk (pid := pid) (sid := sid) (kid := kid) (kbk := kbk)
  have hstk_split := stackAt_subStack_sub_eq sp B (rootStack_le_subStack B) hsp_sub
  have hpre_split :
      stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt CryptoVerification.SignalSession.Cli.Slots.scopeKit A.repAlloc y.fut (some ⟨some sess⟩) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
       LsTokenInit ∗
       CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      ((stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
          y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
        p1LoadedRecordAt CryptoVerification.SignalSession.Cli.Slots.scopeKit A.repAlloc y.fut (some ⟨some sess⟩) ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack) ∗ F_p2) ∗ Fr_tail := by
    rw [hstk_split]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores_in))))))) ?_
    unfold cliPollStoresKitsAtPlaced F_p2 Fr_tail
    sep_frame
  refine sepWPp_conseq_pre hpre_split (sepWPp_pollGoal_frame_placed A lim DecPkEnv B S stk' y ?_)
  refine hP2 mmpl gh W B S CryptoVerification.SignalSession.Cli.Slots.scopeKit y sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 F_p2 _ _
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
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          stackAt sp rootStack := by
      rw [M.stepEvents_append evs_p1 evs_p2 y.st]
      exact hent_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_f')) hm_f
    have hdec_at := apiDecResultAt_proto_entails_decResAt A.repAlloc y.out
      (.invalidMessage .preKey .badCiphertext) err
    have hstores_out := cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc)
      (F0 := y.g.F) (Scope := CryptoVerification.SignalSession.Cli.Slots.scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened
    have hm2 : sf.mem ⊨
        apiDecResultAt A.repAlloc y.out (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer pid sid kid kbk σ
          y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
        (protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
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
          storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
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
        CryptoVerification.SignalSession.Cli.StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_of_reject CryptoVerification.SignalSession.Cli.StoresGhost.opened hS (err := err) nofun nofun
        (decPkDef_pathB_remId_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS htrusted hMatch hrem_ne)
    have hpost_goal := exit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y s0 sf
      (evs_p1 ++ evs_p2) CryptoVerification.SignalSession.Cli.StoresGhost.opened (.error err)
      (LsTokenInit ∗ coinsInstalledPlaced y.g.coinsP y.g.coins)
      (hevs_mismatch hrem_ne evs_p2 hevs_p2) hh hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm4
  · intro hrem_eq evs_p2 s2 g recG whisperMsgPtr whisperG preKeyMsgRem
      opkHi kyberPreKeyId signedPreKeyId hevs_p2 hwg_eq hex hmsg_fold hsteps12 hpc2 hrun2
      hs2_sp hsp_align2 htr2 _ _ _ hvregs2 hro2
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
      exact decPkDef_pathB_panic_pathB X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
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
      ikit.identityAt y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity ∗
      kit.storeAt (y.g.stores + 0xf0#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions ∗
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
    refine sepWPp_conseq_pre hpre_p3 fun R_p3 hm_p3 hL_p3 => ?_
    have hgv : SessionGhostValid recG sess :=
      e2c_sessionGhostValid_of_genP3Pre A lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
        s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
        y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 _ hex
        (Arm64.Satisfies.mono (by sep_frame) hm_p3)
    refine sepWPp_genP3_to_tailQpan_placed A lim DecPkEnv B S stk' y hpan_model ?_ R_p3 hm_p3 hL_p3
    refine hP3 (cliGhostExterns gh (cliExternsPlaced mmpl W)) W.C 0#64 W.Q.K
      hh.alloc (e2c_cliChainClone3_budget_placed_ok mmpl gh W hh)
      (e2c_cliSenderChainClone3_budget_placed_ok mmpl gh W hh)
      hTryDec (e2c_cliDropSessionStructure4_budget_placed_ok_at mmpl gh W hh)
      s0 s2 y.fut y.cx y.out 8#64 y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8 y.g.coins
      g recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message F_p3 _
      (hfits_p3 hrem_eq evs_p2 recG hevs_p2 hex hgv)
      (by decide) (Or.inr (distinctSid_of_decPkOkPathB hdecOk)) hSeeds hRC hPqLt
      hro2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot) htr20 hvregs2 ?_ ?_ ?_
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
      exact e2c_closure_pathB_p4_cont_pathB_placedBudget hDropNz mmpl gh W X B S Scope hh hReadFile hS stk' hneed hstk63
        y (hSkit y.g.F y.g.peer) sess ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 s'
        rngPtr whisperMsgPtr ptCap ptPtr y.g.msgG.msg preKeyMsgRem P_s' R
        opkHi kyberPreKeyId signedPreKeyId g recG G₁ G' pt
        hfPeer hdecOk hIn hloadS htrusted hMatch hrem_eq hex
        (hfits_p4 hrem_eq hver evs_p2 recG G₁ G' evs_p3 pt hevs_p2 hex hgv hcl hdec_rel hevs_p3 hok)
        (fun evs_p4 hevs_p4 =>
          hevs_ok hrem_eq hver evs_p2 recG G₁ G' evs_p3 pt evs_p4
            hevs_p2 hex hgv hcl hdec_rel hevs_p3 hok hevs_p4)
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
        (hevs_err hrem_eq hver evs_p2 recG G₁ G' evs_p3 e hevs_p2 hex hgv hcl hdec_rel hevs_p3 herr hne_p)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathB_err_pathB X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
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
        (hevs_verNe hrem_eq hver_ne evs_p2 recG evs_p3 hevs_p2 hex hgv hevs_p3)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathB_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS htrusted hMatch hrem_eq hver_ne)
        hent_f' hsf_sp htr_f hcs_f hvregs_f

private structure e2c_DpPollEntryPurePathBPlacedBudget [LibsignalPlacement]
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem} (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 : State) : Prop where
  ro : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem
  x0 : s0.readReg64 .x0 = y.out
  x1 : s0.readReg64 .x1 = y.fut
  x2 : s0.readReg64 .x2 = y.cx
  stk_le_sp : stk' ≤ s0.sp.toNat
  files_eq : s0.fs.files = y.g.F
  coins_lt : y.g.coins.length < 2 ^ 63
  filesOkPeer : CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope y.g.F y.g.peer.val
  decPkOk : DecPkOkPathB ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg
  fits : FitsEnv M lim y.st (DecPkEnv y.g)

private theorem e2c_dpPollPre_unpack_pathB_placedBudget [LibsignalPlacement]
    {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope F peer ∧ DecPkOkPathB ⟨W.C, W.Q⟩ Scope F peer me pm)
    (stk' : Nat) (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (R : SepProp) (s0 : State) (hpre : s0.mem ⊨
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre y s0 ∗ R) :
    e2c_DpPollEntryPurePathBPlacedBudget (X := X) (W := W) (Scope := Scope) stk' y s0 ∧
      (s0.mem ⊨ LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget.dpPollEntrySpatialPlaced stk' y s0 R) := by
  obtain ⟨hro, hpre0⟩ := CryptoVerification.LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  have h2 : s0.mem ⊨
      ⌜s0.readReg64 .x0 = y.out ∧ s0.readReg64 .x1 = y.fut ∧ s0.readReg64 .x2 = y.cx ∧
        (dpSlotArgsPlaced y.g).length = 13 ∧ stk' ≤ s0.sp.toNat⌝ ∗ (memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗ dpCxAt y.cx ∗
        (⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
            S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg ∧ FitsEnv M lim y.st (DecPkEnv y.g)⌝ ∗
          (⌜y.g.coins.length < 2 ^ 63⌝ ∗
            (storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
              protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
              protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
              coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit ∗
              CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
              A.pool lim y.st s0 ∗ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗ R)))) := by
    simpa only [dpPollSpecStateBudget, dpSlotPollKStatePlaced,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced, sepConj_assoc]
      using hpre0
  rw [satisfies_pure_sepConj] at h2
  rcases h2 with ⟨⟨hx0, hx1, hx2, _, hstk_sp⟩, h3⟩
  have h3' : s0.mem ⊨
      ⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
          S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg ∧ FitsEnv M lim y.st (DecPkEnv y.g)⌝ ∗
        (⌜y.g.coins.length < 2 ^ 63⌝ ∗ (dpCxAt y.cx ∗ (memRegion y.out 48 ∗
              dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
              storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
              protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
              protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
              coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit ∗
              CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
              A.pool lim y.st s0 ∗ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗ R))) := by
    convert h3 using 1
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at h3'
  rcases h3' with ⟨⟨hfiles, hfOk, hdOk, hfits⟩, h4⟩
  rw [satisfies_pure_sepConj] at h4
  rcases h4 with ⟨hcoins_lt, h5⟩
  obtain ⟨hfPeer, hdecOk⟩ := hSemOk y.g.F y.g.peer.val y.g.me.val y.g.msg hfOk hdOk
  have h5_cx := Satisfies.mono (sepConj_mono_left (dpCxAt_entails_memRegion32 y.cx)) h5
  refine ⟨⟨hro, hx0, hx1, hx2, hstk_sp, hfiles, hcoins_lt, hfPeer, hdecOk, hfits⟩, ?_⟩
  dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget.dpPollEntrySpatialPlaced]
  convert h5_cx using 1
  sep_ac_rfl

private theorem e2c_extHookStack_le_cliPollSess_loadCallStack [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    extHookStack ≤ loadCallStack (cliPollSessKitPlaced A F0 scopeKit peer (cliKitStk B)) := by
  dsimp only [extHookStack, loadCallStack, cliPollSessKitPlaced, cliPollSessKit,
    cliSessionStoreSpec, cliKitStk,
    CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadShimNeed,
    CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadPollNeed,
    CryptoVerification.RustHeap.allocHookStack]
  omega

private theorem e2c_closure_untrusted_pathB_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv)) (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r) (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g))
    (hevs_sub : ∀ evs,
      CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs)
    (R : SepProp) (s0 : State) (hpc : s0.pc = dpPollEntryPlaced) (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true) (hro0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out) (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx) (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkPathB ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗ dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗ memRegion y.cx 32 ∗
      storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗ coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit ∗ lsLogOff ∗ A.pool lim y.st s0 ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗ stackAt s0.sp stk' ∗ R) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
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
  let hUntrusted : StageP1UntrustedMangledPlacedStmt := stageP1_untrusted_mangled_placed_ok
  have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_pathB (A := A.repAlloc) σ y.g.stores
    hsub hfPeer hdecOk (pid := pid) (sid := sid) (kid := kid) (kbk := kbk)
  have hm_stores : s0.mem ⊨
      memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗ memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗ coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗ lsLogOff ∗ A.pool lim y.st s0 ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗ stackAt s0.sp stk' ∗ R :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hent_stores)))) hm_base
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1UntrustedCallStack_le_subStack (A := A.repAlloc)
    0#64 y.g.F scopeKit y.g.peer B
  have hp1_64 : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
      preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
      stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_untrusted s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
    b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  dsimp only [cliPollStoresKitsAtPlaced] at hm_flat
  let P_p1 : SepProp :=
    decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
    cells (y.fut + 0x70#64) 14 ∗ cells (y.fut + 0xe0#64) 4 ∗ memRegion (y.fut + 0x100#64) 336 ∗
    cells (y.fut + 0x250#64) 6 ∗ ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗ cells (y.fut + 0x2c8#64) 25 ∗
    ((y.fut + 0x390#64) ↦₈ b_390) ∗ ((y.fut + 0x398#64) ↦₆₄ u_398) ∗
    ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗ (sp ↦₆₄ v_sp0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
    ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
    ((sp + 0xc8#64) ↦₆₄ u_c8) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗ memRegion (sp + 0xd8#64) 348 ∗
    memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗ cells (sp + 0xa90#64) 6 ∗
    cells (s0.sp - 0x60#64) 12 ∗ memRegion y.out 48 ∗ lsLogOff ∗
    kit.storeAt (y.g.stores + 0xf0#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗ A.pool lim y.st s0 ∗
    stackAt sp (stageP1UntrustedCallStack kit ikit)
  let Fr_inner : SepProp :=
    cells (y.fut + 0x428#64) 8 ∗ cells (y.fut + 0x490#64) 4 ∗ ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
    coroUnusedP1At y.fut ∗ closStackUnusedUntrustedAt sp ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.pub ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit
  have hm_split : s0.mem ⊨ P_p1 ∗ (Fr_inner ∗ R) :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
      cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
      cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced, cliPreKeyStoreSpecPlaced,
      cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
      cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
  refine ⟨P_p1, Fr_inner ∗ R, hm_split, ?_⟩
  have hwp := hUntrusted
    (M := M) (A := A) (lim := lim) (ext := cliGhostExterns gh (cliExternsPlaced mmpl W))
    (Scope := scopeKit) (encRecord := encodeRecord)
    (kit := kit) (kitEnv := LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv)
    (ikit := ikit) (ikitEnv := LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv)
    (st := CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions) (ist := CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity) (st_b := y.st)
    y.g.peer y.g.msg.identityKey
    hh.alloc
    hh.codecHooks.dealloc
    ((show withVmPreserved noAllocShimSpec = sessionShimBudgetSpec from rfl) ▸ hh.codecHooks.shim)
    hh.codecHooks.alloc
    (e2c_hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)
    (cliPollSess_vtablesPlacedOk (A := A.repAlloc) y.g.F scopeKit y.g.peer σ hDropNz)
    (cliPollId_vtablesPlacedOk (A := A.repAlloc) y.g.F y.g.peer σ hDropNz)
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollSess_kitPlacedOkSE mmpl gh W hDropNz hh hRead hDeser)
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollId_kitPlacedOkI mmpl gh W hDropNz hh hRead)
    hp1_64 (e2c_extHookStack_le_cliPollSess_loadCallStack A.repAlloc B y.g.F y.g.peer) rfl rfl
    (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    hfits_p1 s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390
    hro0 (cliPollStageP1_fsAt_placed (runHooks_to_stages hh) y.g.F scopeKit y.g.peer B hfiles0)
    hpc hrun (by simpa [State.spAligned] using hsp) rfl hx0 hx1 hx2
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.SepWPp.mono_post_panic ?_ ?_ hwp
  · rintro sf P_f ⟨⟨opt, evs, hevs_p1, hload, _, htr_evs, hent_f⟩, hspf, hcs, hvregs, _⟩
    refine ⟨?_, hspf, closureCalleeSaved_toCalleeSavedPreserved hcs hvregs⟩
    intro hsteps hmf
    have htr_eq : sf.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollSessKit,
        cliSessionStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
        cliIdentityStoreSpec] using htr_evs
    have hloadRec : CryptoVerification.SignalSession.Cli.Slots.loadRec Scope y.g.F y.g.peer.val =
        .ok opt :=
      loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload
    have hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none := by
      rw [hS]
      exact decPkDef_of_trust_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadRec (Or.inr htrusted)
    have hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) s0.trace sf.trace :=
      slotOutTr_of_err CryptoVerification.SignalSession.Cli.StoresGhost.opened s0.trace sf.trace nofun nofun hans
    have hmf1 := Satisfies.mono (sepConj_mono_left hent_f) hmf
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hmf1
    rcases hmf1 with ⟨v_a8, v_b8, v_d0, hmf2⟩
    have hcoro := coro_of_p1_untrusted_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins b_4f2
    have hstk3280 := clos_stack_3280_of_p1_untrusted s0.sp s0
      0#64 v_a8 (y.fut + 0x390#64) v_b8 y.cx y.out v_d0
    have hres := apiDecResultAt_untrusted_entails_decResAt A.repAlloc y.out y.g.peer.val
    have hstores_back := cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc)
      (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened
    let Leftover : SepProp :=
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit
    have hmf_reord : sf.mem ⊨
        (apiDecResultAt A.repAlloc y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
            pid sid kid kbk σ y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          (((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evs y.st) sf ∗ Leftover ∗
          (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            memRegion (y.fut + 0xe0#64) 368 ∗ cells (y.fut + 0x250#64) 6 ∗
            ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗ processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
              (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
            ((y.fut + 0x390#64) ↦₈ 1#8) ∗ cells (y.fut + 0x398#64) 2 ∗ cells (y.fut + 0x428#64) 8 ∗
            cells (y.fut + 0x490#64) 4 ∗ ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗ coroUnusedP1At y.fut) ∗
          memRegion y.cx 32 ∗ (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
                (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
              stackAt sp (stageP1UntrustedCallStack kit ikit)) ∗
            ((sp ↦₆₄ 0#64) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
              ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗
              ((sp + 0xd0#64) ↦₆₄ v_d0) ∗ memRegion (sp + 0xd8#64) 348 ∗
              memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗
              cells (sp + 0xa90#64) 6 ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
              closStackUnusedUntrustedAt sp))) ∗ R := by
      have htrust_id : ikit.trustUpdate CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity y.g.peer.val
          y.g.msg.identityKey .receiving (.ok false) = CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity := rfl
      rw [htrust_id] at hmf2
      dsimp only [Fr_inner] at hmf2
      refine Satisfies.mono ?_ hmf2
      dsimp only [Leftover, cliPollStoresKitsAtPlaced]
      sep_frame
    rw [← preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
        ← stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
        show sp + 0xcd0#64 = s0.sp from sp_frame_sub_add s0.sp] at hmf_reord
    have hmf_folded : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗ lsLogOff ∗
          A.pool lim (M.stepEvents evs y.st) sf ∗ Leftover ∗ dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            stackAt sp (dpClosSubStack B) ∗ memRegion sp 3280)) ∗ R :=
      Satisfies.mono (sepConj_mono_left
        (sepConj_mono hres (sepConj_mono hstores_back
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono hcoro
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk3280)))))))))))))
        hmf_reord
    dsimp only [sp] at hmf_folded
    rw [← stackAt_poll_entry_split s0.sp B stk' hneed hstk63] at hmf_folded
    have hpost := dpPollPost_of_decResAt_placed A lim DecPkEnv B S stk' y s0 sf evs
      CryptoVerification.SignalSession.Cli.StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) Leftover
      hh (hevs_sub evs hevs_p1) hsteps htr_eq hout
    exact Satisfies.mono (sepConj_mono_left hpost) hmf_folded
  · intro _ _ hfalse _ _
    exact False.elim hfalse

private theorem e2c_p1Ok_post_eq_stageP2PostP1At_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ) (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (opt : Option (SessionRecord (List (BitVec 8)))) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
    (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      p1LoadedRecordAt Scope A.repAlloc y.fut opt ∗ ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗ cells (y.fut + 0x398#64) 2 ∗ ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗ ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
      ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ A.pool lim st_b s1) ∗
    (memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗ closStackUnusedP1OkAt sp ∗ memRegion y.out 48) =
    stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Scope A.repAlloc y.fut opt := by
  dsimp only [stageP2PostP1At, LibsignalBinary.Heap.RustCliAllocBudget.atState, cliPollSessKitPlaced, cliPollIdKitPlaced, cliIdStoreSpecFullPlaced,
    cliPollPkKitPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced, cliPollSpkKitPlaced,
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSignedPreKeyStoreSpecPlaced, cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced,
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced]
  sep_frame

private theorem e2c_p1Ok_recombine_entails_stageP2_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ) (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (opt : Option (SessionRecord (List (BitVec 8)))) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
    (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      p1LoadedRecordAt CryptoVerification.SignalSession.Cli.Slots.scopeKit A.repAlloc y.fut opt ∗ ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗ cells (y.fut + 0x398#64) 2 ∗ ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗ ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
      ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
      kit.storeAt (y.g.stores + 0xf0#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions ∗ ikit.identityAt y.g.stores
        (ikit.trustUpdate CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey
          .receiving (.ok true)) ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗ A.pool lim st_b s1 ∗
      stackAt sp (stageP1CallStack kit ikit)) ∗
    (memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗ closStackUnusedP1OkAt sp ∗ memRegion y.out 48 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP1CallStack kit ikit) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.pub ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit) ⊢
    stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt CryptoVerification.SignalSession.Cli.Slots.scopeKit A.repAlloc y.fut opt ∗
    preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
    LsTokenInit ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ stackAt sp (dpClosSubStack B) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le : stageP1CallStack kit ikit ≤ dpClosSubStack B :=
    stageP1CallStack_le_subStack (A := A.repAlloc)
      0#64 y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer B
  have hstores_back := cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc)
    (F0 := y.g.F) (Scope := CryptoVerification.SignalSession.Cli.Slots.scopeKit) (peer := y.g.peer)
    (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened
  have hp1_eq := e2c_p1Ok_post_eq_stageP2PostP1At_placedBudget (Scope := scopeKit)
    y st_b s0 s1 rngPtr v_a8 v_b8 v_d0 opt
  dsimp only at hp1_eq
  have hp1_ent := Entails.of_eq hp1_eq
  have hpm_ent := Entails.of_eq
    (preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg).symm
  have hstk_ent := Entails.of_eq
    (stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64).symm
  have h4 := sepConj_mono hp1_ent (sepConj_mono hstores_back (sepConj_mono hpm_ent hstk_ent))
  let Pass : SepProp :=
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32
  refine Entails.trans ?_ (Entails.trans (sepConj_mono_left h4 : _ ∗ Pass ⊢ _ ∗ Pass) ?_)
  · dsimp only [cliPollId_trustUpdate_eq_placed, cliPollStoresKitsAtPlaced, Pass,
      sp, σ, pid, sid, kid, kbk, kit, ikit]
    sep_frame
  · dsimp only [Pass, sp, σ, kit, ikit]
    sep_frame

private theorem e2c_sepWPp_bind_p1_false {prog : Program} {mid ret : BitVec 64}
    {s0 : State} {P P_p1 F : SepProp} {Q1 Q Qpan : State → SepProp → Prop}
    (hp1 : SepWPp prog mid s0 P_p1 Q1 (fun _ _ => False)) (hP : P = P_p1 ∗ F)
    (hnext : ∀ sm P_m, Steps prog s0 sm → sm.pc = mid → sm.status = .Running →
      Q1 sm P_m → SepWPp prog ret sm (P_m ∗ F) Q Qpan) :
    SepWPp prog ret s0 P Q Qpan := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hq1⟩ | ⟨_, _, _, hfalse⟩ |
    ⟨_, hoom⟩⟩ := hp1 (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm P_m hsteps hpcm hrunm hq1 R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact False.elim hfalse
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 800000 in
private theorem e2c_closure_trusted_pathB_of_matched_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv)) (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r) (_hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (StageP1OkEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) DeserEnv ReadEnv)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
        (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey))
    (R : SepProp) (s0 : State) (hpc : s0.pc = dpPollEntryPlaced) (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true) (hstk_sp : stk' ≤ s0.sp.toNat)
    (hro0 : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem) (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut) (hx2 : s0.readReg64 .x2 = y.cx) (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkPathB ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (_hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hm_base : s0.mem ⊨ LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget.dpPollEntrySpatialPlaced stk' y s0 R)
    (hMatched : ∀ (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
        (evs_p1 : List AllocEvent) (s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64), StageP1OkEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) DeserEnv ReadEnv)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
        (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey evs_p1 →
      (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer
        (cliKitStk B)).loadRel CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions y.g.peer.val (.ok (some r)) →
      r.currentSession = some sess → Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s1 →
      s1.trace = s0.trace → CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem → s1.sp = s0.sp - 0xcd0#64 →
      dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat → s1.pc = dpPollEntryPlaced + 0x0868#64 →
      s1.status = .Running → (s1.sp &&& 15#64 == 0#64) = true →
      StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
      let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
      let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
      let sp := s0.sp - 0xcd0#64
      SepWPp prog (s0.readReg64 .x30) s1
        (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
         p1LoadedRecordAt CryptoVerification.SignalSession.Cli.Slots.scopeKit A.repAlloc y.fut (some r) ∗
         preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
         protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
         protocolAddressAt A.repAlloc y.g.me y.g.meA ∗ coinsInstalledPlaced y.g.coinsP y.g.coins ∗
         storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ LsTokenInit ∗
         CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ stackAt sp (dpClosSubStack B) ∗
         memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32)
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R))) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
  dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget.dpPollEntrySpatialPlaced] at hm_base
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
  let sp := s0.sp - 0xcd0#64
  have hsp_align0 : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned] using hsp
  have hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat :=
    (subStack_le_sp_of_dpPollNeed hneed hstk_sp).1
  have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_pathB (A := A.repAlloc) σ y.g.stores
    hsub hfPeer hdecOk (pid := pid) (sid := sid) (kid := kid) (kbk := kbk)
  have hm_stores : s0.mem ⊨
      memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗ memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗ coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ A.pool lim y.st s0 ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗ stackAt s0.sp stk' ∗ R :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hent_stores)))) hm_base
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1CallStack_le_subStack (A := A.repAlloc)
    0#64 y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer B
  have hp1_64 : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
      preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
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
    cells (y.fut + 0x70#64) 14 ∗ cells (y.fut + 0xe0#64) 4 ∗ memRegion (y.fut + 0x100#64) 336 ∗
    ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗ cells (y.fut + 0x2c8#64) 25 ∗ ((y.fut + 0x390#64) ↦₈ b_390) ∗
    ((y.fut + 0x398#64) ↦₆₄ u_398) ∗ ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗ cells (y.fut + 0x428#64) 8 ∗
    cells (y.fut + 0x490#64) 4 ∗ ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗ (sp ↦₆₄ v_sp0) ∗
    ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
    ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
    ((sp + 0xc8#64) ↦₆₄ u_c8) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗ memRegion (sp + 0xd8#64) 348 ∗
    memRegion (sp + 0x3e0#64) 368 ∗ cells (s0.sp - 0x60#64) 12 ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
    kit.storeAt (y.g.stores + 0xf0#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗ A.pool lim y.st s0 ∗
    stackAt sp (stageP1CallStack kit ikit)
  let Fr_inner : SepProp :=
    memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut ∗ closStackUnusedP1OkAt sp ∗
    memRegion y.out 48 ∗ memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1CallStack kit ikit) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.pub ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit
  have hm_split : s0.mem ⊨ (P_p1 ∗ Fr_inner) ∗ R :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
      cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
      cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
  refine ⟨P_p1 ∗ Fr_inner, R, hm_split, ?_⟩
  have hwp := stageP1_ok_placed_inst hDropNz mmpl gh W B y.g.F y.g.peer y.g.msg.identityKey
    hh hReadFile hDeser y.st CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity hp1_64 rfl rfl
    (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    hfits_p1 s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390 b_4f2 hro0
    (cliPollStageP1_fsAt_placed hh y.g.F scopeKit y.g.peer B hfiles0)
    hpc hrun hsp_align0 rfl hx0 hx1 hx2
  refine e2c_sepWPp_bind_p1_false hwp rfl ?_
  intro s1 P_1 hsteps01 hpc1 hrun1 hq1
  rcases hq1 with ⟨⟨opt, evs_p1, hevs_p1, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
    hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
    hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, hro1⟩
  have htr1 : s1.trace = s0.trace := CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP1Ok_trace_eq_placed htr_evs
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
  have hrecomb := e2c_p1Ok_recombine_entails_stageP2_placedBudget stk' hneed hstk63 y
    (M.stepEvents evs_p1 y.st) s0 s1 coins v_a8 v_b8 v_d0 opt
  dsimp only at hrecomb
  refine sepWPp_conseq_pre hrecomb ?_
  cases opt with
  | none =>
    have hload0 : loadRec Scope y.g.F y.g.peer.val = .ok none :=
      loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload_rel
    obtain ⟨_, hloadS, _⟩ := hdecOk.loadedMatch
    rw [hload0] at hloadS; cases hloadS
  | some r =>
    obtain ⟨sess, hcur⟩ := CryptoVerification.SignalSession.Cli.RunProofs.Poll.currentSession_some_of_cliPollSessPlaced_loadRel hload_rel
    exact hMatched r sess evs_p1 s1 coins v_a8 v_b8 v_d0 hevs_p1 hload_rel hcur hsteps01 htr1 hro1
      hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1

/-- `SessionGhostValid`-strengthened counterpart of `MatchingPathBPollEnv`, routing the trusted
branch through `MatchingPathBGvMainEnv`. -/
def MatchingPathBGvPollEnv [LibsignalPlacement] (A_r : RustAlloc)
    (W : CliHooks) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (kitEnv4 : ∀ F0 peer, SessionStoreBudgetEnv
      (cliPollSessKitPlaced A_r F0 scopeKit peer (cliKitStk B)))
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let σ := cliKitStk B
  let kit := cliPollSessKitPlaced A_r g.F scopeKit g.peer σ
  let ikit := cliPollIdKitPlaced A_r g.F g.peer σ
  let kitEnv := cliPollSessBudgetEnv A_r g.F g.peer σ DeserEnv ReadEnv
  let ikitEnv := cliPollIdBudgetEnv A_r g.F g.peer σ ReadEnv
  if CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.trusted cliIo.rd g.F g.peer.val g.msg.identityKey = .ok false then
    CliDpPollUntrustedEnv (A := A_r) B ReadEnv DeserEnv g evs
  else
    SeqEnv
      (StageP1OkEnv kit kitEnv CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions ikit ikitEnv
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity g.peer.val g.msg.identityKey)
      (fun evs234 =>
        ∃ r sess,
          kit.loadRel CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions g.peer.val (.ok (some r)) ∧
          r.currentSession = some sess ∧
          MatchingPathBGvMainEnv A_r W B ReadEnv kitEnv4 tdEnv g sess evs234)
      evs

private theorem e2c_decPk_matchingPathB_poll_gv_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (hP3 : StageP3PrevEmptyVRegsPlacedStmt)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    {kitEnv4 : ∀ F0 peer, SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSkit : ∀ F0 peer, SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (kitEnv4 F0 peer) scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 508)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkPathB ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hevs_sub : ∀ g evs,
      MatchingPathBGvPollEnv A.repAlloc W B ReadEnv DeserEnv kitEnv4 tdEnv g evs → DecPkEnv g evs)
    (stk' : Nat) (hneed : (dpSlotPollKStatePlaced A lim DecPkEnv B S).need ≤ stk')
    (hstk63 : stk' ≤ 2 ^ 63) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) dpPollEntryPlaced
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')) := by
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ :=
    e2c_dpPollPre_unpack_pathB_placedBudget (W := W) (X := X) (Scope := Scope) hSemOk stk' y R s0 hpre
  have hfits_poll : FitsEnv M lim y.st
      (MatchingPathBGvPollEnv A.repAlloc W B ReadEnv DeserEnv kitEnv4 tdEnv y.g) :=
    hpure.fits.mono (hevs_sub y.g)
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget.dpPollEntrySpatialPlaced] at hm_base
    have hfits_u : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g) :=
      hfits_poll.mono (fun evs h => by simp [MatchingPathBGvPollEnv, htrusted, h])
    have hevs_u : ∀ evs, CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs →
        DecPkEnv y.g evs := fun evs h =>
      hevs_sub y.g evs (by simp [MatchingPathBGvPollEnv, htrusted, h])
    exact e2c_closure_untrusted_pathB_placedBudget A lim hDropNz mmpl gh W X B S Scope hh hReadFile hDeser
      hinjK hsub hS stk' hneed' hstk63 y hfits_u hevs_u R s0 hpc hrun hsp
      hpure.ro hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.decPkOk
      htrusted hm_base
  | true =>
    have hh_st := runHooks_to_stages hh
    have hne_false :
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey ≠ .ok false := by
      rw [htrusted]; decide
    have hfits_seq : FitsEnv M lim y.st
        (SeqEnv
          (StageP1OkEnv
            (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
            (cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) DeserEnv ReadEnv)
            CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions
            (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
            (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
            CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey)
          (fun evs234 =>
            ∃ r sess,
              (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B)).loadRel
                CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions y.g.peer.val (.ok (some r)) ∧
              r.currentSession = some sess ∧
              MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess evs234)) :=
      hfits_poll.mono (fun evs h => by simpa [MatchingPathBGvPollEnv, hne_false] using h)
    refine e2c_closure_trusted_pathB_of_matched_placedBudget hDropNz mmpl gh W X B S Scope hh_st hReadFile
      hDeser hinjK hsub hS stk' hneed' hstk63 y hfits_seq.seq_left R s0 hpc hrun hsp
      hpure.stk_le_sp hpure.ro hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer
      hpure.decPkOk hpure.coins_lt htrusted hm_base ?_
    intro r sess evs_p1 s1 rngPtr v_a8 v_b8 v_d0 hevs_p1 hload_rel hcur hsteps01 htr1 hro1
      hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
    have hfits_main : FitsEnv M lim (M.stepEvents evs_p1 y.st)
        (MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess) := by
      intro evs234 hmain
      exact ((LibsignalBinary.Heap.fitsEvents_append M lim evs_p1 evs234 y.st).mp
        (hfits_seq (evs_p1 ++ evs234) (LibsignalBinary.Heap.SeqEnv.append hevs_p1 ⟨r, sess, hload_rel, hcur, hmain⟩))).2
    have hevs_main : ∀ evs234,
        MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess evs234 →
        DecPkEnv y.g (evs_p1 ++ evs234) := by
      intro evs234 hmain
      apply hevs_sub y.g (evs_p1 ++ evs234)
      simp only [MatchingPathBGvPollEnv, hne_false, ↓reduceIte]
      exact LibsignalBinary.Heap.SeqEnv.append hevs_p1 ⟨r, sess, hload_rel, hcur, hmain⟩
    exact e2c_decPk_matchingPathB_main_gv_placedBudget hP3 hDropNz mmpl gh W X B S Scope hh_st hReadFile hDeser
      hSkit hTryDec hinjK hsub hS stk' hneed' hstk63 y evs_p1 r sess s0 s1
      rngPtr v_a8 v_b8 v_d0 R hpure.files_eq hpure.filesOkPeer hpure.decPkOk hpure.coins_lt
      htrusted hload_rel hcur hfits_main hevs_main hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1
      hsp_align1 hregs1

private theorem e2c_toSkeletonRunHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

private theorem e2c_withPanics_cliGhostExterns_eq (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) :
    Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      cliGhostExterns gh (cliExternsPlaced mmpl W) := by
  funext name
  by_cases hp : Rust.isPanicSymbol name = true
  · have hother : cliGhostExterns gh (cliExternsPlaced mmpl W) name = cliExternsPlaced mmpl W name :=
      cliGhostExterns_other gh (cliExternsPlaced mmpl W)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustAllocSymCli] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustDeallocSymCli] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustReallocSymCli] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustAllocZeroedSymCli] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustNoAllocShimSymCli] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsReadFileSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsReadStdinSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsMemsetSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsMemcpySym] at hp)
    unfold Rust.withPanics
    rw [hother]
    unfold cliExternsPlaced isCliPanicSymbolPlaced
    simp [hp]
  · simp [Rust.withPanics, hp]

/-- Parametric `SessionGhostValid`-strengthened Path-B `decrypt_prekey` slot envelope. -/
def DecPkD3MatchingPathBGvEnv [LibsignalPlacement] (A : RustAlloc)
    (W : CliHooks) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (kitEnv4 : ∀ F0 peer,
      SessionStoreBudgetEnv (cliPollSessKitPlaced A F0 scopeKit peer (cliKitStk B)))
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (g : DecPkGhost) : List AllocEvent → Prop :=
  MatchingPathBGvPollEnv A W B ReadEnv DeserEnv kitEnv4 tdEnv g

/-- `SessionGhostValid`-strengthened `SeqFree` `ReadEnv`-parametric CLI specialization of
`DecPkD3MatchingPathBGvEnv` wired to `SessDeserializeCancelEnv` and `cliPollSessSeqFreeBudgetEnv`. -/
abbrev DecPkD3MatchingPathBGvSeqFreeOfReadEnv [LibsignalPlacement] (A : RustAlloc)
    (W : CliHooks) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (g : DecPkGhost) : List AllocEvent → Prop :=
  DecPkD3MatchingPathBGvEnv A W B ReadEnv SessDeserializeCancelEnv
    (fun F0 peer =>
      cliPollSessSeqFreeBudgetEnv A F0 peer (cliKitStk B) SessDeserializeCancelEnv ReadEnv)
    tdEnv g

private theorem e2c_cliDecryptPrekey_slot_matchingPathB_gv_placedBudget_at_block [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {kitEnv4 : ∀ F0 peer,
      SessionStoreBudgetEnv (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSkit : ∀ F0 peer, SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (kitEnv4 F0 peer) scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStageP3 : StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkPathB ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hevs_sub : ∀ g evs,
      DecPkD3MatchingPathBGvEnv A.repAlloc W B ReadEnv DeserEnv kitEnv4 tdEnv g evs →
      DecPkEnv g evs)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok prog (lsmpl.base 520) (decPkSlotSpecPlaced A lim DecPkEnv S stk) := by
  have : IsLsBlockProg prog i (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))) := by
    rw [e2c_withPanics_cliGhostExterns_eq mmpl gh W]
    exact hcaller
  exact dpSlot_ok_state_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_placed_at_block (ext := cliGhostExterns gh (cliExternsPlaced mmpl W))
      (K₀_statePlaced A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_inv_vm A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_res_vm A lim DecPkEnv B S)
      (fun stk' h1 h2 => by
        rw [e2c_withPanics_cliGhostExterns_eq mmpl gh W]
        exact e2c_decPk_matchingPathB_poll_gv_placedBudget A lim ReadEnv DeserEnv tdEnv DecPkEnv
          hStageP3 hDropNz mmpl gh W X B S Scope
          (e2c_toSkeletonRunHooks hh) hRead hDeser hSkit hTryDec hinjK hsub hS hok hevs_sub
          stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, K₀_statePlaced,
        dpSlotPollKStatePlaced] at hstk ⊢; omega)
      hstk64 hi)

/-- `GvSeqFree` `ReadEnv`-parametric CLI slot `520` theorem over `DecPkD3MatchingPathBGvSeqFreeOfReadEnv`. -/
theorem decPkPathBSlotOk_gvSeqFree_of_readEnv_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets_placed.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hStageP3 : StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3MatchingPathBGvSeqFreeOfReadEnv A.repAlloc W cliRunBudgets_placed ReadEnv tdEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets_placed) :
    (slotsOfPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  fun stk h1 h2 =>
    e2c_cliDecryptPrekey_slot_matchingPathB_gv_placedBudget_at_block
      (prog := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
      A lim cliRunBudgets_placed mmpl gh W (by decide) X S scopeIn
      h547 hh hRead hDeser
      (fun F0 peer => cliPollSess_seqFreeKitPlacedOkSE mmpl gh W cliRunBudgets_placed F0 peer h547 hh hRead hDeser)
      hStageP3 hTryDec
      encodeInjOn_deserializeScopeP_Q (fun _ h => h) hdecPk
      (fun F peer me pm hf hd => ⟨(hfiles ▸ hf).1, hdecPkOk F peer me pm hd⟩)
      hsEnv stk (hneed ▸ h1) h2

/-! ## 3. Inclusion of `DecPkD3MatchingPathBGvSeqFreeOfReadEnv` into `W4RecvPrekeyCmkDom0` -/

section SubCmkDom0Helpers

open SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (IdentityKey SessionState)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (mismatchRemoteIkStrPlaced_length)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (encodeRecordPrev1Mem)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (sessionModelRel)
open CryptoVerification.LibsignalSession.NonVacuityWitness
  (A₀ ValidMemPlaced deserialize_pk0_serialize pk0 pk0_serialize_length
   satisfies_mapFresh_unmapped)
open CryptoVerification.LibsignalSessionRepr (chainAt vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr
  (noneCap optSenderChainAt optTailVecAt sessionStateAt)
open CryptoVerification.RustHeap (Unmapped vecAt vecBuf vecHeader vecU8At)
open LibsignalBinary.Heap (FreeOnlyEvs rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W4BinarySessStoreStepEnv W4BinaryStageP2MatchedWideEnv W4CloneACDomEnv W4CloneBDomEnv)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W4BinaryIdSaveStepEnvAllFixed W4BinaryIdTrustStepEnvAllFixed W4BinarySessLoadStepEnvAllFixed
   W4BinaryStageP1OkEnvAllFixed W4BinaryStageP1UntrustedEnvAllFixed
   W4BinaryStageP4MatchedWideEnvAllFixed)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (GhostCloneValid RecordGhostValid SessionCloneDom ghostCloneValid_of_sessionGhostValid
   sessionCloneDom_of_scopeIn sessionCloneDom_of_scopeKit_pq)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4StageP2MatchedCheckEnv W4StageP3WideEnv w4StageP2MatchedCheckEnv_of_bridge33
   w4StageP2MatchedCheckEnv_of_mismatch70 w4StageP3WideEnv_of_err w4StageP3WideEnv_of_okPrefix
   w4StageP3WideEnv_of_verNe)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
  (W4BoxedStoreStepEnv boxedDeallocPred_to_w4BoxedStoreStep rustDealloc8_freeOnly)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux (FreshBobPrev1Dom)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (SaveStepEnv TrustStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (LoadStepEnv StoreStepEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
  (RecordDeserializeCancelEnv sessDeserializeCancelEnv_imp_recordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitLoadPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget
  (StageP1OkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
  (StageP3Env StageP3ErrEnv StageP3OkPrefixEnv StageP3VerNeEnv stageP3TryDecryptEnvArgs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (StageP4MatchedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
  (CliDpPollUntrustedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
  (cliPollIdBudgetEnv cliPollSessBudgetEnv cliPollSessSeqFreeBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget (OptLoadDeserEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv TryDecryptEnvArgs)

/-! ### 3.1 Concrete `out1_freshBob` Dummy Witness (`receiverChains = []`, `enc = []`) -/

private def e2c_succInitArenaB : BitVec 64 := 0x10000#64

private def e2c_succInitSessGhost : SessionGhost :=
  { localIk := ⟨33#64, e2c_succInitArenaB + 512#64, pk0.serialize⟩
    remoteIk := ⟨0#64, 1#64, []⟩
    root := ⟨32#64, e2c_succInitArenaB + 560#64⟩
    chainsCap := 0#64
    chainsPtr := 8#64
    chains := []
    alice := ⟨0#64, 1#64, []⟩
    pq := ⟨0#64, 1#64⟩
    sender := none
    pending := none
    kyber := none
    regIds := List.replicate 8 0#8 }

private def e2c_succInitSessVal : Session (List (BitVec 8)) :=
  { state := { sessionVersion := 0#32
               localIdentity := ⟨pk0⟩
               remoteIdentity := none
               rootKey := 0#256
               previousCounter := 0#32
               senderChain := none
               receiverChains := []
               pendingPreKey := false
               pqRatchetState := [] }
    pendingPreKey := none
    pendingKyberPreKey := none
    localRegistrationId := 0#32
    remoteRegistrationId := 0#32
    aliceBaseKey := [] }

private theorem e2c_succInit_localIk_eq :
    vecGhostAt A₀ e2c_succInitSessGhost.localIk e2c_succInitArenaB =
      (e2c_succInitArenaB ↦₆₄ 33#64) ∗
      ((e2c_succInitArenaB + 8#64) ↦₆₄ (e2c_succInitArenaB + 512#64)) ∗
      ((e2c_succInitArenaB + 16#64) ↦₆₄ 33#64) ∗
      ((e2c_succInitArenaB + 512#64) ↦ₛ pk0.serialize) := by
  unfold vecGhostAt vecU8At vecHeader e2c_succInitSessGhost A₀
  simp only [pk0_serialize_length, BitVec.ofNat_eq_ofNat, true_and,
    show (33#64 : BitVec 64).toNat < 2 ^ 63 by decide,
    show (33#64 : BitVec 64).toNat - 33 = 0 by decide,
    memRegion_zero, emp_sepConj, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hpure : (33 ≤ (33#64 : BitVec 64).toNat ∧ e2c_succInitArenaB + 512#64 ≠ 0#64) ↔ True := by
    unfold e2c_succInitArenaB; decide
  have hif : ¬ ((33#64 : BitVec 64) = 0#64) := by decide
  rw [propext hpure, pure_true, emp_sepConj]
  simp only [hif, ↓reduceIte]
  sep_ac_rfl

private theorem e2c_succInit_emptyVecU8At_eq (off : BitVec 64) :
    vecU8At A₀ (e2c_succInitArenaB + off) 0#64 1#64 [] =
      ((e2c_succInitArenaB + off) ↦₆₄ 0#64) ∗
      ((e2c_succInitArenaB + off + 8#64) ↦₆₄ 1#64) ∗
      ((e2c_succInitArenaB + off + 16#64) ↦₆₄ 0#64) := by
  unfold vecU8At vecHeader A₀
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, true_and,
    show (0#64 : BitVec 64).toNat < 2 ^ 63 by decide,
    ↓reduceIte, sepConj_emp,
    BitVec.add_assoc]
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (1#64 : BitVec 64) ≠ 0#64) ↔ True := by decide
  rw [propext hpure, pure_true, sepConj_emp]

private theorem e2c_succInit_rootKey_eq :
    vecU8At A₀ (e2c_succInitArenaB + 48#64) 32#64 (e2c_succInitArenaB + 560#64) (keyToBytes32 0#256) =
      ((e2c_succInitArenaB + 48#64) ↦₆₄ 32#64) ∗
      ((e2c_succInitArenaB + 56#64) ↦₆₄ (e2c_succInitArenaB + 560#64)) ∗
      ((e2c_succInitArenaB + 64#64) ↦₆₄ 32#64) ∗
      ((e2c_succInitArenaB + 560#64) ↦ₛ keyToBytes32 0#256) := by
  have hlen : (keyToBytes32 0#256).length = 32 := by simp [keyToBytes32]
  unfold vecU8At vecHeader A₀
  simp only [hlen, BitVec.ofNat_eq_ofNat, true_and,
    show (32#64 : BitVec 64).toNat < 2 ^ 63 by decide,
    show (32#64 : BitVec 64).toNat - 32 = 0 by decide,
    memRegion_zero, emp_sepConj, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hpure : (32 ≤ (32#64 : BitVec 64).toNat ∧ e2c_succInitArenaB + 560#64 ≠ 0#64) ↔ True := by
    unfold e2c_succInitArenaB; decide
  have hif : ¬ ((32#64 : BitVec 64) = 0#64) := by decide
  rw [propext hpure, pure_true, emp_sepConj]
  simp only [hif, ↓reduceIte]
  sep_ac_rfl

private theorem e2c_succInit_chains_eq :
    vecAt A₀ 104 8 (chainAt A₀) (e2c_succInitArenaB + 72#64) 0#64 8#64 [] =
      ((e2c_succInitArenaB + 72#64) ↦₆₄ 0#64) ∗
      ((e2c_succInitArenaB + 80#64) ↦₆₄ 8#64) ∗
      ((e2c_succInitArenaB + 88#64) ↦₆₄ 0#64) := by
  unfold vecAt vecHeader vecBuf A₀
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, true_and,
    show (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 by decide,
    ↓reduceIte, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (8#64 : BitVec 64) ≠ 0#64) ↔ True := by decide
  rw [propext hpure, pure_true, sepConj_emp]

private theorem e2c_succInit_sessionStateAt_satisfiable :
    ∃ m : Memory, m ⊨ sessionStateAt A₀ e2c_succInitArenaB e2c_succInitSessGhost e2c_succInitSessVal.state ∗ emp := by
  let B := e2c_succInitArenaB
  let mBase := Memory.empty.mapFresh B 1024 Perm.rw
  have hunm : Unmapped Memory.empty B 1024 := fun _ _ => rfl
  have hsat0 := satisfies_mapFresh_unmapped (satisfies_emp Memory.empty) hunm
  have h0 : ValidMemPlaced mBase B (memRegion (B + BitVec.ofNat 64 0) 1024 ∗ emp) :=
    ⟨mBase, by simpa only [BitVec.add_zero] using hsat0, rfl, Memory.KeepsFrozen.refl mBase⟩
  have h1 := h0.step64 (off' := 8) (rem' := 1016) 33#64
  have h2 := h1.step64 (off' := 16) (rem' := 1008) (B + 512#64)
  have h3 := h2.step64 (off' := 24) (rem' := 1000) 33#64
  have h4 := h3.step64 (off' := 32) (rem' := 992) 0#64
  have h5 := h4.step64 (off' := 40) (rem' := 984) 1#64
  have h6 := h5.step64 (off' := 48) (rem' := 976) 0#64
  have h7 := h6.step64 (off' := 56) (rem' := 968) 32#64
  have h8 := h7.step64 (off' := 64) (rem' := 960) (B + 560#64)
  have h9 := h8.step64 (off' := 72) (rem' := 952) 32#64
  have h10 := h9.step64 (off' := 80) (rem' := 944) 0#64
  have h11 := h10.step64 (off' := 88) (rem' := 936) 8#64
  have h12 := h11.step64 (off' := 96) (rem' := 928) 0#64
  have h13 := h12.step64 (off' := 104) (rem' := 920) 0#64
  have h14 := h13.step64 (off' := 112) (rem' := 912) 1#64
  have h15 := h14.step64 (off' := 120) (rem' := 904) 0#64
  have h16 := h15.step64 (off' := 128) (rem' := 896) 0#64
  have h17 := h16.step64 (off' := 136) (rem' := 888) 1#64
  have h18 := h17.step64 (off' := 144) (rem' := 880) 0#64
  have h19 := h18.step64 (off' := 152) (rem' := 872) noneCap
  have h20 := h19.stepSkip (off' := 248) (rem' := 776) 96
  have h21 := h20.step64 (off' := 256) (rem' := 768) noneCap
  have h22 := h21.stepSkip (off' := 296) (rem' := 728) 40
  have h23 := h22.step64 (off' := 304) (rem' := 720) noneCap
  have h24 := h23.stepSkip (off' := 328) (rem' := 696) 24
  have h25 := h24.step32 (off' := 332) (rem' := 692) 0#32
  have h26 := h25.step32 (off' := 336) (rem' := 688) 0#32
  have h27 := h26.stepBytes (off' := 344) (rem' := 680) 8 (List.replicate 8 0#8) rfl
  have h28 := h27.stepDrop (off' := 512) (rem' := 512) 168
  have h29 := h28.stepBytes (off' := 545) (rem' := 479) 33 pk0.serialize pk0_serialize_length
  have h30 := h29.stepDrop (off' := 560) (rem' := 464) 15
  have h31 := h30.stepBytes (off' := 592) (rem' := 432) 32 (keyToBytes32 0#256)
    (by simp [keyToBytes32])
  have h32 := h31.stepDrop (off' := 1024) (rem' := 0) 432
  rcases h32 with ⟨m, hsat, _, _⟩
  refine ⟨m, ?_⟩
  rw [memRegion_zero, emp_sepConj, sepConj_emp] at hsat
  dsimp only [B] at hsat
  unfold sessionStateAt
  rw [sepConj_emp, satisfies_pure_sepConj]
  refine ⟨⟨deserialize_pk0_serialize, rfl, rfl, rfl, rfl, pk0_serialize_length, fun h => nomatch h⟩,
    ?_⟩
  change m ⊨
    vecGhostAt A₀ e2c_succInitSessGhost.localIk e2c_succInitArenaB ∗
    vecU8At A₀ (e2c_succInitArenaB + 24#64) 0#64 1#64 [] ∗
    vecU8At A₀ (e2c_succInitArenaB + 48#64) 32#64 (e2c_succInitArenaB + 560#64) (keyToBytes32 0#256) ∗
    vecAt A₀ 104 8 (chainAt A₀) (e2c_succInitArenaB + 72#64) 0#64 8#64 [] ∗
    vecU8At A₀ (e2c_succInitArenaB + 96#64) 0#64 1#64 [] ∗
    vecU8At A₀ (e2c_succInitArenaB + 120#64) 0#64 1#64 [] ∗
    optSenderChainAt A₀ (e2c_succInitArenaB + 144#64) none none ∗
    optTailVecAt A₀ 48 (e2c_succInitArenaB + 248#64) none ∗
    optTailVecAt A₀ 32 (e2c_succInitArenaB + 296#64) none ∗
    ((e2c_succInitArenaB + 328#64) ↦₃₂ 0#32) ∗
    ((e2c_succInitArenaB + 332#64) ↦₃₂ 0#32) ∗
    ((e2c_succInitArenaB + 336#64) ↦ₛ List.replicate 8 0#8)
  unfold optSenderChainAt optTailVecAt
  rw [e2c_succInit_localIk_eq, e2c_succInit_emptyVecU8At_eq 24#64, e2c_succInit_rootKey_eq,
    e2c_succInit_chains_eq, e2c_succInit_emptyVecU8At_eq 96#64, e2c_succInit_emptyVecU8At_eq 120#64]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.reduceSub] at hsat ⊢
  refine Eq.mp (congrArg (fun P => m ⊨ P) ?_) hsat
  sep_ac_rfl

private theorem e2c_succInit_sessionGhostValid :
    SessionGhostValid e2c_succInitSessGhost e2c_succInitSessVal := by
  refine ⟨?_, ?_⟩
  · unfold sessionModelRel e2c_succInitSessGhost e2c_succInitSessVal
    refine ⟨trivial, trivial, rfl, by decide, by decide⟩
  · obtain ⟨m, hm⟩ := e2c_succInit_sessionStateAt_satisfiable
    exact ⟨A₀, e2c_succInitArenaB, m, emp, hm⟩

private theorem e2c_succInit_sessionCloneDom :
    SessionCloneDom 16384 e2c_succInitSessVal where
  rc_len := by decide
  seeds32 := fun _ hc => nomatch hc
  alice_len := by decide
  kyber_cap := fun _ hk => nomatch hk
  pq_len := by decide

private theorem e2c_succInit_freshBobPrev1Dom :
    FreshBobPrev1Dom 16384 2097152 2457152 e2c_succInitSessGhost e2c_succInitSessVal [] where
  rc_nil := rfl
  gv := e2c_succInit_sessionGhostValid
  dom := e2c_succInit_sessionCloneDom
  prev_len := Nat.zero_le _
  total_len := of_decide_eq_true (by with_unfolding_all rfl)

/-! ### 3.2 Stage P1, Stage P2 (`Matched`), Stage P3 (`prevEmpty`), and Stage P4 (`SeqFree`) Inclusions -/

private theorem e2c_seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) : SeqEnv E₁' E₂' evs :=
  h.elim (fun hE1 => Or.inl (h1 evs hE1))
    fun ⟨e₁, e₂, heq, hE1, hE2⟩ => Or.inr ⟨e₁, e₂, heq, h1 e₁ hE1, h2 e₂ hE2⟩

private theorem e2c_seqEnv_optStage_nil_left {E F : List AllocEvent → Prop}
    {evs : List AllocEvent} (h : F evs) : SeqEnv (OptStageEnv E) F evs :=
  Or.inr ⟨[], evs, rfl, Or.inl (fun _ hm => nomatch hm), h⟩

private theorem e2c_seqEnv_optStage_step {E E' F F' : List AllocEvent → Prop}
    (hE : ∀ evs, E evs → E' evs) (hF : ∀ evs, F evs → F' evs)
    {evs : List AllocEvent} (h : SeqEnv E F evs) : SeqEnv (OptStageEnv E') F' evs :=
  e2c_seqEnv_mono (fun e he => Or.inr (hE e he)) hF h

private theorem e2c_optLoadDeser_dcan_sub_ofBytes
    {gr : Except Unit (List (BitVec 8))} {evs : List AllocEvent}
    (h : OptLoadDeserEnv scopeKit SessDeserializeCancelEnv gr evs) :
    OptLoadDeserEnv scopeKit (ofBytesEnv RecordDeserializeCancelEnv) gr evs := by
  unfold OptLoadDeserEnv at h ⊢
  split at h
  · obtain ⟨r, henc, hsc, hd⟩ := h
    exact ⟨r, henc, hsc, sessDeserializeCancelEnv_imp_recordDeserializeCancelEnv hd⟩
  · exact h

private theorem e2c_loadPoll_dcan_sub_ofBytes
    {F0 : FsFiles} {peer : AddrGhost} {evs : List AllocEvent}
    (h : cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
      (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
      SessDeserializeCancelEnv F0 StoresGhost.opened.sessions peer.val evs) :
    cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
      (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
      (ofBytesEnv RecordDeserializeCancelEnv) F0 StoresGhost.opened.sessions peer.val evs :=
  e2c_seqEnv_mono (fun _ ha => ha)
    (fun _ hg => e2c_seqEnv_mono (fun _ hg' => hg')
      (fun _ hd => e2c_seqEnv_mono (fun _ ho => e2c_optLoadDeser_dcan_sub_ofBytes ho)
        (fun _ hf => hf) hd) hg) h

private theorem e2c_loadStep_sub_w4SessLoadAllFixed [LibsignalPlacement] {A : RustAlloc}
    {B : RunBudgets} {F0 : FsFiles} {peer : AddrGhost} {evs : List AllocEvent}
    (h : LoadStepEnv
      (cliPollSessKitPlaced A F0 scopeKit peer (cliKitStk B))
      (cliPollSessBudgetEnv A F0 peer (cliKitStk B) SessDeserializeCancelEnv
        (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.sessions peer.val evs) :
    W4BinarySessLoadStepEnvAllFixed cliIo.rd F0 peer evs :=
  boxedDeallocPred_to_w4BoxedStoreStep (DeallocEv := (· = rustDeallocEvents 24 8))
    (fun _ hd => rustDealloc8_freeOnly hd)
    (e2c_seqEnv_mono (fun _ hb => hb)
      (fun _ hp => e2c_seqEnv_mono (fun _ hl => e2c_loadPoll_dcan_sub_ofBytes hl)
        (fun _ hd => hd) hp) h)

private theorem e2c_trustStep_sub_w4IdTrustAllFixed [LibsignalPlacement] {A : RustAlloc}
    {B : RunBudgets} {F0 : FsFiles} {peer : AddrGhost} {remoteIk : IdentityKey}
    {evs : List AllocEvent}
    (h : TrustStepEnv
      (cliPollIdKitPlaced A F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A F0 peer (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.identity peer.val remoteIk .receiving evs) :
    W4BinaryIdTrustStepEnvAllFixed cliIo.rd F0 peer remoteIk evs :=
  boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h

private theorem e2c_cliDpPollUntrustedEnv_sub_w4StageP1UntrustedAllFixed [LibsignalPlacement]
    {A : RustAlloc} {B : RunBudgets} {g : DecPkGhost} {evs : List AllocEvent}
    (h : CliDpPollUntrustedEnv (A := A) B (ReadFileRuleEnvFixed cliIo.rd)
      SessDeserializeCancelEnv g evs) :
    W4BinaryStageP1UntrustedEnvAllFixed cliIo.rd g.F g.peer g.msg.identityKey evs :=
  e2c_seqEnv_mono
    (fun _ hl => e2c_loadStep_sub_w4SessLoadAllFixed hl)
    (fun _ ht => e2c_seqEnv_mono
      (fun _ htr => e2c_trustStep_sub_w4IdTrustAllFixed htr)
      (fun _ hcl => hcl) ht)
    h

private theorem e2c_stageP1OkEnv_sub_w4StageP1OkAllFixed [LibsignalPlacement]
    {A : RustAlloc} {B : RunBudgets} {g : DecPkGhost} {evs : List AllocEvent}
    (h : StageP1OkEnv
      (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B))
      (cliPollSessBudgetEnv A g.F g.peer (cliKitStk B) SessDeserializeCancelEnv
        (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.sessions
      (cliPollIdKitPlaced A g.F g.peer (cliKitStk B))
      (cliPollIdBudgetEnv A g.F g.peer (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.identity g.peer.val g.msg.identityKey evs) :
    W4BinaryStageP1OkEnvAllFixed cliIo.rd g.F g.peer g.msg.identityKey evs :=
  e2c_seqEnv_mono
    (fun _ hl => e2c_loadStep_sub_w4SessLoadAllFixed hl)
    (fun _ htr => Or.inr (e2c_trustStep_sub_w4IdTrustAllFixed htr))
    h

private theorem e2c_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedCheck {evs : List AllocEvent}
    (h : StageP2MatchedBridgeEnv evs) :
    W4StageP2MatchedCheckEnv evs := by
  rw [h]
  exact w4StageP2MatchedCheckEnv_of_bridge33
    (Or.inr ⟨rustAllocEvents 33 1, rustDeallocEvents 33 1, rfl, rfl, Or.inl rfl⟩)

private theorem e2c_stageP2MatchedMismatchEnv_sub_w4StageP2MatchedCheck {evs : List AllocEvent}
    (h : StageP2MatchedMismatchEnv evs) :
    W4StageP2MatchedCheckEnv evs := by
  rcases h with hbr | ⟨e₁, e₂, rfl, hbr, e_str, e_free, hstr, hfree, rfl⟩
  · exact e2c_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedCheck hbr
  · rw [hbr, hstr]
    change W4StageP2MatchedCheckEnv
      ((rustAllocEvents 33 1 ++ rustDeallocEvents 33 1) ++ (rustAllocEvents _ 1 ++ e_free))
    rw [mismatchRemoteIkStrPlaced_length, List.append_assoc]
    exact w4StageP2MatchedCheckEnv_of_mismatch70
      (Or.inr ⟨rustAllocEvents 33 1,
        rustDeallocEvents 33 1 ++ (rustAllocEvents 70 1 ++ e_free), rfl, rfl,
        Or.inr ⟨rustDeallocEvents 33 1, rustAllocEvents 70 1 ++ e_free, rfl, rfl,
          Or.inr ⟨rustAllocEvents 70 1, e_free, rfl, rfl, hfree⟩⟩⟩)

private theorem e2c_stageP2MatchedEnv_sub_w4StageP2MatchedCheck
    {sess : Session (List (BitVec 8))} {remIdKey : IdentityKey} {evs : List AllocEvent}
    (h : StageP2MatchedEnv sess remIdKey evs) :
    W4StageP2MatchedCheckEnv evs := by
  unfold StageP2MatchedEnv at h
  split at h
  · exact e2c_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedCheck h
  · exact e2c_stageP2MatchedMismatchEnv_sub_w4StageP2MatchedCheck h

private theorem e2c_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedWide {α : Type}
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    {evs : List AllocEvent} (h : StageP2MatchedBridgeEnv evs) :
    W4BinaryStageP2MatchedWideEnv DecEnv TrialEnv DropEnv xs g_arch r_arch evs :=
  Or.inl (e2c_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedCheck h)

private theorem e2c_stageP2MatchedEnv_sub_w4StageP2MatchedWide {α : Type}
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    {sess : Session (List (BitVec 8))} {remIdKey : IdentityKey} {evs : List AllocEvent}
    (h : StageP2MatchedEnv sess remIdKey evs) :
    W4BinaryStageP2MatchedWideEnv DecEnv TrialEnv DropEnv xs g_arch r_arch evs :=
  Or.inl (e2c_stageP2MatchedEnv_sub_w4StageP2MatchedCheck h)

private theorem e2c_stageP3OkPrefixEnv_sub_w4StageP3Wide
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
    (e2c_seqEnv_mono hClone (fun _ ht => e2c_seqEnv_mono hTd (fun _ hf => hf) ht) h)

private theorem e2c_stageP3ErrEnv_sub_w4StageP3Wide
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
    (e2c_seqEnv_mono hClone (fun _ ht => e2c_seqEnv_mono hTd (fun _ hv => hv) ht) h)

private theorem e2c_stageP3VerNeEnv_sub_w4StageP3Wide
    {CloneEnv : List AllocEvent → Prop} (TryDecEnv : List AllocEvent → Prop)
    {recG : SessionGhost} {st : SessionState (List (BitVec 8))}
    (hClone : ∀ e, SegCloneEnv recG st e → CloneEnv e)
    {evs : List AllocEvent}
    (h : StageP3VerNeEnv recG st evs) :
    W4StageP3WideEnv CloneEnv TryDecEnv evs :=
  w4StageP3WideEnv_of_verNe (e2c_seqEnv_mono hClone (fun _ hm => hm) h)

private theorem e2c_saveStep_sub_w4IdSaveAllFixed [LibsignalPlacement] {A : RustAlloc}
    {B : RunBudgets} {F0 : FsFiles} {peer : AddrGhost} {remoteIk : IdentityKey}
    {evs : List AllocEvent}
    (h : SaveStepEnv
      (cliPollIdKitPlaced A F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A F0 peer (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.identity peer.val remoteIk evs) :
    W4BinaryIdSaveStepEnvAllFixed cliIo.rd F0 peer remoteIk evs :=
  boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h

private theorem e2c_storeStepSeqFree_sub_w4SessStore [LibsignalPlacement] {A : RustAlloc}
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

private theorem e2c_stageP4MatchedSeqFree_sub_w4StageP4MatchedAllFixed [LibsignalPlacement]
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
      e2c_seqEnv_optStage_step
        (fun _ hs => e2c_saveStep_sub_w4IdSaveAllFixed hs)
        (fun _ hf => e2c_seqEnv_optStage_nil_left hf) hsaveErr⟩
  · rcases hstore with hsave | ⟨e_save, e_rest, rfl, hsave, hst_free⟩
    · exact ⟨⟨0#64, 0#64, none⟩, ⟨none⟩, hgv_none, Or.inl rfl,
        Or.inl (Or.inr (e2c_saveStep_sub_w4IdSaveAllFixed hsave))⟩
    · rcases hst_free with hst | ⟨e_st, e_free, rfl, hst, hfree⟩
      · obtain ⟨g_out0, r_out0, hgv, hr, hst'⟩ := e2c_storeStepSeqFree_sub_w4SessStore hst
        exact ⟨g_out0, r_out0, hgv, hr,
          Or.inr ⟨e_save, e_rest, rfl, Or.inr (e2c_saveStep_sub_w4IdSaveAllFixed hsave),
            Or.inl (Or.inr hst')⟩⟩
      · obtain ⟨g_out0, r_out0, hgv, hr, hst'⟩ := e2c_storeStepSeqFree_sub_w4SessStore hst
        exact ⟨g_out0, r_out0, hgv, hr,
          Or.inr ⟨e_save, e_st ++ e_free, rfl, Or.inr (e2c_saveStep_sub_w4IdSaveAllFixed hsave),
            Or.inr ⟨e_st, e_free, rfl, Or.inr hst', hfree⟩⟩⟩

/-! ### 3.3 `encodeRecord` Overhead, Post-`try_decrypt` `TopStateTight`, and `W4BinaryCallSiteDomCmk0` Assembly -/

open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession
  (ChainKey Crypto MessageKeyGenerator MessageType Mut PrivateKey PublicKey RatchetState
   ReceiverChain SenderChain ShaCompress SignalProtocolError Spqr TripleRatchet aesCbcDecrypt
   liftE maxForwardJumps maxMessageKeys zoom)
open CryptoGames.LibsignalSessionApi (PendingKyberPreKey PendingPreKey)
open CryptoVerification.E2E.Record
  (bytesField encChainKey encMessageKey encPendingKyber encPendingPreKey encReceiverChain
   encSenderChain encSession int32Field lenField msgField optUint32Field uint32Field uint64Field)
open CryptoVerification.LibsignalProtoCodec (WireType encodeKey encodeVarint encodeVarintAux)
open CryptoVerification.LibsignalSpqrV1 (ChainParams MlKem)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.SignalSession.Cli (ReadRule)
open CryptoVerification.SignalSession.Cli.Slots (cliSessLoadRel_eq_loadRec)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (RecordSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (TopStateTight topStateTight_length_le topStateTight_spqrV1_recv)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
  (W4BinaryCallSiteDomCmk0 W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
   mkW4RecvPrekeyWideCmkSrSlotParamsOf)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4BinaryCallSiteDomCmk W4BinaryRecvPrekeyParamsCmk W4FailedTryDecryptCallCmk
   W4RecvPrekeyRealParamsCmk W4TryDecryptCallCmk W4TryDecryptCallDomCmkOf)

private theorem e2c_forall_of_zip_eq_len {α β : Type} {P : β → Prop} :
    ∀ {xs : List α} {ys : List β},
      xs.length = ys.length →
      (∀ p ∈ xs.zip ys, P p.2) →
      ∀ y ∈ ys, P y
  | [], [], _, _ => fun _ hy => nomatch hy
  | x :: xs, _ :: ys, hlen, hzip => fun z hz => by
    rcases List.mem_cons.mp hz with rfl | hrest
    · exact hzip (x, z) (List.Mem.head _)
    · exact e2c_forall_of_zip_eq_len (Nat.succ.inj hlen)
        (fun p hp => hzip p (List.Mem.tail _ hp)) z hrest

private theorem e2c_mk_len_le_of_sessionGhostValid {G : SessionGhost}
    {s : Session (List (BitVec 8))} (hgv : SessionGhostValid G s) :
    ∀ c ∈ s.state.receiverChains, c.messageKeys.length ≤ 2000 := by
  have hcl := ghostCloneValid_of_sessionGhostValid hgv
  exact e2c_forall_of_zip_eq_len hcl.chains_len (fun gc hmem => (hcl.chains_ok gc hmem).2.2)

private theorem e2c_encodeVarintAux_length_le :
    ∀ (k : Nat) (v : BitVec 64), (encodeVarintAux k v).length ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, v => by
    unfold encodeVarintAux
    split_ifs
    · simp
    · simp only [List.length_cons]
      exact Nat.add_le_add_right (e2c_encodeVarintAux_length_le k (v >>> 7)) 1

private theorem e2c_encodeVarint_length_le (v : BitVec 64) : (encodeVarint v).length ≤ 10 :=
  e2c_encodeVarintAux_length_le 10 v

private theorem e2c_encodeKey_length_le (tag : Nat) (wt : WireType) :
    (encodeKey tag wt).length ≤ 10 :=
  e2c_encodeVarint_length_le _

private theorem e2c_lenField_length_le (tag : Nat) (payload : List (BitVec 8)) :
    (lenField tag payload).length ≤ 20 + payload.length := by
  unfold lenField
  simp only [List.length_append]
  have h1 := e2c_encodeKey_length_le tag .lengthDelimited
  have h2 := e2c_encodeVarint_length_le (BitVec.ofNat 64 payload.length)
  omega

private theorem e2c_bytesField_length_le (tag : Nat) (v : List (BitVec 8)) :
    (bytesField tag v).length ≤ 20 + v.length := by
  unfold bytesField
  split_ifs <;> [simp; exact e2c_lenField_length_le tag v]

private theorem e2c_uint32Field_length_le (tag : Nat) (v : BitVec 32) :
    (uint32Field tag v).length ≤ 20 := by
  unfold uint32Field
  split_ifs
  · simp
  · rw [List.length_append]
    have h1 := e2c_encodeKey_length_le tag .varint
    have h2 := e2c_encodeVarint_length_le (v.setWidth 64)
    omega

private theorem e2c_uint64Field_length_le (tag : Nat) (v : BitVec 64) :
    (uint64Field tag v).length ≤ 20 := by
  unfold uint64Field
  split_ifs
  · simp
  · rw [List.length_append]
    have h1 := e2c_encodeKey_length_le tag .varint
    have h2 := e2c_encodeVarint_length_le v
    omega

private theorem e2c_int32Field_length_le (tag : Nat) (v : BitVec 32) :
    (int32Field tag v).length ≤ 20 := by
  unfold int32Field
  split_ifs
  · simp
  · rw [List.length_append]
    have h1 := e2c_encodeKey_length_le tag .varint
    have h2 := e2c_encodeVarint_length_le (v.signExtend 64)
    omega

private theorem e2c_optUint32Field_length_le (tag : Nat) (ov : Option (BitVec 32)) :
    (optUint32Field tag ov).length ≤ 20 := by
  cases ov with
  | none => simp [optUint32Field]
  | some v =>
    unfold optUint32Field
    rw [List.length_append]
    have h1 := e2c_encodeKey_length_le tag .varint
    have h2 := e2c_encodeVarint_length_le (v.setWidth 64)
    omega

private theorem e2c_msgField_length_le (tag : Nat) (ob : Option (List (BitVec 8))) (B : Nat)
    (hB : ∀ b, ob = some b → b.length ≤ B) : (msgField tag ob).length ≤ 20 + B := by
  cases ob with
  | none => simp [msgField]
  | some b =>
    dsimp only [msgField]
    have h1 := e2c_lenField_length_le tag b
    have h2 := hB b rfl
    omega

private theorem e2c_length_flatten_map_le {α : Type} :
    ∀ (l : List α) (f : α → List (BitVec 8)) (B : Nat),
      (∀ a ∈ l, (f a).length ≤ B) → ((l.map f).flatten).length ≤ B * l.length
  | [], _, _, _ => by simp
  | a :: tl, f, B, hf => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    have ha := hf a (List.mem_cons_self ..)
    have htl := e2c_length_flatten_map_le tl f B (fun y hy => hf y (List.mem_cons_of_mem a hy))
    rw [Nat.mul_add, Nat.mul_one]
    omega

private theorem e2c_keyToBytes32_length (k : BitVec 256) : (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

private theorem e2c_publicKey_serialize_length (pk : PublicKey) : pk.serialize.length = 33 := by
  simp [PublicKey.serialize]

private theorem e2c_identityKey_serialize_length (ik : IdentityKey) : ik.serialize.length = 33 := by
  simp [IdentityKey.serialize, PublicKey.serialize]

private theorem e2c_privateKey_bytes_length (sk : PrivateKey) : sk.bytes.toList.length = 32 :=
  sk.bytes.toList_length

private theorem e2c_encChainKey_length_le (ck : ChainKey) : (encChainKey ck).length ≤ 72 := by
  unfold encChainKey
  rw [List.length_append]
  have h1 := e2c_uint32Field_length_le 1 ck.index
  have h2 := e2c_bytesField_length_le 2 (keyToBytes32 ck.key)
  rw [e2c_keyToBytes32_length] at h2
  omega

private theorem e2c_encSenderChain_length_le (c : SenderChain) :
    (encSenderChain c).length ≤ 197 := by
  unfold encSenderChain
  simp only [List.length_append]
  have h1 := e2c_bytesField_length_le 1 c.ratchetKey.publicKey.serialize
  rw [e2c_publicKey_serialize_length] at h1
  have h2 := e2c_bytesField_length_le 2 c.ratchetKey.privateKey.bytes.toList
  rw [e2c_privateKey_bytes_length] at h2
  have h3 := e2c_msgField_length_le 3 (some (encChainKey c.chainKey)) 72
    (fun _ hb => Option.some.inj hb ▸ e2c_encChainKey_length_le c.chainKey)
  omega

private theorem e2c_encReceiverChain_length_le (c : ReceiverChain)
    (hlen : c.messageKeys.length ≤ 2000)
    (hseeds : ∀ mk ∈ c.messageKeys, mk.seed.length = 32) :
    (encReceiverChain c).length ≤ 184145 := by
  unfold encReceiverChain
  simp only [List.length_append]
  have h1 := e2c_bytesField_length_le 1 c.senderRatchetKey.serialize
  rw [e2c_publicKey_serialize_length] at h1
  have h2 := e2c_msgField_length_le 3 (c.chainKey.map encChainKey) 72 (by
    intro b hb
    rcases hck : c.chainKey with _ | ck <;> rw [hck] at hb
    · cases hb
    · injection hb with hb'; subst hb'; exact e2c_encChainKey_length_le ck)
  have h3 := e2c_length_flatten_map_le c.messageKeys (fun mk => lenField 4 (encMessageKey mk)) 92
    (by
      intro mk hmk
      have hmk_len : (encMessageKey mk).length ≤ 72 := by
        unfold encMessageKey
        rw [List.length_append]
        have hu := e2c_uint32Field_length_le 1 mk.counter
        have hb := e2c_bytesField_length_le 5 mk.seed
        rw [hseeds mk hmk] at hb
        omega
      have hl := e2c_lenField_length_le 4 (encMessageKey mk)
      omega)
  omega

private theorem e2c_encodeRecord_some_length_le {G : SessionGhost} {s : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G s) (hdom : SessionCloneDom 286196 s) :
    (encodeRecord ⟨some s⟩).length ≤ 2097152 := by
  have hmk_le := e2c_mk_len_le_of_sessionGhostValid hgv
  obtain ⟨hrc_len, hseeds, halice_len, hkyb_cap, hpq_len⟩ := hdom
  change (lenField 1 (encSession s)).length ≤ 2097152
  have houter := e2c_lenField_length_le 1 (encSession s)
  have henc : (encSession s).length ≤ 1209311 := by
    unfold encSession
    dsimp only
    simp only [List.length_append]
    have hf1 := e2c_uint32Field_length_le 1 s.state.sessionVersion
    have hf2 := e2c_bytesField_length_le 2 s.state.localIdentity.serialize
    rw [e2c_identityKey_serialize_length] at hf2
    have hf3 :
        (bytesField 3 ((s.state.remoteIdentity.map IdentityKey.serialize).getD [])).length ≤ 53 := by
      cases hrem : s.state.remoteIdentity with
      | none =>
        have h := e2c_bytesField_length_le 3 []
        simpa using Nat.le_trans h (by decide)
      | some rem =>
        dsimp only [Option.map, Option.getD]
        have h := e2c_bytesField_length_le 3 rem.serialize
        rw [e2c_identityKey_serialize_length] at h
        omega
    have hf4 := e2c_bytesField_length_le 4 (keyToBytes32 s.state.rootKey)
    rw [e2c_keyToBytes32_length] at hf4
    have hf5 := e2c_uint32Field_length_le 5 s.state.previousCounter
    have hf6 := e2c_msgField_length_le 6 (s.state.senderChain.map encSenderChain) 197 (by
      intro b hb
      rcases hsc : s.state.senderChain with _ | sc <;> rw [hsc] at hb
      · cases hb
      · injection hb with hb'; subst hb'; exact e2c_encSenderChain_length_le sc)
    have hf7 := e2c_length_flatten_map_le s.state.receiverChains
      (fun c => lenField 7 (encReceiverChain c)) 184165 (by
        intro rc hrc
        have hl := e2c_lenField_length_le 7 (encReceiverChain rc)
        have he := e2c_encReceiverChain_length_le rc (hmk_le rc hrc) (hseeds rc hrc)
        omega)
    have hf9 := e2c_msgField_length_le 9 (s.pendingPreKey.map encPendingPreKey) 113 (by
      intro b hb
      rcases hpp : s.pendingPreKey with _ | pp <;> rw [hpp] at hb
      · cases hb
      · injection hb with hb'; subst hb'
        unfold encPendingPreKey
        simp only [List.length_append]
        have p1 := e2c_optUint32Field_length_le 1 pp.preKeyId
        have p2 := e2c_bytesField_length_le 2 pp.baseKey.serialize
        rw [e2c_publicKey_serialize_length] at p2
        have p3 := e2c_int32Field_length_le 3 pp.signedPreKeyId
        have p4 := e2c_uint64Field_length_le 4 pp.timestamp
        omega)
    have hf10 := e2c_uint32Field_length_le 10 s.remoteRegistrationId
    have hf11 := e2c_uint32Field_length_le 11 s.localRegistrationId
    have hf13 := e2c_bytesField_length_le 13 s.aliceBaseKey
    have hf14 := e2c_msgField_length_le 14 (s.pendingKyberPreKey.map encPendingKyber) 1609 (by
      intro b hb
      rcases hky : s.pendingKyberPreKey with _ | ky <;> rw [hky] at hb
      · cases hb
      · injection hb with hb'; subst hb'
        unfold encPendingKyber
        rw [List.length_append]
        have k1 := e2c_uint32Field_length_le 1 ky.preKeyId
        have k2 := e2c_bytesField_length_le 2 ky.ciphertext
        have hkcap := hkyb_cap ky hky
        omega)
    have hf15 := e2c_bytesField_length_le 15 s.state.pqRatchetState
    omega
  omega

private theorem e2c_Mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  cases h : m s with
  | mk r s' =>
    cases r <;>
      (simp [Mut.exec, h, bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont,
        StateT.run, ExceptT.run]; try rfl)

private theorem e2c_Mut_exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

private theorem e2c_Mut_exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

private theorem e2c_Mut_exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

private theorem e2c_Mut_exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ Unit) s = (.ok (), s') := rfl

private theorem e2c_Mut_exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ Unit) s = (.ok (), f s) := rfl

private theorem e2c_Mut_exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

private theorem e2c_Mut_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

private theorem e2c_onRatchet_pq {PQ α : Type} (m : Mut RatchetState α) (t t' : TripleRatchet PQ)
    (a : α) (h : Mut.exec (TripleRatchet.onRatchet m) t = (.ok a, t')) :
    t'.pqrState = t.pqrState := by
  unfold TripleRatchet.onRatchet zoom at h
  simp only [e2c_Mut_exec_bind, e2c_Mut_exec_get] at h
  rcases hm : Mut.exec m t.ratchet with ⟨_ | _, _⟩
  · simp [hm, e2c_Mut_exec_set, e2c_Mut_exec_liftE] at h
  · simp only [hm, e2c_Mut_exec_set, e2c_Mut_exec_liftE, Prod.mk.injEq, Except.ok.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl

private theorem e2c_tryDecryptWithState_spqr {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option (List (BitVec 8))) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (record s : SessionState PQ)
    (pt : List (BitVec 8))
    (hd : Mut.exec (SessionState.tryDecryptWithState C spqr expected m msgType coins) record =
      (.ok pt, s)) :
    ∃ salt, spqr.recv record.pqRatchetState m.pqRatchet = .ok (s.pqRatchetState, salt) := by
  unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
    SessionState.takeRatchetState SessionState.takePqRatchetState at hd
  simp only [e2c_Mut_exec_bind, e2c_Mut_exec_get, e2c_Mut_exec_modifyGet] at hd
  rcases hrem : record.remoteIdentity with _ | rem
  · simp [hrem, e2c_Mut_exec_throw] at hd
  · simp only [hrem, e2c_Mut_exec_pure] at hd
    set tr0 : TripleRatchet PQ := ⟨⟨record.rootKey, record.senderChain, record.receiverChains,
      record.previousCounter, maxForwardJumps⟩, record.pqRatchetState, record.localIdentity, rem⟩
    rcases hdec : Mut.exec (TripleRatchet.decrypt C spqr expected m msgType coins) tr0 with
      ⟨_ | _, _⟩
    · simp [hdec, e2c_Mut_exec_liftE] at hd
    · simp only [hdec, e2c_Mut_exec_liftE, e2c_Mut_exec_modify, Prod.mk.injEq] at hd
      rcases hd with ⟨-, rfl⟩
      unfold TripleRatchet.decrypt at hdec
      simp only [e2c_Mut_exec_bind] at hdec
      rcases hens : Mut.exec (TripleRatchet.onRatchet
          (RatchetState.ensureReceiverChain C m.senderRatchetKey coins)) tr0 with ⟨_ | ck, tr1⟩
      · rw [hens] at hdec; cases hdec
      · rw [hens] at hdec; dsimp only at hdec
        have hpq1 := e2c_onRatchet_pq _ tr0 tr1 ck hens
        rcases hcons : Mut.exec (TripleRatchet.onRatchet
            (RatchetState.consumeMessageKey C.F m.senderRatchetKey ck m.counter msgType)) tr1 with
          ⟨_ | mkg, tr2⟩
        · rw [hcons] at hdec; cases hdec
        · rw [hcons] at hdec; dsimp only at hdec
          have hpq2 := e2c_onRatchet_pq _ tr1 tr2 mkg hcons
          simp only [e2c_Mut_exec_get] at hdec
          cases hpan : spqr.recvPanics tr2.pqrState m.pqRatchet
          · simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hdec
            rcases hspqr : spqr.recv tr2.pqrState m.pqRatchet with err | ⟨_, salt⟩
            · cases err <;> simp [hspqr, e2c_Mut_exec_throw] at hdec
            · simp only [hspqr, e2c_Mut_exec_bind, e2c_Mut_exec_pure] at hdec
              split_ifs at hdec
              · simp [e2c_Mut_exec_throw] at hdec
              · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F salt).cipherKey
                    (mkg.generateKeys C.F salt).iv m.ciphertext with _ | _
                · simp [haes, e2c_Mut_exec_throw] at hdec
                · simp only [haes, e2c_Mut_exec_bind, e2c_Mut_exec_modify, e2c_Mut_exec_pure,
                    Prod.mk.injEq] at hdec
                  rcases hdec with ⟨-, rfl⟩
                  exact ⟨salt, by
                    simpa [TripleRatchet.applyToSessionState,
                      SessionState.clearUnacknowledgedPreKeyMessage, hpq2, hpq1, tr0] using hspqr⟩
          · simp [hpan, e2c_Mut_exec_throw] at hdec

private theorem e2c_preSession_bounds [LibsignalPlacement]
    {A : RustAlloc} {W : CliHooks} {B : RunBudgets}
    {g : DecPkGhost} {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    (hfPeer : FilesOkPeer scopeIn g.F g.peer.val)
    (hdecOk : DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val)
    (hload_rel : (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B)).loadRel
      StoresGhost.opened.sessions g.peer.val (.ok (some r)))
    (hcur : r.currentSession = some sess) :
    loadRec scopeIn g.F g.peer.val = .ok (some ⟨some sess⟩) ∧
    scopeIn ⟨some sess⟩ ∧
    SessMatchesPm sess g.msg ∧
    TopStateTight W.C.F W.Q.K sess.state.pqRatchetState ∧
    SessionCloneDom 286196 sess := by
  dsimp only [cliPollSessKitPlaced] at hload_rel
  obtain ⟨hloadS, _, hIn, hmatch, _, _, _⟩ :=
    pathB_scopeIn_and_match_of_decPkOkPathB encodeInjOn_deserializeScopeP_Q (fun _ h => h)
      hfPeer hdecOk hload_rel hcur
  have hloadK : loadRec scopeKit g.F g.peer.val = .ok (some ⟨some sess⟩) :=
    (CryptoVerification.SignalSession.Cli.RunProofs.Poll.loadRec_scopeKit_eq
      encodeInjOn_deserializeScopeP_Q (fun _ h => h) hfPeer).trans hloadS
  have hTop : TopStateTight W.C.F W.Q.K sess.state.pqRatchetState := by
    unfold PeerSpqrStateTight640 at hTight
    rw [hloadK] at hTight
    exact hTight sess rfl
  have hpq_le : sess.state.pqRatchetState.length ≤ 286196 :=
    topStateTight_length_le hTop
  have hdom4G := sessionCloneDom_of_scopeIn hIn rfl
  exact ⟨hloadS, hIn, hmatch, hTop,
    ⟨hdom4G.rc_len, hdom4G.seeds32, hdom4G.alice_len, hdom4G.kyber_cap, hpq_le⟩⟩

private theorem e2c_postSession_bounds
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : DecPkGhost} {sess : Session (List (BitVec 8))} {pt : List (BitVec 8)}
    (hfPeer : FilesOkPeer scopeIn g.F g.peer.val)
    (hdecOk : DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg)
    (hIn : scopeIn ⟨some sess⟩)
    (hloadS : loadRec scopeIn g.F g.peer.val = .ok (some ⟨some sess⟩))
    (htr_ne_false :
      StoresGhost.opened.identity.trusted cliIo.rd g.F g.peer.val g.msg.identityKey ≠ .ok false)
    (hmatch : SessMatchesPm sess g.msg)
    (hrem : sess.state.remoteIdentity = some g.msg.identityKey)
    (hver : sess.state.version = g.msg.message.messageVersion.zeroExtend 32)
    (hok : (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state).1 = .ok pt)
    (hTop_pre : TopStateTight W.C.F W.Q.K sess.state.pqRatchetState) :
    SessionCloneDom 286196
      { sess with
        state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state).2
        pendingPreKey := none
        pendingKyberPreKey := none } := by
  obtain ⟨b, htrusted⟩ := trusted_ok_of_filesOkPeer (peer := g.peer) hfPeer g.msg.identityKey
  cases b with
  | false => exact absurd htrusted htr_ne_false
  | true =>
    have hKit_post :
        scopeKit
          ⟨some
            { sess with
              state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state).2
              pendingPreKey := none
              pendingKyberPreKey := none }⟩ :=
      (decPkDef_pathB_ok_pathB X ⟨W.C, W.Q⟩ scopeIn g.F g.peer g.me g.msg g.coins
        hfPeer hdecOk hIn hloadS htrusted hmatch hrem hver hok).2.2.1
    have hTop_post :
        TopStateTight W.C.F W.Q.K
          (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state).2.pqRatchetState := by
      rcases hm : genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state with
        ⟨res, st'⟩
      rw [hm] at hok
      dsimp only at hok ⊢
      subst hok
      obtain ⟨salt, hspqr⟩ := e2c_tryDecryptWithState_spqr W.C (spqrV1 W.C.F W.Q.K).spqr _ _ _ _
        sess.state st' pt hm
      exact topStateTight_spqrV1_recv hTop_pre hspqr
    exact sessionCloneDom_of_scopeKit_pq hKit_post rfl (topStateTight_length_le hTop_post)

private def e2c_dummyRes : DoReserveCall :=
  { v := 0#64, cap := 0#64, ptr := 1#64, bs := [], additional := 0 }

private def e2c_dummySpqrGhost : InitialStateGhost :=
  { pA := 0#64
    ret := 0#64
    akPtr := 1#64
    p := { direction := .a2b
           version := .v1
           minVersion := .v1
           authKey := []
           chainParams := ChainParams.default } }

private def e2c_dummyTdCall (g : DecPkGhost) : W4TryDecryptCallCmk :=
  ⟨stageP3TryDecryptEnvArgs e2c_succInitSessGhost e2c_succInitSessVal.state
    g.peer g.me g.msgG.msg g.msg.message []⟩

private def e2c_dummyFailedTd (g : DecPkGhost) : W4FailedTryDecryptCallCmk :=
  { td := e2c_dummyTdCall g, failDropPairs := [] }

private def e2c_mkW4Params (W : CliHooks) (g : DecPkGhost)
    (isPathB : Bool) (td_B : W4TryDecryptCallCmk)
    (g_out0 : RecordGhost) (r_out0 : SessionRecord (List (BitVec 8))) :
    W4BinaryRecvPrekeyParamsCmk :=
  { base :=
      { C := W.C
        K := W.Q.K
        rd := cliIo.rd
        files := g.F
        kpkDir := StoresGhost.opened.kyber.oneTime
        peer := g.peer
        hasOpk := false
        spkId := 0#32
        kpkId := 0#32
        opkId := 0#32
        kpkMarkName := []
        ownKeyName := []
        ownRegName := []
        x_res := e2c_dummyRes
        x_spqr := e2c_dummySpqrGhost
        hasCurSession := false
        G_cur := e2c_succInitSessGhost
        st_cur := e2c_succInitSessVal.state
        fc_cur := e2c_dummyFailedTd g
        archivedTrials := []
        isPathB := isPathB
        td_B := td_B
        isPathAC := false
        td_AC := e2c_dummyTdCall g
        g_arch := ⟨0#64, 0#64, none⟩
        r_arch := ⟨none⟩
        g_out0 := g_out0
        r_out0 := r_out0
        G_out1 := e2c_succInitSessGhost
        sess_out1 := e2c_succInitSessVal
        enc_prev1 := [] }
    remoteIdKey := g.msg.identityKey
    baseKey := g.msg.baseKey }

private theorem e2c_callSiteDomCmk0 (W : CliHooks) (g : DecPkGhost)
    (isPathB : Bool) (td_B : W4TryDecryptCallCmk)
    (g_out0 : RecordGhost) (r_out0 : SessionRecord (List (BitVec 8)))
    (hout0_valid : ∀ G ses, g_out0.cur = some G → r_out0.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (hout0_enc : (encodeRecord r_out0).length ≤ 2097152)
    (htdB : isPathB = true →
      W4TryDecryptCallDomCmkOf W.C.F W.Q.K g.msg.message.ciphertext.length td_B) :
    W4BinaryCallSiteDomCmk0 W.C W.Q.K g.msg.message.ciphertext.length g.peer.val g.F
      (e2c_mkW4Params W g isPathB td_B g_out0 r_out0).base := by
  refine ⟨?_, rfl⟩
  refine
    { eq_C := rfl
      eq_K := rfl
      eq_rd := rfl
      eq_files := rfl
      eq_peerVal := rfl
      kpk_dir := Or.inl rfl
      ownKey_len := Nat.zero_le _
      ownReg_len := Nat.zero_le _
      kpkMark_len := Nat.zero_le _
      res_old := by dsimp [e2c_mkW4Params, e2c_dummyRes]; decide
      res_new := by dsimp [e2c_mkW4Params, e2c_dummyRes]; decide
      spqr_key := by dsimp [e2c_mkW4Params, e2c_dummySpqrGhost]; decide
      cur_dom := Or.inl rfl
      arch_valid := fun _ _ h => nomatch h
      arch_enc := by dsimp [e2c_mkW4Params, encodeRecord, msgField]; decide
      out0_valid := hout0_valid
      out0_enc := hout0_enc
      out1_freshBob := e2c_succInit_freshBobPrev1Dom
      trials_len4 := Nat.zero_le _
      cur_fail_dom := fun h => nomatch h
      trials_dom := fun _ h => nomatch h
      tdB_dom := htdB
      tdAC_dom := fun h => nomatch h }

private theorem e2c_out0_bounds_none :
    (∀ G ses, (⟨0#64, 0#64, none⟩ : RecordGhost).cur = some G →
      (⟨none⟩ : SessionRecord (List (BitVec 8))).currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses) ∧
    (encodeRecord (⟨none⟩ : SessionRecord (List (BitVec 8)))).length ≤ 2097152 :=
  ⟨(fun _ _ h => nomatch h), by simp [encodeRecord, msgField]⟩

private theorem e2c_out0_bounds_of_p4 {g_out0 : RecordGhost}
    {r_out0 : SessionRecord (List (BitVec 8))} {ss : Session (List (BitVec 8))}
    (hgv : RecordGhostValid g_out0 r_out0)
    (hr : r_out0 = ⟨none⟩ ∨ r_out0 = ⟨some ss⟩)
    (hdom : SessionCloneDom 286196 ss) :
    (∀ G ses, g_out0.cur = some G → r_out0.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses) ∧
    (encodeRecord r_out0).length ≤ 2097152 := by
  rcases hr with rfl | rfl
  · exact ⟨(fun _ _ _ hs => nomatch hs), by simp [encodeRecord, msgField]⟩
  · cases hcur : g_out0.cur with
    | none =>
      unfold RecordGhostValid at hgv
      rw [hcur] at hgv
      exact nomatch hgv
    | some G_out =>
      have hgv_ss : SessionGhostValid G_out ss := by
        unfold RecordGhostValid at hgv
        rw [hcur] at hgv
        exact hgv
      refine ⟨?_, e2c_encodeRecord_some_length_le hgv_ss hdom⟩
      intro G ses hg hs
      injection hg with hG
      injection hs with hses
      subst hG hses
      exact ⟨hgv_ss, hdom⟩

private theorem e2c_sub_cmkDom0_impl [LibsignalPlacement]
    {SR : W4StatesRecvEnv} {maxOps : Nat}
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (htdSub : ∀ a evs,
      tdEnv a evs → w4c_TryDecryptCliLinkedSrEnvOf SR CmkLoopAdvanceEvs maxOps W.C W.Q.K a evs)
    {g : DecPkGhost} {evs : List AllocEvent}
    (hfPeer : FilesOkPeer scopeIn g.F g.peer.val)
    (hdecOk : DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val)
    (hevs : DecPkD3MatchingPathBGvSeqFreeOfReadEnv A W B (ReadFileRuleEnvFixed cliIo.rd) tdEnv g evs) :
    realCliDecPkBinaryWideSlotEnvCmkDom0FixedOf SR CmkLoopAdvanceEvs maxOps X W g evs := by
  unfold DecPkD3MatchingPathBGvSeqFreeOfReadEnv DecPkD3MatchingPathBGvEnv MatchingPathBGvPollEnv at hevs
  dsimp only at hevs
  have hdom_idle :=
    e2c_callSiteDomCmk0 W g false (e2c_dummyTdCall g) ⟨0#64, 0#64, none⟩ ⟨none⟩
      e2c_out0_bounds_none.1 e2c_out0_bounds_none.2 (fun h => nomatch h)
  by_cases htr_false :
      StoresGhost.opened.identity.trusted cliIo.rd g.F g.peer.val g.msg.identityKey = .ok false
  · simp only [htr_false, ↓reduceIte] at hevs
    exact ⟨e2c_mkW4Params W g false (e2c_dummyTdCall g) ⟨0#64, 0#64, none⟩ ⟨none⟩,
      hdom_idle, rfl, rfl,
      Or.inr (Or.inl (Or.inl (e2c_cliDpPollUntrustedEnv_sub_w4StageP1UntrustedAllFixed hevs)))⟩
  · simp only [htr_false, ↓reduceIte] at hevs
    rcases hevs with hp1 | ⟨e_p1, e_234, rfl, hp1, r, sess, hload_rel, hcur, hmain⟩
    · exact ⟨e2c_mkW4Params W g false (e2c_dummyTdCall g) ⟨0#64, 0#64, none⟩ ⟨none⟩,
        hdom_idle, rfl, rfl,
        Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (e2c_stageP1OkEnv_sub_w4StageP1OkAllFixed hp1)))))⟩
    · obtain ⟨hloadS, hIn, hmatch, hTop_pre, hdom_pre⟩ :=
        e2c_preSession_bounds hfPeer hdecOk hTight hload_rel hcur
      have hp1' := e2c_stageP1OkEnv_sub_w4StageP1OkAllFixed hp1
      unfold MatchingPathBGvMainEnv at hmain
      dsimp only at hmain
      rcases hmain with hp2m | ⟨hrem, recG, _, hgv, hp234⟩
      · exact ⟨e2c_mkW4Params W g false (e2c_dummyTdCall g) ⟨0#64, 0#64, none⟩ ⟨none⟩,
          hdom_idle, rfl, rfl,
          Or.inr (Or.inl (Or.inr (Or.inl (Or.inr ⟨e_p1, e_234, rfl, hp1',
            Or.inl (Or.inr (e2c_stageP2MatchedEnv_sub_w4StageP2MatchedWide _ _ _ _ _ _ hp2m))⟩))))⟩
      · have hClone : ∀ e, SegCloneEnv recG sess.state e → W4CloneBDomEnv e :=
          fun e hseg => ⟨recG, sess, hgv, hdom_pre, hseg⟩
        rcases hp234 with hp2br | ⟨e_p2, e_34, rfl, hp2br, h34⟩
        · exact ⟨e2c_mkW4Params W g false (e2c_dummyTdCall g) ⟨0#64, 0#64, none⟩ ⟨none⟩,
            hdom_idle, rfl, rfl,
            Or.inr (Or.inl (Or.inr (Or.inl (Or.inr ⟨e_p1, e_234, rfl, hp1',
              Or.inl (Or.inr
                (e2c_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedWide _ _ _ _ _ _ hp2br))⟩))))⟩
        · rcases h34 with hp3env | ⟨hver, G₁, _, pt, _, _, hok, hp34⟩
          · unfold StageP3Env at hp3env
            by_cases hver : sess.state.version = g.msg.message.messageVersion.zeroExtend 32
            · simp only [hver, ↓reduceIte] at hp3env
              obtain ⟨G₁, _, hp3err⟩ := hp3env
              let td_B : W4TryDecryptCallCmk :=
                ⟨stageP3TryDecryptEnvArgs G₁ sess.state g.peer g.me g.msgG.msg g.msg.message g.coins⟩
              have htdB_dom :
                  W4TryDecryptCallDomCmkOf W.C.F W.Q.K g.msg.message.ciphertext.length td_B :=
                ⟨hdom_pre.rc_len, e2c_mk_len_le_of_sessionGhostValid hgv, hTop_pre, Nat.le_refl _⟩
              have hp3' :
                  W4StageP3WideEnv W4CloneBDomEnv
                    (w4c_TryDecryptCliLinkedSrEnvOf SR CmkLoopAdvanceEvs maxOps W.C W.Q.K td_B.a)
                    e_34 :=
                e2c_stageP3ErrEnv_sub_w4StageP3Wide hClone (fun e htd => htdSub td_B.a e htd) hp3err
              exact ⟨e2c_mkW4Params W g true td_B ⟨0#64, 0#64, none⟩ ⟨none⟩,
                e2c_callSiteDomCmk0 W g true td_B ⟨0#64, 0#64, none⟩ ⟨none⟩
                  e2c_out0_bounds_none.1 e2c_out0_bounds_none.2 (fun _ => htdB_dom),
                rfl, rfl,
                Or.inr (Or.inl (Or.inr (Or.inl (Or.inr ⟨e_p1, e_p2 ++ e_34, rfl, hp1',
                  Or.inr ⟨e_p2, e_34, rfl,
                    Or.inr (e2c_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedWide _ _ _ _ _ _ hp2br),
                    Or.inl (Or.inr hp3')⟩⟩))))⟩
            · simp only [hver, ↓reduceIte] at hp3env
              exact ⟨e2c_mkW4Params W g false (e2c_dummyTdCall g) ⟨0#64, 0#64, none⟩ ⟨none⟩,
                hdom_idle, rfl, rfl,
                Or.inr (Or.inl (Or.inr (Or.inl (Or.inr ⟨e_p1, e_p2 ++ e_34, rfl, hp1',
                  Or.inr ⟨e_p2, e_34, rfl,
                    Or.inr (e2c_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedWide _ _ _ _ _ _ hp2br),
                    Or.inl (Or.inr (e2c_stageP3VerNeEnv_sub_w4StageP3Wide _ hClone hp3env))⟩⟩))))⟩
          · let td_B : W4TryDecryptCallCmk :=
              ⟨stageP3TryDecryptEnvArgs G₁ sess.state g.peer g.me g.msgG.msg g.msg.message g.coins⟩
            have htdB_dom :
                W4TryDecryptCallDomCmkOf W.C.F W.Q.K g.msg.message.ciphertext.length td_B :=
              ⟨hdom_pre.rc_len, e2c_mk_len_le_of_sessionGhostValid hgv, hTop_pre, Nat.le_refl _⟩
            rcases hp34 with hp3ok | ⟨e_p3, e_p4, rfl, hp3ok, hp4⟩
            · have hp3' :
                  W4StageP3WideEnv W4CloneBDomEnv
                    (w4c_TryDecryptCliLinkedSrEnvOf SR CmkLoopAdvanceEvs maxOps W.C W.Q.K td_B.a)
                    e_34 :=
                e2c_stageP3OkPrefixEnv_sub_w4StageP3Wide hClone
                  (fun e htd => htdSub td_B.a e htd) hp3ok
              exact ⟨e2c_mkW4Params W g true td_B ⟨0#64, 0#64, none⟩ ⟨none⟩,
                e2c_callSiteDomCmk0 W g true td_B ⟨0#64, 0#64, none⟩ ⟨none⟩
                  e2c_out0_bounds_none.1 e2c_out0_bounds_none.2 (fun _ => htdB_dom),
                rfl, rfl,
                Or.inr (Or.inl (Or.inr (Or.inl (Or.inr ⟨e_p1, e_p2 ++ e_34, rfl, hp1',
                  Or.inr ⟨e_p2, e_34, rfl,
                    Or.inr (e2c_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedWide _ _ _ _ _ _ hp2br),
                    Or.inl (Or.inr hp3')⟩⟩))))⟩
            · have hdom_post :=
                e2c_postSession_bounds X W hfPeer hdecOk hIn hloadS htr_false hmatch hrem hver
                  hok hTop_pre
              obtain ⟨g_out0, r_out0, hgv_out0, hr_out0, hp4'⟩ :=
                e2c_stageP4MatchedSeqFree_sub_w4StageP4MatchedAllFixed hp4
              obtain ⟨hout0_valid, hout0_enc⟩ := e2c_out0_bounds_of_p4 hgv_out0 hr_out0 hdom_post
              have hp3' :
                  W4StageP3WideEnv W4CloneBDomEnv
                    (w4c_TryDecryptCliLinkedSrEnvOf SR CmkLoopAdvanceEvs maxOps W.C W.Q.K td_B.a)
                    e_p3 :=
                e2c_stageP3OkPrefixEnv_sub_w4StageP3Wide hClone
                  (fun e htd => htdSub td_B.a e htd) hp3ok
              exact ⟨e2c_mkW4Params W g true td_B g_out0 r_out0,
                e2c_callSiteDomCmk0 W g true td_B g_out0 r_out0 hout0_valid hout0_enc
                  (fun _ => htdB_dom),
                rfl, rfl,
                Or.inr (Or.inl (Or.inr (Or.inl (Or.inr ⟨e_p1, e_p2 ++ (e_p3 ++ e_p4), rfl, hp1',
                  Or.inr ⟨e_p2, e_p3 ++ e_p4, rfl,
                    Or.inr (e2c_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedWide _ _ _ _ _ _ hp2br),
                    Or.inr ⟨e_p3, e_p4, rfl, Or.inr hp3', Or.inr hp4'⟩⟩⟩))))⟩

end SubCmkDom0Helpers

/-- Embeds `DecPkD3MatchingPathBGvSeqFreeOfReadEnv` at `ReadFileRuleEnvFixed cliIo.rd` into
`realCliDecPkBinaryWideSlotEnvCmkDom0FixedOf` (`hasCurSession = false`, `archivedTrials = []`). -/
theorem decPkD3MatchingPathBGvSeqFreeOfReadEnv_sub_cmkDom0 [LibsignalPlacement]
    {SR : W4StatesRecvEnv} {maxOps : Nat}
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (htdSub : ∀ a evs,
      tdEnv a evs → w4c_TryDecryptCliLinkedSrEnvOf SR CmkLoopAdvanceEvs maxOps W.C W.Q.K a evs)
    {g : DecPkGhost} {evs : List AllocEvent}
    (hfPeer : FilesOkPeer scopeIn g.F g.peer.val)
    (hdecOk : DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val)
    (hevs : DecPkD3MatchingPathBGvSeqFreeOfReadEnv A W B (ReadFileRuleEnvFixed cliIo.rd) tdEnv g evs) :
    realCliDecPkBinaryWideSlotEnvCmkDom0FixedOf SR CmkLoopAdvanceEvs maxOps X W g evs :=
  e2c_sub_cmkDom0_impl A X W B htdSub hfPeer hdecOk hTight hevs

/-- Sealed `@StatesRecvProtoEnv'` (`w4c_repairedStatesRecvEnvFam`, `maxOps = 109`) corollary of
`decPkD3MatchingPathBGvSeqFreeOfReadEnv_sub_cmkDom0`. -/
theorem decPkD3MatchingPathBGvSeqFreeOfReadEnv_sub_cmkDom0' [LibsignalPlacement]
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (htdSub : ∀ a evs,
      tdEnv a evs →
        w4c_TryDecryptCliLinkedSrEnvOf w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs
          w4c_defaultDecodeMaxOps W.C W.Q.K a evs)
    {g : DecPkGhost} {evs : List AllocEvent}
    (hfPeer : FilesOkPeer scopeIn g.F g.peer.val)
    (hdecOk : DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val)
    (hevs : DecPkD3MatchingPathBGvSeqFreeOfReadEnv A W B (ReadFileRuleEnvFixed cliIo.rd) tdEnv g evs) :
    realCliDecPkBinaryWideSlotEnvCmkDom0Fixed' X W g evs :=
  decPkD3MatchingPathBGvSeqFreeOfReadEnv_sub_cmkDom0 A X W B htdSub hfPeer hdecOk hTight hevs
end LibsignalBinary.Proofs.PeakBudget.D3MatchingPathBSeqFreeR
