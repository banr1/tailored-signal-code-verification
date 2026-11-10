/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureDefsPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntry
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import ProofLib.SepLogic.WPp

/-!
# Linked `spqr::recv`, Block `507`, and `CodeOk`-Generalized W4 D2(c) Slot Dischargers

Composes `SpqrRecvLinkedWitness` (Block `329`), `TryDecryptCliLinkedEnv` (Block `507`), widened
Path-C Stage P3, and `DecPkD2cSlotOkLinkedBase` into a single `CodeOk`-generalized D2(c) poll
`SepWPp` proof (`dpPoll_d2c_wide_sepWPp_of_codeOk`), yielding both `DecPkD2cSlotOkPlaced`
(`[LibsignalPlacement]`) and `DecPkD2cSlotOkFrozenPlaced` (`[LibsignalFullPlacement]`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet

namespace LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession
  (Crypto PublicKey SessionState SignalMessage SignalProtocolError)
open CryptoGames.LibsignalSessionApi (ApiError Session SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalFrozen LibsignalFullPlacement
   LibsignalPlacement libsignalFrozen_of_keepsFrozen libsignalSessionLib
   lsLogFilterAddr lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
  (genP3S5Model genP3S5ModelPanicProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
  (SessionExtraRel coroOpkIdAtP4 p1LoadedRecordAt sp_sub_cd0_align_std3 stageP1CallStack)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
  (OverPrevEncOK clearPending overPrevEncOK_clearPending_of_scopeIn_placed overScratch
   stageP3Sub5ExtraPrePrev1)
open CryptoVerification.E2E
  (LocalIdentity PreKeyMessageFields ResponderPreKeySecrets UnreachedPqxdhPrimitives
   acceptInput aesDecHookMallocng fmtWriteHook0 formatInnerHook0 modelPrims)
open CryptoVerification.E2E.Pqxdh.ResponderClosure
  (ClosureCalleeSaved decryptPrekeyCoroInitAt)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid)
open CryptoVerification.E2E.Record (encSession)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (lsStringCloneSym)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsAt FsFiles LibsignalCodeRoLoaded extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (preKeyMsgAt)
open CryptoVerification.LibsignalSpqrV1
  (MlKem SpqrRecvModel spqrV1 spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet
  (SeedsLen32 SendCall SpqrModel VecArg rootStack spqrRecvStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SessionGhost SignalMessageGhost decryptDraws protocolAddressAt signalMessageAt
   uuidTryParse)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced cliHookTablePlaced lsFormatInnerSym lsReadFileSym lsReadStdinSym
   lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
   lsRustReallocSymCli)
open CryptoVerification.SignalSession.Cli
  (StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym
   cliSignedPreKeyVtSym dirAt)
open CryptoVerification.SignalSession.Cli.KitInst
  (cliKyberPreKeyStoreSpecPlaced cliPreKeyStoreSpecPlaced cliSignedPreKeyStoreSpecPlaced)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliRunBudgets cliWrOk coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost RunSem decResAt dpPollNeed dpSlotArgsPlaced slotOutTr)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other
   withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs
  (DecPkOkD2c DecPkOk₀ SessMatchesPm decPkDef decPkDefD2c
   decPkDefD2c_eq_decPkDef_of_match decPkDefD2c_eq_decPkDef_of_noCurrent
   dpFutDoneAt dpFutStartAt pkStoreKeys pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (LsTokenInit StageP1PostRegs cliIdStoreSpecFullPlaced cliId_trustRel_eq_of_trusted
   cliKitStk cliKpkStoreSpecFullPlaced cliPollIdKit cliPollIdKitPlaced cliPollKpkKitPlaced
   cliPollPkKitPlaced cliPollSessKit cliPollSessKitPlaced cliPollSessPrev1KitPlaced
   cliPollSpkKitPlaced cliPollStoresKitsAtPlaced cliSess_loadRel_isOk closStackUnusedP1OkAt
   clos_stack_3280_split_for_p1_ok closureCalleeSaved_toCalleeSavedPreserved coroUnusedP1At
   currentSession_some_of_cliPollSessPlaced_loadRel decPkDefD2c_pathC_err
   decPkDefD2c_pathC_panic decPkDefD2c_pathC_ver_ne distinctSid_of_decPkOk₀ dpClosSubStack
   dpPollEntryPlaced dpPollProgPlaced dpPollNeed_eq_frame_add_subStack
   dpFutStartAt_split_for_p1_placed loadRec_of_cliPollSessPlaced_loadRel
   pathAInitSession pathAInitSession_scopeIn pathAInitState pmKyberId pmPreKeyId
   preKeyMsgAt_eq_idKey_sep preKeyMsgRemIdKeyAt rootStack_le_subStack
   scope_of_loadRec_some sepWPp_conseq_pre sepWPp_sepExists_left slotOutTr_d2c_of_reject
   sp_frame_sub_add stageP1CallStack_le_subStack stageP1Ok_trace_eq_placed stageP2PostP1At
   stageP3CoroFrameAt stageP3OverStackFrameAt stageP3StackFrameAt stageP3StackFrameAt_eq_over
   stackAt_poll_entry_split stackAt_subStack_split subStack_le_sp_of_dpPollNeed
   subroutine_ok_of_sepWPp_steps trusted_ok_of_filesOkPeer)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (EncodeInjOn FilesOkPeer cliExternsPlaced_rngFill fmtWrite_row_placed formatInner_row_placed
   loadRec lsRngFillSym scopeIn scopeKit trTrapExternsPlaced)
open CryptoVerification.SignalSession.Coins (coinsAfterPlaced coinsAtPlaced)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.DecodeState (V1InnerHeapPred)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.SpecBudget
  (FmtWriteEnv FormatInnerEnv aesDecBudgetSpec fmtWriteBudgetEnvSpec fmtWriteBudgetSpec
   formatInnerBudgetEnvSpec formatInnerBudgetSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudget
  (tryDecryptPqV1_placed_ok_PTight_cli_at_block_of_tdEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
  (ChainClone3OkPlaced SenderChainClone3OkPlaced)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
  (StageP2MatchedEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
  (StageP3ErrM3Env StageP3OkPrefixM3Env)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
  (StageP3Prev1Env StageP3VerNePrev1Env)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux
  (VerNeTopEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (TryDecryptCliEnvOf)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget
  (tryDecryptRawSpecTPTightAt)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
  (SpqrRecvC07C09aBytesEnv TryDecryptCliLinkedEnv spqrRecvC07C09aBytesEnv_nonempty)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase
  (CliDpPollOkD2cStateFrozenPlacedAt CliDpPollOkD2cStateMemInvAt DecPkD2cSlotOkFrozenPlaced
   PathAPostP1Env StageP2OverQpanCliMemInvPlacedStmt StageP2PathAQpanCliMemInvAtStmt
   closure_pathA_memInv_ok_at decPkD2cSlotOk_of_poll_frozen_placed extract_withMemInv
   withMemInv)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (DecodeStateTightEnv StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness
  (spqr_recv_placed_ok_blockProgram_ext_of_contracts_c07c09aTightLinked)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec (StatesRecvProtoEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget
  (DecPkD2cSlotOkPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget
  (overExit_entails_dpPollPost_placed overGenP3Pre_placed overGenP3S5PostFrame_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget
  (OverCliTryDecryptPqV1PlacedStmt closure_pathC_p4_cont_placed overPollTryDecryptPlacedSpecTPTight
   overSepWPp_genP3_to_tailQpan_placed overSepWPp_pollGoal_frame_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
  (CliStageP4Prev1Envs StageP2OverEnv StageP4Prev1Env StageP4Prev1VRegsPlacedStmt
   cliChainClone3_placed_ok cliDropSessionStructure4_placed_ok_at cliFiles_eq_of_trace_eq_placed
   cliFsAt_of_files_eq_placed cliSenderChainClone3_placed_ok
   overStageP3ErrPostPrevEmptyAt_placed stageP3DispatchOkMidPrev1At_placed
   stageP3_exit_pathC_to_pollPost_placed storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlacedBudget
  (CliDpPollOkD2cStatePlacedAt closure_untrusted_d2c_placed_ok dpPollPre_unpack_d2c_placed
   sepWPp_pollGoal_of_decPk_eq_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.WrapperOverPlacedBudget
  (decPkD2cSlotOk_of_poll_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget
  (dpPollEntrySpatialPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudgetAux
  (p1Ok_recombine_entails_stageP2_placed_budget sepWPp_bind_p1_noPanic)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
  (StageP2MatchedFramedCliPlacedStmt closure_pathB_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
  (StageP3Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (StageP3GenStepsVRegsPlacedStmt StageP3PrevEmptyVRegsPlacedStmt StageP4MatchedPlacedStmt
   StageP4PathAPlacedStmt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget
  (CliDpPollTrustedEnv CliStageP1OkEnv PollBaseStagesPlacedStmt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
  (cliPollStageP1_fsAt_placed runHooks_to_stages)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
  (stageP1_ok_placed_inst)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
  (cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv cliPollSessBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
  (SpqrV1PlacedSeamsOfEnv spqrRecvPlacedInnerSpecXOfEnv spqrRecvPlacedInnerSpecXTOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (InitInnerEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget
  (spqrRecvPlacedRawSpecXOfEnv spqrRecvPlacedSpecXOfEnv spqrRecvPlacedSpecXTOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget (SpqrRecvPlacedContractsOfEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
  (dropSessionStructureLocal2Spec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## 1. `SpqrRecvLinkedWitness` → `SpqrV1PlacedSeamsOfEnv` (Block `329`) -/

private theorem trTrapExternsPlaced_isPanic
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym, Rust.isPanicSymbol sym = true →
      trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym =
        some Rust.panicked := by
  intro sym hsym
  have hp := congrFun (withPanics_cliGhostExterns mmpl gh W) sym
  simp only [Rust.withPanics, hsym, ↓reduceIte] at hp
  have hne : sym ≠ lsRngFillSym := by
    intro heq
    subst heq
    have hnone := cliExternsPlaced_rngFill mmpl gh W
    rw [hnone] at hp
    cases hp
  have hbeq : (sym == lsRngFillSym) = false := beq_false_of_ne hne
  simp only [trTrapExternsPlaced, ProofLib.Variant.trapAt, hbeq, Bool.false_eq_true, ↓reduceIte]
  exact hp.symm

/-- Bridges `ContractsPlacedBudget.spqrRecvPlacedSpecXTOfEnv` to
`StoreKit.withLsCodeRoLoaded lsmpl (spqrRecvPlacedInnerSpecXTOfEnv ...)` on any `prog`/`entry`. -/
theorem spqrRecvPlacedInnerSpecXTOfEnv_of_placedSpecXT [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {R : SpqrRecvModel} {Env : VecArg → VecArg → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64}
    (hok : subroutine_ok prog entry (spqrRecvPlacedSpecXTOfEnv A lim R Env)) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (spqrRecvPlacedInnerSpecXTOfEnv M A lim R Env)) := by
  refine subroutine_ok_mono hok
    (fun ((st, msg, ret), stB) Fr s0 hpre => by
      dsimp only [withLsCodeRoLoaded,
        spqrRecvPlacedInnerSpecXTOfEnv, spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvPlacedSpecXTOfEnv, spqrRecvPlacedSpecXOfEnv,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedRawSpecXOfEnv, lsLogOff] at hpre ⊢
      let H_sp : SepProp :=
        tokenInitPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim stB s0 ∗ stackAt s0.sp spqrRecvStack ∗ Fr
      have hpre' : s0.mem ⊨
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜st.bytes.length < 2 ^ 32 ∧ msg.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s0.sp.toNat⌝ ∗
          (⌜FitsEnv M lim stB (Env st msg)⌝ ∗
          (⌜s0.readReg64 .x0 = st.v ∧ s0.readReg64 .x1 = msg.v ∧ s0.readReg64 .x8 = ret⌝ ∗
            H_sp))) := by
        dsimp only [H_sp]
        exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
      rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcro, hpre'⟩ := hpre'
      rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hbds, hpre'⟩ := hpre'
      rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfit, hpre'⟩ := hpre'
      rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx1, hx8⟩, hsp⟩ := hpre'
      have hcro' : CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem :=
        ⟨hcro.1, hcro.2⟩
      have hgoal : s0.mem ⊨
          ⌜st.bytes.length < 2 ^ 32 ∧ msg.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s0.sp.toNat⌝ ∗
          (⌜CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = st.v ∧ s0.readReg64 .x1 = msg.v ∧ s0.readReg64 .x8 = ret ∧
            FitsEnv M lim stB (Env st msg)⌝ ∗ H_sp)) := by
        rw [satisfies_pure_sepConj]; refine ⟨hbds, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hcro', ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx1, hx8, hfit⟩, hsp⟩
      dsimp only [H_sp] at hgoal
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hgoal)
    (fun ((st, msg, ret), stB) Fr s0 sf hpost => by
      dsimp only [withLsCodeRoLoaded,
        spqrRecvPlacedInnerSpecXTOfEnv, spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvPlacedSpecXTOfEnv, spqrRecvPlacedSpecXOfEnv,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedRawSpecXOfEnv, lsLogOff] at hpost ⊢
      refine Satisfies.mono
        (sepConj_mono_left (sepConj_mono_right (Entails.sepExists_mono fun evs => ?_))) hpost
      apply Entails.pure_left
      rintro ⟨htr, hevs, hnp⟩
      exact Entails.pure_right hevs (Entails.pure_right ⟨htr, hnp⟩ (Entails.refl _)))
    (fun _ _ _ _ hpanic => by
      dsimp only [withLsCodeRoLoaded,
        spqrRecvPlacedInnerSpecXTOfEnv, spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvPlacedSpecXTOfEnv, spqrRecvPlacedSpecXOfEnv,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedRawSpecXOfEnv] at hpanic ⊢
      exact hpanic)

/-- Block `329` (`spqr::recv`) seam at `SpqrRecvC07C09aBytesEnv` from `SpqrRecvPlacedContractsOfEnv`
on `trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem spqrRecv_placed_seam_c07c09a [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hRecvC : SpqrRecvPlacedContractsOfEnv H_inner A lim W.C.F W.Q.K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv W.C.F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => StatesRecvProtoEnv g.self g.msg)
      (fun _ => StatesIntoPbTightEnv)
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
          (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes))) :=
  spqrRecvPlacedInnerSpecXTOfEnv_of_placedSpecXT
    (spqr_recv_placed_ok_blockProgram_ext_of_contracts_c07c09aTightLinked
      (trTrapExternsPlaced_isPanic mmpl gh W) hRecvC)

/-- Upgrades any `SpqrV1PlacedSeamsOfEnv` bundle (reusing its Block-`327` `spqrInitialState` and
Block-`427` `spqrSendCoins` fields) to `SpqrRecvC07C09aBytesEnv` via `spqrRecv_placed_seam_c07c09a`. -/
theorem spqrV1PlacedSeamsOfEnv_of_c07c09aLinked [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {PrevRecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hBase : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv PrevRecvEnv SendEnv)
    (hRecvC : SpqrRecvPlacedContractsOfEnv H_inner A lim W.C.F W.Q.K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv W.C.F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => StatesRecvProtoEnv g.self g.msg)
      (fun _ => StatesIntoPbTightEnv)
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv where
  spqrInitialState := hBase.spqrInitialState
  spqrRecv := spqrRecv_placed_seam_c07c09a mmpl gh W hRecvC
  spqrSendCoins := hBase.spqrSendCoins

/-! ## 2. Block `507` (`try_decrypt_with_state`) Instantiation at `TryDecryptCliLinkedEnv` -/

/-- `TryDecryptCliEnvOf` at `(FmtWriteEnv, SpqrRecvC07C09aBytesEnv C.F K, FormatInnerEnv)` is
definitionally (`rfl`) equal to `DecPkD2cSlotOkLinked.TryDecryptCliLinkedEnv C K`. -/
theorem tryDecryptCliEnvOf_eq_linked (C : Crypto) (K : MlKem) :
    TryDecryptCliEnvOf C (spqrV1 C.F K) FmtWriteEnv (SpqrRecvC07C09aBytesEnv C.F K) FormatInnerEnv =
      TryDecryptCliLinkedEnv C K :=
  rfl

private theorem cliGhost_row_aux (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {sym : String} {f : State → State} (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (h1 : sym ≠ lsRustAllocSymCli := by decide) (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide) (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide) (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ lsReadFileSym := by decide) (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ CryptoVerification.SignalSession.lsMemsetSym := by decide)
    (h10 : sym ≠ CryptoVerification.SignalSession.lsMemcpySym := by decide) :
    cliGhostExterns g (cliExternsPlaced mmpl W) sym = some f :=
  (cliGhostExterns_other g _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).trans (cliExternsPlaced_row mmpl W hrow)

private theorem fmtWriteHook0_budget_ok_aux {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk fmtWriteHook0 (fmtWriteBudgetSpec M A lim) := by
  intro ⟨v, bs, st⟩ R s0 hrun hpre _
  dsimp only [fmtWriteBudgetSpec, fmtWriteBudgetEnvSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_, hmem⟩
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  dsimp only [fmtWriteBudgetSpec, fmtWriteBudgetEnvSpec]
  have hpool : A.pool lim (M.stepEvents [] st) (fmtWriteHook0 s0) = A.pool lim st s0 :=
    A.pool_transport lim st s0 (fmtWriteHook0 s0) ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  refine Satisfies.mono (sepConj_mono_left
    (Entails.sepExists_right ([] : List AllocEvent) ?_)) hmem
  rw [hpool]
  exact Entails.pure_right ⟨by simp only [fmtWriteHook0, retHook, wp_norm], rfl, rfl⟩
    (sepConj_mono_left (Entails.sepExists_right bs (Entails.refl _)))

/-- Caller-block-polymorphic Block-`507` `try_decrypt_with_state` transfer instantiated at
`TryDecryptCliLinkedEnv W.C W.Q.K`. -/
theorem cliTryDecryptPqV1_placed_at_block_linked [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqrLinked : SpqrV1PlacedSeamsOfEnv M A lim mmpl g W InitEnv
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv)
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (tryDecryptRawSpecTPTightAt W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
          (TryDecryptCliLinkedEnv W.C W.Q.K))) :=
  tryDecryptPqV1_placed_ok_PTight_cli_at_block_of_tdEnv mmpl g W ctl hG hAesDec hSpqrLinked
    (hFmtWrite := ⟨fmtWriteHook0, cliGhost_row_aux mmpl g W (fmtWrite_row_placed mmpl W),
      fmtWriteHook0_budget_ok_aux A lim⟩)
    (hFmtInner := ⟨formatInnerHook0, cliGhost_row_aux mmpl g W (formatInner_row_placed mmpl W),
      LibsignalBinary.Heap.Fine.formatInnerHook0_budget_ok M A lim⟩)
    (spqrRecvC07C09aBytesEnv_nonempty W.C.F W.Q.K)
    ⟨[], rfl⟩
    ⟨[], rfl⟩
    (fun _ _ h => h)
    hi

/-- Pointwise Block-`518` (`dpPollProgPlaced`) instantiation of Block-`507` at
`TryDecryptCliLinkedEnv W.C W.Q.K`. -/
theorem overPollTryDecrypt_placed_at_linked [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqrLinked : SpqrV1PlacedSeamsOfEnv M A lim mmpl g W InitEnv
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse
          (spqrV1 W.C.F W.Q.K) (TryDecryptCliLinkedEnv W.C W.Q.K))) :=
  cliTryDecryptPqV1_placed_at_block_linked
    (callerProg := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 518)
    mmpl g W ctl hG hAesDec hSpqrLinked (by decide)

/-- Quantified `OverCliTryDecryptPqV1PlacedStmt` at `TryDecryptCliLinkedEnv`. -/
theorem overPollTryDecrypt_placed_of_spqr_linked [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : CliHooks → InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : CliHooks → SendCall → List AllocEvent → Prop}
    (hAesDec : ∀ mmpl (W : CliHooks),
      HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqrLinked : ∀ mmpl g (W : CliHooks), SpqrV1PlacedSeamsOfEnv M A lim mmpl g W (InitEnv W)
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) (SendEnv W)) :
    OverCliTryDecryptPqV1PlacedStmt A lim (fun W => TryDecryptCliLinkedEnv W.C W.Q.K) :=
  fun mmpl g W ctl hG =>
    overPollTryDecrypt_placed_at_linked mmpl g W ctl hG (hAesDec mmpl W) (hSpqrLinked mmpl g W)

/-! ## 3. Widened Path-C Stage P3 and `CodeOk`-Generalized Path C -/

private theorem x29_eq_sp_add_c70_pathC_aux {s0 s2 : State}
    (hx29 : s2.readReg64 .x29 = s0.sp - 0x60#64)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64) :
    s2.readReg64 .x29 = s2.sp + 0xc70#64 := by
  rw [hx29, hs2_sp]; bv_omega

/-- Widened Path-C Stage P3 (`previous_sessions = [enc]`) statement over
`StageP3Prev1Env _ VerNeTopEnv`, `StageP3OkPrefixM3Env`, `StageP3ErrM3Env`,
`StageP3VerNePrev1Env VerNeTopEnv`, and `CliGhostAllocHooks M A lim g`. -/
def StageP3Prev1WideVRegsAtPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (PrevEncOK : List (BitVec 8) → Prop) : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (st_b : M.σ),
    CliGhostAllocHooks M A lim g →
    AllocContractsXCliPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    ChainClone3OkPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    SenderChainClone3OkPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
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
        (StageP3Prev1Env (tdEnv W) VerNeTopEnv recG st rem loc msgG msg msgVer enc rest) →
      initErrsPtr ≠ 0#64 →
      prevCap ≠ 0#64 →
      PrevEncOK enc →
      st.version = 4#32 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      LibsignalCodeRoLoaded lsmpl s.mem →
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
        Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s s' →
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
        SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s'
          (P_s' ∗ F_frame) Q
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
        StageP3VerNePrev1Env VerNeTopEnv recG st enc evs_p3 →
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
      SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
        (LsTokenInit ∗
          overGenP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr
            locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
            enc b_2c0 ∗
          overScratch s.sp ∗
          F_frame)
        Q
        (genP3S5ModelPanicProp W.C W.Q.K rem loc st msg msgVer rest s0)

abbrev StageP3Prev1WideVRegsPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop) : Prop :=
  StageP3Prev1WideVRegsAtPlacedStmt A lim tdEnv OverPrevEncOK

set_option maxHeartbeats 1200000 in
/-- `CodeOk`-generalized, Stage-P3-widened Path C composition (`¬ SessMatchesPm s_old y.g.msg`),
consuming `StageP2OverQpanCliMemInvPlacedStmt CodeOk` and `StageP3Prev1WideVRegsPlacedStmt`. -/
theorem closure_pathC_wide_memInv_ok [LibsignalPlacement] (CodeOk : Memory → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hP2O : StageP2OverQpanCliMemInvPlacedStmt CodeOk A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1WideVRegsPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hTry507 : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r', Scope r' → scopeIn r')
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (evs_p1 : List AllocEvent)
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hFits2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r))
    (hEnvErr2 : ∀ evs2, P2OverErrEnv y.g r evs2 → DecPkEnv y.g (evs_p1 ++ evs2))
    (hFits3 : ∀ evs2 m i k kp reg dk recG whisperG,
      P2OverOkEnv y.g r evs2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      FitsEnv M lim (M.stepEvents (evs_p1 ++ evs2) y.st)
        (StageP3Prev1Env (tdEnv W) VerNeTopEnv recG
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
          y.g.peer y.g.me whisperG y.g.msg.message
          (y.g.msg.message.messageVersion.zeroExtend 32)
          (encSession (clearPending s_old)) y.g.coins))
    (hEnvErr3 : ∀ evs2 evs3 m k (kp : IdentityKeyPair) reg dk recG G₁ whisperG,
      P2OverOkEnv y.g r evs2 →
      CloneRel recG G₁ →
      StageP3ErrM3Env (tdEnv W) recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me whisperG y.g.msg.message y.g.coins evs3 →
      DecPkEnv y.g (evs_p1 ++ evs2 ++ evs3))
    (hEnvVerNe3 : ∀ evs2 evs3 m k (kp : IdentityKeyPair) reg dk recG,
      P2OverOkEnv y.g r evs2 →
      StageP3VerNePrev1Env VerNeTopEnv recG
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        (encSession (clearPending s_old)) evs3 →
      DecPkEnv y.g (evs_p1 ++ evs2 ++ evs3))
    (hFits4 : ∀ evs2 evs3 m i k kp reg dk recG G₁ G' pt whisperG,
      P2OverOkEnv y.g r evs2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixM3Env (tdEnv W) recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me whisperG y.g.msg.message y.g.coins evs3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      let σ := cliKitStk B
      let pid := pmPreKeyId y.g.msg
      let envs := p4Envs B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
      let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
      let ses' : Session (List (BitVec 8)) :=
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
          pendingPreKey := none
          pendingKyberPreKey := none }
      FitsEnv M lim (M.stepEvents (evs_p1 ++ evs2 ++ evs3) y.st)
        (StageP4Prev1Env
          (cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ) envs.opsEnv
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ) envs.ikitEnv
          (cliPollPkKitPlaced A.repAlloc y.g.F pid σ) envs.pkKitEnv
          (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ) envs.kpkKitEnv
          StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber
          y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey m.opkId G' ses'
          (encSession (clearPending s_old))))
    (hEnv4 : ∀ evs2 evs3 evs4 m i k kp reg dk recG G₁ G' pt whisperG,
      P2OverOkEnv y.g r evs2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixM3Env (tdEnv W) recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me whisperG y.g.msg.message y.g.coins evs3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      let σ := cliKitStk B
      let pid := pmPreKeyId y.g.msg
      let envs := p4Envs B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
      let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
      let ses' : Session (List (BitVec 8)) :=
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
          pendingPreKey := none
          pendingKyberPreKey := none }
      StageP4Prev1Env
        (cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ) envs.opsEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ) envs.ikitEnv
        (cliPollPkKitPlaced A.repAlloc y.g.F pid σ) envs.pkKitEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ) envs.kpkKitEnv
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey m.opkId G' ses'
        (encSession (clearPending s_old)) evs4 →
      DecPkEnv y.g (evs_p1 ++ evs2 ++ evs3 ++ evs4))
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok (some r)))
    (hcur : r.currentSession = some s_old)
    (hnot_match : ¬ SessMatchesPm s_old y.g.msg)
    (hsteps01 : Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s0 s1)
    (htr1 : s1.trace = s0.trace)
    (hcode1 : CodeOk s1.mem)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x0868#64)
    (hrun1 : s1.status = .Running)
    (hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)) :
    let prog := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))
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
       LsTokenInit ∗
       lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post
            y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic
            y s0 sf ∗ R)) := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let st_p1 := M.stepEvents evs_p1 y.st
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  have hloadS : loadRec Scope y.g.F y.g.peer.val = .ok (some r) :=
    loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload_rel
  have hr_eq : r = ⟨some s_old⟩ := by cases r; simpa using hcur
  have hs_old : scopeIn ⟨some s_old⟩ := hr_eq ▸ hsub r (scope_of_loadRec_some hfPeer hloadS)
  have hver_old : s_old.state.sessionVersion = 4#32 := by
    have hv := hdecOk.sessVer4 r s_old hloadS hcur
    unfold SessionState.version at hv
    split at hv <;> simp_all
  have hprevOK : OverPrevEncOK (encSession (clearPending s_old)) :=
    overPrevEncOK_clearPending_of_scopeIn_placed hs_old hver_old
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  have hs1_files : s1.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed hh hsteps01 htr1).trans hf0
  have hfiles1 : FsAt (fun f => f = y.g.F) True
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 :=
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
       LsTokenInit ∗
       lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
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
       LsTokenInit ∗
       lsLogOff ∗
       stackAt sp (dpClosSubStack B)) ∗ Fr_tail := by
    dsimp only [Fr_tail]
    sep_frame
  refine sepWPp_conseq_pre hpre_split
    (overSepWPp_pollGoal_frame_placed A lim DecPkEnv B S stk' y ?_)
  refine hP2O X mmpl g W B S Scope y st_p1 r s_old StoresGhost.opened s0 s1 sp rngPtr v_a8 v_b8 v_d0 _ _
    hh hFits2 hcoins hdecOk hsub hfPeer hloadS hcur hnot_match htrusted rfl
    hfiles1 hcode1 (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hsp_sub hpc1 hrun1 hsp_align1 hregs1 ?_ ?_
  · intro sf Pf _ _ _ hsf_sp hcs_f hvregs_f _ hErr
    rcases hErr with ⟨err, evs2, hevs2, hne_p, hne_s, htr_f, hmodel, hpost_f⟩
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hm1 := Satisfies.mono (sepConj_mono_left hpost_f) hm_f
    have hstep_eq : M.stepEvents evs2 st_p1 = M.stepEvents (evs_p1 ++ evs2) y.st :=
      (M.stepEvents_append evs_p1 evs2 y.st).symm
    rw [hstep_eq] at hm1
    have hm2 : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs2) y.st) sf ∗
          anyHeap ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Satisfies.mono (by dsimp only [Fr_tail]; sep_frame) hm1
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_d2c_of_reject StoresGhost.opened hS hne_p hne_s hmodel
    have hpost_goal := overExit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y
      s0 sf (evs_p1 ++ evs2) StoresGhost.opened (.error err) anyHeap (hEnvErr2 evs2 hevs2)
      (hh.fs (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) 518) hsteps0f htr_sf hout
    exact Satisfies.mono (sepConj_mono_left hpost_goal) hm2
  · intro s2 evs_p2 m i k kp reg dk recG prevCap prevPtr whisperMsgPtr whisperG preKeyMsgRem
      hevs2 hcap_nz hpm_eq hi hk hkp hreg hacc hex hmsg_fold hsteps12 htr2 hpc2 hrun2
      hs2_sp hsp_align2 _ _ hx29_2 hvregs2 hro2
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st0 := pathAInitState ⟨W.C, W.Q⟩ meE k m dk
    let st_p2 := M.stepEvents (evs_p1 ++ evs_p2) y.st
    have hst_p2_eq : M.stepEvents evs_p2 st_p1 = st_p2 :=
      (M.stepEvents_append evs_p1 evs_p2 y.st).symm
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
      exact decPkDefD2c_pathC_panic X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver hpan_s5
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
         overScratch s2.sp ∗
         F_p3 := by
      rw [hst_p2_eq, stageP3StackFrameAt_eq_over sp (y.g.msgA + 0xc8#64) y.g.peerA, hs2_sp]
      dsimp only [F_p3, sp]
      sep_frame
    refine sepWPp_conseq_pre hpre_p3
      (overSepWPp_genP3_to_tailQpan_placed A lim DecPkEnv B S stk' y hpan_model ?_)
    refine hP3O mmpl g W st_p2 hG
      hh.alloc (cliChainClone3_placed_ok mmpl g W hh) (cliSenderChainClone3_placed_ok mmpl g W hh)
      hTry507
      (cliDropSessionStructure4_placed_ok_at mmpl g W hh
        (callerProg := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 518))
      s0 s2 y.fut y.cx y.out 8#64 prevCap prevPtr y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8
      (encSession (clearPending s_old)) y.g.coins
      recG st0 y.g.peer y.g.me whisperG y.g.msg.message F_p3 _
      (hFits3 evs_p2 m i k kp reg dk recG whisperG hevs2 hpm_eq hi hk hkp hreg hacc hex)
      (by decide) hcap_nz hprevOK hver4
      (Or.inr (distinctSid_of_decPkOk₀ hdecOk.toDecPkOk₀_emptyScope)) hSeeds hRC hPqLt
      hro2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot)
      (x29_eq_sp_add_c70_pathC_aux hx29_2 hs2_sp) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' evs_p3 pt ptCap ptPtr s' P_s' hver hcl hdec_rel hevs3 hok
        hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
        hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s'
      have hstep_p3_eq : M.stepEvents evs_p3 st_p2 = M.stepEvents (evs_p1 ++ evs_p2 ++ evs_p3) y.st :=
        (M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st).symm
      rw [hstep_p3_eq] at hent_s'
      have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c A.repAlloc σ
        y.g.stores hsub hfPeer hdecOk pid m.spkId m.kpkId y.g.msg.baseKey
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
        (closure_pathC_p4_cont_placed A lim DecPkEnv hP4O B S hh hS stk' hneed hstk63 y
          (evs_p1 ++ evs_p2 ++ evs_p3)
          hfPeer hs_old hdecOk hloadS hcur htrusted hnot_match m i k kp reg dk recG G₁ G'
          rngPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem P_s' R pt s0 s2 s'
          (hFits4 evs_p2 evs_p3 m i k kp reg dk recG G₁ G' pt whisperG
            hevs2 hpm_eq hi hk hkp hreg hacc hex hcl hdec_rel hevs3 hok)
          (fun evs4 hevs4 =>
            hEnv4 evs_p2 evs_p3 evs4 m i k kp reg dk recG G₁ G' pt whisperG
              hevs2 hpm_eq hi hk hkp hreg hacc hex hcl hdec_rel hevs3 hok hevs4)
          hpm_eq hi hk hkp hreg hacc hex hmsg_fold hs2_files htr20 hs2_sp hsp_align2 hsp_sub
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
          overScratch s2.sp ∗
          anyHeap := by
        refine Entails.trans hent_f ?_
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right
            (Entails.trans (Entails.of_eq (sepConj_emp (overScratch s2.sp)).symm)
              (sepConj_mono_right (entails_anyHeap emp))))))
      exact stageP3_exit_pathC_to_pollPost_placed A lim DecPkEnv B S hh hS stk' hneed hstk63 y
        s0 s2 sf (evs_p1 ++ evs_p2 ++ evs_p3) rngPtr whisperMsgPtr whisperG preKeyMsgRem
        (coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins))
        P_f R m.opkId m.kpkId m.spkId e
        (hEnvErr3 evs_p2 evs_p3 m k kp reg dk recG G₁ whisperG hevs2 hcl hevs3)
        hs2_sp hsp_sub hmsg_fold
        (decPkDefD2c_pathC_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver herr hne_p)
        hent_any hsf_sp htr_f hcs_f hvregs_f
    · intro evs_p3 sf P_f hver_ne hevs3 hent_f hsf_sp htr_f hcs_f hvregs_f _hro_f
      have hstep_p3_eq : M.stepEvents evs_p3 st_p2 = M.stepEvents (evs_p1 ++ evs_p2 ++ evs_p3) y.st :=
        (M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st).symm
      rw [hstep_p3_eq] at hent_f
      exact stageP3_exit_pathC_to_pollPost_placed A lim DecPkEnv B S hh hS stk' hneed hstk63 y
        s0 s2 sf (evs_p1 ++ evs_p2 ++ evs_p3) rngPtr whisperMsgPtr whisperG preKeyMsgRem
        (coinsAtPlaced y.g.coinsP y.g.coins) P_f R m.opkId m.kpkId m.spkId
        (.invalidMessage .preKey .decryptionFailed)
        (hEnvVerNe3 evs_p2 evs_p3 m k kp reg dk recG hevs2 hevs3)
        hs2_sp hsp_sub hmsg_fold
        (decPkDefD2c_pathC_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver_ne)
        hent_f hsf_sp htr_f hcs_f hvregs_f

/-! ## 4. Widened D2(c) Envelope, Poll, and Slot Dischargers -/

/-- Complete D2(c) allocation-event envelope combining `CliDpPollTrustedEnv` (untrusted, Stage P1,
Path A, Path B) with widened Path-C Stage P3 (`StageP3Prev1Env _ VerNeTopEnv`,
`StageP3OkPrefixM3Env`, `StageP3ErrM3Env`, `StageP3VerNePrev1Env VerNeTopEnv`). -/
def CliDpPollD2cWideEnv [LibsignalPlacement] {A : RustAlloc}
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let σ := cliKitStk B
  let P1 := CliStageP1OkEnv (A := A) B ReadEnv DeserEnv g
  CliDpPollTrustedEnv (A := A) W X B ReadEnv DeserEnv
    P2PathAErrEnv P2PathAOkEnv (tdEnv W) g evs ∨
  ∃ (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8))),
    (cliPollSessKitPlaced A g.F scopeKit g.peer σ).loadRel
      StoresGhost.opened.sessions g.peer.val (.ok (some r)) ∧
    r.currentSession = some s_old ∧
    ¬ SessMatchesPm s_old g.msg ∧
    (SeqEnv P1 (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) evs ∨
     (∃ m i k kp reg dk recG whisperG,
       g.msg = pmOfE m i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
         (StageP3Prev1Env (tdEnv W) VerNeTopEnv recG
           (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           g.peer g.me whisperG g.msg.message
           (g.msg.message.messageVersion.zeroExtend 32)
           (encSession (clearPending s_old)) g.coins) evs) ∨
     (∃ m k, ∃ kp : IdentityKeyPair, ∃ reg dk recG G₁ whisperG,
       CloneRel recG G₁ ∧
       SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
         (StageP3ErrM3Env (tdEnv W) recG G₁
           (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           g.peer g.me whisperG g.msg.message g.coins) evs) ∨
     (∃ m k, ∃ kp : IdentityKeyPair, ∃ reg dk recG,
       SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
         (StageP3VerNePrev1Env VerNeTopEnv recG
           (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           (encSession (clearPending s_old))) evs) ∨
     (∃ m i k kp reg dk recG G₁ G' pt whisperG,
       g.msg = pmOfE m i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
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
       SeqEnv
         (SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
           (StageP3OkPrefixM3Env (tdEnv W) recG G₁ st0
             g.peer g.me whisperG g.msg.message g.coins))
         (StageP4Prev1Env
           (cliPollSessPrev1KitPlaced A g.F g.peer σ) envs.opsEnv
           (cliPollIdKitPlaced A g.F g.peer σ) envs.ikitEnv
           (cliPollPkKitPlaced A g.F pid σ) envs.pkKitEnv
           (cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey σ) envs.kpkKitEnv
           StoresGhost.opened.sessions StoresGhost.opened.identity
           StoresGhost.opened.oneTime StoresGhost.opened.kyber
           g.peer.val g.msg.identityKey m.kpkId m.spkId g.msg.baseKey m.opkId G' ses'
           (encSession (clearPending s_old))) evs))

/-- Specialization of `CliDpPollD2cWideEnv` to `TryDecryptCliLinkedEnv W.C W.Q.K`. -/
abbrev CliDpPollD2cLinkedEnv [LibsignalPlacement] {A : RustAlloc}
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
  CliDpPollD2cWideEnv (A := A) W X B ReadEnv DeserEnv P2PathAErrEnv P2PathAOkEnv
    P2OverErrEnv P2OverOkEnv (fun W => TryDecryptCliLinkedEnv W.C W.Q.K) p4Envs g evs

set_option maxHeartbeats 1200000 in
/-- Core `CodeOk`-generalized D2(c) poll `SepWPp` composition on `dpPollEntryPlaced` (`Block 518`)
serving both `[LibsignalPlacement]` (`CliDpPollOkD2cStatePlacedAt`) and `[LibsignalFullPlacement]`
(`CliDpPollOkD2cStateFrozenPlacedAt`). -/
theorem dpPoll_d2c_wide_sepWPp_of_codeOk [LibsignalPlacement] (CodeOk : Memory → Prop)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hkeep : ∀ m m', Memory.KeepsFrozen m m' → CodeOk m → CodeOk m')
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hG : CliGhostAllocHooks M A lim gh)
    (hP2A : StageP2PathAQpanCliMemInvAtStmt CodeOk A lim ReadEnv X mmpl gh W B P2PathAErrEnv P2PathAOkEnv)
    (hP3A : StageP3GenStepsVRegsPlacedStmt)
    (hP4A : StageP4PathAPlacedStmt)
    (hP2B : StageP2MatchedFramedCliPlacedStmt)
    (hP3B : StageP3PrevEmptyVRegsPlacedStmt)
    (hP4B : StageP4MatchedPlacedStmt)
    (hP2O : StageP2OverQpanCliMemInvPlacedStmt CodeOk A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1WideVRegsPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (hTry507 : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hEnv : ∀ g evs,
      CliDpPollD2cWideEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs)
    (hh_skel : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hcode0 : CodeOk s0.mem)
    (hpre : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre y s0 ∗ R) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P' R',
      (s0.mem ⊨ P' ∗ R') ∧
      SepWPp prog (s0.readReg64 .x30) s0 P'
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R') →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R') →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_d2c_placed (W := W) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre
  have hfits_all := hpure.fits.mono (hEnv y.g)
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    exact closure_untrusted_d2c_placed_ok A lim hDropNz mmpl gh W X B S Scope hh_skel hReadFile hDeser
      hinjK hsub hS stk' hneed hstk63 y
      (hfits_all.mono fun _ h => Or.inl (Or.inl h))
      (fun evs h => hEnv y.g evs (Or.inl (Or.inl h)))
      R s0 hpc hrun hsp hpure.ro hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer
      hpure.decPkOk htrusted hm_base
  | true =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    have hh := runHooks_to_stages hh_skel
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
      cliPollKpkBudgetEnv A.repAlloc y.g.F kpkId spkId kbk σ ReadEnv
    let sp := s0.sp - 0xcd0#64
    have hsp_align0 : (s0.sp &&& 15#64 == 0#64) = true := by
      simpa [State.spAligned] using hsp
    have hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat :=
      (subStack_le_sp_of_dpPollNeed hneed hpure.stk_le_sp).1
    have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c A.repAlloc σ
      y.g.stores hsub hpure.filesOkPeer hpure.decPkOk pid sid kid kbk
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
      Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hent_stores)))) hm_base
    have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
      have := dpPollNeed_eq_frame_add_subStack B; omega
    have hp1_le := stageP1CallStack_le_subStack (A := A.repAlloc)
      0#64 y.g.F scopeKit y.g.peer B
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
      cells (y.fut + 0x70#64) 14 ∗
      cells (y.fut + 0xe0#64) 4 ∗
      memRegion (y.fut + 0x100#64) 336 ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      cells (y.fut + 0x2c8#64) 25 ∗
      ((y.fut + 0x390#64) ↦₈ b_390) ∗
      ((y.fut + 0x398#64) ↦₆₄ u_398) ∗
      ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗
      cells (y.fut + 0x428#64) 8 ∗
      cells (y.fut + 0x490#64) 4 ∗
      ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
      (sp ↦₆₄ v_sp0) ∗
      ((sp + 0x98#64) ↦₆₄ u_98) ∗
      ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
      ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
      ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
      ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
      ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
      ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
      ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x3e0#64) 368 ∗
      cells (s0.sp - 0x60#64) 12 ∗
      lsLogOff ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      A.pool lim y.st s0 ∗
      stackAt sp (stageP1CallStack kit ikit)
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
      Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
        cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
        cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced, cliPreKeyStoreSpecPlaced,
        cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
        cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
    refine ⟨P_p1 ∗ Fr_inner, R, hm_split, ?_⟩
    have hfits_p1 : FitsEnv M lim y.st (CliStageP1OkEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g) :=
      hfits_all.mono fun _ h => Or.inl (Or.inr (Or.inl h))
    have hwp := stageP1_ok_placed_inst hDropNz mmpl gh W B y.g.F y.g.peer y.g.msg.identityKey
      hh hReadFile hDeser y.st StoresGhost.opened.sessions StoresGhost.opened.identity
      hp1_64 rfl rfl
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
      (cliPollStageP1_fsAt_placed hh_skel y.g.F scopeKit y.g.peer B hpure.files_eq)
      hpc hrun hsp_align0 rfl hpure.x0 hpure.x1 hpure.x2
    refine sepWPp_bind_p1_noPanic hwp rfl ?_
    intro s1 P_1 hsteps01 hpc1 hrun1 hq1
    rcases hq1 with ⟨⟨opt, evs_p1, hevs_p1, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
      hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
      hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, hro1⟩
    have hcode1 : CodeOk s1.mem := hkeep s0.mem s1.mem hsteps01.keepsFrozen hcode0
    have htr1 : s1.trace = s0.trace := stageP1Ok_trace_eq_placed htr_evs
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
    have hrecomb := p1Ok_recombine_entails_stageP2_placed_budget stk' hneed hstk63 y
      (M.stepEvents evs_p1 y.st) s0 s1 coins v_a8 v_b8 v_d0 opt
    dsimp only at hrecomb
    refine sepWPp_conseq_pre hrecomb ?_
    let S0 : RunSem := { S with decryptPrekey := decPkDef X ⟨W.C, W.Q⟩ Scope }
    let y0 : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S0) :=
      ⟨y.out, y.fut, y.cx, y.g, y.st⟩
    cases opt with
    | none =>
      have hloadNone : loadRec Scope y.g.F y.g.peer.val = .ok none :=
        loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hpure.filesOkPeer hload_rel
      have hnone : ∀ r', loadRec Scope y.g.F y.g.peer.val = .ok (some r') →
          r'.currentSession = none := by
        intro r' hr'; rw [hloadNone] at hr'; cases hr'
      have hdecOk0 : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg :=
        hpure.decPkOk.toDecPkOk₀_of_noCurrent hnone
      have hEq : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
          S0.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins := by
        dsimp only [S0]
        rw [hS]
        exact decPkDefD2c_eq_decPkDef_of_noCurrent X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val
          y.g.me.val y.g.msg y.g.coins hnone
      refine sepWPp_pollGoal_of_decPk_eq_placed stk' y s0 s1 _ R hEq ?_
      have hsub_A : ∀ evs,
          PathAPostP1Env (A := A.repAlloc) W X B ReadEnv DeserEnv P2PathAErrEnv P2PathAOkEnv
            (tdEnv W) y.g kitEnv ikitEnv pkKitEnv kpkKitEnv evs →
          CliDpPollD2cWideEnv (A := A.repAlloc) W X B ReadEnv DeserEnv P2PathAErrEnv P2PathAOkEnv
            P2OverErrEnv P2OverOkEnv tdEnv p4Envs y.g evs :=
        fun _ hA => Or.inl (Or.inr (Or.inr (Or.inl ⟨hload_rel, hA⟩)))
      exact closure_pathA_memInv_ok_at CodeOk mmpl gh W X B S0 Scope
        hP2A hP3A hP4A hh hReadFile hDeser hTry507 hinjK hsub rfl stk' hneed hstk63 y0
        kitEnv ikitEnv pkKitEnv kpkKitEnv evs_p1 hevs_p1
        (hfits_all.mono hsub_A)
        (fun evs hA => hEnv y.g evs (hsub_A evs hA))
        s0 s1 coins v_a8 v_b8 v_d0 R
        hpure.files_eq hpure.filesOkPeer hdecOk0 hpure.coins_lt htrusted hload_rel
        hsteps01 htr1 hcode1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
    | some r =>
      obtain ⟨sess, hcur⟩ := currentSession_some_of_cliPollSessPlaced_loadRel hload_rel
      have hloadSome : loadRec Scope y.g.F y.g.peer.val = .ok (some r) :=
        loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hpure.filesOkPeer hload_rel
      rcases Classical.em (SessMatchesPm sess y.g.msg) with hmatch | hnot_match
      · have hdecOk0 : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg :=
          hpure.decPkOk.toDecPkOk₀_of_match hloadSome hcur hmatch
        have hEq : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
            S0.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins := by
          dsimp only [S0]
          rw [hS]
          exact decPkDefD2c_eq_decPkDef_of_match X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val
            y.g.me.val y.g.msg y.g.coins hloadSome hcur hmatch
        refine sepWPp_pollGoal_of_decPk_eq_placed stk' y s0 s1 _ R hEq ?_
        have hfits_p2 :
            FitsEnv M lim (M.stepEvents evs_p1 y.st)
              (StageP2MatchedEnv sess y.g.msg.identityKey) :=
          (hfits_all.mono fun _ h =>
            Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur, Or.inl h⟩)))).seq_right
            hevs_p1
        refine closure_pathB_placed_ok hP2B hP3B hP4B
          mmpl gh W X B S0 Scope hh hReadFile hDeser hTry507 hinjK hsub rfl
          stk' hneed hstk63 y0 kitEnv ikitEnv evs_p1 r sess s0 s1 coins v_a8 v_b8 v_d0 R
          hpure.files_eq hpure.filesOkPeer hdecOk0 hpure.coins_lt htrusted hload_rel hcur hfits_p2
          ?_ ?_ ?_ ?_ ?_ ?_
          hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
        · intro hne evs_p2 he2
          have he2_env : StageP2MatchedEnv sess y.g.msg.identityKey evs_p2 := by
            dsimp only [y0, dpSlotPollKStatePlaced] at hne
            unfold StageP2MatchedEnv
            simp only [hne, ↓reduceIte]
            exact he2
          exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inr
            ⟨r, sess, hload_rel, hcur, Or.inl (SeqEnv.append hevs_p1 he2_env)⟩))))
        · intro hrem evs_p2 recG he2 hex
          exact (hfits_all.mono fun _ h =>
            Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
              Or.inr ⟨hrem, recG, hex, Or.inl h⟩⟩)))).seq_right (SeqEnv.append hevs_p1 he2)
        · intro hrem hver evs_p2 recG G₁ G' evs_p3 pt he2 hex hcl hdec he3 hok
          exact (hfits_all.mono fun _ h =>
            Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
              Or.inr ⟨hrem, recG, hex, Or.inr ⟨hver, G₁, G', pt, hcl, hdec, hok, h⟩⟩⟩)))).seq_right
            (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
        · intro hrem hver evs_p2 recG G₁ G' evs_p3 pt evs_p4 he2 hex hcl hdec he3 hok he4
          exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
            Or.inr ⟨hrem, recG, hex, Or.inr ⟨hver, G₁, G', pt, hcl, hdec, hok,
              SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3) (Or.inr he4)⟩⟩⟩))))
        · intro hrem hver evs_p2 recG G₁ _G' evs_p3 _e he2 hex hcl _hdec he3 _herr _hne
          have he3_env : StageP3Env (tdEnv W) recG sess.state y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
            dsimp only [y0, dpSlotPollKStatePlaced] at hver
            unfold StageP3Env
            simp only [hver, ↓reduceIte]
            exact ⟨G₁, hcl, he3⟩
          exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
            Or.inr ⟨hrem, recG, hex,
              Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩))))
        · intro hrem hver_ne evs_p2 recG evs_p3 he2 hex he3
          have he3_env : StageP3Env (tdEnv W) recG sess.state y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
            dsimp only [y0, dpSlotPollKStatePlaced] at hver_ne
            unfold StageP3Env
            simp only [hver_ne, ↓reduceIte]
            exact he3
          exact hEnv y.g _ (Or.inl (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
            Or.inr ⟨hrem, recG, hex,
              Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩))))
      · refine closure_pathC_wide_memInv_ok CodeOk A lim DecPkEnv
          hP2O hP3O hP4O mmpl gh W hG hTry507 X B S Scope hh_skel hinjK hsub hS
          stk' hneed hstk63 y evs_p1 r sess s0 s1 coins v_a8 v_b8 v_d0 R
          ((hfits_all.mono fun _ h =>
            Or.inr ⟨r, sess, hload_rel, hcur, hnot_match, Or.inl h⟩).seq_right hevs_p1)
          (fun evs2 he2 =>
            hEnv y.g _ (Or.inr ⟨r, sess, hload_rel, hcur, hnot_match,
              Or.inl (SeqEnv.append hevs_p1 (Or.inl he2))⟩))
          ?_ ?_ ?_ ?_ ?_
          hpure.files_eq hpure.filesOkPeer hpure.decPkOk hpure.coins_lt htrusted
          hload_rel hcur hnot_match
          hsteps01 htr1 hcode1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
        · intro evs2 m i k kp reg dk recG whisperG he2 hpm hi hk hkp hreg hacc hex
          exact (hfits_all.mono fun _ h =>
            Or.inr ⟨r, sess, hload_rel, hcur, hnot_match,
              Or.inr (Or.inl ⟨m, i, k, kp, reg, dk, recG, whisperG,
                hpm, hi, hk, hkp, hreg, hacc, hex, h⟩)⟩).seq_right
            (SeqEnv.append hevs_p1 he2)
        · intro evs2 evs3 m k kp reg dk recG G₁ whisperG he2 hcl he3
          exact hEnv y.g _ (Or.inr ⟨r, sess, hload_rel, hcur, hnot_match,
            Or.inr (Or.inr (Or.inl ⟨m, k, kp, reg, dk, recG, G₁, whisperG, hcl,
              SeqEnv.append (SeqEnv.append hevs_p1 he2) he3⟩))⟩)
        · intro evs2 evs3 m k kp reg dk recG he2 he3
          exact hEnv y.g _ (Or.inr ⟨r, sess, hload_rel, hcur, hnot_match,
            Or.inr (Or.inr (Or.inr (Or.inl ⟨m, k, kp, reg, dk, recG,
              SeqEnv.append (SeqEnv.append hevs_p1 he2) he3⟩)))⟩)
        · intro evs2 evs3 m i k kp reg dk recG G₁ G' pt whisperG
            he2 hpm hi hk hkp hreg hacc hex hcl hdec he3 hok
          exact (hfits_all.mono fun _ h =>
            Or.inr ⟨r, sess, hload_rel, hcur, hnot_match,
              Or.inr (Or.inr (Or.inr (Or.inr
                ⟨m, i, k, kp, reg, dk, recG, G₁, G', pt, whisperG,
                  hpm, hi, hk, hkp, hreg, hacc, hex, hcl, hdec, hok, h⟩)))⟩).seq_right
            (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
        · intro evs2 evs3 evs4 m i k kp reg dk recG G₁ G' pt whisperG
            he2 hpm hi hk hkp hreg hacc hex hcl hdec he3 hok _σ _pid _envs _st0 _ses' he4
          exact hEnv y.g _ (Or.inr ⟨r, sess, hload_rel, hcur, hnot_match,
            Or.inr (Or.inr (Or.inr (Or.inr
              ⟨m, i, k, kp, reg, dk, recG, G₁, G', pt, whisperG,
                hpm, hi, hk, hkp, hreg, hacc, hex, hcl, hdec, hok,
                SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3) he4⟩)))⟩)

/-- `CodeOk`-generalized D2(c) poll contract (`CliDpPollOkD2cStateMemInvAt CodeOk`) on Block `518`. -/
theorem closure_trusted_d2c_wide_memInv_ok [LibsignalPlacement] (CodeOk : Memory → Prop)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hro : ∀ m, CodeOk m → LibsignalCodeRoLoaded lsmpl m)
    (hkeep : ∀ m m', Memory.KeepsFrozen m m' → CodeOk m → CodeOk m')
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hG : CliGhostAllocHooks M A lim gh)
    (hP2A : StageP2PathAQpanCliMemInvAtStmt CodeOk A lim ReadEnv X mmpl gh W B P2PathAErrEnv P2PathAOkEnv)
    (hP3A : StageP3GenStepsVRegsPlacedStmt)
    (hP4A : StageP4PathAPlacedStmt)
    (hP2B : StageP2MatchedFramedCliPlacedStmt)
    (hP3B : StageP3PrevEmptyVRegsPlacedStmt)
    (hP4B : StageP4MatchedPlacedStmt)
    (hP2O : StageP2OverQpanCliMemInvPlacedStmt CodeOk A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1WideVRegsPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (hTry507 : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hEnv : ∀ g evs,
      CliDpPollD2cWideEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs) :
    CliDpPollOkD2cStateMemInvAt CodeOk A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope := by
  intro hh_skel hReadFile hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hcode0, hpre0⟩ := extract_withMemInv hpre
  have hpre_ro : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre y s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hro s0.mem hcode0, hpre0⟩
  obtain ⟨P', R', hm', hwp⟩ :=
    dpPoll_d2c_wide_sepWPp_of_codeOk CodeOk hkeep hDropNz mmpl gh W X B S Scope hG
      hP2A hP3A hP4A hP2B hP3B hP4B hP2O hP3O hP4O hTry507 hEnv
      hh_skel hReadFile hDeser hinjK hsub hS hSemOk stk' hneed hstk63
      y R s0 hpc hrun hsp hcode0 hpre_ro
  refine ⟨P', R', hm', ?_⟩
  intro R_ext hm_ext hL
  obtain ⟨sf, hsteps, hout⟩ := hwp R_ext hm_ext hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpcm, hrunm, Pf, hmf, ⟨hpost_fn, hspf, hcsm⟩⟩ |
      ⟨hpan_st, Pf, hmf, hpan_fn⟩ | ⟨hoom_st, hoom⟩
  · refine Or.inl ⟨hpcm, hrunm, Pf, hmf, ⟨?_, hspf, hcsm⟩⟩
    intro hsteps0f hmf_r
    exact hpost_fn hsteps0f hmf_r
  · exact Or.inr (Or.inl ⟨hpan_st, Pf, hmf, hpan_fn⟩)
  · exact Or.inr (Or.inr ⟨hoom_st, hoom⟩)

/-- `[LibsignalPlacement]` D2(c) poll contract (`CliDpPollOkD2cStatePlacedAt`) on Block `518` under
widened Path-C Stage P3 (`StageP3Prev1WideVRegsPlacedStmt`). -/
theorem closure_trusted_d2c_wide_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hG : CliGhostAllocHooks M A lim gh)
    (hP2A : StageP2PathAQpanCliMemInvAtStmt (LibsignalCodeRoLoaded lsmpl)
      A lim ReadEnv X mmpl gh W B P2PathAErrEnv P2PathAOkEnv)
    (hP3A : StageP3GenStepsVRegsPlacedStmt)
    (hP4A : StageP4PathAPlacedStmt)
    (hP2B : StageP2MatchedFramedCliPlacedStmt)
    (hP3B : StageP3PrevEmptyVRegsPlacedStmt)
    (hP4B : StageP4MatchedPlacedStmt)
    (hP2O : StageP2OverQpanCliMemInvPlacedStmt (LibsignalCodeRoLoaded lsmpl)
      A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1WideVRegsPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (hTry507 : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hEnv : ∀ g evs,
      CliDpPollD2cWideEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs) :
    CliDpPollOkD2cStatePlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope := by
  intro hh_skel hReadFile hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hro0, _⟩ := extract_withLsCodeRoLoaded hpre
  exact dpPoll_d2c_wide_sepWPp_of_codeOk (LibsignalCodeRoLoaded lsmpl)
    (fun _ _ hkf h => h.of_keepsFrozen hkf)
    hDropNz mmpl gh W X B S Scope hG
    hP2A hP3A hP4A hP2B hP3B hP4B hP2O hP3O hP4O hTry507 hEnv
    hh_skel hReadFile hDeser hinjK hsub hS hSemOk stk' hneed hstk63
    y R s0 hpc hrun hsp hro0 hpre

/-- `[LibsignalFullPlacement]` (`LibsignalFrozen lsmpl`) D2(c) poll contract on Block `518` under
widened Path-C Stage P3. -/
theorem closure_trusted_d2c_wide_frozen_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hG : CliGhostAllocHooks M A lim gh)
    (hP2A : StageP2PathAQpanCliMemInvAtStmt (LibsignalFrozen lsmpl)
      A lim ReadEnv X mmpl gh W B P2PathAErrEnv P2PathAOkEnv)
    (hP3A : StageP3GenStepsVRegsPlacedStmt)
    (hP4A : StageP4PathAPlacedStmt)
    (hP2B : StageP2MatchedFramedCliPlacedStmt)
    (hP3B : StageP3PrevEmptyVRegsPlacedStmt)
    (hP4B : StageP4MatchedPlacedStmt)
    (hP2O : StageP2OverQpanCliMemInvPlacedStmt (LibsignalFrozen lsmpl)
      A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1WideVRegsPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (hTry507 : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hEnv : ∀ g evs,
      CliDpPollD2cWideEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs) :
    CliDpPollOkD2cStateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope :=
  closure_trusted_d2c_wide_memInv_ok (LibsignalFrozen lsmpl)
    (fun _ hf => ⟨LibsignalCodeLoaded.of_codeLoaded hf.2, hf.1⟩)
    (fun _ _ hkf hf => libsignalFrozen_of_keepsFrozen hf hkf)
    hDropNz mmpl gh W X B S Scope hG
    hP2A hP3A hP4A hP2B hP3B hP4B hP2O hP3O hP4O hTry507 hEnv

/-- `[LibsignalPlacement]` linked W4 D2(c) slot discharger (`DecPkD2cSlotOkPlaced`), instantiating
Block `507` at `TryDecryptCliLinkedEnv W.C W.Q.K` and lifting Block `518` through Block `520` onto
`lsProg_579`. -/
theorem decPkD2cSlotOk_placed_linked [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2PathAErrEnv P2PathAOkEnv : UnreachedPqxdhPrimitives → DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqrLinked : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2A : ∀ X, StageP2PathAQpanCliMemInvAtStmt (LibsignalCodeRoLoaded lsmpl)
      A lim ReadEnv X mmpl gh W cliRunBudgets (P2PathAErrEnv X) (P2PathAOkEnv X))
    (hP3A : StageP3GenStepsVRegsPlacedStmt)
    (hP4A : StageP4PathAPlacedStmt)
    (hP2B : StageP2MatchedFramedCliPlacedStmt)
    (hP3B : StageP3PrevEmptyVRegsPlacedStmt)
    (hP4B : StageP4MatchedPlacedStmt)
    (hP2O : StageP2OverQpanCliMemInvPlacedStmt (LibsignalCodeRoLoaded lsmpl)
      A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1WideVRegsPlacedStmt A lim (fun W => TryDecryptCliLinkedEnv W.C W.Q.K))
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (hEnv : ∀ X g evs,
      CliDpPollD2cLinkedEnv (A := A.repAlloc) W X cliRunBudgets ReadEnv DeserEnv
        (P2PathAErrEnv X) (P2PathAOkEnv X) P2OverErrEnv P2OverOkEnv p4Envs g evs →
      DecPkEnv g evs) :
    DecPkD2cSlotOkPlaced mmpl gh W A lim DecPkEnv :=
  decPkD2cSlotOk_of_poll_placed mmpl gh W hh hRead hDeser fun X S =>
    closure_trusted_d2c_wide_placed_ok hDropNz mmpl gh W X cliRunBudgets S scopeIn hG
      (hP2A X) hP3A hP4A hP2B hP3B hP4B hP2O hP3O hP4O
      (overPollTryDecrypt_placed_at_linked mmpl gh W 0#64 hG hAesDec hSpqrLinked)
      (hEnv X)

/-- Wrapper for `decPkD2cSlotOk_placed_linked` accepting a `PollBaseStagesPlacedStmt` bundle. -/
theorem decPkD2cSlotOk_placed_of_base_linked [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2PathAErrEnv P2PathAOkEnv : UnreachedPqxdhPrimitives → DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqrLinked : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hBase : PollBaseStagesPlacedStmt)
    (hP2O : StageP2OverQpanCliMemInvPlacedStmt (LibsignalCodeRoLoaded lsmpl)
      A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1WideVRegsPlacedStmt A lim (fun W => TryDecryptCliLinkedEnv W.C W.Q.K))
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (hEnv : ∀ X g evs,
      CliDpPollD2cLinkedEnv (A := A.repAlloc) W X cliRunBudgets ReadEnv DeserEnv
        (P2PathAErrEnv X) (P2PathAOkEnv X) P2OverErrEnv P2OverOkEnv p4Envs g evs →
      DecPkEnv g evs) :
    DecPkD2cSlotOkPlaced mmpl gh W A lim DecPkEnv :=
  decPkD2cSlotOk_placed_linked hDropNz mmpl gh W hG hAesDec hSpqrLinked hh hRead hDeser
    (fun X {_DecPkEnv _DeserEnv _st_b} =>
      hBase.stageP2PathA (ReadEnv := ReadEnv) mmpl gh X W cliRunBudgets)
    hBase.stageP3PathA hBase.stageP4PathA
    hBase.stageP2PathB hBase.stageP3PathB hBase.stageP4PathB
    hP2O hP3O hP4O hEnv

/-- `[LibsignalFullPlacement]` (`withLsFrozen lsmpl`) linked W4 D2(c) slot discharger
(`DecPkD2cSlotOkFrozenPlaced`), lifting Block `518` through `FrozenWrapper520` onto `lsProg_579`. -/
theorem decPkD2cSlotOk_frozen_placed_linked [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2PathAErrEnv P2PathAOkEnv : UnreachedPqxdhPrimitives → DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqrLinked : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2A : ∀ X, StageP2PathAQpanCliMemInvAtStmt (LibsignalFrozen lsmpl)
      A lim ReadEnv X mmpl gh W cliRunBudgets (P2PathAErrEnv X) (P2PathAOkEnv X))
    (hP3A : StageP3GenStepsVRegsPlacedStmt)
    (hP4A : StageP4PathAPlacedStmt)
    (hP2B : StageP2MatchedFramedCliPlacedStmt)
    (hP3B : StageP3PrevEmptyVRegsPlacedStmt)
    (hP4B : StageP4MatchedPlacedStmt)
    (hP2O : StageP2OverQpanCliMemInvPlacedStmt (LibsignalFrozen lsmpl)
      A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1WideVRegsPlacedStmt A lim (fun W => TryDecryptCliLinkedEnv W.C W.Q.K))
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (hEnv : ∀ X g evs,
      CliDpPollD2cLinkedEnv (A := A.repAlloc) W X cliRunBudgets ReadEnv DeserEnv
        (P2PathAErrEnv X) (P2PathAOkEnv X) P2OverErrEnv P2OverOkEnv p4Envs g evs →
      DecPkEnv g evs) :
    DecPkD2cSlotOkFrozenPlaced mmpl gh W A lim DecPkEnv :=
  decPkD2cSlotOk_of_poll_frozen_placed mmpl gh W hh hRead hDeser fun X S =>
    closure_trusted_d2c_wide_frozen_placed_ok hDropNz mmpl gh W X cliRunBudgets S scopeIn hG
      (hP2A X) hP3A hP4A hP2B hP3B hP4B hP2O hP3O hP4O
      (overPollTryDecrypt_placed_at_linked mmpl gh W 0#64 hG hAesDec hSpqrLinked)
      (hEnv X)

end LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux
