/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedOkTrapPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchAuxPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchPathAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathACore
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrusted
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CoinsBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Coins.CoinsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Common.StringClonePlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded `validMatch` Block-`518` Poll and Block-`520` Caller-Block Slot Closure

Composes the untrusted-identity, Path-A (`opt = none`), and Path-B (matched session) branches on
block `518` (`dpPollEntryPlaced`) and lifts the result to the block-`520` `decrypt_prekey` slot
contract for `validMatch`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification (IsLsBlockProg lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (p1LoadedRecordAt sp_sub_cd0_align_std3 stageP1CallStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeyCoroCopyAt decryptPrekeyCoroInitAt decryptPrekeySavedRegsAt processPrekeyInnerInitAt processPrekeyPostTrustAt)
open CryptoVerification.LibsignalPublicApiRepr (preKeyMsgAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt)
open CryptoVerification.SignalSession (lsReadFileSym)
open CryptoVerification.SignalSession.Cli (cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym cliSignedPreKeyVtSym dirAt)
open CryptoVerification.SignalSession.Cli.KitInst (cliIdentityStoreSpec cliSessionStoreSpec)
open CryptoVerification.SignalSession.Cli.MainHops (cliWrOk coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (dpPollNeed dpSlotArgsPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs (decPkDef dpFutStartAt pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (LsTokenInit StageP1PostRegs cliIdStoreSpecFull cliIdStoreSpecFullPlaced cliId_trustRel_eq_of_trusted cliPollIdKit cliPollId_trustUpdate_eq_placed cliPollSessKit cliPollSpkKitPlaced cliPollStoresKitsAtPlaced cliPollStoresKitsAtPlaced_entails_storesAt cliSess_loadRel_isOk closStackUnusedP1OkAt clos_stack_3280_split_for_p1_ok coroUnusedP1At coroUnusedP1AtPlaced currentSession_some_of_cliPollSessPlaced_loadRel dpClosSubStack dpFutStartAt_split_for_p1_placed dpPollEntryPlaced dpPollNeed_eq_frame_add_subStack pmKyberId preKeyMsgAt_eq_idKey_sep preKeyMsgRemIdKeyAt sepWPp_conseq_pre sepWPp_sepExists_left stackAt_poll_entry_split stackAt_subStack_split stageP1CallStack_le_subStack stageP2PostP1At subStack_le_sp_of_dpPollNeed subroutine_ok_of_sepWPp_steps trusted_ok_of_filesOkPeer)
open CryptoVerification.SignalSession.Cli.Slots (EncodeInjOn FilesOkPeer scopeIn)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudgetAux (StageP2MatchedBridgeEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (TryDecryptCliEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchAuxPlacedBudget (closure_pathB_d3_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchPathAContPlacedBudget (StageP2PathAQpanCliD3AtPlacedBudgetStmt)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchPathAPlacedBudget (closure_pathA_d3_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchUntrustedPlacedBudget (closure_untrusted_d3_placed_ok dpPollPre_unpack_d3_placed)

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchSlotPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.SignalSession.Cli.KitInst.IdKit (cliIdentityKitSpecPlaced)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustCliAllocBudgetSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget (drop_session_structure4_placed_ok_at)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedOkTrapPlacedBudget (stageP1_untrusted_ok_kit_x_ext_placed)
open LibsignalBinary.Proofs.Common.StringClonePlaced (lsRustAllocPlacedSym lsRustNoAllocShimPlacedSym)
open LibsignalBinary.Proofs.Common.StringClonePlacedBudget (stringCloneBudget_placed_codeLoaded_ok)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE kitSavePollPlacedSpec kitSavePollPlacedSpecE kitSavePollPlacedSpecI kitTrustPollPlacedSpec kitTrustPollPlacedSpecE kitTrustPollPlacedSpecI)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerContractsXPlaced serializeCanonSpecX)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns cliGhostExterns_other)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget (cliIdKitOkIE_placed cliIdentityKitDefaultBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget (cliSessKitOkSE_placed cliSessionKitDefaultBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (dpPollPost_of_slotTraceFT_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget (StageP1UntrustedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget (serializeCanonX_placed_ok_of_serContractsX)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (session_memcpy_region_lscro_of_cli)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2MemcpyBudgetSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open Arm64 ProofLib
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5Model)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (SessionExtraRel)
open CryptoVerification.E2E ( PreKeyMessageFields UnreachedPqxdhPrimitives acceptInput modelPrims )
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs (pkStoreKeys pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers (dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll ( cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessKitPlaced pathAInitSession pathAInitState pmPreKeyId )
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget ( StageP2MatchedBridgeEnv )
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget ( StageP2MatchedEnv )
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer ( CliGhostHooks cliGhostExterns )
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlacedBudget ( StageP2PathAQpanCliPlacedStmt )
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget ( StageP2MatchedFramedCliPlacedStmt )
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget ( StageP1OkEnv )
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget ( StageP3Env StageP3GenStepsVRegsPlacedStmt StageP3OkPrefixEnv pollTryDecryptPlacedSpecTPTight )
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget ( StageP2PathAEnv StageP3PrevEmptyVRegsPlacedStmt StageP4MatchedEnv StageP4MatchedPlacedStmt StageP4PathAEnv StageP4PathAPlacedStmt )
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget ( CliDpPollUntrustedEnv )
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget ( cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv cliPollSessBudgetEnv )
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget ( CliDpPollOkStatePlacedAt CliDpPollOkStatePlacedStmt )
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (stageP1ProgPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed dpWrapFrame pkToE?)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced)
open LibsignalBinary.Heap (fitsEvents_append)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudget (TryDecryptCliEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget (dpPollEntrySpatialPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget (storesAt_opened_entails_cliPollStoresKitsAtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (StageP3GenStepsVRegsPlacedStmt StageP3PrevEmptyVRegsPlacedStmt pollTryDecryptPlacedSpecTPTight)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (CliDpPollUntrustedEnv stageP1_untrusted_mangled_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedInstPlacedBudget (stageP2Matched_framed_cli_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget (stageP1OkPreAt stageP1_ok_placed_inst)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (cliPollSessBudgetEnv cliPollIdBudgetEnv cliPollPkBudgetEnv cliPollKpkBudgetEnv stageP4PathA_placed_inst stageP4Matched_placed_inst)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget (dpSlotPollKStatePlaced_inv_vm dpSlotPollKStatePlaced_res_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget (cliDecryptPrekey_ok_state_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (decPkSlotSpecPlaced dpSlotPollKStatePlaced dpSlot_ok_state_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv readFileSpecPlaced sessDeserializeSpecPlaced)

def CliStageP1OkEnv [LibsignalPlacement] {A : RustAlloc}
    (B : RunBudgets) (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (g : DecPkGhost) : List AllocEvent → Prop :=
  let σ := cliKitStk B
  StageP1OkEnv
    (cliPollSessKitPlaced A g.F scopeKit g.peer σ)
    (cliPollSessBudgetEnv A g.F g.peer σ DeserEnv ReadEnv)
    CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions
    (cliPollIdKitPlaced A g.F g.peer σ)
    (cliPollIdBudgetEnv A g.F g.peer σ ReadEnv)
    CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
    g.peer.val g.msg.identityKey

def DecPkD3ValidMatchPollEnv [LibsignalPlacement] {A : RustAlloc}
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let σ := cliKitStk B
  let sessKit := cliPollSessKitPlaced A g.F scopeKit g.peer σ
  let kitEnv := cliPollSessBudgetEnv A g.F g.peer σ DeserEnv ReadEnv
  let idKit := cliPollIdKitPlaced A g.F g.peer σ
  let ikitEnv := cliPollIdBudgetEnv A g.F g.peer σ ReadEnv
  let P1 := CliStageP1OkEnv (A := A) B ReadEnv DeserEnv g
  CliDpPollUntrustedEnv (A := A) B ReadEnv DeserEnv g evs ∨
  P1 evs ∨
  (sessKit.loadRel CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions g.peer.val (.ok none) ∧
    (SeqEnv P1 (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv g) evs ∨
     ∃ m i k kp reg dk recG,
       pkToE? g.msg = some m ∧
       g.msg.message = i ∧
       CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       (SeqEnv (SeqEnv P1 (P2PathAOkEnv g))
          (StageP3Env tdEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            g.peer g.me g.msgG.msg g.msg.message
            (g.msg.message.messageVersion.zeroExtend 32) g.coins) evs ∨
        ∃ G₁ G' pt,
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
            g.msg.message.messageVersion.zeroExtend 32 ∧
          CloneRel recG G₁ ∧
          G₁.AfterTryDecrypt true G' ∧
          (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins
            (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt ∧
          SeqEnv
            (SeqEnv (SeqEnv P1 (P2PathAOkEnv g))
              (StageP3OkPrefixEnv tdEnv recG G₁
                (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
                g.peer g.me g.msgG.msg g.msg.message g.coins))
            (StageP4PathAEnv
              sessKit kitEnv idKit ikitEnv
              (cliPollPkKitPlaced A g.F (pmPreKeyId g.msg) σ)
              (cliPollPkBudgetEnv A g.F (pmPreKeyId g.msg) σ ReadEnv)
              (cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey σ)
              (cliPollKpkBudgetEnv A g.F m.kpkId m.spkId g.msg.baseKey σ ReadEnv)
              CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
              CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber
              g.peer.val g.msg.identityKey m.opkId m.kpkId m.spkId g.msg.baseKey
              { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
                state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins
                  (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2
                pendingPreKey := none
                pendingKyberPreKey := none }) evs))) ∨
  (∃ (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8))),
    sessKit.loadRel CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions g.peer.val (.ok (some r)) ∧
    r.currentSession = some sess ∧
    (SeqEnv P1 (StageP2MatchedEnv sess g.msg.identityKey) evs ∨
     (sess.state.remoteIdentity = some g.msg.identityKey ∧
      ∃ recG, SessionExtraRel recG sess ∧
        (SeqEnv (SeqEnv P1 StageP2MatchedBridgeEnv)
           (StageP3Env tdEnv recG sess.state g.peer g.me g.msgG.msg g.msg.message
             (g.msg.message.messageVersion.zeroExtend 32) g.coins) evs ∨
         (sess.state.version = g.msg.message.messageVersion.zeroExtend 32 ∧
          ∃ G₁ G' pt,
            CloneRel recG G₁ ∧
            G₁.AfterTryDecrypt true G' ∧
            (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state).1 = .ok pt ∧
            SeqEnv
              (SeqEnv (SeqEnv P1 StageP2MatchedBridgeEnv)
                (StageP3OkPrefixEnv tdEnv recG G₁ sess.state g.peer g.me g.msgG.msg
                  g.msg.message g.coins))
              (StageP4MatchedEnv sessKit kitEnv idKit ikitEnv
                CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
                g.peer.val g.msg.identityKey
                { sess with
                  state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state).2
                  pendingPreKey := none
                  pendingKyberPreKey := none }) evs)))))

def DecPkD3ValidMatchEnv [LibsignalPlacement] (A : RustAlloc)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  DecPkD3ValidMatchPollEnv (A := A) W X B ReadEnv DeserEnv P2PathAErrEnv P2PathAOkEnv tdEnv g evs

def DecPkD3ValidMatchCliEnv [LibsignalPlacement] (A : RustAlloc)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  DecPkD3ValidMatchEnv A W X B
    (ReadFileRuleEnv cliIo.rd)
    SessDeserializeCancelEnv
    P2PathAErrEnv P2PathAOkEnv
    (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K))
    g evs

def CliDpPollOkD3StatePlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
    A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
  subroutine_ok (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
    (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
  subroutine_ok (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
    (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
  EncodeInjOn scopeKit →
  (∀ r, Scope r → scopeIn r) →
  S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope →
  (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
    FilesOkPeer Scope F peer ∧ DecPkOkD3 ⟨W.C, W.Q⟩ Scope F peer me pm) →
  ∀ stk' : Nat, (dpSlotPollKStatePlaced A lim DecPkEnv B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
    subroutine_ok (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) dpPollEntryPlaced
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk'))

theorem seqEnv_append_d3 {E₁ E₂ : List AllocEvent → Prop} {evs₁ evs₂ : List AllocEvent}
    (h1 : E₁ evs₁) (h2 : E₂ evs₂) : SeqEnv E₁ E₂ (evs₁ ++ evs₂) :=
  Or.inr ⟨evs₁, evs₂, rfl, h1, h2⟩

theorem fitsEnv_after_d3 {M : AllocCostModel} {lim : BudgetLimits}
    {FullEnv RemEnv : List AllocEvent → Prop} {st : M.σ} {evs_pre : List AllocEvent}
    (hfits : FitsEnv M lim st FullEnv)
    (hsub : ∀ evs, RemEnv evs → FullEnv (evs_pre ++ evs)) :
    FitsEnv M lim (M.stepEvents evs_pre st) RemEnv := fun evs hevs =>
  ((fitsEvents_append M lim evs_pre evs st).mp (hfits (evs_pre ++ evs) (hsub evs hevs))).2

theorem sepWPp_bind_p1_false_d3 {prog : Program} {mid target : BitVec 64} {s0 : State}
    {P1 Fr : SepProp} {Q1 Q Qpan : State → SepProp → Prop}
    (hwp1 : SepWPp prog mid s0 P1 Q1 (fun _ _ => False))
    (hk : ∀ s1 P_1, Steps prog s0 s1 → s1.pc = mid → s1.status = .Running →
      Q1 s1 P_1 → SepWPp prog target s1 (P_1 ∗ Fr) Q Qpan) :
    SepWPp prog target s0 (P1 ∗ Fr) Q Qpan := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨s1, hsteps01, ⟨hpc1, hrun1, P_1, hm1, hq1⟩ | ⟨_, _, _, hfalse⟩ | ⟨_, hoom⟩⟩ :=
    hwp1 (Fr ∗ R) hm hL
  · rw [← sepConj_assoc] at hm1
    obtain ⟨sf, hsteps1f, hout⟩ :=
      hk s1 P_1 hsteps01 hpc1 hrun1 hq1 R hm1 (hsteps01.codeLoaded hL)
    exact ⟨sf, Steps.trans hsteps01 hsteps1f, hout⟩
  · exact False.elim hfalse
  · exact (not_satisfies_false_sepConj hoom).elim

theorem p1Ok_post_eq_stageP2PostP1At_budget_d3_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_p1 : M.σ) (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (opt : Option (SessionRecord (List (BitVec 8)))) :
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
    (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      p1LoadedRecordAt Scope A.repAlloc y.fut opt ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗
      cells (y.fut + 0x398#64) 2 ∗
      ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
      ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      A.pool lim st_p1 s1) ∗
    (memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗
      closStackUnusedP1OkAt sp ∗
      memRegion y.out 48) =
    stageP2PostP1At (A.atState lim st_p1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Scope A.repAlloc y.fut opt := by
  dsimp only [stageP2PostP1At, LibsignalBinary.Heap.RustCliAllocBudget.atState, cliPollSessKitPlaced,
    cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced, cliPollKpkKitPlaced,
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliIdStoreSpecFullPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSignedPreKeyStoreSpecPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKpkStoreSpecFullPlaced,
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced]
  sep_frame

theorem p1Ok_recombine_entails_stageP2_budget_d3_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (stk' : Nat) (_hneed : dpPollNeed B ≤ stk') (_hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_p1 : M.σ) (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (opt : Option (SessionRecord (List (BitVec 8)))) :
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
    (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗
      cells (y.fut + 0x398#64) 2 ∗
      ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
      ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      lsLogOff ∗
      kit.storeAt (y.g.stores + 0xf0#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions ∗
      ikit.identityAt y.g.stores
        (ikit.trustUpdate CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey
          .receiving (.ok true)) ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      A.pool lim st_p1 s1 ∗
      stackAt sp (stageP1CallStack kit ikit)) ∗
    (memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗
      closStackUnusedP1OkAt sp ∗
      memRegion y.out 48 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP1CallStack kit ikit) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.pub ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit) ⊢
    stageP2PostP1At (A.atState lim st_p1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗
    preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
    LsTokenInit ∗
    lsLogOff ∗
    stackAt sp (dpClosSubStack B) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le : stageP1CallStack kit ikit ≤ dpClosSubStack B :=
    stageP1CallStack_le_subStack (A := A.repAlloc) 0#64 y.g.F scopeKit y.g.peer B
  have hstores_back := cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc)
    (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer)
    (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened
  have hp1_eq := p1Ok_post_eq_stageP2PostP1At_budget_d3_placed (Scope := scopeKit)
    y st_p1 s0 s1 rngPtr v_a8 v_b8 v_d0 opt
  dsimp only at hp1_eq
  have hp1_ent := Entails.of_eq hp1_eq
  have hpm_ent := Entails.of_eq
    (preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg).symm
  have hstk_ent := Entails.of_eq
    (stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64).symm
  have h4 := sepConj_mono hp1_ent (sepConj_mono hstores_back (sepConj_mono hpm_ent hstk_ent))
  let Pass : SepProp :=
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    LsTokenInit ∗
    lsLogOff ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  refine Entails.trans ?_ (Entails.trans (sepConj_mono_left h4 : _ ∗ Pass ⊢ _ ∗ Pass) ?_)
  · dsimp only [cliPollId_trustUpdate_eq_placed, cliPollStoresKitsAtPlaced, Pass,
      sp, σ, pid, sid, kid, kbk, kit, ikit]
    sep_frame
  · dsimp only [Pass, sp, σ, kit, ikit]
    sep_frame

set_option maxHeartbeats 1200000 in

theorem decPk_d3_validMatch_poll_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop} (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hP2A : StageP2PathAQpanCliD3AtPlacedBudgetStmt A lim ReadEnv DeserEnv X mmpl gh W B
      P2PathAErrEnv P2PathAOkEnv)
    (hP3A : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.StageP3GenStepsVRegsPlacedStmt)
    (hP3B : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hEnv : ∀ g evs,
      DecPkD3ValidMatchPollEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv tdEnv g evs →
      DecPkEnv g evs) :
    CliDpPollOkD3StatePlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope := by
  intro hh hRead hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_d3_placed (X := X) (W := W) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre
  obtain ⟨_m0, _, _, _hpk0, hdec0⟩ := hpure.decPkOk
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  have hEqP :
      CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
    dsimp only [CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced, stageP1ProgPlaced]
    rw [withPanics_cliGhostExterns mmpl gh W]
  have hRead' := hEqP ▸ hRead
  have hDeser' := hEqP ▸ hDeser
  cases b with
  | false =>
    dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget.dpPollEntrySpatialPlaced] at hm_base
    rw [hEqP]
    exact closure_untrusted_d3_placed_ok A lim hDropNz mmpl gh W X B S Scope
      hh hRead' hDeser' hinjK hsub hS stk' hneed' hstk63 y
      (fun evs hevs => hpure.fits evs (hEnv y.g evs (Or.inl hevs)))
      (fun evs hevs => hEnv y.g evs (Or.inl hevs))
      R s0 hpc hrun hsp hpure.ro hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer
      hpure.decPkOk htrusted hm_base
  | true =>
    dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget.dpPollEntrySpatialPlaced] at hm_base
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
          pid sid kid kbk σ y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
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
      stageP1OkPreAt A lim y.st kit ikit CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
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
      pkKit.storeAt (y.g.stores + 0xc8#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.pub ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit
    have hm_split : s0.mem ⊨ (P_p1 ∗ Fr_inner) ∗ R :=
      Satisfies.mono (by
        dsimp only [P_p1, Fr_inner, stageP1OkPreAt, kit, ikit, pkKit, spkKit, kpkKit,
          cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
          cliPollKpkKitPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliIdStoreSpecFullPlaced,
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSignedPreKeyStoreSpecPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKpkStoreSpecFullPlaced,
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
      hhSt hRead' hDeser' y.st CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
      (Nat.le_trans hp1_le hsub64) rfl rfl
      (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
      (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
        cliId_trustRel_eq_of_trusted htrusted h)
      hfits_p1
      s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
      v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
      b_390 b_4f2
      hpure.ro
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollStageP1_fsAt_placed
        hh y.g.F scopeKit y.g.peer B hpure.files_eq)
      hpc hrun hsp_align0 rfl hpure.x0 hpure.x1 hpure.x2
    refine sepWPp_bind_p1_false_d3 hwp ?_
    intro s1 P_1 hsteps01 hpc1 hrun1 hq1
    rcases hq1 with ⟨⟨opt, evs_p1, hP1_raw, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
      hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
      hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, hro1⟩
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
            ⟨hload_rel, Or.inl (LibsignalBinary.Heap.SeqEnv.append hevs_p1 (Or.inl he2))⟩)))
      refine closure_pathA_d3_placed_ok mmpl gh W X B S hP2A hP3A
        (stageP4PathA_placed_inst hDropNz) Scope hhSt hRead' hDeser' hTryDec
        hinjK hsub hS stk' hneed' hstk63 y kitEnv ikitEnv pkKitEnv kpkKitEnv
        rfl rfl rfl (fun _ _ => rfl)
        evs_p1 s0 s1 coins v_a8 v_b8 v_d0 R
        hpure.files_eq hpure.filesOkPeer hpure.decPkOk hpure.coins_lt htrusted hload_rel
        hfits_p2 hevs_p2_err ?_ ?_ ?_ ?_ ?_ ?_
        hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
      · intro evs_p2 m i k kp reg dk recG he2 hpk hmsg_i hi hk hkp hreg hacc hex
        exact (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
            hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, Or.inl h⟩⟩))).seq_right
          (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2)
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt he2 hpk hmsg_i hi hk hkp hreg hacc hex
          hver hcl hdec he3 hok
        exact (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
            hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex,
            Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok, h⟩⟩⟩))).seq_right
          (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3)
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4 he2 hpk hmsg_i hi hk hkp hreg hacc hex
          hver hcl hdec he3 hok he4
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
          hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex,
          Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok,
            LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3)
              (Or.inr (Or.inr (Or.inr he4)))⟩⟩⟩)))
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4 he2 hpk hmsg_i hi hk hkp hreg hacc hex
          hver hcl hdec he3 hok he4
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
          hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex,
          Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok,
            LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3)
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
          Or.inl (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3_env)⟩⟩)))
      · intro evs_p2 m i k kp reg dk recG evs_p3 he2 hpk hmsg_i hi hk hkp hreg hacc hex hver_ne he3
        have he3_env : StageP3Env tdEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
          unfold StageP3Env
          simp only [hver_ne, ↓reduceIte]
          exact he3
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
          hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex,
          Or.inl (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3_env)⟩⟩)))
    | some r =>
      obtain ⟨sess, hcur⟩ := currentSession_some_of_cliPollSessPlaced_loadRel hload_rel
      have hfits_p2 :
          FitsEnv M lim (M.stepEvents evs_p1 y.st)
            (StageP2MatchedEnv sess y.g.msg.identityKey) :=
        (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur, Or.inl h⟩))).seq_right hevs_p1
      refine closure_pathB_d3_placed_ok stageP2Matched_framed_cli_placed_ok hP3B
        (stageP4Matched_placed_inst hDropNz) mmpl gh W X B S Scope
        hhSt hRead' hDeser' hTryDec hinjK hsub hS stk' hneed' hstk63
        y kitEnv ikitEnv rfl rfl evs_p1 r sess s0 s1 coins v_a8 v_b8 v_d0 R
        hpure.files_eq hpure.filesOkPeer hpure.decPkOk hpure.coins_lt htrusted hload_rel hcur hfits_p2
        ?_ ?_ ?_ ?_ ?_ ?_
        hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
      · intro hne evs_p2 he2
        have he2_env : StageP2MatchedEnv sess y.g.msg.identityKey evs_p2 := by
          unfold StageP2MatchedEnv
          simp only [hne, ↓reduceIte]
          exact he2
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inr
          ⟨r, sess, hload_rel, hcur, Or.inl (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2_env)⟩)))
      · intro hrem evs_p2 recG he2 hex
        exact (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
            Or.inr ⟨hrem, recG, hex, Or.inl h⟩⟩))).seq_right (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2)
      · intro hrem hver evs_p2 recG G₁ G' evs_p3 pt he2 hex hcl hdec he3 hok
        exact (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
            Or.inr ⟨hrem, recG, hex, Or.inr ⟨hver, G₁, G', pt, hcl, hdec, hok, h⟩⟩⟩))).seq_right
          (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3)
      · intro hrem hver evs_p2 recG G₁ G' evs_p3 pt evs_p4 he2 hex hcl hdec he3 hok he4
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
          Or.inr ⟨hrem, recG, hex, Or.inr ⟨hver, G₁, G', pt, hcl, hdec, hok,
            LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3) (Or.inr he4)⟩⟩⟩)))
      · intro hrem hver evs_p2 recG G₁ G' evs_p3 e he2 hex hcl _hdec he3 _herr _hne
        have he3_env : StageP3Env tdEnv recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
          unfold StageP3Env
          simp only [hver, ↓reduceIte]
          exact ⟨G₁, hcl, he3⟩
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
          Or.inr ⟨hrem, recG, hex,
            Or.inl (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3_env)⟩⟩)))
      · intro hrem hver_ne evs_p2 recG evs_p3 he2 hex he3
        have he3_env : StageP3Env tdEnv recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
          unfold StageP3Env
          simp only [hver_ne, ↓reduceIte]
          exact he3
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
          Or.inr ⟨hrem, recG, hex,
            Or.inl (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hevs_p1 he2) he3_env)⟩⟩)))

theorem cliDecryptPrekey_slot_d3_match_placedBudget_at_block [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2A : StageP2PathAQpanCliD3AtPlacedBudgetStmt A lim ReadEnv DeserEnv X mmpl gh W B
      P2PathAErrEnv P2PathAOkEnv)
    (hP3A : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.StageP3GenStepsVRegsPlacedStmt)
    (hP3B : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
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
    subroutine_ok prog (lsmpl.base 520) (decPkSlotSpecPlaced A lim DecPkEnv S stk) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hpan : Rust.withPanics H = H := withPanics_cliGhostExterns mmpl gh W
  have : IsLsBlockProg prog i (Rust.withPanics H) := by
    rw [hpan]; exact hcaller
  have hpoll := decPk_d3_validMatch_poll_placedBudget hDropNz mmpl gh W X B S Scope
    hP2A hP3A hP3B hTryDec hevs_sub
  exact dpSlot_ok_state_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_placed_at_block (ext := H)
      (dpSlotPollKStatePlaced A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_inv_vm A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_res_vm A lim DecPkEnv B S)
      (fun stk' hs1 hs2 => hpoll hh hRead hDeser hinjK hsub hS hok stk' hs1 hs2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, dpSlotPollKStatePlaced] at hstk ⊢
          omega)
      hstk64 hi)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchSlotPlacedBudget
