/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.D3MatchingPathBSeqFreeR -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBKitsPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBMainPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1Placed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget -- proof-setup: allow-public-import
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

public section

/-!
# `FdsGe3Closed`-Threaded Poll and Block-`520` Slot Wrapper for Matching-Session Path B

Routes poll-entry store kits through block `589` (`Dir::get`) and lifts the resulting `withFds A`
slot contract to `SkeletonPlacedBudgetFd.slotWithPreFdsGe3Closed` at `A`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPollPlacedBudgetFd

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (
  IsLsBlockProg LibsignalFrozen LibsignalFullPlacement LibsignalHooks LibsignalPlacement
  libsignalFrozen_of_keepsFrozen lsmpl lsρ
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  loadCallStack p1LoadedRecordAt sp_sub_cd0_align_std3 stageP1CallStack stageP1UntrustedCallStack
)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  decryptPrekeyCoroCopyAt decryptPrekeyCoroInitAt decryptPrekeySavedRegsAt
  processPrekeyInnerInitAt processPrekeyPostTrustAt
)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalPublicApiRepr (apiDecResultAt preKeyMsgAt)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (extHookStack noAllocShimSpec withLsFrozen)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced isCliPanicSymbolPlaced lsReadFileSym lsReadStdinSym
  lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
  lsRustReallocSymCli lsStringCloneSym
)
open CryptoVerification.SignalSession.Cli (
  StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym
  cliSignedPreKeyVtSym dirAt
)
open CryptoVerification.SignalSession.Cli.KitInst (
  cliIdentityStoreSpec cliKyberPreKeyStoreSpecPlaced cliPreKeyStoreSpecPlaced
  cliSessionStoreSpec cliSignedPreKeyStoreSpecPlaced
)
open CryptoVerification.SignalSession.Cli.MainHops (
  cliIo cliRunBudgets_placed cliWrOk coinsInstalledPlaced storesAt
)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_589)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost RunNeeds RunSem decResAt dpPollNeed dpSlotArgsPlaced slotOut slotOutTr slotTrace
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliGhostExterns cliGhostExterns_other
)
open CryptoVerification.SignalSession.Cli.RunProofs (
  cliDecryptPrekeyNeed decPkDef dpCxAt dpFutDoneAt dpFutStartAt dpWrapFrame
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit StageP1PostRegs apiDecResultAt_untrusted_entails_decResAt
  cliIdStoreSpecFull cliIdStoreSpecFullPlaced cliId_trustRel_eq_of_trusted cliKitStk
  cliKpkStoreSpecFullPlaced cliPollIdKit cliPollIdKitPlaced cliPollId_trustUpdate_eq_placed
  cliPollId_vtablesPlacedOk cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessKit
  cliPollSessKitPlaced cliPollSess_vtablesPlacedOk cliPollSpkKitPlaced cliPollStoresKitsAtPlaced
  cliPollStoresKitsAtPlaced_entails_storesAt cliSess_loadRel_isOk
  closStackUnusedP1OkAt closStackUnusedUntrustedAt clos_stack_3280_of_p1_untrusted
  clos_stack_3280_split_for_p1_ok clos_stack_3280_split_for_p1_untrusted
  closureCalleeSaved_toCalleeSavedPreserved coroUnusedP1At
  coro_of_p1_untrusted_entails_dpFutDoneAt currentSession_some_of_cliPollSessPlaced_loadRel
  decPkDef_of_trust_err dpClosSubStack dpFutStartAt_split_for_p1_placed
  dpPollEntryPlaced dpPollNeed_eq_frame_add_subStack dpPollProgPlaced
  loadRec_of_cliPollSessPlaced_loadRel pmKyberId pmPreKeyId preKeyMsgAt_eq_idKey_sep
  preKeyMsgRemIdKeyAt sepWPp_conseq_pre sepWPp_sepExists_left slotOutTr_of_err
  sp_frame_sub_add stackAt_poll_entry_split stackAt_subStack_split
  stageP1CallStack_le_subStack stageP1Ok_trace_eq_placed stageP1UntrustedCallStack_le_subStack
  stageP2PostP1At subStack_le_sp_of_dpPollNeed subroutine_ok_of_sepWPp_steps
  trusted_ok_of_filesOkPeer
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  EncodeInjOn FilesOkPeer encodeInjOn_deserializeScopeP_Q filesOk₀ loadRec scopeIn scopeKit
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.PeakBudget.D3MatchingPathBSeqFreeR (
  DecPkD3MatchingPathBGvEnv DecPkD3MatchingPathBGvSeqFreeOfReadEnv
  MatchingPathBGvMainEnv MatchingPathBGvPollEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  DecPkOkPathB storesAt_opened_entails_cliPollStoresKitsAtPlaced_pathB
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBKitsPlacedBudgetFd (
  cliPollId_kitPlacedOkI_untrusted_of_dirGet cliPollSess_kitPlacedOkSE_untrusted_of_dirGet
  cliPollSess_seqFreeKitPlacedOkSE_of_dirGet dpPollPre_unpack_pathB_frozen_placedBudget
  extHookStack_le_cliPollSess_loadCallStack slotOk_decPkFrozenPlaced_withFds_to_preFd
  stageP1_ok_placed_inst_of_dirGet toSkeletonRunHooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBMainPlacedBudgetFd (
  decPk_matchingPathB_main_gv_frozen_placedBudget_of_dirGet
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (withFds withFds_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  RunSlotEnvs decPkSlotSpecFrozenPlaced slotsOfSigPkFrozenPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget (
  dpPollEntrySpatialPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget (
  cliPollStageP1_fsAt_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget (
  StageP1OkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  pollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  CliDpPollUntrustedEnv StageP1UntrustedMangledPlacedStmt dpPollPost_of_decResAt_placed
  runHooks_to_stages stageP1_untrusted_mangled_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollSessBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget (
  dpSlotPollKStatePlaced_inv_vm dpSlotPollKStatePlaced_res_vm
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget (
  cliDecryptPrekey_ok_state_frozen_placed_at_block
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd (
  slotWithPreFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
  dpSlot_ok_state_frozen_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  dirGetSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## 1. Untrusted / Trusted Stage-P1 Continuations (`of_dirGet`) -/

theorem p1Ok_post_eq_stageP2PostP1At_placedBudget [LibsignalPlacement]
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
  dsimp only [stageP2PostP1At, LibsignalBinary.Heap.RustCliAllocBudget.atState,
    cliPollSessKitPlaced, cliPollIdKitPlaced, cliIdStoreSpecFullPlaced,
    cliPollPkKitPlaced, cliPreKeyStoreSpecPlaced,
    cliPollSpkKitPlaced, cliSignedPreKeyStoreSpecPlaced,
    cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced,
    cliKyberPreKeyStoreSpecPlaced]
  sep_frame

theorem p1Ok_recombine_entails_stageP2_placedBudget [LibsignalPlacement]
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
      p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗ ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
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
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ lsLogOff ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗ ikit.identityAt y.g.stores
        (ikit.trustUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey
          .receiving (.ok true)) ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗ A.pool lim st_b s1 ∗
      stackAt sp (stageP1CallStack kit ikit)) ∗
    (memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗ closStackUnusedP1OkAt sp ∗ memRegion y.out 48 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP1CallStack kit ikit) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit) ⊢
    stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗
    preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
    LsTokenInit ∗ lsLogOff ∗ stackAt sp (dpClosSubStack B) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 := by
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
    (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
  have hp1_eq := p1Ok_post_eq_stageP2PostP1At_placedBudget (Scope := scopeKit)
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
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit ∗ lsLogOff ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32
  refine Entails.trans ?_ (Entails.trans (sepConj_mono_left h4 : _ ∗ Pass ⊢ _ ∗ Pass) ?_)
  · dsimp only [cliPollId_trustUpdate_eq_placed, cliPollStoresKitsAtPlaced, Pass,
      sp, σ, pid, sid, kid, kbk, kit, ikit]
    sep_frame
  · dsimp only [Pass, sp, σ, kit, ikit]
    sep_frame

theorem sepWPp_bind_p1_false {prog : Program} {mid ret : BitVec 64}
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

theorem withPanics_cliGhostExterns_eq (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) :
    Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      cliGhostExterns gh (cliExternsPlaced mmpl W) := by
  funext name
  by_cases hp : Rust.isPanicSymbol name = true
  · have hother : cliGhostExterns gh (cliExternsPlaced mmpl W) name = cliExternsPlaced mmpl W name :=
      cliGhostExterns_other gh (cliExternsPlaced mmpl W)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustAllocSymCli] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustDeallocSymCli] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustReallocSymCli] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustAllocZeroedSymCli] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustNoAllocShimSymCli] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsReadFileSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsReadStdinSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsMemsetSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsMemcpySym] at hp)
    unfold Rust.withPanics
    rw [hother]
    unfold cliExternsPlaced isCliPanicSymbolPlaced
    simp [hp]
  · simp [Rust.withPanics, hp]

private theorem hookSat_sessionMemcpyRegionBudget_of_codec {H : CryptoVerification.LibsignalHooks}
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

theorem closure_untrusted_pathB_placedBudget_of_dirGet [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed))
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
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗ dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗ memRegion y.cx 32 ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
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
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
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
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗ A.pool lim y.st s0 ∗
    stackAt sp (stageP1UntrustedCallStack kit ikit)
  let Fr_inner : SepProp :=
    cells (y.fut + 0x428#64) 8 ∗ cells (y.fut + 0x490#64) 4 ∗ ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
    coroUnusedP1At y.fut ∗ closStackUnusedUntrustedAt sp ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit
  have hm_split : s0.mem ⊨ P_p1 ∗ (Fr_inner ∗ R) :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
      cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
      cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced,
      cliPreKeyStoreSpecPlaced,
      cliSignedPreKeyStoreSpecPlaced,
      cliKpkStoreSpecFullPlaced,
      cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
  refine ⟨P_p1, Fr_inner ∗ R, hm_split, ?_⟩
  have hwp := hUntrusted
    (M := M) (A := A) (lim := lim) (ext := cliGhostExterns gh (cliExternsPlaced mmpl W))
    (Scope := scopeKit) (encRecord := encodeRecord)
    (kit := kit) (kitEnv := LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv)
    (ikit := ikit) (ikitEnv := LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv)
    (st := StoresGhost.opened.sessions) (ist := StoresGhost.opened.identity) (st_b := y.st)
    y.g.peer y.g.msg.identityKey
    hh.alloc
    hh.codecHooks.dealloc
    ((show withVmPreserved noAllocShimSpec = sessionShimBudgetSpec from rfl) ▸ hh.codecHooks.shim)
    hh.codecHooks.alloc
    (hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)
    (cliPollSess_vtablesPlacedOk (A := A.repAlloc) y.g.F scopeKit y.g.peer σ hDropNz)
    (cliPollId_vtablesPlacedOk (A := A.repAlloc) y.g.F y.g.peer σ hDropNz)
    (cliPollSess_kitPlacedOkSE_untrusted_of_dirGet mmpl gh W hDropNz hh hGet hDeser)
    (cliPollId_kitPlacedOkI_untrusted_of_dirGet mmpl gh W hDropNz hh hGet)
    hp1_64 (extHookStack_le_cliPollSess_loadCallStack A.repAlloc B y.g.F y.g.peer) rfl rfl
    (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
      StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
      StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
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
    have hloadRec : loadRec Scope y.g.F y.g.peer.val = .ok opt :=
      loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload
    have hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none := by
      rw [hS]
      exact decPkDef_of_trust_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadRec (Or.inr htrusted)
    have hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) s0.trace sf.trace :=
      slotOutTr_of_err StoresGhost.opened s0.trace sf.trace nofun nofun hans
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
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    let Leftover : SepProp :=
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit
    have hmf_reord : sf.mem ⊨
        (apiDecResultAt A.repAlloc y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
            pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
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
      have htrust_id : ikit.trustUpdate StoresGhost.opened.identity y.g.peer.val
          y.g.msg.identityKey .receiving (.ok false) = StoresGhost.opened.identity := rfl
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
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
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
      StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) Leftover
      hh (hevs_sub evs hevs_p1) hsteps htr_eq hout
    exact Satisfies.mono (sepConj_mono_left hpost) hmf_folded
  · intro _ _ hfalse _ _
    exact False.elim hfalse

set_option maxHeartbeats 800000 in
theorem closure_trusted_pathB_of_matched_placedBudget_of_dirGet [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv)) (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r) (_hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (StageP1OkEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) DeserEnv ReadEnv)
        StoresGhost.opened.sessions (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
        (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
        StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey))
    (R : SepProp) (s0 : State) (hpc : s0.pc = dpPollEntryPlaced) (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true) (hstk_sp : stk' ≤ s0.sp.toNat)
    (hro0 : LibsignalCodeRoLoaded lsmpl s0.mem) (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut) (hx2 : s0.readReg64 .x2 = y.cx) (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkPathB ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (_hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hm_base : s0.mem ⊨ dpPollEntrySpatialPlaced stk' y s0 R)
    (hMatched : ∀ (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
        (evs_p1 : List AllocEvent) (s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64), StageP1OkEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) DeserEnv ReadEnv)
        StoresGhost.opened.sessions (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
        (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
        StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey evs_p1 →
      (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer
        (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok (some r)) →
      r.currentSession = some sess → Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s1 →
      s1.trace = s0.trace → LibsignalCodeRoLoaded lsmpl s1.mem → s1.sp = s0.sp - 0xcd0#64 →
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
         p1LoadedRecordAt scopeKit A.repAlloc y.fut (some r) ∗
         preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
         protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
         protocolAddressAt A.repAlloc y.g.me y.g.meA ∗ coinsInstalledPlaced y.g.coinsP y.g.coins ∗
         storesAt A.repAlloc y.g.stores StoresGhost.opened ∗ LsTokenInit ∗
         lsLogOff ∗ stackAt sp (dpClosSubStack B) ∗
         memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32)
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R))) :
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
  dsimp only [dpPollEntrySpatialPlaced] at hm_base
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
    (subStack_le_sp_of_dpPollNeed hneed hstk_sp).1
  have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_pathB (A := A.repAlloc) σ y.g.stores
    hsub hfPeer hdecOk (pid := pid) (sid := sid) (kid := kid) (kbk := kbk)
  have hm_stores : s0.mem ⊨
      memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗ memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗ coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗ lsLogOff ∗ A.pool lim y.st s0 ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗ stackAt s0.sp stk' ∗ R :=
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
    cells (y.fut + 0x70#64) 14 ∗ cells (y.fut + 0xe0#64) 4 ∗ memRegion (y.fut + 0x100#64) 336 ∗
    ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗ cells (y.fut + 0x2c8#64) 25 ∗ ((y.fut + 0x390#64) ↦₈ b_390) ∗
    ((y.fut + 0x398#64) ↦₆₄ u_398) ∗ ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗ cells (y.fut + 0x428#64) 8 ∗
    cells (y.fut + 0x490#64) 4 ∗ ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗ (sp ↦₆₄ v_sp0) ∗
    ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
    ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
    ((sp + 0xc8#64) ↦₆₄ u_c8) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗ memRegion (sp + 0xd8#64) 348 ∗
    memRegion (sp + 0x3e0#64) 368 ∗ cells (s0.sp - 0x60#64) 12 ∗ lsLogOff ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗ A.pool lim y.st s0 ∗
    stackAt sp (stageP1CallStack kit ikit)
  let Fr_inner : SepProp :=
    memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut ∗ closStackUnusedP1OkAt sp ∗
    memRegion y.out 48 ∗ memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1CallStack kit ikit) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit
  have hm_split : s0.mem ⊨ (P_p1 ∗ Fr_inner) ∗ R :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
      cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
      cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced,
      cliPreKeyStoreSpecPlaced,
      cliSignedPreKeyStoreSpecPlaced,
      cliKpkStoreSpecFullPlaced,
      cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
  refine ⟨P_p1 ∗ Fr_inner, R, hm_split, ?_⟩
  have hwp := stageP1_ok_placed_inst_of_dirGet hDropNz mmpl gh W B y.g.F y.g.peer y.g.msg.identityKey
    hh hGet hDeser y.st StoresGhost.opened.sessions StoresGhost.opened.identity hp1_64 rfl rfl
    (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
      StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
      StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    hfits_p1 s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390 b_4f2 hro0
    (cliPollStageP1_fsAt_placed hh y.g.F scopeKit y.g.peer B hfiles0)
    hpc hrun hsp_align0 rfl hx0 hx1 hx2
  refine sepWPp_bind_p1_false hwp rfl ?_
  intro s1 P_1 hsteps01 hpc1 hrun1 hq1
  rcases hq1 with ⟨⟨opt, evs_p1, hevs_p1, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
    hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
    hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, hro1⟩
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
  have hrecomb := p1Ok_recombine_entails_stageP2_placedBudget stk' hneed hstk63 y
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
    obtain ⟨sess, hcur⟩ := currentSession_some_of_cliPollSessPlaced_loadRel hload_rel
    exact hMatched r sess evs_p1 s1 coins v_a8 v_b8 v_d0 hevs_p1 hload_rel hcur hsteps01 htr1 hro1
      hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1

/-! ## 2. Poll, Block-`520` Slot, `withFds` → `slotWithPreFdsGe3Closed`, & Guarded Lift -/

theorem decPk_matchingPathB_poll_gv_frozen_placedBudget_of_dirGet [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    {gh : CliGhostHooks}
    (hG : CliGhostAllocHooks M A lim gh)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    {kitEnv4 : ∀ F0 peer, SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSkit : ∀ F0 peer, SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (kitEnv4 F0 peer) scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
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
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')) := by
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_pathB_frozen_placedBudget (W := W) (X := X) (Scope := Scope) hSemOk stk' y R s0 hpre
  have hfits_poll : FitsEnv M lim y.st
      (MatchingPathBGvPollEnv A.repAlloc W B ReadEnv DeserEnv kitEnv4 tdEnv y.g) :=
    hpure.fits.mono (hevs_sub y.g)
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    have hfits_u : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g) :=
      hfits_poll.mono (fun evs h => by simp [MatchingPathBGvPollEnv, htrusted, h])
    have hevs_u : ∀ evs, CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs →
        DecPkEnv y.g evs := fun evs h =>
      hevs_sub y.g evs (by simp [MatchingPathBGvPollEnv, htrusted, h])
    exact closure_untrusted_pathB_placedBudget_of_dirGet A lim hDropNz mmpl gh W X B S Scope hh hGet hDeser
      hinjK hsub hS stk' hneed' hstk63 y hfits_u hevs_u R s0 hpc hrun hsp
      hpure.ro hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.decPkOk
      htrusted hm_base
  | true =>
    have hh_st := runHooks_to_stages hh
    have hne_false :
        StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey ≠ .ok false := by
      rw [htrusted]; decide
    have hfits_seq : FitsEnv M lim y.st
        (SeqEnv
          (StageP1OkEnv
            (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
            (cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) DeserEnv ReadEnv)
            StoresGhost.opened.sessions
            (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
            (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
            StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey)
          (fun evs234 =>
            ∃ r sess,
              (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B)).loadRel
                StoresGhost.opened.sessions y.g.peer.val (.ok (some r)) ∧
              r.currentSession = some sess ∧
              MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess evs234)) :=
      hfits_poll.mono (fun evs h => by simpa [MatchingPathBGvPollEnv, hne_false] using h)
    refine closure_trusted_pathB_of_matched_placedBudget_of_dirGet hDropNz mmpl gh W X B S Scope hh_st hGet
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
    have hfr1 : LibsignalFrozen lsmpl s1.mem :=
      libsignalFrozen_of_keepsFrozen hpure.fr hsteps01.keepsFrozen
    exact decPk_matchingPathB_main_gv_frozen_placedBudget_of_dirGet hG hDropNz mmpl W X B S Scope
      hh_st hGet hDeser hSkit hTryDec hinjK hsub hS stk' hneed' hstk63 y evs_p1 r sess s0 s1
      rngPtr v_a8 v_b8 v_d0 R hpure.files_eq hpure.filesOkPeer hpure.decPkOk hpure.coins_lt
      htrusted hload_rel hcur hfits_main hevs_main hsteps01 htr1 hfr1 hro1 hs1_sp hsp_sub hpc1 hrun1
      hsp_align1 hregs1

theorem cliDecryptPrekey_slot_matchingPathB_gv_frozen_placedBudget_at_block_of_dirGet [LibsignalFullPlacement]
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
    (hG : CliGhostAllocHooks M A lim gh)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSkit : ∀ F0 peer, SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (kitEnv4 F0 peer) scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)))
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
    subroutine_ok prog (lsmpl.base 520)
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk) := by
  have : IsLsBlockProg prog i (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))) := by
    rw [withPanics_cliGhostExterns_eq mmpl gh W]
    exact hcaller
  exact dpSlot_ok_state_frozen_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_frozen_placed_at_block (ext := cliGhostExterns gh (cliExternsPlaced mmpl W))
      (dpSlotPollKStatePlaced A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_inv_vm A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_res_vm A lim DecPkEnv B S)
      (fun stk' h1 h2 => by
        rw [withPanics_cliGhostExterns_eq mmpl gh W]
        exact decPk_matchingPathB_poll_gv_frozen_placedBudget_of_dirGet A lim ReadEnv DeserEnv tdEnv DecPkEnv
          hG hDropNz mmpl W X B S Scope
          (toSkeletonRunHooks hh) hGet hDeser hSkit hTryDec hinjK hsub hS hok hevs_sub
          stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed,
        dpSlotPollKStatePlaced] at hstk ⊢; omega)
      hstk64 hi)

theorem decPkPathBSlotOk_gvSeqFree_frozen_placedBudget_of_dirGet [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hG : CliGhostAllocHooks M A lim gh)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) cliRunBudgets_placed.dirGetNeed))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
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
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  fun stk h1 h2 =>
    cliDecryptPrekey_slot_matchingPathB_gv_frozen_placedBudget_at_block_of_dirGet
      (prog := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
      A lim cliRunBudgets_placed mmpl gh W (by decide) X S scopeIn
      hG h547 hh hGet hDeser
      (fun F0 peer => cliPollSess_seqFreeKitPlacedOkSE_of_dirGet mmpl gh W cliRunBudgets_placed F0 peer h547 hh hGet hDeser)
      hTryDec
      encodeInjOn_deserializeScopeP_Q (fun _ h => h) hdecPk
      (fun F peer me pm hf hd => ⟨(hfiles ▸ hf).1, hdecPkOk F peer me pm hd⟩)
      hsEnv stk (hneed ▸ h1) h2

/-- Combines `decPkPathBSlotOk_gvSeqFree_frozen_placedBudget_of_dirGet` instantiated at
`AllocWithFds.withFds A` with `slotOk_decPkFrozenPlaced_withFds_to_preFd`, producing the
canonical `SkeletonPlacedBudgetFd.slotWithPreFdsGe3Closed` Slot-`520` contract at `A`. -/
theorem decPkPathBSlotOk_gvSeqFree_frozen_placedBudget_preFd [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hG : CliGhostAllocHooks M (withFds A) lim gh)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced (withFds A) lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk (withFds A) lim (DirGetEnv PathEnv ReadEnv cliIo.rd) cliRunBudgets_placed.dirGetNeed))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit (withFds A) lim SessDeserializeCancelEnv))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C (withFds A) lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3MatchingPathBGvSeqFreeOfReadEnv A.repAlloc W cliRunBudgets_placed ReadEnv tdEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets_placed) :
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  slotOk_decPkFrozenPlaced_withFds_to_preFd henf
    (decPkPathBSlotOk_gvSeqFree_frozen_placedBudget_of_dirGet
      (A := withFds A) X mmpl gh W hG h547 hh hGet hDeser hTryDec S sEnvs needs
      hsEnv hfiles hdecPk hdecPkOk hneed)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPollPlacedBudgetFd
