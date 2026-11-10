/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBKitsPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPathCPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollAuxPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage2PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.Stage4KitsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBob -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobProducerAux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobTightProducer -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAVerNeRawSlot520
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# `FdsGe3Closed`-Threaded Block-`520` `OverD3` Producer

Proves the block-`518` (`dp_poll`) untrusted-identity branch and full `OverD3` block-`520`
(`cliDecryptPrekey`) slot contract directly from `CliDecPkPollKitsPlacedOk` (without raw `hRead` or
`hDeser` hypotheses), and lifts the `withFds A` slot theorem to
`SkeletonPlacedBudgetFd.slotWithPreFdsGe3Closed`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (
  IsLsBlockProg LibsignalFrozen LibsignalFullPlacement LibsignalPlacement
  libsignalFrozen_of_keepsFrozen lsProg_51 lsmpl lsρ withLsCl
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  sp_sub_cd0_align_std3 stageP1CallStack stageP1ProgPlaced stageP1UntrustedCallStack
)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives aesDecHookMallocng modelPrims)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  decryptPrekeyCoroCopyAt decryptPrekeyCoroInitAt decryptPrekeySavedRegsAt processPrekeyInnerInitAt
)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalPublicApiRepr (apiDecResultAt preKeyMsgAt)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall noAllocShimSpec withLsFrozen)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (
  StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSignedPreKeyVtSym dirAt
)
open CryptoVerification.SignalSession.Cli.KitInst (
  cliIdentityStoreSpec cliSessionStoreSpec
)
open CryptoVerification.SignalSession.Cli.MainHops (
  cliIo cliRunBudgets cliRunNeeds coinsInstalledPlaced storesAt
)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost RunSem decResAt dpPollNeed dpSlotArgsPlaced slotOutTr
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliGhostExterns cliGhostExterns_other withPanics_cliGhostExterns
)
open CryptoVerification.SignalSession.Cli.RunProofs (
  cliDecryptPrekeyNeed dpFutDoneAt dpFutStartAt dpWrapFrame
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit StageP1PostRegs apiDecResultAt_untrusted_entails_decResAt
  cliIdStoreSpecFull cliIdStoreSpecFullPlaced cliId_trustRel_eq_of_trusted cliKitStk
  cliKpkStoreSpecFullPlaced cliKyberPreKeyStoreSpecPlaced cliPollIdKit cliPollIdKitPlaced
  cliPollId_vtablesPlacedOk cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessKit
  cliPollSessKitPlaced cliPollSess_vtablesPlacedOk cliPollSpkKitPlaced cliPollStoresKitsAtPlaced
  cliPollStoresKitsAtPlaced_entails_storesAt cliPreKeyStoreSpecPlaced cliSess_loadRel_isOk
  cliSignedPreKeyStoreSpecPlaced closStackUnusedP1OkAt closStackUnusedUntrustedAt
  clos_stack_3280_of_p1_untrusted clos_stack_3280_split_for_p1_ok
  clos_stack_3280_split_for_p1_untrusted closureCalleeSaved_toCalleeSavedPreserved coroUnusedP1At
  coroUnusedP1AtPlaced coro_of_p1_untrusted_entails_dpFutDoneAt decPkDef_of_trust_err
  dpClosSubStack dpFutStartAt_split_for_p1_placed dpPollEntryPlaced dpPollNeed_eq_frame_add_subStack
  dpPollProgPlaced loadRec_of_cliPollSessPlaced_loadRel pmKyberId pmPreKeyId
  preKeyMsgAt_eq_idKey_sep preKeyMsgRemIdKeyAt sepWPp_conseq_pre sepWPp_sepExists_left
  slotOutTr_of_err sp_frame_sub_add stackAt_poll_entry_split stackAt_subStack_split
  stageP1CallStack_le_subStack stageP1UntrustedCallStack_le_subStack subStack_le_sp_of_dpPollNeed
  subroutine_ok_of_sepWPp_steps trusted_ok_of_filesOkPeer
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  EncodeInjOn FilesOkPeer encodeInjOn_deserializeScopeP_Q loadRec scopeIn scopeKit
)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv aesDecBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (TryDecryptCliEnvOf)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs (VerNeTightTopRawEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (EncodeRawPreallocPlacedOkX)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  DecPkOkD3 decPkOverDef decPkOverDef_of_untrusted
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd (
  cliDecPkPollKitsFds_toWithFds
)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget (
  CliDecPkPollKitsPlacedOk CliDecPkPollKitsPlacedOkFds
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBKitsPlacedBudgetFd (
  extHookStack_le_cliPollSess_loadCallStack slotOk_decPkFrozenPlaced_withFds_to_preFd
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget (
  cliRunSemOverV4
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget (
  CliStageP1OkEnv dpPollPre_unpack_over_d3_frozen_placed fitsEnv_after_d3
  p1Ok_recombine_entails_stageP2_budget_d3_placed sepWPp_bind_p1_false_d3 seqEnv_append_d3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPathCPlacedBudgetFd (
  closure_pathCOver_d3_ofVerNe_at_b_full_placedBudget_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage2PlacedBudgetFd (
  h7ra_stageP2Over_archive_at_cliRunBudgets_frozen_of_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage4PlacedBudget (
  storesAt_opened_entails_cliPollStoresKitsAtPlaced_d3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.Stage4KitsPlacedBudgetFd (
  h7ra_stageP4Prev1_seqFree_at_cliRunBudgets_of_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBob (
  DecPkD3ValidOverTightConcreteEnv'
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobProducerAux (
  H7pbDecPkD3ValidOverOfEnv' H7pbStageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt
  H7pbStageP3Prev1D3OfVerNeAtFrozenPlacedStmt H7pbStageP4Prev1VRegsAtBPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobTightProducer (
  stageP3Prev1D3_tightRaw_full_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAVerNeRawSlot520 (
  h7ra_cliStageP4Prev1SeqFreeEnvs h7ra_tryDecrypt507_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (withFds)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  RunSlotEnvs slotsOfSigPkFrozenPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget (
  CliStageP4Prev1Envs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget (
  overPollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  P2OverPathCErrEnvOf P2OverPathCOkEnvOf PromoteOverArchiveCanonSessEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget (
  dpPollEntrySpatialPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  CliDpPollUntrustedEnv cliPollIdBudgetEnv cliPollSessBudgetEnv cliPollStageP1_fsAt_placed
  dpPollPost_of_decResAt_placed stageP1_untrusted_mangled_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget (
  stageP1OkPreAt stageP1_ok_placed_of_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliStageP2KitEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget (
  dpSlotPollKStatePlaced_inv_vm dpSlotPollKStatePlaced_res_vm
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget (
  cliDecryptPrekey_ok_state_frozen_placed_at_block
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd (slotWithPreFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_sessionMemcpyRegion_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced dpSlot_ok_state_frozen_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

private theorem sepWPp_mono_post_panic_d3 {prog : Program} {ret : BitVec 64} {s0 : State}
    {P : SepProp} {Q1 Q2 Qp1 Qp2 : State → SepProp → Prop}
    (hq : ∀ sf P_f, Q1 sf P_f → Q2 sf P_f)
    (hqp : ∀ sf P_f, Qp1 sf P_f → Qp2 sf P_f)
    (h : SepWPp prog ret s0 P Q1 Qp1) :
    SepWPp prog ret s0 P Q2 Qp2 := by
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc, hrun, P_f, hmf, h1⟩ | ⟨hpan, P_f, hmf, h1⟩ | hex⟩ := h R hm hL
  · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, P_f, hmf, hq sf P_f h1⟩⟩
  · exact ⟨sf, hst, Or.inr (Or.inl ⟨hpan, P_f, hmf, hqp sf P_f h1⟩)⟩
  · exact ⟨sf, hst, Or.inr (Or.inr hex)⟩

/-! ## 1. Kit-Parametric Untrusted-Identity Branch (`trusted = .ok false`) -/

/-- Kit-parametric counterpart of `closure_untrusted_over_d3_placedBudget_ok` consuming `hKits.sessOk` and `hKits.idOk`. -/
private theorem hookSat_sessionMemcpyRegionBudget_of_vm
    {H : CryptoVerification.LibsignalHooks}
    (h : HookSat H "memcpy"
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    HookSat H "memcpy"
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    rcases x with ⟨dst, src, bs⟩
    dsimp only [LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hpost.1, hpost.2.1, hpost.2.2⟩
  · exact ⟨hkf, hsym, Or.inr hrest⟩

theorem closure_untrusted_over_d3_placedBudget_of_kits [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CliDecPkPollKitsPlacedOk A lim B ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g))
    (hevs_sub : ∀ evs,
      CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs)
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced) (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true) (hro0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out) (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx) (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hd3False : DecPkOkD3 ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗ dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗ memRegion y.cx 32 ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit ∗ lsLogOff ∗ A.pool lim y.st s0 ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗ R) :
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
  have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d3 A.repAlloc σ
    y.g.stores hsub hfPeer hd3False pid sid kid kbk
  have hm_stores : s0.mem ⊨
      memRegion y.out 48 ∗ dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗ memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗ lsLogOff ∗ A.pool lim y.st s0 ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        stackAt s0.sp stk' ∗ R :=
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
    cells (y.fut + 0x70#64) 14 ∗ cells (y.fut + 0xe0#64) 4 ∗
    memRegion (y.fut + 0x100#64) 336 ∗ cells (y.fut + 0x250#64) 6 ∗
    ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗ cells (y.fut + 0x2c8#64) 25 ∗
    ((y.fut + 0x390#64) ↦₈ b_390) ∗ ((y.fut + 0x398#64) ↦₆₄ u_398) ∗
    ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗ (sp ↦₆₄ v_sp0) ∗
    ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
    ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
    ((sp + 0xc8#64) ↦₆₄ u_c8) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
    memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x370#64) 36 ∗
    memRegion (sp + 0x3e0#64) 368 ∗ cells (sp + 0xa90#64) 6 ∗
    cells (s0.sp - 0x60#64) 12 ∗ memRegion y.out 48 ∗ lsLogOff ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    A.pool lim y.st s0 ∗ stackAt sp (stageP1UntrustedCallStack kit ikit)
  let Fr_inner : SepProp :=
    cells (y.fut + 0x428#64) 8 ∗ cells (y.fut + 0x490#64) 4 ∗
    ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗ coroUnusedP1At y.fut ∗
    closStackUnusedUntrustedAt sp ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 ∗
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
      cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced, cliPreKeyStoreSpecPlaced,
      cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
      cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
  refine ⟨P_p1, Fr_inner ∗ R, hm_split, ?_⟩
  have hwp := stageP1_untrusted_mangled_placed_ok
    (M := M) (A := A) (lim := lim) (ext := cliGhostExterns gh (cliExternsPlaced mmpl W))
    (Scope := scopeKit) (encRecord := encodeRecord)
    (kit := kit) (kitEnv := cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv)
    (ikit := ikit) (ikitEnv := cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv)
    (st := StoresGhost.opened.sessions) (ist := StoresGhost.opened.identity)
    (st_b := y.st) y.g.peer y.g.msg.identityKey
    hh.alloc hh.codecHooks.dealloc
    ((show withVmPreserved noAllocShimSpec = sessionShimBudgetSpec from rfl) ▸ hh.codecHooks.shim)
    hh.codecHooks.alloc
    (hookSat_sessionMemcpyRegionBudget_of_vm hh.codecHooks.memcpy)
    (cliPollSess_vtablesPlacedOk (A := A.repAlloc) y.g.F scopeKit y.g.peer σ hDropNz)
    (cliPollId_vtablesPlacedOk (A := A.repAlloc) y.g.F y.g.peer σ hDropNz)
    (hKits.sessOk y.g.F y.g.peer)
    (hKits.idOk y.g.F y.g.peer)
    hp1_64
    (extHookStack_le_cliPollSess_loadCallStack A.repAlloc B y.g.F y.g.peer)
    rfl rfl
    (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
      StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
      StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    hfits_p1 s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390
    hro0 (cliPollStageP1_fsAt_placed hh y.g.F scopeKit y.g.peer B hfiles0)
    hpc hrun (by simpa [State.spAligned] using hsp) rfl hx0 hx1 hx2
  refine sepWPp_mono_post_panic_d3 ?_ ?_ hwp
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
      rw [hS, decPkOverDef_of_untrusted X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins htrusted]
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
    let Leftover : SepProp := coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit
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
            ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
            processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
              (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
            ((y.fut + 0x390#64) ↦₈ 1#8) ∗ cells (y.fut + 0x398#64) 2 ∗
            cells (y.fut + 0x428#64) 8 ∗ cells (y.fut + 0x490#64) 4 ∗
            ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗ coroUnusedP1At y.fut) ∗
          memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
                (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
              stackAt sp (stageP1UntrustedCallStack kit ikit)) ∗
            ((sp ↦₆₄ 0#64) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗
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
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evs y.st) sf ∗ Leftover ∗
          dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            stackAt sp (dpClosSubStack B) ∗ memRegion sp 3280)) ∗ R :=
      Satisfies.mono (sepConj_mono_left
        (sepConj_mono hres
          (sepConj_mono hstores_back
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono hcoro
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

/-! ## 2. Kit-Parametric Block-`518` `OverD3` Poll Producer -/

/-- Steps block `518` (`dp_poll`) across both `trusted = false` and `trusted = true` from
`CliDecPkPollKitsPlacedOk` without raw `hRead` or `hDeser` hypotheses. -/
theorem decPk_d3_validOver_poll_ofVerNe_at_b_of_kits [LibsignalPlacement]
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
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CliDecPkPollKitsPlacedOk A lim B ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
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
      DecPkEnv g evs)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ Scope)
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧
        LibsignalBinary.Proofs.SignalSession.Cli.D3.DecPkOkOverV4 ⟨W.C, W.Q⟩ Scope F peer me pm)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      dpPollEntryPlaced
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')) := by
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
    exact closure_untrusted_over_d3_placedBudget_of_kits A lim hDropNz mmpl gh W X B S Scope
      hh hKits hinjK hsub hS stk' hneed' hstk63 y
      (fun evs hevs => hpure.fits evs (hEnv y.g evs (Or.inl hevs)))
      (fun evs hevs => hEnv y.g evs (Or.inl hevs))
      R s0 hpc hrun hsp
      (CryptoVerification.LibsignalTripleRatchet.Record.LibsignalCodeRoLoaded.of_libsignalFrozen hpure.froz)
      hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer
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
    have hwp := stageP1_ok_placed_of_kits (Qp := fun _ _ => False) mmpl gh W B y.g.F y.g.peer
      y.g.msg.identityKey
      hDropNz hhSt (hKits.sessOk y.g.F y.g.peer) (hKits.idOk y.g.F y.g.peer)
      y.st StoresGhost.opened.sessions StoresGhost.opened.identity
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
      (CryptoVerification.LibsignalTripleRatchet.Record.LibsignalCodeRoLoaded.of_libsignalFrozen hpure.froz)
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
      exact closure_pathCOver_d3_ofVerNe_at_b_full_placedBudget_ok A lim DecPkEnv B S Scope
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

/-! ## 3. Closed Fixed-`cliRunBudgets` Slot-`520` `OverD3` Producer (`of_kits` & `slotWithPreFdsGe3Closed`) -/

/-- Proves `.decryptPrekey.OkPlaced` at `lsmpl.base 520` from
`CliDecPkPollKitsPlacedOk A lim cliRunBudgets` without raw `hRead` or `hDeser` hypotheses. -/
theorem decPk_d3_validOver_tightRaw_slot520_of_kits [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (sEnvs : RunSlotEnvs)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CliDecPkPollKitsPlacedOk A lim cliRunBudgets
      (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W
      (InitialStateEnv W.C.F) (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv W a evs)
    (hsEnv' : ∀ g evs,
      DecPkD3ValidOverTightConcreteEnv' A.repAlloc W X tdEnv g evs →
      sEnvs.decryptPrekey g evs) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hpan : Arm64.Rust.withPanics H = H := withPanics_cliGhostExterns mmpl gh W
  have hcaller : IsLsBlockProg (lsProg_579 H) 579 (Arm64.Rust.withPanics H) := by
    rw [hpan]; infer_instance
  let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
  let selfEnv := fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv
  let kitEnvs := cliStageP2KitEnvs (A := A.repAlloc) ReadEnv cliRunBudgets selfEnv
  have hP2 := h7ra_stageP2Over_archive_at_cliRunBudgets_frozen_of_kits
    A lim mmpl gh W X h547 hG hKits hRaw hGrow hSpqr
  have hP3 := stageP3Prev1D3_tightRaw_full_placed_ok A lim tdEnv mmpl gh W
  have hP4 := h7ra_stageP4Prev1_seqFree_at_cliRunBudgets_of_kits A lim mmpl gh W h547 hKits
  have hTry := h7ra_tryDecrypt507_placed_ok A lim mmpl gh W hG hAesDec hSpqr hRecv_ne htd
  intro stk hstk hstk64
  exact dpSlot_ok_state_frozen_placed cliRunBudgets (cliRunSemOverV4 X W) stk hstk hstk64
    (cliDecryptPrekey_ok_state_frozen_placed_at_block (ext := H)
      (dpSlotPollKStatePlaced A lim sEnvs.decryptPrekey cliRunBudgets (cliRunSemOverV4 X W))
      (dpSlotPollKStatePlaced_inv_vm A lim sEnvs.decryptPrekey cliRunBudgets (cliRunSemOverV4 X W))
      (dpSlotPollKStatePlaced_res_vm A lim sEnvs.decryptPrekey cliRunBudgets (cliRunSemOverV4 X W))
      (fun stk' hs1 hs2 => by
        rw [hpan]
        exact decPk_d3_validOver_poll_ofVerNe_at_b_of_kits
          (verNeEnv := VerNeTightTopRawEnv)
          (ReadEnv := ReadEnv)
          (DeserEnv := SessDeserializeCancelEnv)
          (DecPkEnv := sEnvs.decryptPrekey)
          (P2OverErrEnv := P2OverPathCErrEnvOf (A := A.repAlloc) X W cliRunBudgets
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))) kitEnvs)
          (P2OverOkEnv := P2OverPathCOkEnvOf (A := A.repAlloc) X W cliRunBudgets
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv kitEnvs)
          (tdEnv := tdEnv)
          (p4Envs := fun B F0 peer pid kpkId spkId kbk =>
            h7ra_cliStageP4Prev1SeqFreeEnvs A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv)
          h547 mmpl gh W X cliRunBudgets (cliRunSemOverV4 X W) scopeIn
          hG hh hKits hP2 hP3
          (fun F0 peer pid kpkId spkId kbk st_b => hP4 F0 peer pid kpkId spkId kbk st_b)
          hTry (fun g evs h => hsEnv' g evs h)
          encodeInjOn_deserializeScopeP_Q (fun _ h => h) rfl
          (fun _F _peer _me _pm hf hd => ⟨hf.1, hd⟩) stk' hs1 hs2)
      stk
      (by
        dsimp only [slotsOfSigPkFrozenPlaced, cliRunNeeds,
          CryptoVerification.SignalSession.Cli.RunCompose.mkSlot] at hstk
        simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, dpSlotPollKStatePlaced] at hstk ⊢
        omega)
      hstk64 (by decide))

/-- `slotWithPreFdsGe3Closed` Slot-`520` `OverD3` producer at `A, lim` (`lim.enforced = true`),
instantiating `decPk_d3_validOver_tightRaw_slot520_of_kits` directly at `withFds A` from
`CliDecPkPollKitsPlacedOk (withFds A)`. -/
theorem decPk_d3_validOver_tightRaw_slot520_preFd_of_kits [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (henf : lim.enforced = true)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (sEnvs : RunSlotEnvs)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M (withFds A) lim gh)
    (hh : RunHooksPlaced (withFds A) lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CliDecPkPollKitsPlacedOk (withFds A) lim cliRunBudgets
      (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M (withFds A) lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M (withFds A) lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M (withFds A) lim mmpl gh W
      (InitialStateEnv W.C.F) (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv W a evs)
    (hsEnv' : ∀ g evs,
      DecPkD3ValidOverTightConcreteEnv' A.repAlloc W X tdEnv g evs →
      sEnvs.decryptPrekey g evs) :
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  slotOk_decPkFrozenPlaced_withFds_to_preFd henf
    (decPk_d3_validOver_tightRaw_slot520_of_kits (withFds A) lim mmpl gh W X sEnvs h547
      hG hh hKits hRaw hGrow hAesDec hSpqr hRecv_ne htd hsEnv')

/-- `slotWithPreFdsGe3Closed` Slot-`520` `OverD3` producer at `A, lim` (`lim.enforced = true`),
instantiating `decPk_d3_validOver_tightRaw_slot520_of_kits` at `withFds A` via
`CliDecPkPollKitsPlacedOkFds.toWithFds` and lifting via `slotOk_decPkFrozenPlaced_withFds_to_preFd`. -/
theorem decPk_d3_validOver_tightRaw_slot520_preFd_of_pollKits [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (henf : lim.enforced = true)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (sEnvs : RunSlotEnvs)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M (withFds A) lim gh)
    (hh : RunHooksPlaced (withFds A) lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKitsFds : CliDecPkPollKitsPlacedOkFds A lim cliRunBudgets
      (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M (withFds A) lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M (withFds A) lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M (withFds A) lim mmpl gh W
      (InitialStateEnv W.C.F) (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv W a evs)
    (hsEnv' : ∀ g evs,
      DecPkD3ValidOverTightConcreteEnv' A.repAlloc W X tdEnv g evs →
      sEnvs.decryptPrekey g evs) :
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  slotOk_decPkFrozenPlaced_withFds_to_preFd henf
    (decPk_d3_validOver_tightRaw_slot520_of_kits (withFds A) lim mmpl gh W X sEnvs h547
      hG hh
      ((cliDecPkPollKitsFds_toWithFds henf
        (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd.CliDecPkPollKitsPlacedOkFds.ofKitInst
          hKitsFds)).toKitInst)
      hRaw hGrow hAesDec hSpqr hRecv_ne htd
      hsEnv')

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudgetFd
