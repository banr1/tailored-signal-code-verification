/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemPollRejectAuxPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectAuxPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemRejectPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Agree -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPathAPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5PlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3V3PathAKitsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux

/-!
# Kit-Parametric and `withFds` Stage-P2 Bad-KEM Rejection

Proves `stageP2_badKem_reject_full_placedBudget_of_kits` from `CliDecPkPollKitsPlacedOk` without
raw `hRead`/`hDeser` hypotheses.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectAuxPlacedBudgetFd

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSessionApi (ApiError KyberPayload PreKeySignalMessage SessionRecord)
open CryptoVerification (LibsignalFrozen LibsignalFullPlacement LibsignalPlacement lsmpl lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  StageP2MemInv hdrOpkIdBv? p1LoadedRecordAt p2_bobStack_le_v1CallStack p2_callStack_le_v1CallStack
  p2_sub56Stack_le_v1CallStack stageP1ProgPlaced
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  p2_over_baseV1Call_le_v1CallStack p2_over_callStack_le_v1CallStack p2_over_dropSS3_le_overPure
  p2_over_pure_le_v1CallStack stageP2OverCallStack4K_eq
)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives modelPrims vecU8)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput Primitives WellSizedAcceptKeysInput bytesToBv8 dhOptNonZero
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderCore (bytesToBv8_vecU8 ofSignalPqxdhPrimitives vecU8_length)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsAt FsFiles speWordsAt withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost preKeyMsgAt)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded extract_withLsFrozen framelessMemcpySpec lsRustNoAllocShimSym
  noAllocShimSpec sessionMemcpySpec withLsFrozen
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost boxU8At protocolAddressAt)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsMemcpySym)
open CryptoVerification.SignalSession.Cli (
  StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym
  cliSignedPreKeyVtSym
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem decResAt dpPollNeed)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other
)
open CryptoVerification.SignalSession.Cli.RunProofs (dpFutDoneAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit PathAEntryWords StageP1PostRegs calleeSavedPreserved_of_closure cliKitStk
  cliPollIdKitPlaced cliPollKpkKitPlaced cliPollKpk_vtablesPlacedOk cliPollPkKitPlaced
  cliPollPk_vtablesPlacedOk cliPollSelfKitPlaced cliPollSelf_vtablesPlacedOk cliPollSessKitPlaced
  cliPollSpkKitPlaced cliPollSpk_vtablesPlacedOk dpClosSubStack dpPollEntryPlaced
  dpPollProgPlaced entails_sepConj_anyHeap pmKyberId pmPreKeyId sepWPp_conseq_pre sp_frame_sub_add
  stageP2PostP1At subroutine_ok_of_sepWPp_steps trusted_ok_of_filesOkPeer
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  EncodeInjOn FilesOkPeer blackBox_row_placed loadRec scopeIn scopeKit
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  fitsEvents_append rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2BaseCalleesPlaced4K StageP2PureCalleesPlaced4KOfEnv VacuousBobAllocEnv
  initializeBobSessionErr4KInnerPlacedSpec initializeBobSessionErr4KPlacedSpec
  not_fitsEnv_vacuousBobAllocEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget (
  P2Sub1To4Arm3Env P2Sub1To4OkEnv P2Sub4OkEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  StageP2BaseCalleesPlaced4K.of_hooks isSameAccount_4k_placed_ok_on_stageP1
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget (
  isSameAccountDistinctSpecExt_to_at_placed p2_stageP2bStack_le_bobV1
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget (
  P2V1Arm4Env P2V1Arm5EnvOfAcceptErr
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget (
  promoteMatchingMissAt_placed_of_gen
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid2PlacedBudget (
  P2OverSub1To3Arm1Env P2OverSub1To3Arm2Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget (
  P2OverSub1To4Arm3Env P2OverSub1To4Env P2OverSub1To4OkEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget (
  P2OverV1Arm4Env P2OverV1Arm5EnvOfAcceptErr
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  MsgCondBadKem badKemSpeWords_entails_decResAt_anyHeap bytesToBv8_mkBadKemHdr_ekAPk
  cliPollKpk_getEvs_nil cliPollPk_getEvs_nil cliPollPk_opkOkEvs_nil cliPollPk_opkOkUpdate_eq
  cliPollSelf_kpEvs_nil cliPollSpk_getEvs_nil distinctSid_of_not_sameAcct_d3
  hdrOpkIdBv?_mkBadKemHdr mkBadKemHdr not_p2SessMatchesMsg_of_v4_badKem pqxdhBadKemErrPayloadAt
  stageP1ProgPlaced_eq_dpPollProgPlaced stageP2OverV1CallStack_le_subStack_badKem_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget (
  DecPkD3UntypedPollEnv PqxdhAcceptBadKemErrEnv StageP2BadKemRejectEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd (
  CliDecPkPollKitsPlacedOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemPollRejectAuxPlacedBudgetFd (
  closure_trusted_p1_d3_placedBudget_bind_of_kits closure_untrusted_d3_placedBudget_of_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget (
  StageP1OkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  cliFiles_eq_of_trace_eq_placed cliPollIdBudgetEnv cliPollSessBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectAuxPlacedBudget (
  badKemInnerFramePlacedBudget cliInitBob_badKem_errOwned_full_placed_ok_on_stageP1
  p2BadKemErrFrame_fold_placedBudget stageP2_entry_unpack_badKem_over_placedBudget
  stageP2_entry_unpack_badKem_pathA_placedBudget
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget (
  DecPkStoreOk cliPromoteMatchingMissGen_placed_d3
  d3_pollPost_of_stageP2_err_placedBudget dpPollPre_unpack_d3_placedBudget
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  cliGhostAllocHooks_withFds withFds
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux (
  cliStageP2ClosureHooksPlaced uuidTryParse_placed_vm_code_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlacedBudget (
  cliPollKpk_wf_of_preKeysWf_placed cliPollPk_wf_of_preKeysWf_placed cliPollSelf_kpRel_ok_placed
  cliPollSpk_wf_of_preKeysWf_placed sepWPp_with_steps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget (
  cliPollKpk_getErr_entails_decResAt_anyHeap_placed cliPollPk_getErr_entails_decResAt_anyHeap_placed
  cliPollSelf_kpErr_entails_decResAt_err_placed cliPollSpk_getErr_entails_decResAt_anyHeap_placed
  cliPollStageP2_fsAt_stages_placed stageP2V1CallStack_le_subStack_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliPollKpkFullBudgetEnv cliPollPkFullBudgetEnv cliPollSpkFullBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)

private theorem r20f_toSkeletonRunHooksPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : CryptoVerification.LibsignalHooks}
    (hh : RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

private def r20a6w_dummyExtras : UnreachedPqxdhPrimitives :=
  ⟨fun _ => [], fun _ _ _ => [], fun _ _ => [], fun _ _ => [], fun _ => ([], []),
   fun _ => [], fun _ _ _ => false⟩

private def r20a6w_alwaysSomePrims (W : CliHooks) : Primitives :=
  { ofSignalPqxdhPrimitives (modelPrims r20a6w_dummyExtras ⟨W.C, W.Q⟩) with
    isCanonical := fun _ => true
    x25519 := fun _ _ => [1]
    kemDecaps := fun _ _ => some [] }

private theorem r20a6w_acceptKeys_ne_none (W : CliHooks) (inp : AcceptKeysInput)
    (htrust : inp.trustedPeer = true) (hrep : inp.replayOk = true)
    (hwell : WellSizedAcceptKeysInput inp)
    (hopk : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome) :
    acceptKeys (r20a6w_alwaysSomePrims W) inp ≠ none := by
  have hik : inp.hdr.ikAPk.length = 32 := by
    try (unfold WellSizedAcceptKeysInput at hwell)
    try (cases hwell)
    tauto
  have hek : inp.hdr.ekAPk.length = 32 := by
    try (unfold WellSizedAcceptKeysInput at hwell)
    try (cases hwell)
    tauto
  cases hopk1 : inp.hdr.opkId? <;> cases hopk2 : inp.opkBSk?
  · simp [acceptKeys, r20a6w_alwaysSomePrims, dhOptNonZero, htrust, hrep, hik, hek, hopk1, hopk2]
  · simp [hopk1, hopk2] at hopk
  · simp [hopk1, hopk2] at hopk
  · simp [acceptKeys, r20a6w_alwaysSomePrims, dhOptNonZero, htrust, hrep, hik, hek, hopk1, hopk2]

private theorem r20a6w_hookSat_noAllocShimBudget {H : String → Option (State → State)}
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

private theorem r20a6w_hookSat_sessionMemcpyBudget {H : String → Option (State → State)}
    (stk : Nat) (hsat : HookSat H lsMemcpySym (withVmPreserved framelessMemcpySpec)) :
    HookSat H "memcpy" (sessionMemcpyBudgetSpec stk) := by
  rcases hsat with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  have hpre' : s0.mem ⊨ (withVmPreserved framelessMemcpySpec).pre (dst, src, bs) s0 ∗
      (stackAt s0.sp stk ∗ R) := by
    dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec,
      withVmPreserved, framelessMemcpySpec] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  rcases hok (dst, src, bs) (stackAt s0.sp stk ∗ R) s0 hrun hpre' hsp with
    ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec,
      withVmPreserved, framelessMemcpySpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · rcases hrest with ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · dsimp only [withVmPreserved, framelessMemcpySpec] at hp
      rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
    · dsimp only [withVmPreserved, framelessMemcpySpec] at he
      rw [satisfies_pure_sepConj] at he; exact False.elim he.1
    · dsimp only [withVmPreserved, framelessMemcpySpec] at ho
      rw [satisfies_pure_sepConj] at ho; exact False.elim ho.1

private theorem r20a6w_baseCalleesPlaced4K [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2BaseCalleesPlaced4K A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  StageP2BaseCalleesPlaced4K.of_hooks
    (r20a6w_hookSat_noAllocShimBudget hh.codecHooks.shim)
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    (r20a6w_hookSat_sessionMemcpyBudget allocHookStack hh.codecHooks.memcpy)
    (isSameAccount_4k_placed_ok_on_stageP1
      ((cliGhostExterns_other gh _ (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans
        (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W)))
      (uuidTryParse_placed_vm_code_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))))

private theorem r20a6w_pureCalleesPlaced4K [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PureCalleesPlaced4KOfEnv (r20a6w_alwaysSomePrims W) A lim W.C.F
      (fun _ _ => VacuousBobAllocEnv) (fun _ => PqxdhAcceptBadKemErrEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have hbase := r20a6w_baseCalleesPlaced4K mmpl gh W hh
  refine {
    publicKeySerialize := hbase.publicKeySerialize
    promoteMatchingSessionEmpty := hbase.promoteMatchingSessionEmpty
    curveKeyPairSerde := hbase.curveKeyPairSerde
    kemKeyPairSerde := hbase.kemKeyPairSerde
    preKeyRecordKeyPair := hbase.preKeyRecordKeyPair
    dropSpe2 := hbase.dropSpe2
    isSameAccount := hbase.isSameAccount
    initializeBobV1 := ?_
    initializeBobErr := ?_
    promoteStateEmpty := hbase.promoteStateEmpty
    dropProcessPrekeyImplState1 := hbase.dropProcessPrekeyImplState1
    dropSessionStructure3 := hbase.dropSessionStructure3
  }
  · intro st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfits
    exact (not_fitsEnv_vacuousBobAllocEnv hfits).elim
  · apply subroutine_ok_outcome_intro
    rintro ⟨g, st⟩ R s0 _ _ hpre _
    dsimp only [initializeBobSessionErr4KPlacedSpec, withLsCodeRoLoaded,
      initializeBobSessionErr4KInnerPlacedSpec] at hpre
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨_, hpre⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨_, _, _, htrust, hrep, hopk, hwell, _, _, hnone, _⟩, _⟩
    exact (r20a6w_acceptKeys_ne_none W g.inp htrust hrep hwell hopk hnone).elim

private theorem r20a6w_dup_pure_right {φ : Prop} {P Q : SepProp}
    (h : Q ⊢ ⌜φ⌝ ∗ Q) : P ∗ Q ⊢ ⌜φ⌝ ∗ (P ∗ Q) :=
  Entails.trans (sepConj_mono_right h) (by rw [sepConj_pure_left_comm]; exact Entails.refl _)

private theorem r20a6w_dup_pure_left {φ : Prop} {P Q : SepProp}
    (h : P ⊢ ⌜φ⌝ ∗ P) : P ∗ Q ⊢ ⌜φ⌝ ∗ (P ∗ Q) :=
  Entails.trans (sepConj_mono_left h) (by rw [sepConj_assoc]; exact Entails.refl _)

private theorem r20a6w_badKemInnerFrame_dup_kyber [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (kp : KyberPayload) (rngPtr sp : BitVec 64) :
    badKemInnerFramePlacedBudget A y kp rngPtr sp ⊢
      ⌜y.g.msgG.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
        badKemInnerFramePlacedBudget A y kp rngPtr sp := by
  have hleaf :
      (⌜y.g.msgG.kyberPtr ≠ 0 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
        (if kp.ciphertext = [] then emp else A.repAlloc.live y.g.msgG.kyberPtr kp.ciphertext.length 1) ∗
        memRegion (y.g.msgA + 164#64) 4 ∗
        boxU8At A.repAlloc (y.g.msgA + 128#64) y.g.msgG.serPtr y.g.msg.serialized ∗
        memRegion (y.g.msgA + 241#64) 7) ⊢
      ⌜y.g.msgG.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
        (⌜y.g.msgG.kyberPtr ≠ 0 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
          (if kp.ciphertext = [] then emp else A.repAlloc.live y.g.msgG.kyberPtr kp.ciphertext.length 1) ∗
          memRegion (y.g.msgA + 164#64) 4 ∗
          boxU8At A.repAlloc (y.g.msgA + 128#64) y.g.msgG.serPtr y.g.msg.serialized ∗
          memRegion (y.g.msgA + 241#64) 7) := by
    refine Entails.pure_left fun hp => ?_
    have hp' : y.g.msgG.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63 := hp
    rw [pure_sepConj_of_true hp', pure_sepConj_of_true hp]
    exact Entails.refl _
  unfold badKemInnerFramePlacedBudget
  repeat (first
    | exact hleaf
    | exact r20a6w_dup_pure_left hleaf
    | refine r20a6w_dup_pure_right ?_)

private theorem r20a6w_stageP2BadKemPreAt_dup_kyber [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (kp : KyberPayload) (w : PathAEntryWords) (st1 : M.σ) (s0 s1 : State)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64) :
    LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2BadKemPreAtPlaced A lim
      (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
      (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      st1 s0 s1 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
      y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkBadKemHdr y.g.msg kp) kp.ciphertext y.g.msg.message.messageVersion
      0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B)
      (badKemInnerFramePlacedBudget A y kp rngPtr sp) ⊢
      ⌜y.g.msgG.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
      LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2BadKemPreAtPlaced A lim
        (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
        (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B))
        (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
        st1 s0 s1 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
        y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
        y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
        (mkBadKemHdr y.g.msg kp) kp.ciphertext y.g.msg.message.messageVersion
        0#8 0#8 w.b_4b0 w.b_4f1 0#8
        w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
        StoresGhost.opened.signed StoresGhost.opened.kyber
        StoresGhost.opened.oneTime StoresGhost.opened.identity
        y.g.me y.g.peer (dpClosSubStack B)
        (badKemInnerFramePlacedBudget A y kp rngPtr sp) := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2BadKemPreAtPlaced
  repeat (first
    | exact r20a6w_badKemInnerFrame_dup_kyber A y kp rngPtr sp
    | exact r20a6w_dup_pure_left (r20a6w_badKemInnerFrame_dup_kyber A y kp rngPtr sp)
    | refine r20a6w_dup_pure_right ?_)

private theorem r20a6w_freeOnlyEvs_rustDeallocEvents (size align : Nat) :
    FreeOnlyEvs (rustDeallocEvents size align) := by
  unfold FreeOnlyEvs rustDeallocEvents
  intro ev hev
  try split at hev
  all_goals simp at hev
  all_goals rcases hev with rfl
  all_goals exact ⟨_, _, rfl⟩

private theorem r20a6w_fitsEnv_drop_freeOnly {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E : List AllocEvent → Prop} (h : FitsEnv M lim st (SeqEnv E FreeOnlyEvs)) :
    FitsEnv M lim st E :=
  h.mono fun _ he => Or.inl he

private theorem r20a6w_fitsEnv_step3 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E1 E2 E3 E4 : List AllocEvent → Prop} {e1 e2 e3 : List AllocEvent}
    (h : FitsEnv M lim st (SeqEnv E1 (SeqEnv E2 (SeqEnv E3 (SeqEnv E4 FreeOnlyEvs)))))
    (h1 : E1 e1) (h2 : E2 e2) (h3 : E3 e3) :
    FitsEnv M lim (M.stepEvents (e2 ++ e3) (M.stepEvents e1 st)) E4 := by
  rw [M.stepEvents_append]
  exact r20a6w_fitsEnv_drop_freeOnly (((h.seq_right h1).seq_right h2).seq_right h3)

private theorem r20a6w_opk_env_eq
    {spkBox : Nat} {spkPoll : List AllocEvent → Prop}
    {kpkBox : Nat} {kpkPoll : List AllocEvent → Prop}
    {pkBox1 pkBox2 : Nat}
    {pkPoll1 pkPoll2 : BitVec 32 → List AllocEvent → Prop}
    {kpBox : Nat} {pm : PreKeySignalMessage} {kp : KyberPayload} {opkWord : BitVec 32}
    (hopk : ∀ id : BitVec 32, pm.preKeyId = some id → opkWord = id)
    (hbox : opkWord = pmPreKeyId pm → pkBox1 = pkBox2)
    (hpoll : opkWord = pmPreKeyId pm → pkPoll1 = pkPoll2) :
    P2Sub1To4Arm3Env spkBox spkPoll kpkBox kpkPoll pkBox1 pkPoll1 (hdrOpkIdBv? (mkBadKemHdr pm kp)) =
      P2Sub1To4Arm3Env spkBox spkPoll kpkBox kpkPoll pkBox2 pkPoll2 pm.preKeyId ∧
    P2Sub1To4OkEnv spkBox spkPoll kpkBox kpkPoll pkBox1 pkPoll1 kpBox (hdrOpkIdBv? (mkBadKemHdr pm kp)) =
      P2Sub1To4OkEnv spkBox spkPoll kpkBox kpkPoll pkBox2 pkPoll2 kpBox pm.preKeyId := by
  rw [hdrOpkIdBv?_mkBadKemHdr]
  cases hid : pm.preKeyId with
  | none => exact ⟨rfl, rfl⟩
  | some id =>
    have hw : opkWord = pmPreKeyId pm := by
      unfold pmPreKeyId
      rw [hopk id hid, hid]
      rfl
    unfold P2Sub1To4Arm3Env P2Sub1To4OkEnv P2Sub4OkEnv
    rw [hbox hw, hpoll hw]
    exact ⟨rfl, rfl⟩

set_option maxHeartbeats 1200000 in
private theorem r20a6w_stageP2_badKem_reject_body_of_kits [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CliDecPkPollKitsPlacedOk A lim B ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (R : SepProp) (s0 : State) (opt : Option (SessionRecord (List (BitVec 8))))
    (evs_p1 : List AllocEvent) (s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hstoreOk : DecPkStoreOk ⟨W.C, W.Q⟩ y.g.F)
    (hbadCond : MsgCondBadKem Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none)
    (hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g opt))
    (hevs_sub : ∀ evs_p2,
      StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g opt evs_p2 →
      DecPkEnv y.g (evs_p1 ++ evs_p2))
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok opt))
    (htr1 : s1.trace = s0.trace) (hro1 : LibsignalFrozen lsmpl s1.mem)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64) (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x868#64) (hrun1 : s1.status = .Running)
    (halign1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym))
    (hs1_files : s1.fs.files = y.g.F) :
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (s0.sp - 0xcd0#64) v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗ lsLogOff ∗ stackAt (s0.sp - 0xcd0#64) (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32)
      (fun sf P_f =>
        (Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsFrozen lsmpl
            (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsFrozen lsmpl
            (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).onPanic y s0 sf ∗ R)) := by
  obtain ⟨hnotSameSid, hv4, ⟨kp, hkp, hbadKem⟩, hnoMatch⟩ := hbadCond
  let ext := cliGhostExterns gh (cliExternsPlaced mmpl W)
  let sp := s0.sp - 0xcd0#64
  let fp := sp + 3184#64
  let st1 := M.stepEvents evs_p1 y.st
  let LeftoverBase : SepProp := coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit
  let Leftover : SepProp := LeftoverBase ∗ anyHeap
  let Fr_p2 : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 ∗ LeftoverBase
  let err0 : ApiError AddrVal Unit := .protocol .invalidKeyAgreement
  have herr0_p : err0 ≠ .panic := nofun
  have herr0_s : err0 ≠ .store () := nofun
  have hkpkId : pmKyberId y.g.msg = kp.preKeyId := by
    unfold pmKyberId; rw [hkp]
  have hpre_split :
      (stageP2PostP1At (A.atState lim st1 s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (s0.sp - 0xcd0#64) v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗ lsLogOff ∗ stackAt (s0.sp - 0xcd0#64) (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32) =
      (stageP2PostP1At (A.atState lim st1 s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       lsLogOff ∗ stackAt sp (dpClosSubStack B)) ∗ Fr_p2 := by
    dsimp only [Fr_p2, LeftoverBase, sp]
    sep_ac_rfl
  rw [hpre_split, ← stageP1ProgPlaced_eq_dpPollProgPlaced mmpl gh W]
  rcases hregs1 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, _, hx29, hvregs1⟩
  have hsp_align : (sp &&& 15#64 == 0#64) = true := by
    change ((s0.sp - 0xcd0#64) &&& 15#64 == 0#64) = true; rw [← hs1_sp]; exact halign1
  have hx29_fp : s1.readReg64 .x29 = fp :=
    hx29.trans (bv_sub_add_lit s0.sp 3280 3184).symm
  have hsame_le :
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt ≤ dpClosSubStack B :=
    Nat.le_trans
      (by decide : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt ≤ 1048576 - 3280)
      (Nat.le_add_right _ _)
  have htr_pref : s0.trace <+: s1.trace := by rw [htr1]
  let ikBSk : List UInt8 :=
    match StoresGhost.opened.identity.keyPair cliIo.rd y.g.F with
    | .ok kp₀ => vecU8 kp₀.privateKey.bytes | .error _ => List.replicate 32 0
  let ikBPk : List UInt8 :=
    match StoresGhost.opened.identity.keyPair cliIo.rd y.g.F with
    | .ok kp₀ => vecU8 kp₀.identityKey.publicKey.bytes | .error _ => List.replicate 32 0
  have hikBSk_len : ikBSk.length = 32 := by dsimp only [ikBSk]; split <;> [exact vecU8_length _; simp]
  have hikBPk_len : ikBPk.length = 32 := by dsimp only [ikBPk]; split <;> [exact vecU8_length _; simp]
  have hkp_sk : ∀ kp₀ : IdentityKeyPair,
      (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp₀) → kp₀.privateKey.bytes.toList = bytesToBv8 ikBSk := by
    intro kp₀ hrel; dsimp only [ikBSk]; rw [cliPollSelf_kpRel_ok_placed hrel, bytesToBv8_vecU8]
  have hkp_pk : ∀ kp₀ : IdentityKeyPair,
      (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp₀) →
      kp₀.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk := by
    intro kp₀ hrel; dsimp only [ikBPk]; rw [cliPollSelf_kpRel_ok_placed hrel, bytesToBv8_vecU8]
  have hikAPk_len : (mkBadKemHdr y.g.msg kp).ikAPk.length = 32 := vecU8_length _
  have hekAPk_len : (mkBadKemHdr y.g.msg kp).ekAPk.length = 32 := vecU8_length _
  have hkemCt_len : (mkBadKemHdr y.g.msg kp).kemCt.length = 1568 := by simp [mkBadKemHdr]
  have hH := cliStageP2ClosureHooksPlaced mmpl gh W hh
  have hBase := r20a6w_baseCalleesPlaced4K mmpl gh W hh
  have hPure := r20a6w_pureCalleesPlaced4K mmpl gh W hh
  have hSameAcct := isSameAccountDistinctSpecExt_to_at_placed hBase.isSameAccount
  have hInitBob :=
    LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5PlacedBudget.of_full_badKem_errOwned_placed
      (cliInitBob_badKem_errOwned_full_placed_ok_on_stageP1 r20a6w_dummyExtras mmpl gh W hG)
  have hSelfVt := cliPollSelf_vtablesPlacedOk (A := A.repAlloc) y.g.F y.g.peer (cliKitStk B) hDropNz
  have hSelfOk := hKits.selfOk y.g.F y.g.peer
  have hSpkVt := cliPollSpk_vtablesPlacedOk (A := A.repAlloc) y.g.F y.g.msg.signedPreKeyId (cliKitStk B) hDropNz
  have hSpkOk := hKits.spkOk y.g.F y.g.msg.signedPreKeyId
  have hKpkVt := cliPollKpk_vtablesPlacedOk (A := A.repAlloc) y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B) hDropNz
  have hKpkOk := hKits.kpkOk y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey
  have hfs1 : FsAt (fun f => f = y.g.F) True (dpPollProgPlaced ext) s1 :=
    .inr ⟨trivial, hh.fs (dpPollProgPlaced ext) 518, hs1_files⟩
  let finishArm := fun (w : PathAEntryWords)
      (hopkWord : ∀ id : BitVec 32, y.g.msg.preKeyId = some id → w.opkWord = id)
      (evs_p2 : List AllocEvent) (sf : State) (P_f : SepProp)
      (hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g opt evs_p2)
      (_hsteps1f : Steps (stageP1ProgPlaced ext) s1 sf)
      (htrf : sf.trace = s1.trace) (hspf : sf.sp = sp + 3280#64)
      (hcsf : _) (hvregsf : calleeSavedVRegs sf = calleeSavedVRegs s0)
      (hPf_err : P_f ⊢
        ((decResAt A.repAlloc y.out (.error err0) ∗ anyHeap) ∗
          (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B)).storeAt
            (y.g.stores + 80#64) StoresGhost.opened.signed ∗
          (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey
            (cliKitStk B)).storeAt (y.g.stores + 120#64) StoresGhost.opened.kyber ∗
          (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B)).storeAt
            (y.g.stores + 200#64) StoresGhost.opened.oneTime ∗
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).identityAt
            y.g.stores StoresGhost.opened.identity ∗
          LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced A lim (M.stepEvents evs_p2 st1) s0 sf sp fp y.fut y.g.msgA y.g.msgG.kyberPtr
            y.g.peerA y.g.meA
            y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
            (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym)
            y.g.peerA (y.g.msgA + 200#64) (mkBadKemHdr y.g.msg kp) kp.ciphertext
            y.g.msg.message.messageVersion
            w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
            y.g.me y.g.peer (dpClosSubStack B)
            (badKemInnerFramePlacedBudget A y kp rngPtr sp)) ∗ Fr_p2) =>
    show (Steps (dpPollProgPlaced ext) s0 sf → (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withLsFrozen lsmpl
          (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf from by
      refine ⟨?_, hspf.trans (sp_frame_sub_add s0.sp), calleeSavedPreserved_of_closure hcsf hvregsf⟩
      intro hsteps0f hmf
      have hevs_eq : M.stepEvents (evs_p1 ++ evs_p2) y.st = M.stepEvents evs_p2 st1 :=
        AllocCostModel.stepEvents_append M evs_p1 evs_p2 y.st
      have hent : P_f ⊢
          dpFutDoneAt y.fut ∗ memRegion sp 3280 ∗ decResAt A.repAlloc y.out (.error err0) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          lsLogOff ∗ A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
          memRegion y.cx 32 ∗ Leftover := by
        rw [hevs_eq]
        refine Entails.trans hPf_err ?_
        refine Entails.trans (sepConj_mono_left
          (p2BadKemErrFrame_fold_placedBudget A lim y kp w (M.stepEvents evs_p2 st1) s0 sf
            sp fp rngPtr err0 hv4 hkp rfl hopkWord)) ?_
        dsimp only [Fr_p2, Leftover, LeftoverBase, sp]
        exact Entails.of_eq (by sep_ac_rfl)
      exact d3_pollPost_of_stageP2_err_placedBudget A lim B S
        (r20f_toSkeletonRunHooksPlaced hh) stk' hneed hstk63 y s0 sf
        (evs_p1 ++ evs_p2) err0 P_f Leftover R herr0_p herr0_s hans (hevs_sub evs_p2 hevs2)
        hsteps0f (htrf.trans htr1) hent hmf
  refine sepWPp_with_steps ?_
  cases opt with
  | none =>
    have hunpack :
        ((stageP2PostP1At (A.atState lim st1 s1)
           y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
         p1LoadedRecordAt scopeKit A.repAlloc y.fut none ∗
         preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
         protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
         protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
         storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
         lsLogOff ∗ stackAt sp (dpClosSubStack B)) ∗ Fr_p2) ⊢
          ∃∗ w : PathAEntryWords,
            ⌜(y.g.msgG.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63) ∧
              (∀ id : BitVec 32, y.g.msg.preKeyId = some id → w.opkWord = id)⌝ ∗
            LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2BadKemPreAtPlaced A lim
              (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
              (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B))
              (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
              (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
              st1 s0 s1 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
              y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
              y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
              (mkBadKemHdr y.g.msg kp) kp.ciphertext y.g.msg.message.messageVersion
              0#8 0#8 w.b_4b0 w.b_4f1 0#8
              w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
              StoresGhost.opened.signed StoresGhost.opened.kyber
              StoresGhost.opened.oneTime StoresGhost.opened.identity
              y.g.me y.g.peer (dpClosSubStack B)
              (badKemInnerFramePlacedBudget A y kp rngPtr sp ∗ Fr_p2) := by
      refine Entails.trans (sepConj_mono_left
        (stageP2_entry_unpack_badKem_pathA_placedBudget A lim y kp st1 s0 s1 sp fp
          rngPtr v_a8 v_b8 v_d0 hv4 hkp rfl hstoreOk hfPeer hsub)) ?_
      simp only [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun w => Entails.sepExists_right w ?_
      rw [sepConj_assoc]
      refine Entails.pure_left fun hopkWord => ?_
      refine Entails.trans (sepConj_mono_left
        (r20a6w_stageP2BadKemPreAt_dup_kyber A lim y kp w st1 s0 s1 sp fp rngPtr v_a8 v_b8 v_d0)) ?_
      rw [sepConj_assoc]
      refine Entails.pure_left fun hkyb => Entails.pure_right ⟨hkyb, hopkWord⟩ ?_
      unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2BadKemPreAtPlaced
      exact Entails.of_eq (by sep_ac_rfl)
    refine sepWPp_conseq_pre hunpack ?_
    refine SepWPp.exists_elim fun w => SepWPp.pure_left fun ⟨⟨hct_nz, hct_bd⟩, hopkWord⟩ => ?_
    have ⟨hArm3_eq, hOk14_eq⟩ := r20a6w_opk_env_eq
      (spkBox := (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B)).getBoxSize)
      (spkPoll := (cliPollSpkFullBudgetEnv A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B) ReadEnv).getPollEnv
        StoresGhost.opened.signed y.g.msg.signedPreKeyId)
      (kpkBox := (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B)).getBoxSize)
      (kpkPoll := (cliPollKpkFullBudgetEnv A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B) ReadEnv).getPollEnv
        StoresGhost.opened.kyber kp.preKeyId)
      (pkBox1 := (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B)).getBoxSize)
      (pkBox2 := (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)).getBoxSize)
      (pkPoll1 := (cliPollPkFullBudgetEnv A.repAlloc y.g.F w.opkWord (cliKitStk B) ReadEnv).getPollEnv
        StoresGhost.opened.oneTime)
      (pkPoll2 := (cliPollPkFullBudgetEnv A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B) ReadEnv).getPollEnv
        StoresGhost.opened.oneTime)
      (kpBox := (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpBoxSize)
      (pm := y.g.msg) (kp := kp) (opkWord := w.opkWord)
      hopkWord (fun hw => by rw [hw]) (fun hw => by rw [hw])
    have hstk := stageP2V1CallStack_le_subStack_placed (A := A.repAlloc)
      y.g.F y.g.peer y.g.msg.signedPreKeyId kp.preKeyId w.opkWord y.g.msg.baseKey B
    have hfs := stageP1ProgPlaced_eq_dpPollProgPlaced mmpl gh W ▸
      cliPollStageP2_fsAt_stages_placed hh y.g.F y.g.peer y.g.msg.signedPreKeyId kp.preKeyId
        w.opkWord y.g.msg.baseKey B hfs1
    exact LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPathAPlacedBudget.stageP2_pathA_badKem_kits_memInv_at_placed
      StageP2MemInv.frozen ext hH hPure hSameAcct hInitBob
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollSelfBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
      hSelfVt hSelfOk
      (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
      (cliPollSpkFullBudgetEnv A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B) ReadEnv)
      hSpkVt hSpkOk
      (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B))
      (cliPollKpkFullBudgetEnv A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B) ReadEnv)
      hKpkVt hKpkOk
      (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
      (cliPollPkFullBudgetEnv A.repAlloc y.g.F w.opkWord (cliKitStk B) ReadEnv)
      (cliPollPk_vtablesPlacedOk (A := A.repAlloc) y.g.F w.opkWord (cliKitStk B) hDropNz)
      (hKits.pkOk y.g.F w.opkWord)
      (dpClosSubStack B)
      (Nat.le_trans (p2_callStack_le_v1CallStack _ _ _ _) hstk)
      hsame_le
      (Nat.le_trans LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5PlacedBudget.p2_badKem_entry_le_stageP2bStack
        (Nat.le_trans p2_stageP2bStack_le_bobV1
          (Nat.le_trans (p2_bobStack_le_v1CallStack _ _ _ _) hstk)))
      st1 s0 s1 (badKemInnerFramePlacedBudget A y kp rngPtr sp ∗ Fr_p2) _
      sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
      y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkBadKemHdr y.g.msg kp) kp.ciphertext ikBSk ikBPk
      y.g.msg.message.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer
      (hfits_p2.mono fun evs hevs => by
        unfold StageP2BadKemRejectEnv; rw [hkpkId]
        rcases hevs with h1 | h2 | h3 | hok4
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · rw [hArm3_eq] at h3; exact Or.inr (Or.inr (Or.inl h3))
        · rw [hOk14_eq] at hok4; exact Or.inr (Or.inr (Or.inr (Or.inl (SeqEnv.inl hok4)))))
      (fun evs14 hevs14 => by
        rw [hOk14_eq] at hevs14
        have hArm4 := hfits_p2.mono fun evs h4 => by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]
          exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
        exact r20a6w_fitsEnv_drop_freeOnly (hArm4.seq_right hevs14))
      (fun _ _ _ _ _ _ _ _ _ _ evs14 evsKp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hevs14 hevsKp => by
        rw [hOk14_eq] at hevs14
        have hArm5 := hfits_p2.mono fun evs h5 => by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]
          exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
        exact r20a6w_fitsEnv_step3 hArm5 hevs14 hevsKp
          (r20a6w_freeOnlyEvs_rustDeallocEvents
            (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpBoxSize 8))
      hct_nz hsp_sub hikBSk_len hikBPk_len hikAPk_len hekAPk_len hkemCt_len hct_bd hbadKem hro1 hfs
      rfl (fun r' hrel _ => cliPollSpk_wf_of_preKeysWf_placed hstoreOk.preKeysWf r' hrel)
      rfl (fun r' hrel _ => cliPollKpk_wf_of_preKeysWf_placed hstoreOk.preKeysWf r' hrel)
      (fun id hid => hopkWord id ((hdrOpkIdBv?_mkBadKemHdr y.g.msg kp).symm.trans hid))
      (fun id hid => (hopkWord id ((hdrOpkIdBv?_mkBadKemHdr y.g.msg kp).symm.trans hid)).symm)
      (fun _id r' _ hrel _ => cliPollPk_wf_of_preKeysWf_placed hstoreOk.preKeysWf r' hrel)
      hkp_sk hkp_pk (Or.inr (distinctSid_of_not_sameAcct_d3 hnotSameSid))
      hpc1 hrun1 hs1_sp hsp_align htr_pref hvregs1
      hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx29_fp
      (fun e evs sf P_f _ hevs _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, List.append_nil] at htrf
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g none evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inl hevs
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        refine Entails.trans hPf (Entails.trans
          (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
            y.g.F y.g.msg.signedPreKeyId (cliKitStk B) y.out e err0)) ?_)
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
      (fun _spkRec e evs sf P_f _ _ _ hevs _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, cliPollKpk_getEvs_nil, List.append_nil, List.append_nil] at htrf
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g none evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inr (Or.inl hevs)
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        refine Entails.trans hPf (Entails.trans
          (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
            y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B) y.out e err0)) ?_)
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
      (fun _spkRec _kpkRec opkId e evs sf P_f _ _ _ _ hopkHdr _ hevs _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, cliPollKpk_getEvs_nil, cliPollPk_getEvs_nil,
            List.append_nil, List.append_nil, List.append_nil] at htrf
        rw [← hopkHdr, hArm3_eq] at hevs
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g none evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inr (Or.inr (Or.inl hevs))
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        refine Entails.trans hPf (Entails.trans
          (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
            y.g.F w.opkWord (cliKitStk B) y.out e err0)) ?_)
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
      (fun _spkRec _kpkRec wOpk e evs sf P_f _ _ _ _ _ _ hevs _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, cliPollKpk_getEvs_nil, cliPollPk_opkOkEvs_nil,
            cliPollSelf_kpEvs_nil, List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htrf
        have hopkUpd := cliPollPk_opkOkUpdate_eq A.repAlloc y.g.F w.opkWord (cliKitStk B)
          (hdrOpkIdBv? (mkBadKemHdr y.g.msg kp)) wOpk
        rw [hopkUpd] at hPf
        unfold P2V1Arm4Env at hevs; rw [hOk14_eq] at hevs
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g none evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inr (Or.inr (Or.inr (Or.inl hevs)))
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        have hkpEnt := Entails.trans
          (cliPollSelf_kpErr_entails_decResAt_err_placed A.repAlloc y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)
        refine Entails.trans hPf (Entails.trans (sepConj_mono_left hkpEnt) ?_)
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
      (fun _ _ _ _ _ _ wOpk _ _ _ errTag w2 w3 w4 w5 w6 evs sf P_f
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hevs _ _ _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, cliPollKpk_getEvs_nil, cliPollPk_opkOkEvs_nil,
            cliPollSelf_kpEvs_nil, List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htrf
        have hopkUpd := cliPollPk_opkOkUpdate_eq A.repAlloc y.g.F w.opkWord (cliKitStk B)
          (hdrOpkIdBv? (mkBadKemHdr y.g.msg kp)) wOpk
        rw [hopkUpd] at hPf
        unfold P2V1Arm5EnvOfAcceptErr at hevs; rw [hOk14_eq] at hevs
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g none evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inr (Or.inr (Or.inr (Or.inr hevs)))
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        have hbobEnt := badKemSpeWords_entails_decResAt_anyHeap A.repAlloc y.out errTag w2 w3 w4 w5 w6 err0
        refine Entails.trans (Entails.trans hPf (Entails.of_eq (by sep_ac_rfl : _ =
          (speWordsAt y.out errTag w2 w3 w4 w5 w6 ∗ pqxdhBadKemErrPayloadAt A.repAlloc errTag w2 w3 w4) ∗ _))) ?_
        refine Entails.trans (sepConj_mono_left hbobEnt) ?_
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
  | some r =>
    obtain ⟨sess, hcur⟩ :=
      LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.currentSession_some_of_cliPollSessPlaced_loadRel
        hload_rel
    have hloadS : loadRec Scope y.g.F y.g.peer.val = .ok (some r) :=
      LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.loadRec_of_cliPollSessPlaced_loadRel
        hinjK hsub hfPeer hload_rel
    have hnm := hnoMatch r sess hloadS hcur
    have hunpack :
        ((stageP2PostP1At (A.atState lim st1 s1)
           y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
         p1LoadedRecordAt scopeKit A.repAlloc y.fut (some r) ∗
         preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
         protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
         protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
         storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
         lsLogOff ∗ stackAt sp (dpClosSubStack B)) ∗ Fr_p2) ⊢
          ∃∗ g : RecordGhost, ∃∗ recG : SessionGhost, ∃∗ w : PathAEntryWords,
            ⌜(y.g.msgG.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63) ∧
              (∀ id : BitVec 32, y.g.msg.preKeyId = some id → w.opkWord = id)⌝ ∗
            LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2OverBadKemPreAtPlaced A lim
              (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
              (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B))
              (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
              (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
              st1 s0 s1 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
              y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
              y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
              (mkBadKemHdr y.g.msg kp) kp.ciphertext y.g.msg.message.messageVersion
              0#8 0#8 w.b_4b0 w.b_4f1 0#8
              w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
              StoresGhost.opened.signed StoresGhost.opened.kyber
              StoresGhost.opened.oneTime StoresGhost.opened.identity
              y.g.me y.g.peer g recG sess (dpClosSubStack B)
              (badKemInnerFramePlacedBudget A y kp rngPtr sp ∗ Fr_p2) := by
      refine Entails.trans (sepConj_mono_left
        (stageP2_entry_unpack_badKem_over_placedBudget A lim y r sess kp st1 s0 s1 sp fp
          rngPtr v_a8 v_b8 v_d0 hcur hv4 hkp rfl hstoreOk hfPeer hsub)) ?_
      simp only [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun g => Entails.sepExists_right g ?_
      refine Entails.sepExists_elim fun recG => Entails.sepExists_right recG ?_
      refine Entails.sepExists_elim fun w => Entails.sepExists_right w ?_
      rw [sepConj_assoc]
      refine Entails.pure_left fun hp => Entails.pure_right hp ?_
      unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2OverBadKemPreAtPlaced
      exact Entails.of_eq (by sep_ac_rfl)
    refine sepWPp_conseq_pre hunpack ?_
    refine SepWPp.exists_elim fun g => SepWPp.exists_elim fun recG =>
      SepWPp.exists_elim fun w => SepWPp.pure_left fun ⟨⟨hct_nz, hct_bd⟩, hopkWord⟩ => ?_
    have ⟨hArm3_eq, hOk14_eq⟩ := r20a6w_opk_env_eq
      (spkBox := (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B)).getBoxSize)
      (spkPoll := (cliPollSpkFullBudgetEnv A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B) ReadEnv).getPollEnv
        StoresGhost.opened.signed y.g.msg.signedPreKeyId)
      (kpkBox := (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B)).getBoxSize)
      (kpkPoll := (cliPollKpkFullBudgetEnv A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B) ReadEnv).getPollEnv
        StoresGhost.opened.kyber kp.preKeyId)
      (pkBox1 := (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B)).getBoxSize)
      (pkBox2 := (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)).getBoxSize)
      (pkPoll1 := (cliPollPkFullBudgetEnv A.repAlloc y.g.F w.opkWord (cliKitStk B) ReadEnv).getPollEnv
        StoresGhost.opened.oneTime)
      (pkPoll2 := (cliPollPkFullBudgetEnv A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B) ReadEnv).getPollEnv
        StoresGhost.opened.oneTime)
      (kpBox := (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpBoxSize)
      (pm := y.g.msg) (kp := kp) (opkWord := w.opkWord)
      hopkWord (fun hw => by rw [hw]) (fun hw => by rw [hw])
    have hstk := stageP2OverV1CallStack_le_subStack_badKem_placed (A := A.repAlloc)
      y.g.F y.g.peer y.g.msg.signedPreKeyId kp.preKeyId w.opkWord y.g.msg.baseKey B
    have hfs := stageP1ProgPlaced_eq_dpPollProgPlaced mmpl gh W ▸
      cliPollStageP2_fsAt_stages_placed hh y.g.F y.g.peer y.g.msg.signedPreKeyId kp.preKeyId
        w.opkWord y.g.msg.baseKey B hfs1
    have hPromMissAt :=
      promoteMatchingMissAt_placed_of_gen
        (cliPromoteMatchingMissGen_placed_d3 A.repAlloc mmpl gh W)
        y.fut g recG sess 4#8 (5#8 :: bytesToBv8 (mkBadKemHdr y.g.msg kp).ekAPk)
        (not_p2SessMatchesMsg_of_v4_badKem kp hv4 hnm)
        (by
          rw [bytesToBv8_mkBadKemHdr_ekAPk]
          exact LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3V3PathAKitsPlacedBudget.baseKey_serialize_length y.g.msg.baseKey)
    exact LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudget.stageP2_over_badKem_kits_memInv_at_placed
      StageP2MemInv.frozen ext hH hPure hSameAcct hInitBob
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollSelfBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
      hSelfVt hSelfOk
      (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
      (cliPollSpkFullBudgetEnv A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B) ReadEnv)
      hSpkVt hSpkOk
      (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B))
      (cliPollKpkFullBudgetEnv A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B) ReadEnv)
      hKpkVt hKpkOk
      (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
      (cliPollPkFullBudgetEnv A.repAlloc y.g.F w.opkWord (cliKitStk B) ReadEnv)
      (cliPollPk_vtablesPlacedOk (A := A.repAlloc) y.g.F w.opkWord (cliKitStk B) hDropNz)
      (hKits.pkOk y.g.F w.opkWord)
      (dpClosSubStack B)
      ((stageP2OverCallStack4K_eq _ _ _ _).symm ▸
        Nat.le_trans (p2_over_callStack_le_v1CallStack _ _ _ _) hstk)
      (Nat.le_trans (p2_sub56Stack_le_v1CallStack _ _ _ _)
        (Nat.le_trans (p2_over_baseV1Call_le_v1CallStack _ _ _ _) hstk))
      (Nat.le_trans p2_over_dropSS3_le_overPure
        (Nat.le_trans (p2_over_pure_le_v1CallStack _ _ _ _) hstk))
      hsame_le
      (Nat.le_trans LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5PlacedBudget.p2_badKem_entry_le_stageP2bStack
        (Nat.le_trans p2_stageP2bStack_le_bobV1
          (Nat.le_trans (p2_bobStack_le_v1CallStack _ _ _ _)
            (Nat.le_trans (p2_over_baseV1Call_le_v1CallStack _ _ _ _) hstk))))
      st1 s0 s1 (badKemInnerFramePlacedBudget A y kp rngPtr sp ∗ Fr_p2) _
      sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
      y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkBadKemHdr y.g.msg kp) kp.ciphertext ikBSk ikBPk
      y.g.msg.message.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer g recG sess hPromMissAt
      (hfits_p2.mono fun evs hevs => by
        unfold StageP2BadKemRejectEnv; rw [hkpkId]
        dsimp only [P2OverSub1To4Env, P2OverSub1To3Arm1Env, P2OverSub1To3Arm2Env,
          P2OverSub1To4Arm3Env, P2OverSub1To4OkEnv] at hevs
        rcases hevs with h1 | h2 | h3 | hok4
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · rw [hArm3_eq] at h3; exact Or.inr (Or.inr (Or.inl h3))
        · rw [hOk14_eq] at hok4; exact Or.inr (Or.inr (Or.inr (Or.inl (SeqEnv.inl hok4)))))
      (fun evs14 hevs14 => by
        dsimp only [P2OverSub1To4OkEnv] at hevs14; rw [hOk14_eq] at hevs14
        have hArm4 := hfits_p2.mono fun evs h4 => by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]
          exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
        exact r20a6w_fitsEnv_drop_freeOnly (hArm4.seq_right hevs14))
      (fun _ _ _ _ _ _ _ _ _ _ evs14 evsKp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hevs14 hevsKp => by
        dsimp only [P2OverSub1To4OkEnv] at hevs14; rw [hOk14_eq] at hevs14
        have hArm5 := hfits_p2.mono fun evs h5 => by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]
          exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
        exact r20a6w_fitsEnv_step3 hArm5 hevs14 hevsKp
          (r20a6w_freeOnlyEvs_rustDeallocEvents
            (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpBoxSize 8))
      hct_nz hsp_sub hikBSk_len hikBPk_len hikAPk_len hekAPk_len hkemCt_len hct_bd hbadKem hro1 hfs
      rfl (fun r' hrel _ => cliPollSpk_wf_of_preKeysWf_placed hstoreOk.preKeysWf r' hrel)
      rfl (fun r' hrel _ => cliPollKpk_wf_of_preKeysWf_placed hstoreOk.preKeysWf r' hrel)
      (fun id hid => hopkWord id ((hdrOpkIdBv?_mkBadKemHdr y.g.msg kp).symm.trans hid))
      (fun id hid => (hopkWord id ((hdrOpkIdBv?_mkBadKemHdr y.g.msg kp).symm.trans hid)).symm)
      (fun _id r' _ hrel _ => cliPollPk_wf_of_preKeysWf_placed hstoreOk.preKeysWf r' hrel)
      hkp_sk hkp_pk (Or.inr (distinctSid_of_not_sameAcct_d3 hnotSameSid))
      hpc1 hrun1 hs1_sp hsp_align htr_pref hvregs1
      hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx29_fp
      (fun e evs sf P_f _ hevs _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, List.append_nil] at htrf
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g (some r) evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inl hevs
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        refine Entails.trans hPf (Entails.trans
          (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
            y.g.F y.g.msg.signedPreKeyId (cliKitStk B) y.out e err0)) ?_)
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
      (fun _spkRec e evs sf P_f _ _ _ hevs _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, cliPollKpk_getEvs_nil, List.append_nil, List.append_nil] at htrf
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g (some r) evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inr (Or.inl hevs)
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        refine Entails.trans hPf (Entails.trans
          (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
            y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B) y.out e err0)) ?_)
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
      (fun _spkRec _kpkRec opkId e evs sf P_f _ _ _ _ hopkHdr _ hevs _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, cliPollKpk_getEvs_nil, cliPollPk_getEvs_nil,
            List.append_nil, List.append_nil, List.append_nil] at htrf
        dsimp only [P2OverSub1To4Arm3Env] at hevs
        rw [← hopkHdr, hArm3_eq] at hevs
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g (some r) evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inr (Or.inr (Or.inl hevs))
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        refine Entails.trans hPf (Entails.trans
          (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
            y.g.F w.opkWord (cliKitStk B) y.out e err0)) ?_)
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
      (fun _spkRec _kpkRec wOpk e evs sf P_f _ _ _ _ _ _ hevs _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, cliPollKpk_getEvs_nil, cliPollPk_opkOkEvs_nil,
            cliPollSelf_kpEvs_nil, List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htrf
        have hopkUpd := cliPollPk_opkOkUpdate_eq A.repAlloc y.g.F w.opkWord (cliKitStk B)
          (hdrOpkIdBv? (mkBadKemHdr y.g.msg kp)) wOpk
        rw [hopkUpd] at hPf
        unfold P2OverV1Arm4Env P2V1Arm4Env at hevs; rw [hOk14_eq] at hevs
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g (some r) evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inr (Or.inr (Or.inr (Or.inl hevs)))
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        have hkpEnt := Entails.trans
          (cliPollSelf_kpErr_entails_decResAt_err_placed A.repAlloc y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)
        refine Entails.trans hPf (Entails.trans (sepConj_mono_left hkpEnt) ?_)
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
      (fun _ _ _ _ _ _ wOpk _ _ _ errTag w2 w3 w4 w5 w6 evs sf P_f
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hevs _ _ _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, cliPollKpk_getEvs_nil, cliPollPk_opkOkEvs_nil,
            cliPollSelf_kpEvs_nil, List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htrf
        have hopkUpd := cliPollPk_opkOkUpdate_eq A.repAlloc y.g.F w.opkWord (cliKitStk B)
          (hdrOpkIdBv? (mkBadKemHdr y.g.msg kp)) wOpk
        rw [hopkUpd] at hPf
        unfold P2OverV1Arm5EnvOfAcceptErr P2V1Arm5EnvOfAcceptErr at hevs
        rw [hOk14_eq] at hevs
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g (some r) evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inr (Or.inr (Or.inr (Or.inr hevs)))
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        have hbobEnt := badKemSpeWords_entails_decResAt_anyHeap A.repAlloc y.out errTag w2 w3 w4 w5 w6 err0
        refine Entails.trans (Entails.trans hPf (Entails.of_eq (by sep_ac_rfl : _ =
          (speWordsAt y.out errTag w2 w3 w4 w5 w6 ∗ pqxdhBadKemErrPayloadAt A.repAlloc errTag w2 w3 w4) ∗ _))) ?_
        refine Entails.trans (sepConj_mono_left hbobEnt) ?_
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))

/-- Kit-parametric counterpart of `D3BadKemRejectAuxPlacedBudget.stageP2_badKem_reject_full_placedBudget`. -/
theorem stageP2_badKem_reject_full_placedBudget_of_kits [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CliDecPkPollKitsPlacedOk A lim B ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (R : SepProp) (s0 : State) (opt : Option (SessionRecord (List (BitVec 8))))
    (evs_p1 : List AllocEvent) (s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hstoreOk : DecPkStoreOk ⟨W.C, W.Q⟩ y.g.F)
    (hbadCond : MsgCondBadKem Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g opt))
    (hevs_sub : ∀ evs_p2,
      StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g opt evs_p2 →
      DecPkEnv y.g (evs_p1 ++ evs_p2))
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok opt))
    (htr1 : s1.trace = s0.trace) (hro1 : LibsignalFrozen lsmpl s1.mem)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64) (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x868#64) (hrun1 : s1.status = .Running)
    (halign1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym))
    (hs1_files : s1.fs.files = y.g.F) :
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (s0.sp - 0xcd0#64) v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗ lsLogOff ∗ stackAt (s0.sp - 0xcd0#64) (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32)
      (fun sf P_f =>
        (Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsFrozen lsmpl
            (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsFrozen lsmpl
            (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).onPanic y s0 sf ∗ R)) := by
  let _ := hcoins
  exact r20a6w_stageP2_badKem_reject_body_of_kits
    A lim mmpl gh W B S Scope hDropNz hG hh hKits hinjK hsub stk' hneed hstk63
    y R s0 opt evs_p1 s1 rngPtr v_a8 v_b8 v_d0
    hfPeer hstoreOk hbadCond hans
    hfits_p2 hevs_sub hload_rel htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 halign1 hregs1 hs1_files

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectAuxPlacedBudgetFd
