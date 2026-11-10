/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PollPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAVerNeRawSlot520 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget
import ProofLib.SepLogic.WPp

/-!
# Kit-Parametric Stage-P2 Overwrite Producer (`OverD3`)

Proves `h7ra_stageP2Over_archive_at_cliRunBudgets_frozen_of_kits`, discharging
`H7RAStageP2OverAtBStmt` at `A, lim, cliRunBudgets` from `CliDecPkPollKitsPlacedOk` without a raw
`hRead` hypothesis.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage2PlacedBudgetFd

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (ApiError PreKeySignalMessage Session SessionRecord)
open CryptoVerification (
  LibsignalFrozen LibsignalFullPlacement LibsignalPlacement
  libsignalFrozen_of_keepsFrozen lsProg_51 lsProg_75 lsmpl lsρ withLsCl
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  hdrOpkIdBv? mkP2AcceptKeysInput stageP1ProgPlaced
)
open CryptoVerification.E2E (
  PreKeyMessageFields UnreachedPqxdhPrimitives acceptInput keyPairOf modelPrims toU8 vecU8
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  bytesToBv8 ofSignalPqxdhAcceptKeysInput ofSignalPqxdhDRKey
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys acceptKeys_ofSignalPqxdhPrimitives)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  bytesToBv8_vecU8 ls_subroutine_ok_withLsFrozen_of_block ofSignalPqxdhPrimitives vecU8_length
)
open CryptoVerification.E2E.Pqxdh.ResponderStore (clampBv8List_length)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (
  AddrVal PreKeyMsgGhost RecordGhost preKeyMsgAt
)
open CryptoVerification.LibsignalTripleRatchet (SendCall noAllocShimSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost signalMessageAt)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.KitInst (
  cliKpk_getRel_error_iff cliPk_getRel_error_iff cliSpk_getRel_error_iff
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other
)
open CryptoVerification.SignalSession.Cli.RunProofs (pkStoreKeys pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  cliKitStk cliModelPrims_matchCrypto cliModelPrims_structural
  cliPollIdKitPlaced cliPollKpkKitPlaced cliPollKpk_vtablesPlacedOk
  cliPollPkKitPlaced cliPollPk_vtablesPlacedOk cliPollSelfKitPlaced cliPollSelf_kpRel_err_placed
  cliPollSelf_kpRel_ok_placed cliPollSelf_regIdRel_err_placed cliPollSelf_regIdRel_ok_placed
  cliPollSelf_vtablesPlacedOk cliPollSpkKitPlaced cliPollSpk_vtablesPlacedOk
  distinctSid_of_decPkOk₀ dpClosSubStack dpPollProgPlaced entails_sepConj_anyHeap
  hdrOpkIdBv?_mkPathAHdr mkPathAHdr
  p2Over_cliPollKpk_getEvs_placed p2Over_cliPollPk_getEvs_placed p2Over_cliPollPk_opkOkEvs_placed
  p2Over_cliPollPk_opkOkUpdate_placed p2Over_cliPollSelf_kpEvs_placed
  p2Over_cliPollSelf_regIdEvs_placed p2Over_cliPollSpk_getEvs_placed pathAInitState
  pkStoreKeys_eq_none_of_kpk_err pkStoreKeys_eq_none_of_opk_err pkStoreKeys_eq_none_of_spk_err
  pmOfE_fields pqxdhAcceptErr_entails_decResAt_anyHeap_ext preKeyMsgAt_eq_base_idKey_sep
  preKeyMsgRemBaseIdKeyAt scope_of_loadRec_some sepWPp_conseq_pre sp_sub_576_ne_zero
  x29_eq_sp0_sub_60 x29_eq_sp_add_c70
)
open CryptoVerification.SignalSession.Cli.Slots (
  blackBox_row_placed cliGhostExterns_sat_of_cliExternsPlaced scopeIn
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  InitializeBobV1FrozenOkPlaced4KOfEnv StageP2BaseCalleesPlaced4K
  initializeBobSessionErrOwnedFrozen4KPlacedSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget (
  P2Sub1To4Arm3Env P2Sub1To4OkEnv P2Sub4OkEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv StageP2BaseCalleesPlaced4K.of_hooks
  initializeBobSession_ok_v1_of_env_4k_frozen_placed_on_stageP1 isSameAccount_4k_placed_ok_on_stageP1
  p2_errOwned_frozen_to_defs4K_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget (
  P2Sub6Env P2V1Arm4Env P2V1Arm5EnvOfAcceptErr P2V1Arm6EnvOfBob
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget (
  p2PromoteOverAtSpecWithEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget (
  PromoteMatchingMissAtPlacedProp PromoteOverAtPlacedWithEnvProp promoteMatchingMissAt_placed_of_gen
  promoteOverAt_placed_of_gen_withEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget (
  P2OverSub1To4Arm3Env P2OverSub1To4OkEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget (
  P2OverSub6EnvOf P2OverV1Arm4Env P2OverV1Arm5EnvOfAcceptErr P2OverV1Arm6EnvOfBob
  P2OverV1OkEnvOfBobAndProm stageP2OverV1KitsMemInvAtPlacedOfEnvProp
  stageP2_over_v1_kits_frozen_ext_defs_placed_ofEnv
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget (
  initializeBobSession_err_owned_frozen_placed_ok_of_accept
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (EncodeRawPreallocPlacedOkX)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  decPkOverDef_pathCOver_stage2_rej_placed pm_fields_of_pkToE
)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget (
  CliDecPkPollKitsPlacedOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PollPlacedBudget (
  p2ErrFrame_fold_pathA_d3_placed_rep p2OverOkPost_fold_pathCOver_d3_placed
  p2Over_not_sessMatchesMsg_d3 stageP2_entry_unpack_pathCOver_d3_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAVerNeRawSlot520 (H7RAStageP2OverAtBStmt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlacedBudget (
  encSessionMem_clearPending_lt_32 p2Over_serBytes_len stageP2OverV1CallStack4K_le_subStack_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  P2OverPathCErrEnvOf P2OverPathCOkEnvOf PromoteOverArchiveCanonSessEnv
  cliPromoteMatchingMissGen_placed_ok cliPromoteOverGen_archive_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux (
  cliStageP2ClosureHooksPlaced promoteOverArchiveEnv_eq_canon uuidTryParse_placed_vm_code_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget (
  cliPqxdhAccept_err_owned_full_placed_ok cliPqxdhAccept_opt_fields_full_placed_ok
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
  cliPollKpk_getErr_entails_decResAt_anyHeap_placed cliPollPk_getErr_entails_decResAt_anyHeap_placed
  cliPollSelf_kpErr_entails_decResAt_err_placed cliPollSelf_regIdErr_entails_decResAt_err_placed
  cliPollSpk_getErr_entails_decResAt_anyHeap_placed cliPollStageP2_fsAt_stages_placed
  cliResponderPqxdhHookContractsPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliStageP2KitEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_framelessMemcpy_budget_sat
  cliExternsPlaced_sessionMemcpyRegion_budget_sat cliExternsPlaced_sessionMemcpy_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  framelessMemcpyBudgetSpec framelessMemcpySpec noAllocShimBudgetSpec
)

private theorem hookSat_noAllocShimBudget_of_withVmPreserved
    {H : String → Option (State → State)}
    (hsat : HookSat H CryptoVerification.lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)) :
    HookSat H CryptoVerification.lsRustNoAllocShimSym noAllocShimBudgetSpec := by
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

private theorem hookSat_framelessMemcpy_of_vm
    {H : CryptoVerification.LibsignalHooks}
    (h : HookSat H "memcpy"
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    HookSat H CryptoVerification.lsMemcpySym framelessMemcpySpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    rcases x with ⟨dst, src, bs⟩
    dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      framelessMemcpySpec, framelessMemcpyBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact ⟨hkf, hsym, Or.inr hrest⟩

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

private theorem hookSat_p2Memcpy4K_of_vm
    {H : CryptoVerification.LibsignalHooks}
    (h : HookSat H "memcpy"
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    HookSat H CryptoVerification.lsMemcpySym
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget.p2Memcpy4KSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases x with ⟨dst, src, bs⟩
  dsimp only [LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget.p2Memcpy4KSpec,
    LibsignalBinary.Heap.SpecBudget.withVmPreserved,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Memcpy4KSpec,
    ProofLib.libcMemcpySpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  have hpre' : s0.mem ⊨
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec).pre (dst, src, bs) s0 ∗
        (stackAt s0.sp CryptoVerification.RustHeap.allocHookStack ∗ R) := by
    dsimp only [LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by sep_ac_rfl)⟩
  rcases hok (dst, src, bs) (stackAt s0.sp CryptoVerification.RustHeap.allocHookStack ∗ R)
      s0 hrun hpre' hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget.p2Memcpy4KSpec,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Memcpy4KSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpost.1, hpost.2.1, Satisfies.of_eq hpost.2.2 (by sep_ac_rfl)⟩
  · exfalso
    rcases hrest with ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩ <;> {
      dsimp only [LibsignalBinary.Heap.SpecBudget.withVmPreserved,
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec] at hp
      rw [satisfies_pure_sepConj] at hp
      exact hp.1
    }

private theorem cliStageP2BaseCalleesPlaced4K [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2BaseCalleesPlaced4K A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  StageP2BaseCalleesPlaced4K.of_hooks
    (hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim)
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    (hookSat_p2Memcpy4K_of_vm hh.codecHooks.memcpy)
    (isSameAccount_4k_placed_ok_on_stageP1
      ((cliGhostExterns_other gh (cliExternsPlaced mmpl W)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W)))
      (uuidTryParse_placed_vm_code_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))))

private theorem cliInitBobV1FrozenOkPlaced4K [LibsignalFullPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives) (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W
      (InitialStateEnv W.C.F) (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv) :
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
    (hookSat_sessionMemcpyRegionBudget_of_vm hh.codecHooks.memcpy)
    (cliPqxdhAccept_opt_fields_full_placed_ok
      (callerProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 75)
      X mmpl gh W hG)
    hSpqr.initialStateMemInv_lsProg75
    (fun _ _ _ => Iff.rfl)

private theorem cliInitBobErrOwnedFrozen4K_ok [LibsignalFullPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    (_hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok
      (stageP1ProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 75)
      (initializeBobSessionErrOwnedFrozen4KPlacedSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
        A lim
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))) := by
  have h75 :=
    initializeBobSession_err_owned_frozen_placed_ok_of_accept
      (cliPqxdhAccept_err_owned_full_placed_ok
        (callerProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 75)
        X mmpl gh W hG)
  have hbase :=
    ls_subroutine_ok_withLsFrozen_of_block
      (callerProg := stageP1ProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (calleeProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (i := 518) (j := 75) h75
  refine p2_errOwned_frozen_to_defs4K_placed ?_
  refine subroutine_ok_map hbase ?_
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun _ hpost => hpost⟩
  dsimp only [withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

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

private theorem preKeyMsg_reasm_d3 (A : CryptoVerification.RustHeap.RustAlloc)
    (msgG : PreKeyMsgGhost) (msgA : BitVec 64)
    (msg : PreKeySignalMessage) :
    signalMessageAt A msgG.msg msgA msg.message ∗
      ((msgA + 0xa8#64) ↦ₛ msg.baseKey.bytes.toList) ∗
      ((msgA + 0xc8#64) ↦ₛ msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRemBaseIdKeyAt A msgG msgA msg ⊢
      preKeyMsgAt A msgG msgA msg := by
  rw [preKeyMsgAt_eq_base_idKey_sep]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem stageP2Over_kitsMemInv_of_kits [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W
      (InitialStateEnv W.C.F) (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hKits : CliDecPkPollKitsPlacedOk A lim cliRunBudgets
      (ReadFileRuleEnvFixed cliIo.rd) DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkWord opkWord0 : BitVec 32) (kbk : PublicKey) :
    let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
    let B := cliRunBudgets
    let selfEnv := fun F' peer' => cliPollSelfBudgetEnv A.repAlloc F' peer' (cliKitStk B) ReadEnv
    let kitEnvs := cliStageP2KitEnvs (A := A.repAlloc) ReadEnv B selfEnv
    let P_m := ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)
    stageP2OverV1KitsMemInvAtPlacedOfEnvProp
      (LibsignalFrozen lsmpl)
      P_m A lim W.C.F
      (InitializeBobV1OptFieldsEnv P_m W.C.F)
      (AcceptOptFieldsEnv P_m)
      (fun _ s => PromoteOverArchiveCanonSessEnv s)
      (cliGhostExterns gh (cliExternsPlaced mmpl W))
      (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (kitEnvs F0 peer spkId kpkId opkWord0 kbk).selfEnv
      (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
      (kitEnvs F0 peer spkId kpkId opkWord0 kbk).spkEnv
      (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
      (kitEnvs F0 peer spkId kpkId opkWord0 kbk).kpkEnv
      (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
      (kitEnvs F0 peer spkId kpkId opkWord kbk).pkEnv
      (dpClosSubStack B) :=
  let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
  let B := cliRunBudgets
  let selfEnv := fun F' peer' => cliPollSelfBudgetEnv A.repAlloc F' peer' (cliKitStk B) ReadEnv
  let kitEnvs := cliStageP2KitEnvs (A := A.repAlloc) ReadEnv B selfEnv
  let P_m := ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)
  stageP2_over_v1_kits_frozen_ext_defs_placed_ofEnv
    (M := M) (P := P_m) (A := A) (lim := lim) (F := W.C.F)
    (BobV1Env := InitializeBobV1OptFieldsEnv P_m W.C.F)
    (AcceptErrEnv := AcceptOptFieldsEnv P_m)
    (PromEnv := fun _ s => PromoteOverArchiveCanonSessEnv s)
    (cliGhostExterns gh (cliExternsPlaced mmpl W)) (cliModelPrims_structural X W)
    (cliStageP2ClosureHooksPlaced mmpl gh W hh)
    (cliStageP2BaseCalleesPlaced4K mmpl gh W hh)
    (cliInitBobErrOwnedFrozen4K_ok X mmpl gh W hG hh)
    (cliInitBobV1FrozenOkPlaced4K X mmpl gh W hG hh hSpqr)
    (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
    (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
    (kitEnvs F0 peer spkId kpkId opkWord0 kbk).selfEnv
    (cliPollSelf_vtablesPlacedOk F0 peer (cliKitStk B) h547)
    (hKits.selfOk F0 peer)
    (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
    (kitEnvs F0 peer spkId kpkId opkWord0 kbk).spkEnv
    (cliPollSpk_vtablesPlacedOk F0 spkId (cliKitStk B) h547)
    (hKits.spkOk F0 spkId)
    (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
    (kitEnvs F0 peer spkId kpkId opkWord0 kbk).kpkEnv
    (cliPollKpk_vtablesPlacedOk F0 kpkId spkId kbk (cliKitStk B) h547)
    (hKits.kpkOk F0 kpkId spkId kbk)
    (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
    (kitEnvs F0 peer spkId kpkId opkWord kbk).pkEnv
    (cliPollPk_vtablesPlacedOk F0 opkWord (cliKitStk B) h547)
    (hKits.pkOk F0 opkWord)
    (dpClosSubStack B) (stageP2OverV1CallStack4K_le_subStack_placed (A := A.repAlloc)
      F0 peer spkId kpkId opkWord kbk B)

/-- Kit-parametric counterpart of `h7ra_stageP2Over_archive_at_cliRunBudgets_frozen_ok` proving
`H7RAStageP2OverAtBStmt` from `CliDecPkPollKitsPlacedOk` without a raw `hRead` hypothesis. -/
theorem h7ra_stageP2Over_archive_at_cliRunBudgets_frozen_of_kits [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hKits : CliDecPkPollKitsPlacedOk A lim cliRunBudgets
      (ReadFileRuleEnvFixed cliIo.rd) DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W
      (InitialStateEnv W.C.F) (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv) :
    let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
    let selfEnv := fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv
    let kitEnvs := cliStageP2KitEnvs (A := A.repAlloc) ReadEnv cliRunBudgets selfEnv
    H7RAStageP2OverAtBStmt A lim X mmpl gh W cliRunBudgets
      (P2OverPathCErrEnvOf (A := A.repAlloc) X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        kitEnvs)
      (P2OverPathCOkEnvOf (A := A.repAlloc) X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv
        kitEnvs) := by
  dsimp only
  let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
  let B := cliRunBudgets
  let selfEnv := fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv
  let kitEnvs := cliStageP2KitEnvs (A := A.repAlloc) ReadEnv B selfEnv
  intro S DecPkEnv Scope y st_b r sess g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hh0 hfits0 hcoins hdecOk hScope hFok hload hcur hnotMatch htrust hg1
    hfs1 hCode1 htr01 hsp1 hsp0 hsub hpc1 hrun1 halign1 hregs1 herr0 hok
  have hIn : scopeIn r := hScope r (scope_of_loadRec_some hFok hload)
  have hh :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    ⟨hh0.alloc, hh0.allocFs, hh0.panics, hh0.memcpyRO, hh0.bcmp, hh0.fs, hh0.utf8, hh0.memrchr,
      hh0.codecHooks, hh0.allocZeroed, hh0.stringClone, hh0.formatInner⟩
  have hPromMiss := cliPromoteMatchingMissGen_placed_ok A.repAlloc mmpl gh W
  have hPromOver := cliPromoteOverGen_archive_placed_ok mmpl gh W hh hGrow hRaw
  subst hg1
  rcases hregs1 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, _, hx29, hvregs1⟩
  obtain ⟨m, _, hi, hpkToE, hdec0⟩ := hdecOk
  let i : SignalMessage := y.g.msg.message
  have hmsg_i : y.g.msg.message = i := rfl
  have hbk_eq : y.g.msg.baseKey = (pmOfE m i).baseKey :=
    (pm_fields_of_pkToE hpkToE hmsg_i).2.2.2.2.1.trans (pmOfE_fields m i).2.2.2.2.1.symm
  have hfp_reg : s1.readReg64 .x29 = sp + 0xc70#64 := x29_eq_sp_add_c70 hsp0 hx29
  have hsp_align : (sp &&& 15#64 == 0#64) = true := by rw [← hsp1]; exact halign1
  refine sepWPp_with_steps ?_
  refine sepWPp_conseq_pre
    (D3NonCanonStage2PollPlacedBudget.stageP2_entry_unpack_pathCOver_d3_placed (st_b := st_b) (s1 := s1)
      y r sess m i s0 sp (sp + 0xc70#64) rngPtr v_a8 v_b8 v_d0 hcur hpkToE hmsg_i rfl
      hdec0 hFok hScope) ?_
  refine SepWPp.exists_elim fun g => SepWPp.exists_elim fun recG =>
    SepWPp.exists_elim fun w => SepWPp.pure_left fun ⟨_hkit, _hgcur, hcanon, hctBuf_nz, hopkWord⟩ => ?_
  have hPromMissAt : PromoteMatchingMissAtPlacedProp A.repAlloc
      (cliGhostExterns gh (cliExternsPlaced mmpl W))
      y.fut g recG sess 4#8 (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk) :=
    promoteMatchingMissAt_placed_of_gen hPromMiss y.fut g recG sess 4#8
      (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk)
      (D3NonCanonStage2PollPlacedBudget.p2Over_not_sessMatchesMsg_d3 sess y.g.msg m i hpkToE hmsg_i hnotMatch)
      (p2Over_serBytes_len m)
  have hPromOverAt0 := promoteOverAt_placed_of_gen_withEnv hPromOver y.fut g recG sess
    (encSessionMem_clearPending_lt_32 hIn hcur hcanon)
  have hPromOverAt : PromoteOverAtPlacedWithEnvProp M A lim
      (fun _ s => PromoteOverArchiveCanonSessEnv s)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) y.fut g recG sess :=
    promoteOverAtPlacedWithEnv_of_eq (promoteOverArchiveEnv_eq_canon hcanon) hPromOverAt0
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
  let ErrEnv := P2OverPathCErrEnvOf (A := A.repAlloc) X W B
    (InitializeBobV1OptFieldsEnv P_m W.C.F) (AcceptOptFieldsEnv P_m) kitEnvs
  let OkEnv := P2OverPathCOkEnvOf (A := A.repAlloc) X W B
    (InitializeBobV1OptFieldsEnv P_m W.C.F) PromoteOverArchiveCanonSessEnv kitEnvs
  exact stageP2Over_kitsMemInv_of_kits A lim mmpl gh W X h547 hG hh hSpqr hKits
    y.g.F y.g.peer m.spkId m.kpkId w.opkWord opkWord0 y.g.msg.baseKey (st := st_b)
    (Qp := fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Qpan sf Pf)
    s0 s1
    (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PollPlacedBudget.pathAInnerFrameD3Placed
      A.repAlloc y i rngPtr sp)
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
      have hevs' : ErrEnv y.g r evs := by
        dsimp only [ErrEnv]; unfold P2OverPathCErrEnvOf; rw [hpkToE]; exact Or.inl hevs
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F m.spkId (cliKitStk B) y.out e err0))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr0 sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          decPkOverDef_pathCOver_stage2_rej_placed hload hcur htrust hnotMatch
            ⟨m, i, hpkToE, hi, hmsg_i, Or.inl (Or.inl hspkNone)⟩, hpost⟩)
    (fun _spkRec e sf Pf evs _ _ hkpkErr hevs hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          List.append_nil, List.append_nil] at htr_f
      have hkpkNone : pkStoreKeys y.g.F m = none := pkStoreKeys_eq_none_of_kpk_err
        ((cliKpk_getRel_error_iff (A := A.repAlloc) cliIo.rd y.g.F cliWrOk m.kpkId
          StoresGhost.opened.kyber m.kpkId).mp ⟨e, hkpkErr⟩)
      have hevs' : ErrEnv y.g r evs := by
        dsimp only [ErrEnv]; unfold P2OverPathCErrEnvOf; rw [hpkToE]; exact Or.inr (Or.inl hevs)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) y.out e err0))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr0 sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          decPkOverDef_pathCOver_stage2_rej_placed hload hcur htrust hnotMatch
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
      have hevs' : ErrEnv y.g r evs := by
        dsimp only [ErrEnv]; unfold P2OverPathCErrEnvOf; rw [hpkToE]; exact Or.inr (Or.inr (Or.inl hevs))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F w.opkWord (cliKitStk B) y.out e err0))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr0 sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          decPkOverDef_pathCOver_stage2_rej_placed hload hcur htrust hnotMatch
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
      have hevs' : ErrEnv y.g r evs := by
        dsimp only [ErrEnv]; unfold P2OverPathCErrEnvOf; rw [hpkToE]
        exact Or.inr (Or.inr (Or.inr (Or.inl hevs)))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (Entails.trans
          (cliPollSelf_kpErr_entails_decResAt_err_placed A.repAlloc
            y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr0 sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          decPkOverDef_pathCOver_stage2_rej_placed hload hcur htrust hnotMatch
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
      have hevs' : ErrEnv y.g r evs := by
        dsimp only [ErrEnv]; unfold P2OverPathCErrEnvOf; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hevs))))
      have hPf' := Entails.trans hPf (by rw [← sepConj_assoc]; exact Entails.refl _)
      have hpost := Entails.trans hPf' (Entails.trans
        (sepConj_mono_left (pqxdhAcceptErr_entails_decResAt_anyHeap_ext A.repAlloc
          y.out errTag w2 w3 w4 w5 w6 err0))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr0 sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          decPkOverDef_pathCOver_stage2_rej_placed hload hcur htrust hnotMatch
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
      have hevs' : ErrEnv y.g r evs := by
        dsimp only [ErrEnv]; unfold P2OverPathCErrEnvOf; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        rw [haccSome]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hevs))))
      have hregNone := cliPollSelf_regIdRel_err_placed hregErr
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (Entails.trans
          (cliPollSelf_regIdErr_entails_decResAt_err_placed A.repAlloc
            y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)))
        (D3NonCanonStage2PollPlacedBudget.p2ErrFrame_fold_pathA_d3_placed_rep (stf := M.stepEvents evs st_b) (sf := sf)
          y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpkToE hmsg_i rfl hopkWord))
      exact herr0 sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          decPkOverDef_pathCOver_stage2_rej_placed hload hcur htrust hnotMatch
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
      have hevs' : OkEnv y.g r evs := by
        dsimp only [OkEnv]; unfold P2OverPathCOkEnvOf; rw [hpkToE, hcur]; dsimp only; rw [hk, hkpOk]; dsimp only
        rw [haccSome0]; exact hevs
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
      have hmsg_reasm := preKeyMsg_reasm_d3 A.repAlloc y.g.msgG y.g.msgA y.g.msg
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
        hSteps12 htr2 hpc2 hrun2 hsp2 halign2 hx19_2 hx27_2 hx29_sp0 hvregs2
        (libsignalFrozen_of_keepsFrozen hCode1 hSteps12.keepsFrozen))

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage2PlacedBudgetFd
