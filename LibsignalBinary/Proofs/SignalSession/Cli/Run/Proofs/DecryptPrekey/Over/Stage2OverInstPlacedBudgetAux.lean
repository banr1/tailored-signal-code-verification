/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget
import LibsignalBinary.Proofs.TripleRatchet.InImage.UuidTryParse.ParserTryParse
import ProofLib.Placed.OpcodeExclusion
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Auxiliary Lemmas for Budget-Threaded CLI Poll Stage P2 Over-Path (`Path C`) Instantiation

Proves `VmPreserved`-strengthened `uuidTryParseCodeSpec` on Block `252`, constructs the 4 KiB
Stage P2 callee bundles at `cliExternsPlaced mmpl W`, and discharges the CPS proof of Path C
Stage P2 V1 (`+0x0868 -> +0x1778` and error arms) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (PublicKey ShaCompress SignalMessage)
open CryptoGames.LibsignalSessionApi (ApiError Session SessionRecord)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalFrozen LibsignalFullPlacement LibsignalHooks
  LibsignalPlacement blkPC_252 blkPl_252 blkPC_254 blkPl_254 blkPC_255 blkPl_255
  libsignalSessionLib ls_subroutine_ok_cl_of_block ls_subroutine_ok_cl_of_plain
  lsBlackBoxU8Sym lsMemcpySym lsProg_75 lsRustNoAllocShimSym lsmpl lsρ sepWP_seq_lscl
  withLsCl withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.RecordCodecs (
  IdentityKeyPair KyberPreKeyRecord PreKeyRecord SignedPreKeyRecord
)
open CryptoVerification.E2E (
  PreKeyMessageFields ResponderPreKeySecrets UnreachedPqxdhPrimitives
  acceptInput keyPairOf modelPrims toU8 vecU8
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput DRKey Primitives bytesToBv8 ofSignalPqxdhAcceptKeysInput ofSignalPqxdhDRKey
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys acceptKeys_ofSignalPqxdhPrimitives)
open CryptoVerification.E2E.Pqxdh.ResponderStore (clampBv8List_length)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  bytesToBv8_vecU8 ofSignalPqxdhPrimitives vecU8_length
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved)
open CryptoVerification.E2E.Record (encSession)
open CryptoVerification.E2E.Record.Serialization (CanonSession encSessionMem)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost preKeyMsgAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsAt FsFiles IdentitySelfStoreSpec
  KyberPreKeyStoreSpec LibsignalCodeRoLoaded
  PreKeyStoreSpec SignedPreKeyStoreSpec
)
open CryptoVerification.LibsignalTripleRatchet (
  noAllocShimSpec rootStack uuidErrParseOther uuidResultAt uuidTryParseCodeSpec uuidTryParseSpec
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse (
  ParserRegsPreserved braced_all_eq braced_ne_0 braced_ne_37 decodeHex32ResultAt_sp52_none
  decodeHex32ResultAt_sp52_some decodeHex32ResultAt_sp88_none decodeHex32ResultAt_sp88_some
  decodeHex32Spec eq_ofNat_of_toNat_eq exists_36_parts exists_38_parts exists_45_parts
  len_eq_of_reg_eq len_ne_of_reg_ne memRegion_out17_split memRegion_out28_split
  memRegion_out32_split memRegion_sp52_17_none memRegion_sp52_17_some memRegion_sp56_17_split
  memRegion_sp88_17_none memRegion_sp88_17_some memRegion_sp88_32_for_hyphen
  memRegion_sp88_32_for_simple parseHyphenated_all_eq parseHyphenated_ne_13
  parseHyphenated_ne_18 parseHyphenated_ne_23 parseHyphenated_ne_8 parseHyphenated_of_parts
  parserTryParseResultAt parserTryParseResultAt_some_eq parserTryParseResultAt_sp56_none
  parserTryParseResultAt_sp56_some parserTryParseSpec sepWP_parser_branch sepWP_parser_hyph36
  stackAt_parser_split stackAt_uuid_split subroutine_ok_of_sepWP_simple urn_all_eq
  uuidResultAt_some_eq uuidTryParse_of_other_len
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost decodeHex32 parseHyphenated parseSimple
  protocolAddressAt signalMessageAt uuidTryParse
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  OpkOkWitness SessionExtraRel coroOpkIdAtP4 hdrOpkIdBv? mkP2AcceptKeysInput opkOkEvs
  opkOkUpdate p1LoadedRecordAt stageP1ProgPlaced
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  clearPending stageP3Sub5ExtraPrePrev1
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2 (clearPendingGhost)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (
  CliGhostHooks StoresGhost cliGhostExterns cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym
  cliSessionVtSym cliSignedPreKeyVtSym
)
open CryptoVerification.SignalSession.Cli.KitInst (
  cliKpk_getRel_error_iff cliPk_getRel_error_iff cliSpk_getRel_error_iff
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.MainHops.UuidFs (decodeHex32_placed_okFs)
open CryptoVerification.SignalSession.Cli.RunGlue (cliExternsPlaced_row cliGhostExterns_other)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem decResAt)
open CryptoVerification.SignalSession.Cli.RunProofs (
  DecPkOk₀ dpFutDoneAt pkStoreKeys pkToE? pmOfE
)
open CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0 (SessMatchesPm)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit StageP1PostRegs cliKitStk cliModelPrims_structural
  cliPollIdKitPlaced cliPollKpkKitPlaced cliPollKpk_vtablesPlacedOk
  cliPollPkKitPlaced cliPollPk_vtablesPlacedOk cliPollSelfKitPlaced cliPollSelf_kpRel_err_placed
  cliPollSelf_kpRel_ok_placed cliPollSelf_regIdRel_err_placed cliPollSelf_regIdRel_ok_placed
  cliPollSelf_vtablesPlacedOk cliPollSpkKitPlaced cliPollSpk_vtablesPlacedOk
  distinctSid_of_decPkOk₀ dpClosSubStack dpPollEntryPlaced
  dpPollProgPlaced entails_decResAt_anyHeap_of_err hdrOpkIdBv?_mkPathAHdr mkPathAHdr
  pathAInitSession pathAInitState pathA_pm_typed
  pkStoreKeys_eq_none_of_kpk_err pkStoreKeys_eq_none_of_opk_err pkStoreKeys_eq_none_of_spk_err
  pqxdhAcceptErr_entails_decResAt_anyHeap
  preKeyMsgAt_eq_base_idKey_sep preKeyMsgRemBaseIdKeyAt sepWPp_conseq_pre sp_sub_576_ne_zero
  stageP2PostP1At stageP3CoroFrameAt stageP3StackFrameAt x29_eq_sp0_sub_60 x29_eq_sp_add_c70
)
open CryptoVerification.SignalSession.Cli.Slots (
  FilesOkPeer blackBox_row_placed cliGhostExterns_sat_of_cliExternsPlaced scopeIn scopeKit
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget SeqEnv VmPreserved rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (
  sepWP_rebase_vmPreserved trapHooks vmPreserved_advancePC vmPreserved_applyWriteback
  vmPreserved_appendTrace vmPreserved_refl_iff vmPreserved_setFs vmPreserved_setMem_write16
  vmPreserved_setMem_write32 vmPreserved_setMem_write64 vmPreserved_setMem_write8
  vmPreserved_setMem_writeBytes vmPreserved_setPC vmPreserved_setPState vmPreserved_setStatus
  vmPreserved_stepExclLoop vmPreserved_writeReg vmPreserved_writeReg32 vmPreserved_writeReg64
  vmPreserved_writeVReg128 vmPreserved_writeVReg32 vmPreserved_writeVReg64 tpidrEl0_applyWriteback
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  BoxAllocEnv PreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (
  SignedPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  IdentitySelfStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk PreKeyStoreKitPlacedOk
  SignedPreKeyStoreKitPlacedOk
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget (ArchiveCoreEnv)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (pqxdhAcceptOptFieldsPlacedSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget (AcceptSuccessEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget (
  pqxdhAcceptErrOwnedPlacedSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget (p2Memcpy4KSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  InitializeBobV1Env StageP2ClosureHooksPlaced StageP2PureCalleesPlaced4K
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv initializeBobSession_err_owned_4k_placed_ok_on_stageP1
  isSameAccount_4k_placed_ok_on_stageP1 stageP2PureCalleesPlaced4K_of_hooks
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget (
  P2Sub1To4Arm3Env P2Sub1To4Env P2Sub1To4OkEnv P2Sub4OkEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget (
  P2Sub6Env P2V1Arm4Env P2V1Arm5EnvOfAcceptErr P2V1Arm6EnvOfBob
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget (
  PromoteOverAllocMidEnv p2PromoteOverAtSpecWithEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget (
  PromoteMatchingMissAtPlacedProp PromoteMatchingMissGenPlacedProp
  PromoteOverAtPlacedWithEnvProp PromoteOverEnv PromoteOverGenPlacedWithEnvProp
  promoteMatchingMissAt_placed_of_gen promoteOverAt_placed_of_gen
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid2PlacedBudget (
  P2OverSub1To3Arm1Env P2OverSub1To3Arm2Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget (
  P2OverSub1To4Arm3Env P2OverSub1To4Env P2OverSub1To4OkEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub6AuxPlacedBudget (
  P2OverSub6TailEnvOf
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget (
  P2OverSub6EnvOf P2OverV1Arm4Env P2OverV1Arm5EnvOfAcceptErr P2OverV1Arm6EnvOfBob
  P2OverV1OkEnvOfBobAndProm stageP2_over_v1_kits_ext_placed_ofEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeams)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget (
  cliPollKpk_getErr_entails_decResAt_anyHeap_placed
  cliPollPk_getErr_entails_decResAt_anyHeap_placed cliPollSelf_kpErr_entails_decResAt_err_placed
  cliPollSelf_regIdErr_entails_decResAt_err_placed
  cliPollSpk_getErr_entails_decResAt_anyHeap_placed cliPollStageP2_fsAt_stages_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlacedBudget (
  cliPollKpk_wf_of_preKeysWf_placed cliPollPk_wf_of_preKeysWf_placed
  cliPollSpk_wf_of_preKeysWf_placed p2BobInitSessionV1_eq_pathAInitState
  pathA_acceptInput_agree_placed sepWPp_drop_steps sepWPp_with_steps
  sessionExtraRel_pathAInitSession
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget (
  p2ErrFrame_fold_pathA_placed_rep
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (
  overGenP3Pre_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  StageP2OverEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlacedBudget (
  encSessionMem_clearPending_eq encSessionMem_clearPending_lt_32 p2OverOkPost_fold_pathCOver_placed
  p2Over_not_sessMatchesMsg p2Over_serBytes_len pathAInnerFramePlaced
  stageP2OverV1CallStack4K_le_subStack_placed stageP2_entry_unpack_pathCOver_placed
)

set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! ## 1. `VmPreserved` `uuidTryParse` on Block `252` -/

/-- Relocatable `VmPreserved`-strengthened `uuidTryParseCodeSpec` `subroutine_ok` on Block `252`. -/
theorem uuidTryParse_placed_vm_code_ok [LibsignalPlacement] (hooks : LibsignalHooks) :
    subroutine_ok ((blkPC_252).rebase (blkPl_252).base hooks) (blkPl_252).base
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse))) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse).keepsFs)).pre x s0 ∗ R :=
    hpre
  refine (LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressPlacedBudget.uuidTryParse_placed_vm_ok
    hooks).mono_outcome x R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcs, hpost⟩ | ⟨hp1, hpa⟩ | ⟨c, he1, he2⟩ | ⟨ho1, hoo⟩)
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [withLsCodeLoaded, withVmPreserved, Spec.keepsFs] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    refine ⟨hpost.1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.2
  · exact Or.inr (Or.inl ⟨hp1, hpa⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he1, he2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho1, hoo⟩))

/-! ## 2. Stage P2 Callee Bundles & Envelope Congruence Helpers -/

private theorem hookSat_noAllocShimBudget_of_withVmPreserved {H : String → Option (State → State)}
    (hsat : Arm64.HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)) :
    Arm64.HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec := by
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

private theorem hookSat_sessionMemcpyRegionBudget_of_codec {H : LibsignalHooks}
    (h : HookSat H CryptoVerification.lsMemcpySym
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    HookSat H CryptoVerification.lsMemcpySym
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec :=
  ProofLib.HookSat.mono h fun x R _ hpre => ⟨x, R, hpre, fun _ hpost => hpost⟩

private theorem hookSat_sessionMemcpyBudget_of_codec {H : LibsignalHooks} (stk : Nat)
    (h : HookSat H CryptoVerification.lsMemcpySym
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    HookSat H CryptoVerification.lsMemcpySym
      (LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyBudgetSpec stk) := by
  refine ProofLib.HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), ProofLib.stackAt s0.sp stk ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec,
      ProofLib.libcMemcpySpec,
      LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec] at hpre ⊢
    exact ProofLib.Satisfies.mono (ProofLib.Entails.of_eq (by ac_rfl)) hpre
  · dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec,
      LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec] at hpost ⊢
    exact ProofLib.Satisfies.mono (ProofLib.Entails.of_eq (by ac_rfl)) hpost

/-- `StageP2ClosureHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))` from `RunHooksPlaced`. -/
theorem cliStageP2ClosureHooksPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2ClosureHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  StageP2ClosureHooksPlaced.of_hooks
    (hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim)
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    (hookSat_sessionMemcpyBudget_of_codec allocHookStack hh.codecHooks.memcpy)

/-- `StageP2PureCalleesPlaced4K` at `cliGhostExterns gh (cliExternsPlaced mmpl W)` from `RunHooksPlaced`,
`SpqrV1PlacedSeams`, and Block `79` `Pqxdh::accept` contracts. -/
theorem cliStageP2PureCalleesPlaced4K [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (h_accept_ok : subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim AcceptSuccessEnv))
    (h_accept_err : subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim AcceptErrEnv)) :
    StageP2PureCalleesPlaced4K
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      A lim W.C.F AcceptErrEnv (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  stageP2PureCalleesPlaced4K_of_hooks
    (cliModelPrims_structural X W)
    (hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim)
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    (hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)
    (hookSat_sessionMemcpyBudget_of_codec allocHookStack hh.codecHooks.memcpy)
    (isSameAccount_4k_placed_ok_on_stageP1
      ((cliGhostExterns_other gh _ (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans
        (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W)))
      (uuidTryParse_placed_vm_code_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    h_accept_ok
    h_accept_err
    hSpqr.initialStateMemInv_lsProg75

def PromoteOverCanonSessEnvLocal (sess : Session (List (BitVec 8))) :
    List AllocEvent → Prop :=
  let n := (encSession (clearPending sess)).length
  SeqEnv FreeOnlyEvs (SeqEnv (BoundedRustEvs (4 * n + 34) (2 * n + 96)) FreeOnlyEvs)

private theorem promoteOverEnv_eq_canon {recG : SessionGhost} {sess : Session (List (BitVec 8))}
    (hcanon : CanonSession recG sess) :
    PromoteOverEnv recG sess = PromoteOverCanonSessEnvLocal sess := by
  unfold PromoteOverEnv PromoteOverAllocMidEnv PromoteOverCanonSessEnvLocal
  rw [encSessionMem_clearPending_eq hcanon]; rfl

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

private theorem p2Sub4OkEnv_opkWord_eq [LibsignalPlacement] {A : RustAlloc}
    {F0 : FsFiles} {σ : CryptoVerification.SignalSession.Cli.RunProofs.Poll.DpKitStk}
    (pkEnvOf : BitVec 32 → PreKeyStoreBudgetEnv (cliPollPkKitPlaced A F0 0#32 σ))
    (pkBox1 pkBox2 : Nat)
    (pkPoll1 pkPoll2 : BitVec 32 → List AllocEvent → Prop)
    (kpBox : Nat) (m : PreKeyMessageFields) (opkWord : BitVec 32)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → opkWord = id)
    (hbox : opkWord = m.opkId.getD 0#32 → pkBox1 = pkBox2)
    (hpoll : opkWord = m.opkId.getD 0#32 → pkPoll1 = pkPoll2) :
    P2Sub4OkEnv pkBox1 pkPoll1 kpBox (hdrOpkIdBv? (mkPathAHdr m)) =
      P2Sub4OkEnv pkBox2 pkPoll2 kpBox (hdrOpkIdBv? (mkPathAHdr m)) := by
  let _ := pkEnvOf
  cases hid : hdrOpkIdBv? (mkPathAHdr m) with
  | none => rfl
  | some id =>
    have hm : m.opkId = some id := (hdrOpkIdBv?_mkPathAHdr m).symm.trans hid
    have hw : opkWord = m.opkId.getD 0#32 := by rw [hopk id hm, hm]; rfl
    simp only [P2Sub4OkEnv, hbox hw, hpoll hw]

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
    rw [hbox hw, hpoll hw]
    exact ⟨rfl, rfl⟩

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

/-! ## 3. Path C Over Stage P2 V1 CPS Instantiation (`stageP2PathCOver_qpan_cli_placed_of_seams_aux`) -/

def P2OverPathCErrEnvAux [LibsignalPlacement] {A : RustAlloc}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (selfEnvOf : ∀ (F0 : FsFiles) (peer : AddrGhost), BitVec 32 → BitVec 32 → BitVec 32 →
      PublicKey → IdentitySelfStoreBudgetEnv (cliPollSelfKitPlaced A F0 peer (cliKitStk B)))
    (spkEnvOf : ∀ (F0 : FsFiles), AddrGhost → ∀ (spkId : BitVec 32), BitVec 32 → BitVec 32 →
      PublicKey → SignedPreKeyStoreBudgetEnv (cliPollSpkKitPlaced A F0 spkId (cliKitStk B)))
    (kpkEnvOf : ∀ (F0 : FsFiles), AddrGhost → ∀ (spkId kpkId : BitVec 32), BitVec 32 →
      ∀ (kbk : PublicKey),
      KyberPreKeyStoreBudgetEnv (cliPollKpkKitPlaced A F0 kpkId spkId kbk (cliKitStk B)))
    (pkEnvOf : ∀ (F0 : FsFiles), AddrGhost → BitVec 32 → BitVec 32 → ∀ (opkWord : BitVec 32),
      PublicKey → PreKeyStoreBudgetEnv (cliPollPkKitPlaced A F0 opkWord (cliKitStk B)))
    (g : DecPkGhost) (_r : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  match pkToE? g.msg with
  | none => False
  | some m =>
      let opkWord := m.opkId.getD 0#32
      let spkBox := (cliPollSpkKitPlaced A g.F m.spkId (cliKitStk B)).getBoxSize
      let spkPoll := (spkEnvOf g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey).getPollEnv
        StoresGhost.opened.signed m.spkId
      let kpkBox := (cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey (cliKitStk B)).getBoxSize
      let kpkPoll := (kpkEnvOf g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey).getPollEnv
        StoresGhost.opened.kyber m.kpkId
      let pkBox := (cliPollPkKitPlaced A g.F opkWord (cliKitStk B)).getBoxSize
      let pkPoll := (pkEnvOf g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey).getPollEnv
        StoresGhost.opened.oneTime
      let kpBox := (cliPollSelfKitPlaced A g.F g.peer (cliKitStk B)).kpBoxSize
      let kpPoll := (selfEnvOf g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey).kpPollEnv
        StoresGhost.opened.identity
      let regBox := (cliPollSelfKitPlaced A g.F g.peer (cliKitStk B)).regIdBoxSize
      let regPoll := (selfEnvOf g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey).regIdPollEnv
        StoresGhost.opened.identity
      let opkId? := hdrOpkIdBv? (mkPathAHdr m)
      P2OverSub1To3Arm1Env spkBox spkPoll evs ∨
      P2OverSub1To3Arm2Env spkBox spkPoll kpkBox kpkPoll evs ∨
      P2OverSub1To4Arm3Env spkBox spkPoll kpkBox kpkPoll pkBox pkPoll opkId? evs ∨
      P2OverV1Arm4Env spkBox spkPoll kpkBox kpkPoll pkBox pkPoll kpBox opkId? kpPoll evs ∨
      (match pkStoreKeys g.F m, StoresGhost.opened.identity.keyPair cliIo.rd g.F with
       | some k, .ok kp =>
           let inp := ofSignalPqxdhAcceptKeysInput
             (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)
           P2OverV1Arm5EnvOfAcceptErr spkBox spkPoll kpkBox kpkPoll pkBox pkPoll kpBox opkId?
             kpPoll (AcceptErrEnv inp) evs ∨
           (match acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) inp with
            | none => False
            | some drKey =>
                P2OverV1Arm6EnvOfBob spkBox spkPoll kpkBox kpkPoll pkBox pkPoll kpBox opkId?
                  kpPoll (BobV1Env inp drKey) regBox regPoll evs)
       | _, _ => False)

def P2OverPathCOkEnvAux [LibsignalPlacement] {A : RustAlloc}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (selfEnvOf : ∀ (F0 : FsFiles) (peer : AddrGhost), BitVec 32 → BitVec 32 → BitVec 32 →
      PublicKey → IdentitySelfStoreBudgetEnv (cliPollSelfKitPlaced A F0 peer (cliKitStk B)))
    (spkEnvOf : ∀ (F0 : FsFiles), AddrGhost → ∀ (spkId : BitVec 32), BitVec 32 → BitVec 32 →
      PublicKey → SignedPreKeyStoreBudgetEnv (cliPollSpkKitPlaced A F0 spkId (cliKitStk B)))
    (kpkEnvOf : ∀ (F0 : FsFiles), AddrGhost → ∀ (spkId kpkId : BitVec 32), BitVec 32 →
      ∀ (kbk : PublicKey),
      KyberPreKeyStoreBudgetEnv (cliPollKpkKitPlaced A F0 kpkId spkId kbk (cliKitStk B)))
    (pkEnvOf : ∀ (F0 : FsFiles), AddrGhost → BitVec 32 → BitVec 32 → ∀ (opkWord : BitVec 32),
      PublicKey → PreKeyStoreBudgetEnv (cliPollPkKitPlaced A F0 opkWord (cliKitStk B)))
    (g : DecPkGhost) (r : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  match pkToE? g.msg, r.currentSession with
  | some m, some sess =>
      match pkStoreKeys g.F m, StoresGhost.opened.identity.keyPair cliIo.rd g.F with
      | some k, .ok kp =>
          let inp := ofSignalPqxdhAcceptKeysInput
            (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)
          match acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) inp with
          | none => False
          | some drKey =>
              let opkWord := m.opkId.getD 0#32
              let spkBox := (cliPollSpkKitPlaced A g.F m.spkId (cliKitStk B)).getBoxSize
              let spkPoll := (spkEnvOf g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey).getPollEnv
                StoresGhost.opened.signed m.spkId
              let kpkBox := (cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey (cliKitStk B)).getBoxSize
              let kpkPoll := (kpkEnvOf g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey).getPollEnv
                StoresGhost.opened.kyber m.kpkId
              let pkBox := (cliPollPkKitPlaced A g.F opkWord (cliKitStk B)).getBoxSize
              let pkPoll := (pkEnvOf g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey).getPollEnv
                StoresGhost.opened.oneTime
              let kpBox := (cliPollSelfKitPlaced A g.F g.peer (cliKitStk B)).kpBoxSize
              let kpPoll := (selfEnvOf g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey).kpPollEnv
                StoresGhost.opened.identity
              let regBox := (cliPollSelfKitPlaced A g.F g.peer (cliKitStk B)).regIdBoxSize
              let regPoll := (selfEnvOf g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey).regIdPollEnv
                StoresGhost.opened.identity
              let opkId? := hdrOpkIdBv? (mkPathAHdr m)
              let promTail := SeqEnv (fun e => e = rustDeallocEvents regBox 8)
                (SeqEnv (PromoteOverCanonSessEnvLocal sess)
                  (fun e => e = rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1))
              P2OverV1OkEnvOfBobAndProm spkBox spkPoll kpkBox kpkPoll pkBox pkPoll kpBox opkId?
                kpPoll (BobV1Env inp drKey) regBox regPoll promTail evs
      | _, _ => False
  | _, _ => False

set_option maxHeartbeats 1600000 in
/-- Core CPS proof for `Stage2OverInstPlacedBudget.stageP2PathCOver_qpan_cli_placed_of_seams`. -/
theorem stageP2PathCOver_qpan_cli_placed_of_seams_aux [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {AcceptErrEnv : UnreachedPqxdhPrimitives → CliHooks → AcceptKeysInput → List AllocEvent → Prop}
    {selfEnvOf : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (_spkId _kpkId _opkWord : BitVec 32) (_kbk : PublicKey),
      IdentitySelfStoreBudgetEnv (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))}
    {spkEnvOf : ∀ (B : RunBudgets) (F0 : FsFiles) (_peer : AddrGhost)
      (spkId _kpkId _opkWord : BitVec 32) (_kbk : PublicKey),
      SignedPreKeyStoreBudgetEnv (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))}
    {kpkEnvOf : ∀ (B : RunBudgets) (F0 : FsFiles) (_peer : AddrGhost)
      (spkId kpkId _opkWord : BitVec 32) (kbk : PublicKey),
      KyberPreKeyStoreBudgetEnv (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))}
    {pkEnvOf : ∀ (B : RunBudgets) (F0 : FsFiles) (_peer : AddrGhost)
      (_spkId _kpkId opkWord : BitVec 32) (_kbk : PublicKey),
      PreKeyStoreBudgetEnv (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ X W B g r evs,
      P2OverPathCErrEnvAux X W B (InitializeBobV1Env W.C.F) (AcceptErrEnv X W)
        (selfEnvOf B) (spkEnvOf B) (kpkEnvOf B) (pkEnvOf B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X W B g r evs,
      P2OverPathCOkEnvAux X W B (InitializeBobV1Env W.C.F)
        (selfEnvOf B) (spkEnvOf B) (kpkEnvOf B) (pkEnvOf B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X W B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvAux X W B (InitializeBobV1Env W.C.F) (AcceptErrEnv X W)
            (selfEnvOf B) (spkEnvOf B) (kpkEnvOf B) (pkEnvOf B))
          (P2OverPathCOkEnvAux X W B (InitializeBobV1Env W.C.F)
            (selfEnvOf B) (spkEnvOf B) (kpkEnvOf B) (pkEnvOf B))
          g r))
    (_hDropNz : lsmpl.base 547 ≠ 0#64)
    (hSpqr : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      SpqrV1PlacedSeams M A lim mmpl gh W)
    (h_accept_ok : ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement)
      (gh : CliGhostHooks) (W : CliHooks),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim AcceptSuccessEnv))
    (h_accept_err : ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement)
      (gh : CliGhostHooks) (W : CliHooks),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim (AcceptErrEnv X W)))
    (h_accept_err_owned : ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement)
      (gh : CliGhostHooks) (W : CliHooks),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptErrOwnedPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim (AcceptErrEnv X W)))
    (hSelfKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (selfEnvOf B F0 peer spkId kpkId opkWord kbk)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (spkEnvOf B F0 peer spkId kpkId opkWord kbk)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kpkEnvOf B F0 peer spkId kpkId opkWord kbk)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (pkEnvOf B F0 peer spkId kpkId opkWord kbk)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets) (S : RunSem)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ) (g1 : StoresGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop)
    (hPromMiss : PromoteMatchingMissGenPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPromOver : PromoteOverGenPlacedWithEnvProp M A lim PromoteOverEnv (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hfits : FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r))
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hdec0 : DecPkOk₀ ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hScope : ∀ r', Scope r' → scopeIn r')
    (hFok : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hcur : r.currentSession = some sess)
    (hIn : scopeIn r)
    (hnotMatch : ¬ SessMatchesPm sess y.g.msg)
    (_htrust : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey =
      .ok true)
    (hg1 : g1 = StoresGhost.opened)
    (hfs1 : FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1)
    (hCode1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (htr01 : s0.trace <+: s1.trace)
    (hsp1 : s1.sp = sp)
    (hsp0 : sp + 0xcd0#64 = s0.sp)
    (hsub : dpClosSubStack B ≤ sp.toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x0868#64)
    (hrun1 : s1.status = .Running)
    (halign1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym))
    (herr : ∀ sf Pf,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf →
      sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      (∃ (err : ApiError AddrVal Unit) (evs : List AllocEvent),
        P2OverErrEnv y.g r evs ∧
        err ≠ .panic ∧
        err ≠ .store () ∧
        sf.trace = s1.trace ∧
        (∃ (m : PreKeyMessageFields) (i : SignalMessage),
          pkToE? y.g.msg = some m ∧
          SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
          y.g.msg = pmOfE m i ∧
          ((pkStoreKeys y.g.F m = none ∨
            StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .error () ∨
            StoresGhost.opened.identity.regId cliIo.rd y.g.F = .error ()) ∨
           (∃ (k : ResponderPreKeySecrets) (kp : IdentityKeyPair),
             pkStoreKeys y.g.F m = some k ∧
             StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp ∧
             ∀ reg : BitVec 32,
               SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
                 (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none))) ∧
        (Pf ⊢
          dpFutDoneAt y.fut ∗
          memRegion sp 3280 ∗
          decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp (dpClosSubStack B) ∗
          anyHeap)) →
      Q sf Pf)
    (hok : ∀ (s2 : State) (evs_p2 : List AllocEvent)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (G_bob : SessionGhost)
      (prevCap' prevPtr' : BitVec 64)
      (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2OverOkEnv y.g r evs_p2 →
      prevCap' ≠ 0#64 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel G_bob
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
      LibsignalCodeRoLoaded lsmpl s2.mem →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_b) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           G_bob (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
           (encSession (clearPending sess)) 0#8 ∗
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
        Q Qpan) :
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
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
      Q Qpan := by
  open CryptoVerification.E2E (toU8) in
  open CryptoVerification.SignalSession.Cli.MainHops (cliWrOk) in
  open CryptoVerification.SignalSession.Cli.KitInst (
    cliKpk_getRel_error_iff cliPk_getRel_error_iff cliSpk_getRel_error_iff) in
  open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
    entails_sepConj_anyHeap p2Over_cliPollSpk_getEvs_placed p2Over_cliPollKpk_getEvs_placed
    p2Over_cliPollPk_getEvs_placed p2Over_cliPollPk_opkOkEvs_placed
    p2Over_cliPollPk_opkOkUpdate_placed p2Over_cliPollSelf_kpEvs_placed
    p2Over_cliPollSelf_regIdEvs_placed pkStoreKeys_eq_none_of_kpk_err
    pkStoreKeys_eq_none_of_opk_err pkStoreKeys_eq_none_of_spk_err
    pqxdhAcceptErr_entails_decResAt_anyHeap_ext) in
  subst hg1
  rcases hregs1 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, _, hx29, hvregs1⟩
  obtain ⟨m, i, _, hi, hpm, hpkToE⟩ := pathA_pm_typed hdec0
  have hfp_reg : s1.readReg64 .x29 = sp + 0xc70#64 := x29_eq_sp_add_c70 hsp0 hx29
  have hsp_align : (sp &&& 15#64 == 0#64) = true := by rw [← hsp1]; exact halign1
  have hfits0 := hFitsSplit X W B st_b y.g r hfits
  refine sepWPp_with_steps ?_
  refine sepWPp_conseq_pre
    (stageP2_entry_unpack_pathCOver_placed y r sess m i s0 sp (sp + 0xc70#64)
      rngPtr v_a8 v_b8 v_d0 hcur hpm rfl hdec0 hFok hScope) ?_
  refine SepWPp.exists_elim fun g => SepWPp.exists_elim fun recG =>
    SepWPp.exists_elim fun w => SepWPp.pure_left fun ⟨_hkit, _hgcur, hcanon, hctBuf_nz, hopkWord⟩ => ?_
  have hPromMissAt : PromoteMatchingMissAtPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W))
      y.fut g recG sess 4#8 (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk) :=
    promoteMatchingMissAt_placed_of_gen hPromMiss y.fut g recG sess 4#8
      (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk)
      (p2Over_not_sessMatchesMsg sess y.g.msg m i hpm hnotMatch) (p2Over_serBytes_len m)
  have hPromOverAt0 := promoteOverAt_placed_of_gen hPromOver y.fut g recG sess
    (encSessionMem_clearPending_lt_32 hIn hcur hcanon)
  have hPromOverAt : PromoteOverAtPlacedWithEnvProp M A lim
      (fun _ s => PromoteOverCanonSessEnvLocal s) (cliGhostExterns gh (cliExternsPlaced mmpl W)) y.fut g recG sess :=
    promoteOverAtPlacedWithEnv_of_eq (promoteOverEnv_eq_canon hcanon) hPromOverAt0
  let opkWord0 : BitVec 32 := m.opkId.getD 0#32
  have ⟨hArm3_eq, hOk14_eq⟩ := p2Sub1To4_opkWord_eq
    (spkBox := (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B)).getBoxSize)
    (spkPoll := (spkEnvOf B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
      StoresGhost.opened.signed m.spkId)
    (kpkBox := (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).getBoxSize)
    (kpkPoll := (kpkEnvOf B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
      StoresGhost.opened.kyber m.kpkId)
    (pkBox1 := (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B)).getBoxSize)
    (pkBox2 := (cliPollPkKitPlaced A.repAlloc y.g.F opkWord0 (cliKitStk B)).getBoxSize)
    (pkPoll1 := (pkEnvOf B y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey).getPollEnv
      StoresGhost.opened.oneTime)
    (pkPoll2 := (pkEnvOf B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
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
  exact stageP2_over_v1_kits_ext_placed_ofEnv (M := M)
    (P := ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) (A := A) (lim := lim) (F := W.C.F)
    (BobV1Env := InitializeBobV1Env W.C.F) (AcceptErrEnv := AcceptErrEnv X W)
    (PromEnv := fun _ s => PromoteOverCanonSessEnvLocal s) (st := st_b)
    (Qp := fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Qpan sf Pf)
    (cliGhostExterns gh (cliExternsPlaced mmpl W)) (cliModelPrims_structural X W)
    (cliStageP2ClosureHooksPlaced mmpl gh W hh)
    (cliStageP2PureCalleesPlaced4K X mmpl gh W hh (hSpqr mmpl gh W)
      (h_accept_ok X mmpl gh W) (h_accept_err X mmpl gh W))
    (initializeBobSession_err_owned_4k_placed_ok_on_stageP1 (h_accept_err_owned X mmpl gh W))
    (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
    (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
    (selfEnvOf B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey)
    (cliPollSelf_vtablesPlacedOk y.g.F y.g.peer (cliKitStk B) _hDropNz)
    (hSelfKit mmpl gh W B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
    (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
    (spkEnvOf B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey)
    (cliPollSpk_vtablesPlacedOk y.g.F m.spkId (cliKitStk B) _hDropNz)
    (hSpkKit mmpl gh W B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
    (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
    (kpkEnvOf B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey)
    (cliPollKpk_vtablesPlacedOk y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) _hDropNz)
    (hKpkKit mmpl gh W B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
    (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
    (pkEnvOf B y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey)
    (cliPollPk_vtablesPlacedOk y.g.F w.opkWord (cliKitStk B) _hDropNz)
    (hPkKit mmpl gh W B y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey hh)
    (dpClosSubStack B) (stageP2OverV1CallStack4K_le_subStack_placed (A := A.repAlloc)
      y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B)
    s0 s1 (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp)
    (fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Q sf Pf)
    sp (sp + 0xc70#64) y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
    y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
    y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
    (mkPathAHdr m) ikBSk ikBPk i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
    w.opkWord m.kpkId m.regId m.spkId StoresGhost.opened.signed StoresGhost.opened.kyber
    StoresGhost.opened.oneTime StoresGhost.opened.identity y.g.me y.g.peer g recG sess
    hPromMissAt hPromOverAt
    -- Substages P2.1–P2.4
    (hfits0.mono fun evs hevs => by
      refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]
      rcases hevs with h1 | h2 | h3 | hok4
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · rw [hArm3_eq] at h3; exact Or.inr (Or.inr (Or.inl h3))
      · rw [hOk14_eq] at hok4; exact Or.inr (Or.inr (Or.inr (Or.inl (SeqEnv.inl hok4)))))
    -- `kpPollEnv` + `FreeOnlyEvs`
    (fun evs14 hevs14 => by
      dsimp only [P2OverSub1To4OkEnv] at hevs14; rw [hOk14_eq] at hevs14
      have hArm4 : FitsEnv M lim st_b (P2OverV1Arm4Env
          (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B)).getBoxSize
          ((spkEnvOf B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
            StoresGhost.opened.signed m.spkId)
          (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).getBoxSize
          ((kpkEnvOf B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
            StoresGhost.opened.kyber m.kpkId)
          (cliPollPkKitPlaced A.repAlloc y.g.F opkWord0 (cliKitStk B)).getBoxSize
          ((pkEnvOf B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
            StoresGhost.opened.oneTime)
          (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpBoxSize
          (hdrOpkIdBv? (mkPathAHdr m))
          ((selfEnvOf B y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).kpPollEnv
            StoresGhost.opened.identity)) :=
        hfits0.mono fun evs h4 => by
          refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]
          exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
      exact hArm4.seq_right hevs14)
    -- `acceptKeys = some drKey` (`BobV1Env` + `P2OverSub6EnvOf`)
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey evs14 evsKp
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccSome hevs14 hevsKp => by
      dsimp only [P2OverSub1To4OkEnv] at hevs14; rw [hOk14_eq] at hevs14
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hikBSk_ok : ikBSk = vecU8 kp.privateKey.bytes := by dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = vecU8 kp.identityKey.publicKey.bytes := by dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0 hspkRel hspkPubEq hspkPrivEq
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have hinp0 := hinp 0#32; rw [hinp0] at haccSome ⊢
      refine fitsEnv_step3 (hfits0.mono fun evs hseq => ?_)
        hevs14 hevsKp (FreeOnlyEvs.singleton 8 _)
      rcases hseq with h14 | ⟨e14, er1, heq1, h14, hr1⟩
      · refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]
        exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h14))))
      · rcases hr1 with hkp | ⟨eKp, er2, heq2, hkp, hr2⟩
        · refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]
          exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨e14, er1, heq1, h14, Or.inl hkp⟩))))
        · rcases hr2 with hfr | ⟨eFr, er3, heq3, hfr, hr3⟩
          · refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]
            exact Or.inr (Or.inr (Or.inr (Or.inl
              (Or.inr ⟨e14, er1, heq1, h14, Or.inr ⟨eKp, er2, heq2, hkp, hfr⟩⟩))))
          · rcases p2OverSub6_or hr3 with hArm6 | hOk
            · refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]; dsimp only
              rw [hk, hkpOk]; dsimp only; rw [haccSome]
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e14, er1, heq1, h14,
                Or.inr ⟨eKp, er2, heq2, hkp, Or.inr ⟨eFr, er3, heq3, hfr, hArm6⟩⟩⟩)))))
            · refine Or.inr ?_; unfold P2OverPathCOkEnvAux; rw [hpkToE, hcur]; dsimp only
              rw [hk, hkpOk]; dsimp only; rw [haccSome]
              exact Or.inr ⟨e14, er1, heq1, h14,
                Or.inr ⟨eKp, er2, heq2, hkp, Or.inr ⟨eFr, er3, heq3, hfr, hOk⟩⟩⟩)
    -- `acceptKeys = none` (`AcceptErrEnv` + `FreeOnlyEvs`)
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp evs14 evsKp
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel _haccNone hevs14 hevsKp => by
      dsimp only [P2OverSub1To4OkEnv] at hevs14; rw [hOk14_eq] at hevs14
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hikBSk_ok : ikBSk = vecU8 kp.privateKey.bytes := by dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = vecU8 kp.identityKey.publicKey.bytes := by dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0 hspkRel hspkPubEq hspkPrivEq
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      rw [hinp 0#32]
      refine fitsEnv_step3 (hfits0.mono fun evs h5 => ?_) hevs14 hevsKp (FreeOnlyEvs.singleton 8 _)
      refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]; dsimp only
      rw [hk, hkpOk]; dsimp only; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
    hctBuf_nz (sp_sub_576_ne_zero B hsub) hsub hikBSk_len hikBPk_len
    (vecU8_length m.idPub) (vecU8_length m.baseKey) (vecU8_length m.kyberCt) hCode1
    (cliPollStageP2_fsAt_stages_placed hh y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B hfs1)
    rfl (fun r' hrel _ => cliPollSpk_wf_of_preKeysWf_placed hdec0.preKeysWf r' hrel)
    rfl (fun r' hrel _ => cliPollKpk_wf_of_preKeysWf_placed hdec0.preKeysWf r' hrel)
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid))
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid) |>.symm)
    (fun _id r' _ hrel _ => cliPollPk_wf_of_preKeysWf_placed hdec0.preKeysWf r' hrel)
    hkp_sk hkp_pk (Or.inr (distinctSid_of_decPkOk₀ hdec0))
    hpc1 hrun1 hsp1 hsp_align htr01 hvregs1
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hfp_reg
    -- SPK lookup error
    (fun e sf Pf evs hspkErr hevs hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, List.append_nil] at htr_f
      have hspkNone : pkStoreKeys y.g.F m = none := pkStoreKeys_eq_none_of_spk_err
        ((cliSpk_getRel_error_iff (A := A.repAlloc) (b := 0#64) cliIo.rd y.g.F cliWrOk m.spkId
          (cliKitStk B).spkGetShim (cliKitStk B).spkGetPoll
          StoresGhost.opened.signed m.spkId).mp ⟨e, hspkErr⟩)
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv X W B y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; exact Or.inl hevs)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F m.spkId (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inl hspkNone)⟩, hpost⟩)
    -- KPK lookup error
    (fun _spkRec e sf Pf evs _ _ hkpkErr hevs hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          List.append_nil, List.append_nil] at htr_f
      have hkpkNone : pkStoreKeys y.g.F m = none := pkStoreKeys_eq_none_of_kpk_err
        ((cliKpk_getRel_error_iff (A := A.repAlloc) cliIo.rd y.g.F cliWrOk m.kpkId
          StoresGhost.opened.kyber m.kpkId).mp ⟨e, hkpkErr⟩)
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv X W B y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; exact Or.inr (Or.inl hevs))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inl hkpkNone)⟩, hpost⟩)
    -- OPK lookup error
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
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv X W B y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; exact Or.inr (Or.inr (Or.inl hevs)))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F w.opkWord (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inl hpkNone)⟩, hpost⟩)
    -- Identity keypair lookup error
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
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv X W B y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; exact Or.inr (Or.inr (Or.inr (Or.inl hevs))))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (Entails.trans
          (cliPollSelf_kpErr_entails_decResAt_err_placed A.repAlloc
            y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inr (Or.inl hkpNone))⟩, hpost⟩)
    -- PQXDH acceptKeys rejection
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
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have haccNone0 : ∀ reg : BitVec 32, SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
          (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none := fun reg =>
        Option.map_eq_none_iff.mp (by
          rw [← acceptKeys_ofSignalPqxdhPrimitives, ← hinp reg]; exact haccNone)
      unfold P2OverV1Arm5EnvOfAcceptErr P2V1Arm5EnvOfAcceptErr at hevs
      rw [hOk14_eq, hinp 0#32] at hevs
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv X W B y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hevs)))))
      have hPf' := Entails.trans hPf (by rw [← sepConj_assoc]; exact Entails.refl _)
      have hpost := Entails.trans hPf' (Entails.trans
        (sepConj_mono_left (pqxdhAcceptErr_entails_decResAt_anyHeap_ext A.repAlloc
          y.out errTag w2 w3 w4 w5 w6 err0))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inr ⟨k, kp, hk, hkpOk, haccNone0⟩⟩, hpost⟩)
    -- Local registration-ID lookup error
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
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have hinp0 := hinp 0#32; rw [hinp0] at haccSome
      unfold P2OverV1Arm6EnvOfBob P2V1Arm6EnvOfBob at hevs; rw [hOk14_eq, hinp0] at hevs
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv X W B y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        rw [haccSome]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hevs)))))
      have hregNone := cliPollSelf_regIdRel_err_placed hregErr
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (Entails.trans
          (cliPollSelf_regIdErr_entails_decResAt_err_placed A.repAlloc
            y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inr (Or.inr hregNone))⟩, hpost⟩)
    -- Success case: `+0x1778` fresh Bob V1 session with archived `sess` in `previous_sessions`
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey localRegId G_bob s2 evs
        hspkRel _ hspkPub_len hspkPriv_len hspkPubEq hspkPrivEq
        hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccSome hregRel hevs
        hG_pend hG_kyb hG_alice hG_regs
        hSteps12 _ hpc2 hrun2 hsp2 htr2
        _ _ _ _ hx19_2 _ _ _ _ _ _ hx27_2 _ hx29_2 hvregs2 hCode2 => by
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
        hspkPrivEq hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have hinp0 := hinp 0#32
      have haccSome0 : acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
          (ofSignalPqxdhAcceptKeysInput (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)) =
          some drKey := by rw [← hinp0]; exact haccSome
      unfold P2OverV1OkEnvOfBobAndProm P2OverSub1To4OkEnv at hevs
      rw [hOk14_eq, hinp0] at hevs
      have hevs' : P2OverOkEnv y.g r evs := hOkEnv X W B y.g r evs (by
        unfold P2OverPathCOkEnvAux; rw [hpkToE, hcur]; dsimp only; rw [hk, hkpOk]; dsimp only
        rw [haccSome0]; exact hevs)
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
      have hmsg_reasm : signalMessageAt A.repAlloc y.g.msgG.msg y.g.msgA y.g.msg.message ∗
          ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ⊢
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg := by
        rw [preKeyMsgAt_eq_base_idKey_sep]; exact Entails.of_eq (by ac_rfl)
      have halign2 : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
      have hx29_sp0 : s2.readReg64 .x29 = s0.sp - 0x60#64 := x29_eq_sp0_sub_60 hsp0 hx29_2
      rw [hst_eq, hopkUpd]
      refine sepWPp_drop_steps hSteps12 (sepWPp_conseq_pre
        (p2OverOkPost_fold_pathCOver_placed (st_b := M.stepEvents evs st_b)
          y m i w s0 s2 sp (sp + 0xc70#64) rngPtr
          recG G_bob sess (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m dk0)
          hcanon hpm hcoins hsub rfl hopkWord hsp2 hx19_2 hx27_2) ?_)
      refine SepWPp.exists_elim fun prevCap' => SepWPp.exists_elim fun prevPtr' =>
        SepWPp.pure_left fun hcap_ne => ?_
      exact hok s2 evs m i k kp localRegId dk0 G_bob prevCap' prevPtr' y.g.msgA y.g.msgG.msg
        (preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
        hevs' hcap_ne hpm hi hk hkpOk hregOk haccModel hextra hmsg_reasm
        hSteps12 htr2 hpc2 hrun2 hsp2 halign2 hx19_2 hx27_2 hx29_sp0 hvregs2 hCode2)

/-! ## 4. Tight `ArchiveCoreEnv` Envelope & `[LibsignalFullPlacement]` `withLsFrozen` Instantiation -/

/-- Branch-independent (`prevCap = 0#64 ∨ prevCap ≠ 0#64`) `ArchiveCoreEnv` envelope for
`promote_state` (`lsmpl.base 47`) on D2(c) empty-`previous_sessions` records. -/
def PromoteOverArchiveEnvLocal (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  ArchiveCoreEnv 0#64 G sess evs ∨ ArchiveCoreEnv 1#64 G sess evs

/-- Canonical-session specialization of `PromoteOverArchiveEnvLocal` eliminating `SessionGhost`. -/
def PromoteOverArchiveCanonSessEnvLocal (sess : Session (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  let n := (encSession (clearPending sess)).length
  SeqEnv FreeOnlyEvs
    (SeqEnv (fun e => e = rustAllocEvents n 1)
      (SeqEnv (fun e => e = rustAllocEvents 96 8) FreeOnlyEvs)) evs ∨
  SeqEnv FreeOnlyEvs
    (SeqEnv (fun e => e = rustAllocEvents n 1)
      (SeqEnv (fun e => e = []) FreeOnlyEvs)) evs

theorem promoteOverArchiveEnv_eq_canon {recG : SessionGhost} {sess : Session (List (BitVec 8))}
    (hcanon : CanonSession recG sess) :
    PromoteOverArchiveEnvLocal recG sess = PromoteOverArchiveCanonSessEnvLocal sess := by
  funext evs
  unfold PromoteOverArchiveEnvLocal ArchiveCoreEnv PromoteOverArchiveCanonSessEnvLocal
  have hn_eq :
      (encSessionMem
        (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.clearPendingGhost recG)
        (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.clearPending sess)).length =
      (encSession (clearPending sess)).length :=
    congrArg List.length (encSessionMem_clearPending_eq hcanon)
  have h10 : (1#64 : BitVec 64) ≠ 0#64 := by decide
  rw [hn_eq]
  simp only [↓reduceIte, h10]

theorem promoteOverEnv_eq_canon_pub {recG : SessionGhost} {sess : Session (List (BitVec 8))}
    (hcanon : CanonSession recG sess) :
    PromoteOverEnv recG sess = PromoteOverCanonSessEnvLocal sess :=
  promoteOverEnv_eq_canon hcanon

/-- `PromSessEnv`-parametric generalization of `P2OverPathCOkEnvAux`. -/
def P2OverPathCOkEnvAuxOf [LibsignalPlacement] {A : RustAlloc}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (PromSessEnv : Session (List (BitVec 8)) → List AllocEvent → Prop)
    (selfEnvOf : ∀ (F0 : FsFiles) (peer : AddrGhost), BitVec 32 → BitVec 32 → BitVec 32 →
      PublicKey → IdentitySelfStoreBudgetEnv (cliPollSelfKitPlaced A F0 peer (cliKitStk B)))
    (spkEnvOf : ∀ (F0 : FsFiles), AddrGhost → ∀ (spkId : BitVec 32), BitVec 32 → BitVec 32 →
      PublicKey → SignedPreKeyStoreBudgetEnv (cliPollSpkKitPlaced A F0 spkId (cliKitStk B)))
    (kpkEnvOf : ∀ (F0 : FsFiles), AddrGhost → ∀ (spkId kpkId : BitVec 32), BitVec 32 →
      ∀ (kbk : PublicKey),
      KyberPreKeyStoreBudgetEnv (cliPollKpkKitPlaced A F0 kpkId spkId kbk (cliKitStk B)))
    (pkEnvOf : ∀ (F0 : FsFiles), AddrGhost → BitVec 32 → BitVec 32 → ∀ (opkWord : BitVec 32),
      PublicKey → PreKeyStoreBudgetEnv (cliPollPkKitPlaced A F0 opkWord (cliKitStk B)))
    (g : DecPkGhost) (r : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  match pkToE? g.msg, r.currentSession with
  | some m, some sess =>
      match pkStoreKeys g.F m, StoresGhost.opened.identity.keyPair cliIo.rd g.F with
      | some k, .ok kp =>
          let inp := ofSignalPqxdhAcceptKeysInput
            (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)
          match acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) inp with
          | none => False
          | some drKey =>
              let opkWord := m.opkId.getD 0#32
              let spkBox := (cliPollSpkKitPlaced A g.F m.spkId (cliKitStk B)).getBoxSize
              let spkPoll := (spkEnvOf g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey).getPollEnv
                StoresGhost.opened.signed m.spkId
              let kpkBox := (cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey (cliKitStk B)).getBoxSize
              let kpkPoll := (kpkEnvOf g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey).getPollEnv
                StoresGhost.opened.kyber m.kpkId
              let pkBox := (cliPollPkKitPlaced A g.F opkWord (cliKitStk B)).getBoxSize
              let pkPoll := (pkEnvOf g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey).getPollEnv
                StoresGhost.opened.oneTime
              let kpBox := (cliPollSelfKitPlaced A g.F g.peer (cliKitStk B)).kpBoxSize
              let kpPoll := (selfEnvOf g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey).kpPollEnv
                StoresGhost.opened.identity
              let regBox := (cliPollSelfKitPlaced A g.F g.peer (cliKitStk B)).regIdBoxSize
              let regPoll := (selfEnvOf g.F g.peer m.spkId m.kpkId opkWord g.msg.baseKey).regIdPollEnv
                StoresGhost.opened.identity
              let opkId? := hdrOpkIdBv? (mkPathAHdr m)
              let promTail := SeqEnv (fun e => e = rustDeallocEvents regBox 8)
                (SeqEnv (PromSessEnv sess)
                  (fun e => e = rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1))
              P2OverV1OkEnvOfBobAndProm spkBox spkPoll kpkBox kpkPoll pkBox pkPoll kpBox opkId?
                kpPoll (BobV1Env inp drKey) regBox regPoll promTail evs
      | _, _ => False
  | _, _ => False

/-- Pointwise per-`(X, mmpl, gh, W, B)` Stage P2 Path C (`Over`) CPS contract statement at
`dpPollEntryPlaced + 0x0868#64` under `RustCliAllocBudget M` and memory invariant `Φ`. -/
def StageP2PathCOverQpanCliMemInvPlacedAtStmt (Φ : Memory → Prop) [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (S : RunSem)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ)
    (g1 : StoresGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    PromoteMatchingMissGenPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    PromoteOverGenPlacedWithEnvProp M A lim PromEnv (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOk₀ ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → scopeIn r') →
    FilesOkPeer Scope y.g.F y.g.peer.val →
    r.currentSession = some sess →
    scopeIn r →
    ¬ SessMatchesPm sess y.g.msg →
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
      (∃ (err : ApiError AddrVal Unit) (evs : List AllocEvent),
        P2OverErrEnv y.g r evs ∧
        err ≠ .panic ∧
        err ≠ .store () ∧
        sf.trace = s1.trace ∧
        (∃ (m : PreKeyMessageFields) (i : SignalMessage),
          pkToE? y.g.msg = some m ∧
          SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
          y.g.msg = pmOfE m i ∧
          ((pkStoreKeys y.g.F m = none ∨
            StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .error () ∨
            StoresGhost.opened.identity.regId cliIo.rd y.g.F = .error ()) ∨
           (∃ (k : ResponderPreKeySecrets) (kp : IdentityKeyPair),
             pkStoreKeys y.g.F m = some k ∧
             StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp ∧
             ∀ reg : BitVec 32,
               SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
                 (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none))) ∧
        (Pf ⊢
          dpFutDoneAt y.fut ∗
          memRegion sp 3280 ∗
          decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp (dpClosSubStack B) ∗
          anyHeap)) →
      Q sf Pf) →
    (hok : ∀ (s2 : State) (evs_p2 : List AllocEvent)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (G_bob : SessionGhost)
      (prevCap' prevPtr' : BitVec 64)
      (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2OverOkEnv y.g r evs_p2 →
      prevCap' ≠ 0#64 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel G_bob
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
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_b) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           G_bob (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
           (encSession (clearPending sess)) 0#8 ∗
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

/-- `LibsignalFrozen`-guarded pointwise per-`(X, mmpl, gh, W, B)` Stage P2 Path C (`Over`) CPS
contract statement at `dpPollEntryPlaced + 0x0868#64`. -/
abbrev StageP2PathCOverQpanCliFrozenPlacedAtStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  StageP2PathCOverQpanCliMemInvPlacedAtStmt (LibsignalFrozen lsmpl) A lim PromEnv X mmpl gh W B
    P2OverErrEnv P2OverOkEnv

set_option maxHeartbeats 1600000 in
/-- Pointwise per-`(X, mmpl, gh, W, B)` closed `[LibsignalFullPlacement]` `withLsFrozen` CPS proof
of Path C Over Stage P2 V1 (`+0x0868 -> +0x1778` and error arms) under `RustCliAllocBudget M`,
discharging Block `79` (`Pqxdh::accept`) internally at `InitializeBobV1OptFieldsEnv` /
`AcceptOptFieldsEnv` with zero `h_accept*` seams and zero universal-`mmpl` premises. -/
theorem stageP2PathCOver_qpan_cli_full_placed_at_of_seams_aux [LibsignalFullPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {PromSessEnv : Session (List (BitVec 8)) → List AllocEvent → Prop}
    (hPromEq : ∀ {recG : SessionGhost} {sess : Session (List (BitVec 8))},
      CanonSession recG sess → PromEnv recG sess = PromSessEnv sess)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    {selfEnvOf : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (_spkId _kpkId _opkWord : BitVec 32) (_kbk : PublicKey),
      IdentitySelfStoreBudgetEnv (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))}
    {spkEnvOf : ∀ (F0 : FsFiles) (_peer : AddrGhost)
      (spkId _kpkId _opkWord : BitVec 32) (_kbk : PublicKey),
      SignedPreKeyStoreBudgetEnv (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))}
    {kpkEnvOf : ∀ (F0 : FsFiles) (_peer : AddrGhost)
      (spkId kpkId _opkWord : BitVec 32) (kbk : PublicKey),
      KyberPreKeyStoreBudgetEnv (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))}
    {pkEnvOf : ∀ (F0 : FsFiles) (_peer : AddrGhost)
      (_spkId _kpkId opkWord : BitVec 32) (_kbk : PublicKey),
      PreKeyStoreBudgetEnv (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ g r evs,
      P2OverPathCErrEnvAux X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        selfEnvOf spkEnvOf kpkEnvOf pkEnvOf g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ g r evs,
      P2OverPathCOkEnvAuxOf X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromSessEnv selfEnvOf spkEnvOf kpkEnvOf pkEnvOf g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvAux X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            selfEnvOf spkEnvOf kpkEnvOf pkEnvOf)
          (P2OverPathCOkEnvAuxOf X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromSessEnv selfEnvOf spkEnvOf kpkEnvOf pkEnvOf)
          g r))
    (_hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hSelfKit : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (selfEnvOf F0 peer spkId kpkId opkWord kbk)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (spkEnvOf F0 peer spkId kpkId opkWord kbk)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kpkEnvOf F0 peer spkId kpkId opkWord kbk)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (pkEnvOf F0 peer spkId kpkId opkWord kbk)
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PathCOverQpanCliFrozenPlacedAtStmt A lim PromEnv X mmpl gh W B
      P2OverErrEnv P2OverOkEnv := by
  open CryptoVerification.E2E (toU8) in
  open CryptoVerification.SignalSession.Cli.MainHops (cliWrOk) in
  open CryptoVerification.SignalSession.Cli.KitInst (
    cliKpk_getRel_error_iff cliPk_getRel_error_iff cliSpk_getRel_error_iff) in
  open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
    entails_sepConj_anyHeap p2Over_cliPollSpk_getEvs_placed p2Over_cliPollKpk_getEvs_placed
    p2Over_cliPollPk_getEvs_placed p2Over_cliPollPk_opkOkEvs_placed
    p2Over_cliPollPk_opkOkUpdate_placed p2Over_cliPollSelf_kpEvs_placed
    p2Over_cliPollSelf_regIdEvs_placed pkStoreKeys_eq_none_of_kpk_err
    pkStoreKeys_eq_none_of_opk_err pkStoreKeys_eq_none_of_spk_err
    pqxdhAcceptErr_entails_decResAt_anyHeap_ext) in
  unfold StageP2PathCOverQpanCliFrozenPlacedAtStmt StageP2PathCOverQpanCliMemInvPlacedAtStmt
  intro S DecPkEnv Scope y st_b g1 r sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hPromMiss hPromOver hh hfits hcoins hdec0 hScope hFok hcur hIn hnotMatch _htrust
    hg1 hfs1 hCode1 htr01 hsp1 hsp0 hsub hpc1 hrun1 halign1 hregs1 herr hok
  subst hg1
  rcases hregs1 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, _, hx29, hvregs1⟩
  obtain ⟨m, i, _, hi, hpm, hpkToE⟩ := pathA_pm_typed hdec0
  have hfp_reg : s1.readReg64 .x29 = sp + 0xc70#64 := x29_eq_sp_add_c70 hsp0 hx29
  have hsp_align : (sp &&& 15#64 == 0#64) = true := by rw [← hsp1]; exact halign1
  have hfits0 := hFitsSplit st_b y.g r hfits
  refine sepWPp_with_steps ?_
  refine sepWPp_conseq_pre
    (stageP2_entry_unpack_pathCOver_placed y r sess m i s0 sp (sp + 0xc70#64)
      rngPtr v_a8 v_b8 v_d0 hcur hpm rfl hdec0 hFok hScope) ?_
  refine SepWPp.exists_elim fun g => SepWPp.exists_elim fun recG =>
    SepWPp.exists_elim fun w => SepWPp.pure_left fun ⟨_hkit, _hgcur, hcanon, hctBuf_nz, hopkWord⟩ => ?_
  have hPromMissAt : PromoteMatchingMissAtPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W))
      y.fut g recG sess 4#8 (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk) :=
    promoteMatchingMissAt_placed_of_gen hPromMiss y.fut g recG sess 4#8
      (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk)
      (p2Over_not_sessMatchesMsg sess y.g.msg m i hpm hnotMatch) (p2Over_serBytes_len m)
  have hPromOverAt0 :=
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget.promoteOverAt_placed_of_gen_withEnv
      hPromOver y.fut g recG sess
      (encSessionMem_clearPending_lt_32 hIn hcur hcanon)
  have hPromOverAt : PromoteOverAtPlacedWithEnvProp M A lim
      (fun _ s => PromSessEnv s) (cliGhostExterns gh (cliExternsPlaced mmpl W)) y.fut g recG sess :=
    promoteOverAtPlacedWithEnv_of_eq (hPromEq hcanon) hPromOverAt0
  let opkWord0 : BitVec 32 := m.opkId.getD 0#32
  have ⟨hArm3_eq, hOk14_eq⟩ := p2Sub1To4_opkWord_eq
    (spkBox := (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B)).getBoxSize)
    (spkPoll := (spkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
      StoresGhost.opened.signed m.spkId)
    (kpkBox := (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).getBoxSize)
    (kpkPoll := (kpkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
      StoresGhost.opened.kyber m.kpkId)
    (pkBox1 := (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B)).getBoxSize)
    (pkBox2 := (cliPollPkKitPlaced A.repAlloc y.g.F opkWord0 (cliKitStk B)).getBoxSize)
    (pkPoll1 := (pkEnvOf y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey).getPollEnv
      StoresGhost.opened.oneTime)
    (pkPoll2 := (pkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
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
  have hShim :
      Arm64.HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
        lsRustNoAllocShimSym noAllocShimBudgetSpec :=
    hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim
  have hPure4K :
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.StageP2BaseCalleesPlaced4K
        A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget.StageP2BaseCalleesPlaced4K.of_hooks
      hShim
      hh.codecHooks.alloc
      hh.codecHooks.dealloc
      (hookSat_sessionMemcpyBudget_of_codec allocHookStack hh.codecHooks.memcpy)
      (isSameAccount_4k_placed_ok_on_stageP1
        ((cliGhostExterns_other gh _ (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans
          (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W)))
        (uuidTryParse_placed_vm_code_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))))
  have hMemcpyVm := hh.codecHooks.memcpy
  have hMemcpyFrame :
      Arm64.HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsMemcpySym
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpySpec := by
    rcases hMemcpyVm with ⟨f, hf, hok_m⟩
    refine ⟨f, hf, fun x R s_m hrun_m hpre_m hsp_m => ?_⟩
    rcases hok_m x R s_m hrun_m hpre_m hsp_m with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
    · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
      rcases x with ⟨dst, src, bs⟩
      dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpySpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec] at hpost ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
    · exact ⟨hkf, hsym, Or.inr hrest⟩
  have hRespContracts :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget.cliResponderPqxdhHookContractsPlaced_of_hookSat
      X mmpl gh W hG hh.codecHooks.alloc hh.codecHooks.dealloc hShim
  have hAcceptOk :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget.pqxdhAccept_opt_fields_responder_full_placed_ok_of_block
      (callerProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 75)
      (cliModelPrims_structural X W)
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliModelPrims_matchCrypto X W)
      hRespContracts hMemcpyFrame
  have hAcceptErrOwned :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget.pqxdhAccept_err_owned_responder_full_placed_ok_of_block
      (callerProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 75)
      (cliModelPrims_structural X W)
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliModelPrims_matchCrypto X W)
      hRespContracts hMemcpyFrame
  have hInitBobErrOwnedBase :=
    CryptoVerification.E2E.Pqxdh.ResponderCore.ls_subroutine_ok_withLsFrozen_of_block
      (callerProg := stageP1ProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (calleeProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 518) (j := 75)
      (LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget.initializeBobSession_err_owned_frozen_placed_ok_of_accept
        hAcceptErrOwned)
  have hInitBobErrOwned0 :
      subroutine_ok (stageP1ProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 75)
        (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
          (LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget.initializeBobSessionErrOwnedFrozenPlacedSpec
            (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))))) := by
    refine subroutine_ok_map hInitBobErrOwnedBase ?_
    intro g_e R s_e hpre
    refine ⟨g_e, R, ?_, fun _ hpost => hpost⟩
    dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hpre
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
    exact hpre.2
  have hInitBobErrOwned :=
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget.p2_errOwned_frozen_to_defs4K_placed
      hInitBobErrOwned0
  have hInitBobV1 :
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.InitializeBobV1FrozenOkPlaced4KOfEnv
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim W.C.F
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget.initializeBobSession_ok_v1_of_env_4k_frozen_placed_on_stageP1
      (cliModelPrims_structural X W)
      hShim
      hh.codecHooks.alloc
      hh.codecHooks.dealloc
      (hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)
      hAcceptOk
      hSpqr.initialStateMemInv_lsProg75
      (fun _ _ _ => Iff.rfl)
  have hStageP2 :
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget.stageP2OverV1KitsMemInvAtPlacedOfEnvProp
        (LibsignalFrozen lsmpl)
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim W.C.F
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (fun _ s => PromSessEnv s)
        (cliGhostExterns gh (cliExternsPlaced mmpl W))
        (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
        (selfEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey)
        (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
        (spkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey)
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
        (kpkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey)
        (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
        (pkEnvOf y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey)
        (dpClosSubStack B) :=
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget.stageP2_over_v1_kits_frozen_ext_defs_placed_ofEnv
      (M := M)
      (P := ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) (A := A) (lim := lim) (F := W.C.F)
      (BobV1Env := InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
      (AcceptErrEnv := AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
      (PromEnv := fun _ s => PromSessEnv s)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) (cliModelPrims_structural X W)
      (cliStageP2ClosureHooksPlaced mmpl gh W hh)
      hPure4K
      hInitBobErrOwned
      hInitBobV1
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (selfEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey)
      (cliPollSelf_vtablesPlacedOk y.g.F y.g.peer (cliKitStk B) _hDropNz)
      (hSelfKit y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
      (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
      (spkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey)
      (cliPollSpk_vtablesPlacedOk y.g.F m.spkId (cliKitStk B) _hDropNz)
      (hSpkKit y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
      (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (kpkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey)
      (cliPollKpk_vtablesPlacedOk y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) _hDropNz)
      (hKpkKit y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey hh)
      (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
      (pkEnvOf y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey)
      (cliPollPk_vtablesPlacedOk y.g.F w.opkWord (cliKitStk B) _hDropNz)
      (hPkKit y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey hh)
      (dpClosSubStack B) (stageP2OverV1CallStack4K_le_subStack_placed (A := A.repAlloc)
        y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B)
  exact hStageP2 (st := st_b)
    (Qp := fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Qpan sf Pf)
    s0 s1 (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp)
    (fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Q sf Pf)
    sp (sp + 0xc70#64) y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
    y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
    y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
    (mkPathAHdr m) ikBSk ikBPk i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
    w.opkWord m.kpkId m.regId m.spkId StoresGhost.opened.signed StoresGhost.opened.kyber
    StoresGhost.opened.oneTime StoresGhost.opened.identity y.g.me y.g.peer g recG sess
    hPromMissAt hPromOverAt
    -- Substages P2.1–P2.4
    (hfits0.mono fun evs hevs => by
      refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]
      rcases hevs with h1 | h2 | h3 | hok4
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · rw [hArm3_eq] at h3; exact Or.inr (Or.inr (Or.inl h3))
      · rw [hOk14_eq] at hok4; exact Or.inr (Or.inr (Or.inr (Or.inl (SeqEnv.inl hok4)))))
    -- `kpPollEnv` + `FreeOnlyEvs`
    (fun evs14 hevs14 => by
      dsimp only [P2OverSub1To4OkEnv] at hevs14; rw [hOk14_eq] at hevs14
      have hArm4 : FitsEnv M lim st_b (P2OverV1Arm4Env
          (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B)).getBoxSize
          ((spkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
            StoresGhost.opened.signed m.spkId)
          (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).getBoxSize
          ((kpkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
            StoresGhost.opened.kyber m.kpkId)
          (cliPollPkKitPlaced A.repAlloc y.g.F opkWord0 (cliKitStk B)).getBoxSize
          ((pkEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).getPollEnv
            StoresGhost.opened.oneTime)
          (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpBoxSize
          (hdrOpkIdBv? (mkPathAHdr m))
          ((selfEnvOf y.g.F y.g.peer m.spkId m.kpkId opkWord0 y.g.msg.baseKey).kpPollEnv
            StoresGhost.opened.identity)) :=
        hfits0.mono fun evs h4 => by
          refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]
          exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
      exact hArm4.seq_right hevs14)
    -- `acceptKeys = some drKey` (`BobV1Env` + `P2OverSub6EnvOf`)
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey evs14 evsKp
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccSome hevs14 hevsKp => by
      dsimp only [P2OverSub1To4OkEnv] at hevs14; rw [hOk14_eq] at hevs14
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hikBSk_ok : ikBSk = vecU8 kp.privateKey.bytes := by dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = vecU8 kp.identityKey.publicKey.bytes := by dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0 hspkRel hspkPubEq hspkPrivEq
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have hinp0 := hinp 0#32; rw [hinp0] at haccSome ⊢
      refine fitsEnv_step3 (hfits0.mono fun evs hseq => ?_)
        hevs14 hevsKp (FreeOnlyEvs.singleton 8 _)
      rcases hseq with h14 | ⟨e14, er1, heq1, h14, hr1⟩
      · refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]
        exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h14))))
      · rcases hr1 with hkp | ⟨eKp, er2, heq2, hkp, hr2⟩
        · refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]
          exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨e14, er1, heq1, h14, Or.inl hkp⟩))))
        · rcases hr2 with hfr | ⟨eFr, er3, heq3, hfr, hr3⟩
          · refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]
            exact Or.inr (Or.inr (Or.inr (Or.inl
              (Or.inr ⟨e14, er1, heq1, h14, Or.inr ⟨eKp, er2, heq2, hkp, hfr⟩⟩))))
          · rcases p2OverSub6_or hr3 with hArm6 | hOk
            · refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]; dsimp only
              rw [hk, hkpOk]; dsimp only; rw [haccSome]
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e14, er1, heq1, h14,
                Or.inr ⟨eKp, er2, heq2, hkp, Or.inr ⟨eFr, er3, heq3, hfr, hArm6⟩⟩⟩)))))
            · refine Or.inr ?_; unfold P2OverPathCOkEnvAuxOf; rw [hpkToE, hcur]; dsimp only
              rw [hk, hkpOk]; dsimp only; rw [haccSome]
              exact Or.inr ⟨e14, er1, heq1, h14,
                Or.inr ⟨eKp, er2, heq2, hkp, Or.inr ⟨eFr, er3, heq3, hfr, hOk⟩⟩⟩)
    -- `acceptKeys = none` (`AcceptErrEnv` + `FreeOnlyEvs`)
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp evs14 evsKp
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel _haccNone hevs14 hevsKp => by
      dsimp only [P2OverSub1To4OkEnv] at hevs14; rw [hOk14_eq] at hevs14
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hikBSk_ok : ikBSk = vecU8 kp.privateKey.bytes := by dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = vecU8 kp.identityKey.publicKey.bytes := by dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0 hspkRel hspkPubEq hspkPrivEq
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      rw [hinp 0#32]
      refine fitsEnv_step3 (hfits0.mono fun evs h5 => ?_) hevs14 hevsKp (FreeOnlyEvs.singleton 8 _)
      refine Or.inl ?_; unfold P2OverPathCErrEnvAux; rw [hpkToE]; dsimp only
      rw [hk, hkpOk]; dsimp only; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
    hctBuf_nz (sp_sub_576_ne_zero B hsub) hsub hikBSk_len hikBPk_len
    (vecU8_length m.idPub) (vecU8_length m.baseKey) (vecU8_length m.kyberCt) hCode1
    (cliPollStageP2_fsAt_stages_placed hh y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B hfs1)
    rfl (fun r' hrel _ => cliPollSpk_wf_of_preKeysWf_placed hdec0.preKeysWf r' hrel)
    rfl (fun r' hrel _ => cliPollKpk_wf_of_preKeysWf_placed hdec0.preKeysWf r' hrel)
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid))
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid) |>.symm)
    (fun _id r' _ hrel _ => cliPollPk_wf_of_preKeysWf_placed hdec0.preKeysWf r' hrel)
    hkp_sk hkp_pk (Or.inr (distinctSid_of_decPkOk₀ hdec0))
    hpc1 hrun1 hsp1 hsp_align htr01 hvregs1
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hfp_reg
    -- SPK lookup error
    (fun e sf Pf evs hspkErr hevs hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, List.append_nil] at htr_f
      have hspkNone : pkStoreKeys y.g.F m = none := pkStoreKeys_eq_none_of_spk_err
        ((cliSpk_getRel_error_iff (A := A.repAlloc) (b := 0#64) cliIo.rd y.g.F cliWrOk m.spkId
          (cliKitStk B).spkGetShim (cliKitStk B).spkGetPoll
          StoresGhost.opened.signed m.spkId).mp ⟨e, hspkErr⟩)
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; exact Or.inl hevs)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F m.spkId (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inl hspkNone)⟩, hpost⟩)
    -- KPK lookup error
    (fun _spkRec e sf Pf evs _ _ hkpkErr hevs hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          List.append_nil, List.append_nil] at htr_f
      have hkpkNone : pkStoreKeys y.g.F m = none := pkStoreKeys_eq_none_of_kpk_err
        ((cliKpk_getRel_error_iff (A := A.repAlloc) cliIo.rd y.g.F cliWrOk m.kpkId
          StoresGhost.opened.kyber m.kpkId).mp ⟨e, hkpkErr⟩)
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; exact Or.inr (Or.inl hevs))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inl hkpkNone)⟩, hpost⟩)
    -- OPK lookup error
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
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; exact Or.inr (Or.inr (Or.inl hevs)))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
          y.g.F w.opkWord (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inl hpkNone)⟩, hpost⟩)
    -- Identity keypair lookup error
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
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; exact Or.inr (Or.inr (Or.inr (Or.inl hevs))))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (Entails.trans
          (cliPollSelf_kpErr_entails_decResAt_err_placed A.repAlloc
            y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inr (Or.inl hkpNone))⟩, hpost⟩)
    -- PQXDH acceptKeys rejection
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
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have haccNone0 : ∀ reg : BitVec 32, SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
          (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none := fun reg =>
        Option.map_eq_none_iff.mp (by
          rw [← acceptKeys_ofSignalPqxdhPrimitives, ← hinp reg]; exact haccNone)
      unfold P2OverV1Arm5EnvOfAcceptErr P2V1Arm5EnvOfAcceptErr at hevs
      rw [hOk14_eq, hinp 0#32] at hevs
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hevs)))))
      have hPf' := Entails.trans hPf (by rw [← sepConj_assoc]; exact Entails.refl _)
      have hpost := Entails.trans hPf' (Entails.trans
        (sepConj_mono_left (pqxdhAcceptErr_entails_decResAt_anyHeap_ext A.repAlloc
          y.out errTag w2 w3 w4 w5 w6 err0))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inr ⟨k, kp, hk, hkpOk, haccNone0⟩⟩, hpost⟩)
    -- Local registration-ID lookup error
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
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have hinp0 := hinp 0#32; rw [hinp0] at haccSome
      unfold P2OverV1Arm6EnvOfBob P2V1Arm6EnvOfBob at hevs; rw [hOk14_eq, hinp0] at hevs
      have hevs' : P2OverErrEnv y.g r evs := hErrEnv y.g r evs (by
        unfold P2OverPathCErrEnvAux; rw [hpkToE]; dsimp only; rw [hk, hkpOk]; dsimp only
        rw [haccSome]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hevs)))))
      have hregNone := cliPollSelf_regIdRel_err_placed hregErr
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (Entails.trans
          (cliPollSelf_regIdErr_entails_decResAt_err_placed A.repAlloc
            y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)))
        (p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, evs, hevs', herr0_p, herr0_s, htr_f,
          ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inr (Or.inr hregNone))⟩, hpost⟩)
    -- Success case: `+0x1778` fresh Bob V1 session with archived `sess` in `previous_sessions`
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
        hspkPrivEq hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have hinp0 := hinp 0#32
      have haccSome0 : acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
          (ofSignalPqxdhAcceptKeysInput (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)) =
          some drKey := by rw [← hinp0]; exact haccSome
      unfold P2OverV1OkEnvOfBobAndProm P2OverSub1To4OkEnv at hevs
      rw [hOk14_eq, hinp0] at hevs
      have hevs' : P2OverOkEnv y.g r evs := hOkEnv y.g r evs (by
        unfold P2OverPathCOkEnvAuxOf; rw [hpkToE, hcur]; dsimp only; rw [hk, hkpOk]; dsimp only
        rw [haccSome0]; exact hevs)
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
      have hmsg_reasm : signalMessageAt A.repAlloc y.g.msgG.msg y.g.msgA y.g.msg.message ∗
          ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ⊢
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg := by
        rw [preKeyMsgAt_eq_base_idKey_sep]; exact Entails.of_eq (by ac_rfl)
      have halign2 : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
      have hx29_sp0 : s2.readReg64 .x29 = s0.sp - 0x60#64 := x29_eq_sp0_sub_60 hsp0 hx29_2
      rw [hst_eq, hopkUpd]
      refine sepWPp_drop_steps hSteps12 (sepWPp_conseq_pre
        (p2OverOkPost_fold_pathCOver_placed (st_b := M.stepEvents evs st_b)
          y m i w s0 s2 sp (sp + 0xc70#64) rngPtr
          recG G_bob sess (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m dk0)
          hcanon hpm hcoins hsub rfl hopkWord hsp2 hx19_2 hx27_2) ?_)
      refine SepWPp.exists_elim fun prevCap' => SepWPp.exists_elim fun prevPtr' =>
        SepWPp.pure_left fun hcap_ne => ?_
      exact hok s2 evs m i k kp localRegId dk0 G_bob prevCap' prevPtr' y.g.msgA y.g.msgG.msg
        (preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
        hevs' hcap_ne hpm hi hk hkpOk hregOk haccModel hextra hmsg_reasm
        hSteps12 htr2 hpc2 hrun2 hsp2 halign2 hx19_2 hx27_2 hx29_sp0 hvregs2
        (CryptoVerification.libsignalFrozen_of_keepsFrozen hCode1 hSteps12.keepsFrozen))

/-- Closed `[LibsignalFullPlacement]` `withLsFrozen` CPS proof of Path C Over Stage P2 V1
(`+0x0868 -> +0x1778` and error arms) under `RustCliAllocBudget M`, discharging Block `79`
(`Pqxdh::accept`) internally at `InitializeBobV1OptFieldsEnv` / `AcceptOptFieldsEnv` with zero
`h_accept*` seams and parameterized over `(PromEnv, PromSessEnv, hPromEq)`. -/
theorem stageP2PathCOver_qpan_cli_full_placed_of_seams_aux [LibsignalFullPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {PromSessEnv : Session (List (BitVec 8)) → List AllocEvent → Prop}
    (hPromEq : ∀ {recG : SessionGhost} {sess : Session (List (BitVec 8))},
      CanonSession recG sess → PromEnv recG sess = PromSessEnv sess)
    {selfEnvOf : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (_spkId _kpkId _opkWord : BitVec 32) (_kbk : PublicKey),
      IdentitySelfStoreBudgetEnv (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))}
    {spkEnvOf : ∀ (B : RunBudgets) (F0 : FsFiles) (_peer : AddrGhost)
      (spkId _kpkId _opkWord : BitVec 32) (_kbk : PublicKey),
      SignedPreKeyStoreBudgetEnv (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))}
    {kpkEnvOf : ∀ (B : RunBudgets) (F0 : FsFiles) (_peer : AddrGhost)
      (spkId kpkId _opkWord : BitVec 32) (kbk : PublicKey),
      KyberPreKeyStoreBudgetEnv (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))}
    {pkEnvOf : ∀ (B : RunBudgets) (F0 : FsFiles) (_peer : AddrGhost)
      (_spkId _kpkId opkWord : BitVec 32) (_kbk : PublicKey),
      PreKeyStoreBudgetEnv (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hErrEnv : ∀ X W B g r evs,
      P2OverPathCErrEnvAux X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        (selfEnvOf B) (spkEnvOf B) (kpkEnvOf B) (pkEnvOf B) g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ X W B g r evs,
      P2OverPathCOkEnvAuxOf X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromSessEnv (selfEnvOf B) (spkEnvOf B) (kpkEnvOf B) (pkEnvOf B) g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ X W B st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvAux X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            (selfEnvOf B) (spkEnvOf B) (kpkEnvOf B) (pkEnvOf B))
          (P2OverPathCOkEnvAuxOf X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromSessEnv (selfEnvOf B) (spkEnvOf B) (kpkEnvOf B) (pkEnvOf B))
          g r))
    (_hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : ∀ (gh : CliGhostHooks), CliGhostAllocHooks M A lim gh)
    (hSpqr : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      SpqrV1PlacedSeams M A lim mmpl gh W)
    (hSelfKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (selfEnvOf B F0 peer spkId kpkId opkWord kbk)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (spkEnvOf B F0 peer spkId kpkId opkWord kbk)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kpkEnvOf B F0 peer spkId kpkId opkWord kbk)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
      (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (pkEnvOf B F0 peer spkId kpkId opkWord kbk)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets) (S : RunSem)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ) (g1 : StoresGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop)
    (hPromMiss : PromoteMatchingMissGenPlacedProp A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPromOver : PromoteOverGenPlacedWithEnvProp M A lim PromEnv (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hfits : FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r))
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hdec0 : DecPkOk₀ ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hScope : ∀ r', Scope r' → scopeIn r')
    (hFok : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hcur : r.currentSession = some sess)
    (hIn : scopeIn r)
    (hnotMatch : ¬ SessMatchesPm sess y.g.msg)
    (_htrust : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey =
      .ok true)
    (hg1 : g1 = StoresGhost.opened)
    (hfs1 : FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1)
    (hCode1 : LibsignalFrozen lsmpl s1.mem)
    (htr01 : s0.trace <+: s1.trace)
    (hsp1 : s1.sp = sp)
    (hsp0 : sp + 0xcd0#64 = s0.sp)
    (hsub : dpClosSubStack B ≤ sp.toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x0868#64)
    (hrun1 : s1.status = .Running)
    (halign1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym))
    (herr : ∀ sf Pf,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf →
      sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      (∃ (err : ApiError AddrVal Unit) (evs : List AllocEvent),
        P2OverErrEnv y.g r evs ∧
        err ≠ .panic ∧
        err ≠ .store () ∧
        sf.trace = s1.trace ∧
        (∃ (m : PreKeyMessageFields) (i : SignalMessage),
          pkToE? y.g.msg = some m ∧
          SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
          y.g.msg = pmOfE m i ∧
          ((pkStoreKeys y.g.F m = none ∨
            StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .error () ∨
            StoresGhost.opened.identity.regId cliIo.rd y.g.F = .error ()) ∨
           (∃ (k : ResponderPreKeySecrets) (kp : IdentityKeyPair),
             pkStoreKeys y.g.F m = some k ∧
             StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp ∧
             ∀ reg : BitVec 32,
               SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
                 (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none))) ∧
        (Pf ⊢
          dpFutDoneAt y.fut ∗
          memRegion sp 3280 ∗
          decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp (dpClosSubStack B) ∗
          anyHeap)) →
      Q sf Pf)
    (hok : ∀ (s2 : State) (evs_p2 : List AllocEvent)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (G_bob : SessionGhost)
      (prevCap' prevPtr' : BitVec 64)
      (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2OverOkEnv y.g r evs_p2 →
      prevCap' ≠ 0#64 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel G_bob
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
      LibsignalFrozen lsmpl s2.mem →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_b) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           G_bob (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
           (encSession (clearPending sess)) 0#8 ∗
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
        Q Qpan) :
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
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
      Q Qpan :=
  stageP2PathCOver_qpan_cli_full_placed_at_of_seams_aux A lim hPromEq X mmpl gh W B
    (hErrEnv X W B) (hOkEnv X W B) (hFitsSplit X W B) _hDropNz (hG gh) (hSpqr mmpl gh W)
    (hSelfKit mmpl gh W B) (hSpkKit mmpl gh W B) (hKpkKit mmpl gh W B) (hPkKit mmpl gh W B)
    S Scope y st_b g1 r sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hPromMiss hPromOver hh hfits hcoins hdec0 hScope hFok hcur hIn hnotMatch _htrust
    hg1 hfs1 hCode1 htr01 hsp1 hsp0 hsub hpc1 hrun1 halign1 hregs1 herr hok

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux
