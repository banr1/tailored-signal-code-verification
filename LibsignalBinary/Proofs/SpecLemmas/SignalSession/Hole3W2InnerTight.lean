/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitnessAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf
public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesFromPbGateU2Bridge
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudgetInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.V1MergeBlk325Cli
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlacedTightBudgetR
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesCountedR
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStatePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeStateClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudget
public import LibsignalBinary.Specifications.SignalSession.CliElf
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudgetSat
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecv

/-!
# Guarded-Tight Block-463 `decryptSignal` (`W2`) Slot Bridge

**Checked by Lean.**

Proves `w2t_hole3_w2_inner`, discharging the block-463 `decryptSignal` (`W2`) slot
contract at `TryDecryptCliLinkedEnvOf 109 W.C W.Q.K`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W2InnerTight

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession
  (ChainKey Crypto MessageKeyGenerator Mut RatchetState SessionState ShaCompress TripleRatchet)
open CryptoVerification
  (IsLsBlockProg LibsignalFrozen LibsignalFullPlacement LibsignalPlacement libsignalMutatedBlocks
   libsignalSessionExterns ls_blockPlacement_base ls_hook_ok_ultra_of_mem lsmpl)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt (region_ok_restrictPre_true)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (recEntryPlaced recExitPlaced)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.E2E
  (PEParams UnreachedPqxdhPrimitives aesDecHookMallocng fmtWriteHook0 formatInnerHook0
   pqxdhSpqrModel)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Record.Placed (lsProg_46 lsProg_52)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (lsStringCloneSym recGhostOf)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles subroutine_ok_withLsCodeRoLoaded_of_plain withEnvPre)
open CryptoVerification.LibsignalSpqrV1
  (Bytes MlKem Message PqRatchetState States V1Recv V1State VersionNegotiationPB
   pbToPqRatchetState spqrAuthApi spqrPolyApi spqrV1 spqrV1Recv)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeState spqrDecodeState)
open CryptoVerification.LibsignalTripleRatchet
  (SendCall SpqrModel TrGhost TryDecryptGhost VecArg
   region_ok sessionMemmoveSpec withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost coinsOf signalMessageAt uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced cliHookTablePlaced libsignalSessionLib
   lsFmtWriteSym lsFormatInnerSym lsReadFileSym lsReadStdinSym lsRustAllocSymCli
   lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.KitInst
  (cliGhostExterns_blackBox cliIdentityVtRoSym)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit (cliIdentityKitSpecPlaced_quiet)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit (cliSessionKitSpecPlaced_quiet)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliRunBudgets cliRunNeeds cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_589)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecSigGhost RunSem idVtPlaced mkSlot sessVtPlaced withCodeOk)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks CliGhostHooksFs cliExternsPlaced_row cliGhostExterns cliGhostExterns_other
   hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed cliDecryptSignalNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas (toDecryptGhost)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (cliDecModelRecOkAt_opened cliExternsPlaced_rngFill cliGhostExterns_sat_of_cliExternsPlaced
   encodeInjOn_deserializeScopeP_Q fmtWrite_row_placed
   formatInner_row_placed loadRec loadRec_unique lsRngFillSym
   scopeIn scopeKit scopeKit_pqrState_lt scopeKit_recordInScopeP trTrapExternsPlaced)
open CryptoVerification.SpqrV1.Alloc (growOneStack)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost V1InnerHeapPred canonicalV1InnerHeap)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open CryptoVerification.SpqrV1.Top.Recv (spqrRecvPlacedProg)
open CryptoVerification.SpqrV1.Top.StateSize (rawV1State)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open CryptoVerification.SpqrV1Sync.Codec (spqrDecodeState_encodeState)
open CryptoVerification.SpqrV1Sync.SendTotal
  (BOkTight isEkSide st_bCodec st_bRecvCt_tight st_bRecvEk_tight st_bSize_tight)
open CryptoVerification.SpqrV1Sync.TopSync (topPb)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.Fine
  (fineCostModel fineCostModelSound fineHookRustCliAllocBudget formatInnerHook0_budget_ok)
open LibsignalBinary.Heap.SpecBudget
  (FmtWriteEnv FormatInnerEnv aesDecBudgetSpec fmtWriteBudgetEnvSpec fmtWriteBudgetSpec
   formatInnerBudgetEnvSpec)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget
  (withStoresDecPlacedSpecVX)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget
  (recordDecryptPlacedSpecTPTight withStoresDecPlacedSpecVTPF)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget
  (cliDecryptSignalWithStores_frozen_placed_okVTP_distinct_fs_of_runHooks)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1TrapPlacedBudget
  (recordDecryptV1_full_placed_region_vregs_ok_PTight_cli_of_tdEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (TryDecryptCliEnvOf)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (aesDecHookMallocng_budget_ok)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
  (TryDecryptCliEnvOfPure tryDecryptCmkSeg4Env tryDecryptEnvArgsToGhost)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux
  (spqrRecvPlacedInnerSpecXTOfEnv_of_placedSpecXT)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (decBinaryIdKitPlacedBudgetFixed decBinarySessKitPlacedBudgetFixed)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec (StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv (SpqrRecvTightLinkedEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness (spqrRecvTightLinkedEnv_nil_exists)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitnessAux (spqrRecvBranchHyps_tightLinked)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired
  (StatesRecvExactTightEnv StatesRecvProtoEnv' statesRecvExactTightEnv_sub_statesRecvProtoEnv'
   states_recv_placed_ok_x_exactTight)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (ValidV1PtsAt)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_DecodeStateGuardedEnv tlb_DecodeStateTightEnvOf tlb_V1StateMergeBlk325TightOkOf
   tlb_decodeStateGuardedEnv_sub_tight_of_topStateTight)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (TopStateTight topStateTight_decode_props topStateTight_to_tightValid640)
open LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf
  (SpqrRecvC07C09aBytesEnvOf SpqrRecvC07C09aTightLinkedEnvOf TryDecryptCliLinkedEnvOf
   spqrRecvC07C09aBytesEnvOf_nonempty tryDecryptCliLinkedEnvOf_eq_pure)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (FromLoadPolledEnv FromRegionSomeEnv WithStoresDecEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdKitOkIE_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (cliSessKitOkSE_seqFree_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
  (w2IdVt_placed_ok w2SessVt_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliRunHooksBundle)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (decSigSlotSpecBasePlaced decSigSlotSpecFrozenPlaced decSigSlotSpecPlacedOf slotFramePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (InnerDecryptFrozenPlacedOk decIdKitPlaced decSessKitPlaced withStoresDecPlacedSpecVTP)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
  (CliDecryptSignalSlotEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
  (cliDecryptSignal_slot_full_placed decSigDef_eq_runProofs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks cliExternsPlaced_sessionMemsetRegion_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget
  (cliV1StateMerge_closed_cl)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
  (chainParamsMerge_decodeState_of_prost cliChainParams_294_cl cliDeallocBudget_at_block
   cliDrop_267_cl cliDrop_270_cl cliEpochDir_299_cl cliFrom_261_cl cliGrowOne_356_cl
   cliLibcMemcpyBudget_at_block cliPushMerge_257_cl cliSessionMemcpyBudget_at_block
   cliSkipBudget_263_cl cliVarint_291_cl decodeErrorPush_of_merge
   epochDirectionMerge_decodeState_of_prost)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget
  (hpo_cliLibcruxHmac_budget_hookSat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInstBudget
  (cliBytesExact_290_cro)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
  (cliExternsPlaced_mlkemDecaps_budget_sat cliExternsPlaced_mlkemEncaps2_budget_sat
   cliExternsPlaced_mlkemValidatePk_budget_sat cliExternsPlaced_sessionMemmove_allocVm_sat
   cliRecvCt2PlacedAllocExt)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesFromPbGateU2Bridge
  (gu2b_StatesFromPbGuardedEnv gu2b_cliSpqrRecv_statesFromPb_fromPbGuard_ok
   gu2b_spqrV1PlacedSeams_exactFromPb)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
  (SpqrV1PlacedSeamsOfEnv spqrRecvPlacedInnerSpecXTOfEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudgetInst
  (cliSpqrRecvPlacedContracts_exact trTrapExternsPlaced_isPanic)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
  (sessDeserialize_cli_dcan_byBytes_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
  (serializeCanonSeqFree_cli_placed)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.V1MergeBlk325Cli
  (v1StateMergeBlk325_cli_of_hExt)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget (StatesIntoPbExactEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlacedTightBudgetR
  (statesIntoPbExactEnv_tight statesIntoPbTightDom_of_bokTight)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudgetSat
  (statesRecvPlacedContracts_of_ro_leaves_sat)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesCountedR
  (e2ar_epochDirectionMerge_blk325_cl_ok_tight)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStatePlacedBudget
  (e2a_decodeState_cl_placed_ok_of_v1Merge_109)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (spqrDecodeStatePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeStateClPlacedBudget
  (mkDecodeStateCalleeContractsClPlacedX_of_blocks)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (InitInnerEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContractsOfEnv decodeStatePlacedSpecXOfEnv statesRecvPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudget
  (spqr_recv_placed_ok_blockProgram_ext_of_contracts_ofEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux (s8Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux (s9Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
  (FromS2GenEnv FromS3GenEnv FromS4GenEnv FromS5GenEnv s1InitTrGhost stdAesOpt)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux (s7Env)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (FromVEnv RecordDecryptEnv TryDecryptEnvArgs recordTryDecryptEnvArgs)

/-- Constructs `LibsignalFullPlacement` from `libsignalSessionLib.LinkedAt cliElfBytes mpl`. -/
@[instance_reducible]
def w2t_libsignalFullPlacementOf (mpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup) : LibsignalFullPlacement where
  toLibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  placeable := hLs.choose_spec.2.1

/-- Guarded-tight binary-kit `W2` (`decryptSignal`) slot envelope (`maxOps = 109`). -/
noncomputable abbrev w2t_cliDecryptSignalBinaryKitSlotEnvExact [LibsignalPlacement]
    {M : AllocCostModel} (W : CliHooks) (A : RustCliAllocBudget M)
    (B : RunBudgets := cliRunBudgets) : DecSigGhost → List AllocEvent → Prop :=
  fun x evs =>
    LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
        W.C.F W.Q.K x.F x.peer.val →
      CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B
        (LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.TryDecryptCliLinkedEnvOf
          109 W.C W.Q.K)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc B)
        x evs

/-! ## Hook Dischargers and Binary-Kit Decrypt Producers -/

/-- `trTrapExternsPlaced` agrees with `cliGhostExterns gh (cliExternsPlaced mmpl W)` outside `"libsignal_session_rng_fill"`. -/
theorem w2t_trTrap_hExt (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym =
        cliGhostExterns gh (cliExternsPlaced mmpl W) sym :=
  fun sym hne => by simp [trTrapExternsPlaced, lsRngFillSym, ProofLib.Variant.trapAt, hne]

private theorem w2t_hExt_withPanics (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym := fun sym hne => by
  rw [← withPanics_cliGhostExterns mmpl gh W]
  simp only [Rust.withPanics, hExt sym hne]

private theorem w2t_cliGhost_row_aux (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {sym : String} {f : State → State} (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (h1 : sym ≠ lsRustAllocSymCli := by decide) (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide) (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide) (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ lsReadFileSym := by decide) (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ "memset" := by decide) (h10 : sym ≠ "memcpy" := by decide) :
    cliGhostExterns g (cliExternsPlaced mmpl W) sym = some f :=
  (cliGhostExterns_other g _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).trans (cliExternsPlaced_row mmpl W hrow)

private theorem w2t_fmtWriteHook0_budget_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk fmtWriteHook0 (fmtWriteBudgetSpec M A lim) := by
  intro ⟨_, bs, st⟩ R s0 hrun hpre _
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

private theorem w2t_fmtWrite_hookSat {M : AllocCostModel}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetEnvSpec M A lim FmtWriteEnv) :=
  ⟨fmtWriteHook0, w2t_cliGhost_row_aux mmpl gh W (fmtWrite_row_placed mmpl W),
   w2t_fmtWriteHook0_budget_ok A lim⟩

private theorem w2t_formatInner_hookSat {M : AllocCostModel}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim FormatInnerEnv) :=
  ⟨formatInnerHook0, w2t_cliGhost_row_aux mmpl gh W (formatInner_row_placed mmpl W),
   formatInnerHook0_budget_ok M A lim⟩

private theorem w2t_aesDec_hookOk {mmpl : MultiPlacement}
    (hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    HookOk (aesDecHookMallocng mmpl W.C.D)
      (aesDecBudgetSpec W.C.D fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
  aesDecHookMallocng_budget_ok fineCostModelSound γ tp cliElfImage.brkStart cliBudgetLimits
    hPl_mng W.C.D

private theorem w2t_decBinarySessKitPlacedFixed_okSE [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd))) :
    SessionOnlyKitPlacedOkSE A lim
      (decSessKitPlaced A.repAlloc F0 peer B)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B F0 peer)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_seqFree_placed
    (readProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 589)
    (deserProg := lsProg_46 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (deserBlk := 46)
    (serProg := lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (serBlk := 52)
    hDropNz (fun _ hp => hp.2) hh
    (subroutine_ok_withLsCodeRoLoaded_of_plain
      (ls_hook_ok_ultra_of_mem
        (prog := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 589)
        hReadHook (by decide) (by decide) (by decide)))
    (sessDeserialize_cli_dcan_byBytes_placed_ok mmpl gh W hG (fun _ h => h))
    (serializeCanonSeqFree_cli_placed mmpl gh W hG)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem w2t_decBinaryIdKitPlacedFixed_okIE [LibsignalPlacement]
    {M : AllocCostModel}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd))) :
    IdentityStoreKitPlacedOkI A lim
      (decIdKitPlaced A.repAlloc F0 peer B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B F0 peer)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliIdKitOkIE_placed
    (readProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 589)
    (vtSym := cliIdentityVtRoSym)
    hDropNz (fun _ hp => hp.2) hh
    (subroutine_ok_withLsCodeRoLoaded_of_plain
      (ls_hook_ok_ultra_of_mem
        (prog := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 589)
        hReadHook (by decide) (by decide) (by decide)))
    (cliGhostExterns_blackBox mmpl gh W)
    (by decide) (Nat.le_refl _) (by decide) (Nat.le_refl _)

private theorem w2t_w2_inner_binaryKitFixed_frozen_placed_ok_of_region [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (_hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hrec : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) tdEnv)).withVRegs.restrictPre (fun _ => True))) :
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) := by
  intro F0 peer hPeer
  have hSess := w2t_decBinarySessKitPlacedFixed_okSE mmpl gh W A lim B F0 peer
    hDropNz hG hh hReadHook
  have hId := w2t_decBinaryIdKitPlacedFixed_okIE mmpl gh W A lim B F0 peer
    hDropNz hh hReadHook
  have hq : (decSessKitPlaced A.repAlloc F0 peer B).Quiet ∧
      (decIdKitPlaced A.repAlloc F0 peer B).Quiet :=
    ⟨cliSessionKitSpecPlaced_quiet, cliIdentityKitSpecPlaced_quiet⟩
  have hraw :=
    cliDecryptSignalWithStores_frozen_placed_okVTP_distinct_fs_of_runHooks
      mmpl gh W
      (A := A) (lim := lim) (ctl := 0#64) (S := pqxdhSpqrModel ⟨W.C, W.Q⟩) (tdEnv := tdEnv)
      (kit := decSessKitPlaced A.repAlloc F0 peer B)
      (kitEnv := decBinarySessKitPlacedBudgetFixed A.repAlloc B F0 peer)
      (ikit := decIdKitPlaced A.repAlloc F0 peer B)
      (ikitEnv := decBinaryIdKitPlacedBudgetFixed A.repAlloc B F0 peer)
      (st0 := StoresGhost.opened.sessions) (ist0 := StoresGhost.opened.identity)
      (Scope := scopeKit) (Q := fun _ => True)
      hh hSess hId hq
      (fun _ hr => scopeKit_recordInScopeP hr)
      (fun x rec pt rec' haddr hsc hdec =>
        cliDecModelRecOkAt_opened
          (A := A.repAlloc) (b := 0#64) (pathOk := cliWrOk)
          (Scope₀ := scopeIn) (F0 := F0) (peer := peer)
          (s1 := 0) (s2 := 0) (s3 := 0) (s4 := 0)
          (C := W.C) (K := W.Q.K) (parse := uuidTryParse)
          (fun _ h => h) hPeer x rec rec' pt haddr hsc hdec)
      hrec
      (fun _ _ ses hsc hcur => ⟨scopeKit_pqrState_lt hsc.1 ses hcur, trivial⟩)
  refine Arm64.subroutine_ok_mono hraw ?_ ?_
  · intro xs R s0 hpre
    dsimp only [withEnvPre,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP,
      withStoresDecPlacedSpecVTPF, Arm64.Spec.restrictPre] at hpre ⊢
    generalize (withStoresDecPlacedSpecVX W.C A lim 0#64 uuidTryParse
      (pqxdhSpqrModel ⟨W.C, W.Q⟩) tdEnv encodeRecord
      (decSessKitPlaced A.repAlloc F0 peer B)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B F0 peer)
      (decIdKitPlaced A.repAlloc F0 peer B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B F0 peer)
      StoresGhost.opened.sessions StoresGhost.opened.identity
      scopeKit (fun _ _ => False)).pre xs s0 = Bpre at hpre ⊢
    generalize tokenInitPlacedAt = T at hpre ⊢
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · intro xs R s0 sf hpost
    dsimp only [withEnvPre,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP,
      withStoresDecPlacedSpecVTPF, Arm64.Spec.restrictPre] at hpost ⊢
    exact hpost

private theorem w2t_w2_inner_binaryKitFixed_full_placed_ok_ofEnv [LibsignalFullPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv a evs) :
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) :=
  w2t_w2_inner_binaryKitFixed_frozen_placed_ok_of_region mmpl gh W A lim
    hDropNz hG hFs hh hReadHook
    (region_ok_restrictPre_true
      (recordDecryptV1_full_placed_region_vregs_ok_PTight_cli_of_tdEnv
        mmpl gh W 0#64 hG hAesDec hSpqr
        (w2t_fmtWrite_hookSat mmpl gh W A lim)
        (w2t_formatInner_hookSat mmpl gh W A lim)
        hRecv_ne ⟨[], rfl⟩ ⟨[], rfl⟩ htd))

/-! ## Guard Upgrade (`TopStateTight` to `PeerSpqrStateTight640`) -/

private theorem w2t_not_fitsEnv_top {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    ¬ FitsEnv M lim st (fun _ => True) := fun h =>
  Nat.not_succ_le_self MallocngMaxAllocSize
    (h [AllocEvent.alloc (MallocngMaxAllocSize + 1)] trivial).1.1

private theorem w2t_seqEnv_congr {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : E₁ = E₁') (h2 : E₂ = E₂') :
    SeqEnv E₁ E₂ = SeqEnv E₁' E₂' := by
  subst h1; subst h2; rfl

private theorem w2t_or_congr {P P' Q Q' : Prop} (hp : P = P') (hq : Q = Q') :
    (P ∨ Q) = (P' ∨ Q') := by
  rw [hp, hq]

private theorem w2t_and_congr {P P' Q Q' : Prop} (hp : P = P') (hq : Q = Q') :
    (P ∧ Q) = (P' ∧ Q') := by
  rw [hp, hq]

private theorem w2t_exists_congr {α : Sort _} {P Q : α → Prop} (h : ∀ a, P a = Q a) :
    (∃ a, P a) = (∃ a, Q a) := by
  simp only [h]

/-- `TopStateTight`-guarded `spqr::recv` byte-slice envelope at `maxOps = 109`. -/
def w2t_SpqrRecvTopStateGuardedBytesEnv (F : ShaCompress) (K : MlKem)
    (stBs msgBs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  TopStateTight F K stBs → SpqrRecvC07C09aBytesEnvOf 109 F K stBs msgBs evs

/-- `TryDecryptCliEnvOfPure` instantiated at `w2t_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K`. -/
noncomputable def w2t_TryDecryptTopStateGuardedEnv (W : CliHooks) :
    TryDecryptEnvArgs → List AllocEvent → Prop :=
  TryDecryptCliEnvOfPure W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv
    (w2t_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) FormatInnerEnv

private theorem w2t_fromSessionState_ok_pqrState {PQ : Type} [Inhabited PQ]
    {s s1 : SessionState PQ} {tr0 : TripleRatchet PQ}
    (h : Mut.exec TripleRatchet.fromSessionState s = (.ok tr0, s1)) :
    tr0.pqrState = s.pqRatchetState := by
  unfold Mut.exec TripleRatchet.fromSessionState SessionState.takeRatchetState
    SessionState.takePqRatchetState at h
  rcases s with ⟨_, _, _ | rem, _, _, _, _, _, _⟩
  · cases h
  · cases h; rfl

private theorem w2t_pqRecvEnv_topStateGuarded_eq (W : CliHooks)
    (x : TryDecryptGhost) (tr : TripleRatchet (List (BitVec 8)))
    (hTop : TopStateTight W.C.F W.Q.K tr.pqrState) :
    PqRecvEnv (spqrV1 W.C.F W.Q.K) (w2t_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K)
        FormatInnerEnv x tr =
      PqRecvEnv (spqrV1 W.C.F W.Q.K) (SpqrRecvC07C09aBytesEnvOf 109 W.C.F W.Q.K)
        FormatInnerEnv x tr := by
  have hrecv :
      w2t_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K tr.pqrState x.msg.pqRatchet =
        SpqrRecvC07C09aBytesEnvOf 109 W.C.F W.Q.K tr.pqrState x.msg.pqRatchet := by
    funext evs
    exact propext ⟨fun h => h hTop, fun h _ => h⟩
  unfold PqRecvEnv
  rw [hrecv]

private theorem w2t_tryDecryptTopStateGuardedEnv_eq_linked_of_top (W : CliHooks)
    (a : TryDecryptEnvArgs)
    (hTop : TopStateTight W.C.F W.Q.K a.st.pqRatchetState) :
    w2t_TryDecryptTopStateGuardedEnv W a = TryDecryptCliLinkedEnvOf 109 W.C W.Q.K a := by
  rw [tryDecryptCliLinkedEnvOf_eq_pure 109 W.C W.Q.K]
  unfold w2t_TryDecryptTopStateGuardedEnv TryDecryptCliEnvOfPure
  cases hfrom : Mut.exec TripleRatchet.fromSessionState a.st with
  | mk res st1 =>
    cases res with
    | error _ => rfl
    | ok tr0 =>
      dsimp only
      apply congrArg (SeqEnv FreeOnlyEvs)
      let x := tryDecryptEnvArgsToGhost a
      let S := spqrV1 W.C.F W.Q.K
      let s4Env := tryDecryptCmkSeg4Env FmtWriteEnv
      have hTop0 : TopStateTight W.C.F W.Q.K tr0.pqrState :=
        (w2t_fromSessionState_ok_pqrState hfrom).symm ▸ hTop
      have hs5g : ∀ (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
          (mkg : MessageKeyGenerator),
          TopStateTight W.C.F W.Q.K tr.pqrState →
          FromS5GenEnv W.C uuidTryParse S (stdAesOpt W.C)
              (PqRecvEnv S (w2t_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 mkg =
            FromS5GenEnv W.C uuidTryParse S (stdAesOpt W.C)
              (PqRecvEnv S (SpqrRecvC07C09aBytesEnvOf 109 W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 mkg := by
        intro trG tr mkg hT
        unfold FromS5GenEnv
        rw [w2t_pqRecvEnv_topStateGuarded_eq W x tr hT]
      have hs4g : ∀ (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8))) (ck : ChainKey),
          TopStateTight W.C.F W.Q.K tr.pqrState →
          FromS4GenEnv W.C uuidTryParse S (stdAesOpt W.C) s4Env
              (PqRecvEnv S (w2t_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 ck =
            FromS4GenEnv W.C uuidTryParse S (stdAesOpt W.C) s4Env
              (PqRecvEnv S (SpqrRecvC07C09aBytesEnvOf 109 W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 ck := by
        intro trG tr ck hT
        unfold FromS4GenEnv
        cases Mut.exec
            (RatchetState.consumeMessageKey W.C.F x.msg.senderRatchetKey ck x.msg.counter x.msgType)
            tr.ratchet with
        | mk r4 r2 =>
          cases r4 with
          | error _ => rfl
          | ok mkg =>
            dsimp only
            exact congrArg (SeqEnv (s4Env x trG tr ck))
              (hs5g trG { tr with ratchet := r2 } mkg hT)
      have hs3g : ∀ (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8))),
          TopStateTight W.C.F W.Q.K tr.pqrState →
          FromS3GenEnv W.C uuidTryParse S (stdAesOpt W.C)
              (s3DefaultEnv W.C) s4Env
              (PqRecvEnv S (w2t_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 =
            FromS3GenEnv W.C uuidTryParse S (stdAesOpt W.C)
              (s3DefaultEnv W.C) s4Env
              (PqRecvEnv S (SpqrRecvC07C09aBytesEnvOf 109 W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 := by
        intro trG tr hT
        unfold FromS3GenEnv
        cases Mut.exec (RatchetState.dhRatchetStep W.C x.msg.senderRatchetKey (coinsOf x.rest))
            tr.ratchet with
        | mk r3 r1 =>
          cases r3 with
          | error _ => rfl
          | ok ck =>
            dsimp only
            exact congrArg (SeqEnv (s3DefaultEnv W.C x trG tr))
              (hs4g _ { tr with ratchet := r1 } ck hT)
      unfold FromS2GenEnv
      cases tr0.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | error _ => rfl
      | ok cko =>
        cases cko with
        | some ck =>
          dsimp only
          exact hs4g (s1InitTrGhost a.G) tr0 ck hTop0
        | none =>
          dsimp only
          exact hs3g (s1InitTrGhost a.G) tr0 hTop0

private theorem w2t_cliDecryptSignalSlotEnv_topStateGuarded_eq_linked_of_peer [LibsignalPlacement]
    {M : AllocCostModel} (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (x : DecSigGhost)
    (hPeer : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val) :
    CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (w2t_TryDecryptTopStateGuardedEnv W)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x =
      CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (TryDecryptCliLinkedEnvOf 109 W.C W.Q.K)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x := by
  let P : PEParams := ⟨W.C, W.Q⟩
  let z := toDecryptGhost x
  let kit := decSessKitPlaced A.repAlloc x.F x.peer B
  let ke := decBinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer
  let ikit := decIdKitPlaced A.repAlloc x.F x.peer B
  let ike := decBinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer
  let st0 := StoresGhost.opened.sessions
  let ist0 := StoresGhost.opened.identity
  let TdLinked := TryDecryptCliLinkedEnvOf 109 W.C W.Q.K
  have hrd : ∀ G (ses_st : SessionState (List (BitVec 8))),
      TopStateTight W.C.F W.Q.K ses_st.pqRatchetState →
      RecordDecryptEnv (w2t_TryDecryptTopStateGuardedEnv W) (recGhostOf z 0#64 G ses_st) =
        RecordDecryptEnv TdLinked (recGhostOf z 0#64 G ses_st) := by
    intro G ses_st hTop
    funext evs
    unfold RecordDecryptEnv FromVEnv
    by_cases hv : (recGhostOf z 0#64 G ses_st).st.version.toNat =
        (recGhostOf z 0#64 G ses_st).msg.messageVersion.toNat
    · simp only [hv, ↓reduceIte]
      refine w2t_exists_congr fun G₁ => ?_
      have htd := w2t_tryDecryptTopStateGuardedEnv_eq_linked_of_top W
        (recordTryDecryptEnvArgs (recGhostOf z 0#64 G ses_st) G₁) hTop
      exact w2t_and_congr rfl (congrFun (w2t_seqEnv_congr rfl (w2t_seqEnv_congr htd rfl)) evs)
    · simp only [hv, ↓reduceIte]
  have hlp :
      FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse
          (w2t_TryDecryptTopStateGuardedEnv W) kit ke st0 ikit ike ist0 scopeKit z =
        FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse
          TdLinked kit ke st0 ikit ike ist0 scopeKit z := by
    refine w2t_seqEnv_congr rfl (funext fun evs => ?_)
    refine w2t_or_congr rfl (w2t_or_congr rfl (w2t_or_congr rfl ?_))
    refine w2t_exists_congr fun rec =>
      w2t_exists_congr fun ses =>
        w2t_exists_congr fun G => propext ⟨?_, ?_⟩
    · rintro ⟨hScAt, hcur, hGV, hrs⟩
      have hTop : TopStateTight W.C.F W.Q.K ses.state.pqRatchetState := by
        obtain ⟨bs, hbs, hla⟩ := hScAt.2
        have hlr : loadRec scopeKit x.F x.peer.val = .ok (some rec) :=
          (loadRec_unique encodeInjOn_deserializeScopeP_Q (hbs ▸ hla)).symm
        have hPeer' := hPeer
        unfold PeerSpqrStateTight640 at hPeer'
        rw [hlr] at hPeer'
        exact hPeer' ses hcur
      have hrs_eq :
          FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse
              (w2t_TryDecryptTopStateGuardedEnv W) kit ke st0 ikit ike ist0 z rec G ses.state =
            FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse
              TdLinked kit ke st0 ikit ike ist0 z rec G ses.state :=
        w2t_seqEnv_congr (hrd G ses.state hTop) rfl
      exact ⟨hScAt, hcur, hGV, Eq.mp (congrFun hrs_eq evs) hrs⟩
    · rintro ⟨hScAt, hcur, hGV, hrs⟩
      have hTop : TopStateTight W.C.F W.Q.K ses.state.pqRatchetState := by
        obtain ⟨bs, hbs, hla⟩ := hScAt.2
        have hlr : loadRec scopeKit x.F x.peer.val = .ok (some rec) :=
          (loadRec_unique encodeInjOn_deserializeScopeP_Q (hbs ▸ hla)).symm
        have hPeer' := hPeer
        unfold PeerSpqrStateTight640 at hPeer'
        rw [hlr] at hPeer'
        exact hPeer' ses hcur
      have hrs_eq :
          FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse
              (w2t_TryDecryptTopStateGuardedEnv W) kit ke st0 ikit ike ist0 z rec G ses.state =
            FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse
              TdLinked kit ke st0 ikit ike ist0 z rec G ses.state :=
        w2t_seqEnv_congr (hrd G ses.state hTop) rfl
      exact ⟨hScAt, hcur, hGV, Eq.mpr (congrFun hrs_eq evs) hrs⟩
  unfold CliDecryptSignalSlotEnv WithStoresDecEnv
  exact w2t_seqEnv_congr rfl hlp

private theorem w2t_decSigSlotSpecFrozenPlaced_mono_guarded [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    (W : CliHooks) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem) (stk : Nat)
    (hok : subroutine_ok prog entry
      (decSigSlotSpecFrozenPlaced A lim
        (CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (w2t_TryDecryptTopStateGuardedEnv W)
          (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
          (decBinaryIdKitPlacedBudgetFixed A.repAlloc B))
        S stk)) :
    subroutine_ok prog entry
      (decSigSlotSpecFrozenPlaced A lim
        (w2t_cliDecryptSignalBinaryKitSlotEnvExact W A B) S stk) := by
  refine subroutine_ok_mono hok (fun (x, st) R s0 hpre => ?_) (fun (x, st) R s0 sf hpost => ?_)
  · by_cases hPeer : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val
    · have henv :
          w2t_cliDecryptSignalBinaryKitSlotEnvExact W A B x =
            CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (w2t_TryDecryptTopStateGuardedEnv W)
              (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
              (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x := by
        have h1 :
            w2t_cliDecryptSignalBinaryKitSlotEnvExact W A B x =
              CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B
                (TryDecryptCliLinkedEnvOf 109 W.C W.Q.K)
                (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
                (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x := by
          funext evs
          exact propext ⟨fun f => f hPeer, fun hp _ => hp⟩
        exact h1.trans
          (w2t_cliDecryptSignalSlotEnv_topStateGuarded_eq_linked_of_peer W A B x hPeer).symm
      dsimp only [decSigSlotSpecFrozenPlaced, decSigSlotSpecPlacedOf, withCodeOk,
        decSigSlotSpecBasePlaced] at hpre ⊢
      rwa [henv] at hpre
    · dsimp only [decSigSlotSpecFrozenPlaced, decSigSlotSpecPlacedOf, withCodeOk,
        decSigSlotSpecBasePlaced] at hpre
      let H_sp : SepProp :=
        slotFramePlaced A lim st x.toSlotCtx s0 ∗ signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ ⌜LibsignalFrozen lsmpl s0.mem⌝ ∗ R
      have hpre' : s0.mem ⊨
          ⌜s0.readReg64 .x0 = x.msgA ∧ s0.readReg64 .x1 = x.peerA ∧ s0.readReg64 .x2 = x.meA ∧
            s0.readReg64 .x3 = x.stores + 0xf0#64 ∧ s0.readReg64 .x4 = sessVtPlaced ∧
            s0.readReg64 .x5 = x.stores ∧ s0.readReg64 .x6 = idVtPlaced ∧
            s0.readReg64 .x8 = x.ret ∧ s0.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
            stk ≤ s0.sp.toNat ∧ FitsEnv M lim st (w2t_cliDecryptSignalBinaryKitSlotEnvExact W A B x)⌝ ∗
          H_sp := by
        dsimp only [H_sp]
        exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
      rw [satisfies_pure_sepConj] at hpre'
      have hfit := hpre'.1.2.2.2.2.2.2.2.2.2.2.2
      have htop : FitsEnv M lim st (fun _ => True) :=
        FitsEnv.mono (fun _ _ h => False.elim (hPeer h)) hfit
      exact False.elim (w2t_not_fitsEnv_top htop)
  · dsimp only [decSigSlotSpecFrozenPlaced, decSigSlotSpecPlacedOf, withCodeOk,
      decSigSlotSpecBasePlaced] at hpost ⊢
    refine Satisfies.mono (sepConj_mono_left
      (Entails.sepExists_mono fun evs =>
        Entails.sepExists_mono fun g' =>
          Entails.sepExists_mono fun e => ?_)) hpost
    apply Entails.pure_left
    rintro ⟨hevs, htr, hout⟩
    refine Entails.pure_right ⟨?_, htr, hout⟩ (Entails.refl _)
    intro hPeer
    exact Eq.mp
      (congrFun
        (w2t_cliDecryptSignalSlotEnv_topStateGuarded_eq_linked_of_peer W A B x hPeer) evs)
      hevs

private theorem w2t_hole3_w2_inner_of_spqr
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64)
    (hSpqrGuarded : @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      mmpl ghFixed W InitEnv
      (fun st msg => w2t_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
      SendEnv) :
    letI : LibsignalFullPlacement := w2t_libsignalFullPlacementOf mpl hLs hblk hext_nodup
    (mkSlot
      (decSigSlotSpecFrozenPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (w2t_cliDecryptSignalBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463) := by
  letI : LibsignalFullPlacement := w2t_libsignalFullPlacementOf mpl hLs hblk hext_nodup
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  have hInner :
      InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ A cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliRunBudgets
        (w2t_TryDecryptTopStateGuardedEnv W)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets) :=
    w2t_w2_inner_binaryKitFixed_full_placed_ok_ofEnv mmpl ghFixed W A cliBudgetLimits
      h547 hGSpqr.toCliGhostAllocHooks hFs hHooks.runHooks hsat
      (w2t_aesDec_hookOk hPl_mng W γ tp) hSpqrGuarded
      (fun stBs msgBs =>
        let ⟨evs, hevs⟩ := spqrRecvC07C09aBytesEnvOf_nonempty 109 W.C.F W.Q.K stBs msgBs
        ⟨evs, fun _ => hevs⟩)
      (fun _ _ h => h)
  intro stk hstk hstk64
  dsimp only [mkSlot] at hstk ⊢
  have hstk' : cliDecryptSignalNeed cliRunBudgets ≤ stk := hstk
  have hSlot :
      subroutine_ok (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
        (lsmpl.base 463)
        (decSigSlotSpecFrozenPlaced A cliBudgetLimits
          (CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets
            (w2t_TryDecryptTopStateGuardedEnv W)
            (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
            (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets))
          (cliRunSemD2c_placed X W) stk) :=
    cliDecryptSignal_slot_full_placed (i := 579)
      mmpl ghFixed W A cliBudgetLimits cliRunBudgets (cliRunSemD2c_placed X W) scopeIn
      (w2t_TryDecryptTopStateGuardedEnv W)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
      hHooks.runHooks
      (w2SessVt_placed_ok A.repAlloc cliRunBudgets h547)
      (w2IdVt_placed_ok A.repAlloc cliRunBudgets h547)
      hInner
      encodeInjOn_deserializeScopeP_Q (fun _ h => h)
      (decSigDef_eq_runProofs ⟨W.C, W.Q⟩ scopeIn).symm
      (fun _ _ _ hf => ⟨hf.1, hf.2.1⟩)
      stk hstk' hstk64
  exact w2t_decSigSlotSpecFrozenPlaced_mono_guarded W A cliBudgetLimits cliRunBudgets
    (cliRunSemD2c_placed X W) stk hSlot

/-! ## Block-329 `spqr::recv` Seam and Leaf Discharges -/

private def w2t_FromPbStateGuard (F : ShaCompress) (pb : V1State) : Prop :=
  (∃ st : States spqrPolyApi (spqrAuthApi F), BOkTight st ∧ pb = st.into_pb) ∧
    rawV1State pb ≤ 46880 ∧ ValidV1PtsAt 640 pb

private def w2t_IntoPbStateGuard {F : ShaCompress} (st1 : States spqrPolyApi (spqrAuthApi F)) : Prop :=
  BOkTight st1 ∧ rawV1State st1.into_pb ≤ 46880

private def w2t_StatesRecvExactPairTightEnv {F : ShaCompress} (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (evs : List AllocEvent) : Prop :=
  ∃ outA selfA msgA, StatesRecvExactTightEnv K ⟨outA, selfA, msgA, st, msg⟩ evs

private theorem w2t_topStateTight_fromPbStateGuard {F : ShaCompress} {K : MlKem} {stBytes : Bytes}
    (hTop : TopStateTight F K stBytes)
    {pre_pb : PqRatchetState} (hdec : spqrDecodeState stBytes = .ok pre_pb)
    {pb : V1State} (hinner : pre_pb.inner = some (.v1 pb)) :
    w2t_FromPbStateGuard F pb := by
  have hprops := (topStateTight_decode_props hTop hdec).2.2.1 pb hinner
  obtain ⟨_, _, hlt31⟩ := topStateTight_to_tightValid640 hTop
  have hsize : stBytes.length < 2 ^ 64 := Nat.lt_trans hlt31 (by decide)
  obtain ⟨_, _, _, st, _, _, _, vn?, ch?, _, hw⟩ := hTop
  have hdec_eq : spqrDecodeState stBytes = .ok (pbToPqRatchetState (topPb st vn? ch?)) := by
    have hbeq : stBytes = encodeState (pbToPqRatchetState (topPb st vn? ch?)) := hw.htop.hbytes
    rw [hbeq] at hsize ⊢
    exact spqrDecodeState_encodeState (pbToPqRatchetState (topPb st vn? ch?)) hsize
  rw [hdec_eq] at hdec
  have hpre := Except.ok.inj hdec; subst hpre
  simp only [pbToPqRatchetState, topPb, Option.map, Option.some.injEq] at hinner
  cases hinner
  exact ⟨⟨st, hw.hbok, rfl⟩, hprops⟩

private theorem w2t_topStateTight_intoPbStateGuard {F : ShaCompress} {K : MlKem} {stBytes : Bytes}
    (hTop : TopStateTight F K stBytes)
    {pre_pb : PqRatchetState} (hdec : spqrDecodeState stBytes = .ok pre_pb)
    {pb : V1State} (hinner : pre_pb.inner = some (.v1 pb))
    {st0 : States spqrPolyApi (spqrAuthApi F)}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    {sckaMsg : Message spqrPolyApi} {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    (hrecv : States.recv K st0 sckaMsg = .ok v) :
    w2t_IntoPbStateGuard v.state := by
  obtain ⟨⟨st, hbok, rfl⟩, -⟩ := w2t_topStateTight_fromPbStateGuard hTop hdec hinner
  have hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st :=
    st_bCodec F st hbok.1
  rw [hcodec] at hfrom
  have hst0 := Except.ok.inj hfrom; subst hst0
  rcases v with ⟨key, st1⟩
  have hbok1 : BOkTight st1 := by
    cases hek : isEkSide st
    · exact st_bRecvCt_tight F K hek hbok hrecv
    · exact st_bRecvEk_tight F K hek hbok hrecv
  exact ⟨hbok1, st_bSize_tight F st1 hbok1⟩

private theorem w2t_seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) :
    SeqEnv E₁' E₂' evs := by
  rcases h with hpre | ⟨evs₁, evs₂, rfl, he1, he2⟩
  · exact Or.inl (h1 evs hpre)
  · exact Or.inr ⟨evs₁, evs₂, rfl, h1 evs₁ he1, h2 evs₂ he2⟩

private theorem w2t_spqrRecvTightLinkedEnv_imp_c07c09aOf109_of_topStateTight
    {F : ShaCompress} {K : MlKem}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hFromPb_sub : ∀ pb evs, w2t_FromPbStateGuard F pb → FromPbEnv pb evs → StatesFromPbTightEnv evs)
    (hIntoPb_sub : ∀ g evs, w2t_IntoPbStateGuard g.st → IntoPbEnv g evs → StatesIntoPbTightEnv evs)
    {stBytes : Bytes} (hTop : TopStateTight F K stBytes)
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xInit : InitInnerGhost} {xNew : ChainNewGhost}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    {evs : List AllocEvent}
    (h : SpqrRecvTightLinkedEnv F K
      (fun _ => tlb_DecodeStateTightEnvOf 109) FromPbEnv IntoPbEnv
      (w2t_StatesRecvExactPairTightEnv K)
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    SpqrRecvC07C09aTightLinkedEnvOf 109 F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs := by
  rcases h with ⟨hTight, hLink⟩
  refine ⟨?_, hLink⟩
  rcases hTight with hfree | hseq
  · exact Or.inl hfree
  · refine Or.inr (w2t_seqEnv_mono (fun _ hd => hd) (fun evsAfterDec hafter => ?_) hseq)
    rcases hafter with hfree1 | ⟨hdec, hbr⟩
    · exact Or.inl hfree1
    · refine Or.inr ⟨hdec, ?_⟩
      rcases hbr with hless | hgt | ⟨hinner, heq⟩
      · exact Or.inl hless
      · exact Or.inr (Or.inl hgt)
      · refine Or.inr (Or.inr ⟨hinner, ?_⟩)
        have hPbG : w2t_FromPbStateGuard F pb :=
          w2t_topStateTight_fromPbStateGuard hTop hdec hinner
        refine w2t_seqEnv_mono (fun _ hf => hf) (fun evsAfterMd hmd => ?_) heq
        rcases hmd with hfree2 | hfromSeq
        · exact Or.inl hfree2
        · refine Or.inr (w2t_seqEnv_mono (fun evsF hf => hFromPb_sub pb evsF hPbG hf)
            (fun evsAfterFrom haf => ?_) hfromSeq)
          rcases haf with hfree3 | ⟨hfrom, hrecvSeq⟩
          · exact Or.inl hfree3
          · refine Or.inr ⟨hfrom, w2t_seqEnv_mono
              (fun _ ⟨outA, selfA, msgA, hr⟩ =>
                statesRecvExactTightEnv_sub_statesRecvProtoEnv' K
                  ⟨outA, selfA, msgA, st0, sckaMsg⟩ hfrom hr)
              (fun evsAfterRecv har => ?_) hrecvSeq⟩
            rcases har with hfree4 | ⟨hrecv, hxS, hv1c⟩
            · exact Or.inl hfree4
            · refine Or.inr ⟨hrecv, hxS, ?_⟩
              have hIntoG : w2t_IntoPbStateGuard xSInto.st :=
                hxS.symm ▸ w2t_topStateTight_intoPbStateGuard hTop hdec hinner hfrom hrecv
              refine w2t_seqEnv_mono (fun _ hc => hc) (fun evs1 he1 => ?_) hv1c
              rcases he1 with hfree5 | ⟨hc1, hc2, haddSeq⟩
              · exact Or.inl hfree5
              · refine Or.inr ⟨hc1, hc2, w2t_seqEnv_mono (fun _ ha => ha) (fun evs2 he2 => ?_) haddSeq⟩
                rcases he2 with hfree6 | hrkSeq
                · exact Or.inl hfree6
                · refine Or.inr (w2t_seqEnv_mono (fun _ hrk => hrk) (fun evs3 he3 => ?_) hrkSeq)
                  rcases he3 with hfree7 | ⟨hrkOk, hintoSeq⟩
                  · exact Or.inl hfree7
                  · exact Or.inr ⟨hrkOk,
                      w2t_seqEnv_mono (fun evsI hi => hIntoPb_sub xSInto evsI hIntoG hi)
                        (fun _ ht => ht) hintoSeq⟩

private theorem w2t_spqrRecv_topStateGuarded_seam_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    (hDecPre_sub : ∀ g evs, TopStateTight W.C.F W.Q.K g.st.bytes →
      DecodePreEnv g evs → tlb_DecodeStateTightEnvOf 109 evs)
    (hDecPost_sub : ∀ g evs, TopStateTight W.C.F W.Q.K g.st.bytes →
      DecodePostEnv g evs → tlb_DecodeStateTightEnvOf 109 evs)
    (hFromPb_sub : ∀ pb evs, w2t_FromPbStateGuard W.C.F pb →
      FromPbEnv pb evs → StatesFromPbTightEnv evs)
    (hIntoPb_sub : ∀ (g : StatesIntoPbGhost W.C.F) evs, w2t_IntoPbStateGuard g.st →
      IntoPbEnv g evs → StatesIntoPbTightEnv evs)
    (hRecvC : SpqrRecvPlacedContractsOfEnv H_inner A lim W.C.F W.Q.K
      DecodePreEnv DecodePostEnv
      (InitInnerEnv W.C.F)
      FromPbEnv
      (fun g => w2t_StatesRecvExactPairTightEnv W.Q.K g.self g.msg)
      IntoPbEnv
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
          (fun st msg => w2t_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes))) := by
  refine spqrRecvPlacedInnerSpecXTOfEnv_of_placedSpecXT
    (spqr_recv_placed_ok_blockProgram_ext_of_contracts_ofEnv
      (fun (st msg : VecArg) => w2t_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
      (trTrapExternsPlaced_isPanic mmpl gh W)
      hRecvC
      (fun st _ _ _ _ _ =>
        spqrRecvTightLinkedEnv_nil_exists W.C.F W.Q.K
          (fun _ => tlb_DecodeStateTightEnvOf 109)
          (fun _ => StatesFromPbTightEnv)
          (fun _ => StatesIntoPbTightEnv)
          (StatesRecvProtoEnv' W.Q.K)
          st.bytes)
      (fun st msg s0 st_cost _ _ _ _ hfit => ?_))
  by_cases hTop : TopStateTight W.C.F W.Q.K st.bytes
  · refine spqrRecvBranchHyps_tightLinked
      (DecodeStateEnv' := fun _ => tlb_DecodeStateTightEnvOf 109)
      (StatesFromPbEnv' := FromPbEnv)
      (StatesIntoPbEnv' := IntoPbEnv)
      (StatesRecvEnv' := w2t_StatesRecvExactPairTightEnv W.Q.K)
      st msg s0 st_cost
      (fun evs hpre => hDecPre_sub ⟨st, s0.sp - 3056#64⟩ evs hTop hpre)
      (fun evs hpost => hDecPost_sub ⟨st, s0.sp - 3056#64⟩ evs hTop hpost)
      (fun _ _ h => h)
      (fun _ _ _ h => h)
      (fun _ _ h => h)
      (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto =>
        FitsEnv.mono
          (fun evs hevs _ =>
            ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto,
              w2t_spqrRecvTightLinkedEnv_imp_c07c09aOf109_of_topStateTight
                hFromPb_sub hIntoPb_sub hTop hevs⟩)
          hfit)
      (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs hevs _ =>
        ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto,
          w2t_spqrRecvTightLinkedEnv_imp_c07c09aOf109_of_topStateTight
            hFromPb_sub hIntoPb_sub hTop hevs⟩)
  · exact False.elim
      (w2t_not_fitsEnv_top (FitsEnv.mono (fun _ _ h => False.elim (hTop h)) hfit))

private theorem w2t_hookSat_withAllocVmPreserved_memmove_of_zero
    {H : String → Option (State → State)} {sym : String} (hookStack : Nat)
    (h : HookSat H sym (withAllocVmPreserved (sessionMemmoveSpec 0))) :
    HookSat H sym (withAllocVmPreserved (sessionMemmoveSpec hookStack)) := by
  refine ProofLib.HookSat.mono h fun ⟨base, buf, dst, src, len⟩ R s0 hpre =>
    ⟨(base, buf, dst, src, len), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withAllocVmPreserved, sessionMemmoveSpec, libcMemmoveSpec, stackAt] at hpre ⊢
    simp only [ProofLib.memRegion_zero, sepConj_emp]
    ac_nf at hpre ⊢
  · dsimp only [withAllocVmPreserved, sessionMemmoveSpec, stackAt] at hpost ⊢
    simp only [ProofLib.memRegion_zero, sepConj_emp] at hpost
    ac_nf at hpost ⊢

private theorem w2t_statesRecv_recv_exactTight_ok [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      spqrLibcruxHmacSym
      (LibsignalBinary.Heap.SpecBudget.libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (statesRecvPlacedSpecOfEnv M A lim W.C.F W.Q.K
          (fun g => w2t_StatesRecvExactPairTightEnv W.Q.K g.self g.msg))) := by
  let ext := trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
  have hExt := w2t_trTrap_hExt mmpl gh W
  have hExt_wp := w2t_hExt_withPanics mmpl gh W hExt
  have hMemset_wp := hookSat_of_eq (hExt_wp _ (by decide))
    (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl gh W hA.toCliGhostAllocHooks)
  haveI : HkdfPlacedHooksExactSat W.C.F (Rust.withPanics ext) :=
    HkdfPlacedHooksExactSat.of_allocHooks_ext hA.toCliGhostAllocHooks hExt_wp
  haveI : HkdfPlacedHooksExactBudgetSat W.C.F (Rust.withPanics ext) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hMemset_wp
  have hC := statesRecvPlacedContracts_of_ro_leaves_sat
    (cliRecvCt2PlacedAllocExt mmpl gh W hA hExt)
    (w2t_hookSat_withAllocVmPreserved_memmove_of_zero growOneStack
      (hookSat_of_eq (hExt_wp _ (by decide))
        (cliExternsPlaced_sessionMemmove_allocVm_sat mmpl gh W)))
    hMemset_wp
    (hookSat_of_eq (hExt_wp _ (by decide))
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (cliExternsPlaced_mlkemValidatePk_budget_sat mmpl W)))
    (hookSat_of_eq (hExt_wp _ (by decide))
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (cliExternsPlaced_mlkemEncaps2_budget_sat mmpl W)))
    (hookSat_of_eq (hExt_wp _ (by decide))
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (cliExternsPlaced_mlkemDecaps_budget_sat mmpl W)))
    (hookSat_of_eq (hExt_wp _ (by decide)) hHmac)
  have h332 := states_recv_placed_ok_x_exactTight A lim W.C.F W.Q.K ext hC
  have h0 :=
    LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget.ls_subroutine_ok_of_blockProgram_cro
      (callerProg := spqrRecvPlacedProg ext) (i := 329) h332
  exact subroutine_ok_mono h0
    (fun (g, stB) _ _ hpre => by
      dsimp only [withLsCodeRoLoaded, statesRecvPlacedSpecOfEnv,
        LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget.statesRecvPlacedSpecOfEnv]
        at hpre ⊢
      refine Satisfies.mono ?_ hpre
      refine sepConj_mono_left (sepConj_mono_left (sepConj_mono_left ?_))
      exact Entails.pure_mono fun ⟨h1, h2, h3, h4, hfit⟩ =>
        ⟨h1, h2, h3, h4, ⟨hfit.1.mono fun evs hevs => ⟨g.outA, g.selfA, g.msgA, hevs⟩, hfit.2⟩⟩)
    (fun (g, stB) _ _ _ hpost => by
      dsimp only [withLsCodeRoLoaded, statesRecvPlacedSpecOfEnv,
        LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget.statesRecvPlacedSpecOfEnv]
        at hpost ⊢
      refine Satisfies.mono ?_ hpost
      refine sepConj_mono_left (Entails.sepExists_mono fun evs => ?_)
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨h1, hevs⟩ =>
        ⟨h1, ⟨g.outA, g.selfA, g.msgA, hevs⟩⟩)
    (fun _ _ _ _ hp => hp)

private theorem w2t_decodeStateCalleeContractsClPlacedX_cliExt [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    DecodeStateCalleeContractsClPlacedX canonicalV1InnerHeap A lim ext := by
  have hExt_wp := w2t_hExt_withPanics mmpl gh W hExt
  exact mkDecodeStateCalleeContractsClPlacedX_of_blocks
    (cliDeallocBudget_at_block mmpl gh W hA hExt_wp (i := 325))
    (fun stk _ _ => cliLibcMemcpyBudget_at_block mmpl gh W hA hExt_wp stk (i := 325))
    (fun stk _ _ => cliSessionMemcpyBudget_at_block mmpl gh W hA hExt_wp stk (i := 325))
    (cliFrom_261_cl mmpl gh W hA hExt)
    (decodeErrorPush_of_merge (cliPushMerge_257_cl mmpl gh W hA hExt))
    (cliVarint_291_cl mmpl gh W hA hExt)
    (cliSkipBudget_263_cl mmpl gh W hA hExt)
    (chainParamsMerge_decodeState_of_prost (cliChainParams_294_cl mmpl gh W hA hExt))
    (cliGrowOne_356_cl mmpl gh W hA hExt)
    (cliDrop_267_cl mmpl gh W hA hExt)
    (cliDrop_270_cl mmpl gh W hA hExt)
    (cliBytesExact_290_cro mmpl gh W hA hExt)
    (epochDirectionMerge_decodeState_of_prost (cliEpochDir_299_cl mmpl gh W hA hExt))
    (cliV1StateMerge_closed_cl mmpl gh W hA hExt)

private theorem w2t_decodeState_recv_tight109_ok [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hV1Merge : tlb_V1StateMergeBlk325TightOkOf A lim 80
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecXOfEnv canonicalV1InnerHeap A lim
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) := by
  let ext := trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
  have hc := w2t_decodeStateCalleeContractsClPlacedX_cliExt mmpl gh W hA
    (w2t_trTrap_hExt mmpl gh W)
  have hEpochDir := e2ar_epochDirectionMerge_blk325_cl_ok_tight hc
  have hDec325 := e2a_decodeState_cl_placed_ok_of_v1Merge_109
    (F := W.C.F) (K := W.Q.K) hc hEpochDir hV1Merge
  have hblk325 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (spqrDecodeStatePlacedSpecOfEnv canonicalV1InnerHeap A lim
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) := by
    have h0 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (blkPl_325).base
        (withLsCodeRoLoaded lsmpl
          (spqrDecodeStatePlacedSpecOfEnv canonicalV1InnerHeap A lim
            (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
            (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) := hDec325
    rwa [IsLsBlockProg.eq_blockProgram
          (prog := (blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext)),
        ls_blockPlacement_base (i := 325)] at h0
  exact LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget.ls_subroutine_ok_of_blockProgram_cro
    (callerProg := spqrRecvPlacedProg ext) (i := 329) hblk325

/-- Block-463 `decryptSignal` (`W2`) slot witness parameterized by `V1State::merge` on `trTrapExternsPlaced`. -/
theorem w2t_hole3_w2_inner_of_v1Merge
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64)
    (hV1Merge : @tlb_V1StateMergeBlk325TightOkOf (libsignalPlacementOf mpl hblk hext_nodup)
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits 80
      (trTrapExternsPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))) :
    letI : LibsignalFullPlacement := w2t_libsignalFullPlacementOf mpl hLs hblk hext_nodup
    (mkSlot
      (decSigSlotSpecFrozenPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (w2t_cliDecryptSignalBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  have hHmac :=
    hpo_cliLibcruxHmac_budget_hookSat γ mmpl tp cliElfImage.brkStart cliBudgetLimits ghFixed W
      hPl_mng
  have hBase :=
    gu2b_spqrV1PlacedSeams_exactFromPb γ mmpl tp cliElfImage.brkStart cliBudgetLimits ghFixed W
      hPl_mng hGSpqr
  have hRecvBase := cliSpqrRecvPlacedContracts_exact mmpl ghFixed W hGSpqr hHmac
  have hDec := w2t_decodeState_recv_tight109_ok mmpl ghFixed W hGSpqr.toCliGhostAllocHooks hV1Merge
  have hFromPb := gu2b_cliSpqrRecv_statesFromPb_fromPbGuard_ok mmpl ghFixed W hGSpqr
  have hRecv := w2t_statesRecv_recv_exactTight_ok mmpl ghFixed W hGSpqr hHmac
  have hSpqrGuarded :
      SpqrV1PlacedSeamsOfEnv fineCostModel A cliBudgetLimits mmpl ghFixed W
        _ (fun st msg => w2t_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes) _ :=
    { spqrInitialState := hBase.spqrInitialState
      spqrRecv := w2t_spqrRecv_topStateGuarded_seam_of_contracts mmpl ghFixed W
        (DecodePreEnv := tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
        (DecodePostEnv := tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
        (FromPbEnv := gu2b_StatesFromPbGuardedEnv W.C.F)
        (IntoPbEnv := StatesIntoPbExactEnv)
        (fun _ _ hTop h => tlb_decodeStateGuardedEnv_sub_tight_of_topStateTight hTop h)
        (fun _ _ hTop h => tlb_decodeStateGuardedEnv_sub_tight_of_topStateTight hTop h)
        (fun _ _ hG hf => hf hG)
        (fun _ _ hG hEnv =>
          statesIntoPbExactEnv_tight (statesIntoPbTightDom_of_bokTight hG.1) hEnv)
        { dealloc_ok := hRecvBase.dealloc_ok
          memcpy_ok := hRecvBase.memcpy_ok
          dropEpochSlice_ok := hRecvBase.dropEpochSlice_ok
          dropOptProtoInnerState_ok := hRecvBase.dropOptProtoInnerState_ok
          dropOptProtoChain_ok := hRecvBase.dropOptProtoChain_ok
          dropChain_ok := hRecvBase.dropChain_ok
          dropPqRatchetState_ok := hRecvBase.dropPqRatchetState_ok
          dropStates_ok := hRecvBase.dropStates_ok
          decodeState_ok := hDec
          initInner_ok := hRecvBase.initInner_ok
          chainFrom_ok := hRecvBase.chainFrom_ok
          chainFromPb_ok := hRecvBase.chainFromPb_ok
          chainNew_ok := hRecvBase.chainNew_ok
          chainAddEpoch_ok := hRecvBase.chainAddEpoch_ok
          chainRecvKey_ok := hRecvBase.chainRecvKey_ok
          chainIntoPb_ok := hRecvBase.chainIntoPb_ok
          messageDeserialize_ok := hRecvBase.messageDeserialize_ok
          statesFromPb_ok := hFromPb
          statesRecv_ok := hRecv
          statesIntoPb_ok := hRecvBase.statesIntoPb_ok
          encodeToVec_ok := hRecvBase.encodeToVec_ok
          h_inner_eq := hRecvBase.h_inner_eq }
      spqrSendCoins := hBase.spqrSendCoins }
  exact w2t_hole3_w2_inner_of_spqr hLs hblk hext_nodup ghFixed hPl_mng X W γ tp
    hGSpqr hFs hsat hHooks h547 hSpqrGuarded

/-- Closed block-463 `decryptSignal` (`W2`) slot witness at `TryDecryptCliLinkedEnvOf 109 W.C W.Q.K`. -/
theorem w2t_hole3_w2_inner
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64) :
    letI : LibsignalFullPlacement := w2t_libsignalFullPlacementOf mpl hLs hblk hext_nodup
    (mkSlot
      (decSigSlotSpecFrozenPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (w2t_cliDecryptSignalBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  exact w2t_hole3_w2_inner_of_v1Merge hLs hblk hext_nodup ghFixed hPl_mng X W γ tp
    hGSpqr hFs hsat hHooks h547
    (@v1StateMergeBlk325_cli_of_hExt (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      _ _ _ _ (w2t_trTrap_hExt mmpl ghFixed W) hGSpqr.toCliGhostAllocHooks)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W2InnerTight
