/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
public import LibsignalBinary.Proofs.CliCBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridgeX
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget
public import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
public import LibsignalBinary.Proofs.RecordCodecs.SignedAssemblyBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsSelfPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.StageP3RawBodyPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberPreKeyKitFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeyKitFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SignedPreKeyKitFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage3Prev1PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesFromPbGateU2Bridge
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWordPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollXPlacedBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2LsRetAddrKeep
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkClosePostBob
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkR2
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWire
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudgetSat
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecv

/-!
# Spine-C Slot `520` (`decryptPrekey`, `canon'`) Closure at `h2k_ghFixedK` (`ElfSlicesPqOomH2KSlot520Canon`)

**Checked by Lean.**

Discharges `ElfSlicesPqOomH2KIfaces.h2ki_W4DecPkCanonSlot520OkK` unconditionally from
`(hLs, hMm, hBranch2)`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520Canon

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (SessionState ShaCompress SignalMessage)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (IsLsBlockProg LibsignalFullPlacement LibsignalHooks LibsignalPlacement
  libsignalMutatedBlocks libsignalSessionExterns lsBlackBoxU8Sym lsProg_51 ls_blockPlacement_base
  lsmpl withLsCl withLsCodeLoaded)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (stageP1ProgPlaced)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (OverPrevEncOK)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives aesDecHookMallocng)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Record.Placed (lsProg_52)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Bytes Message MlKem PqRatchetState States V1Recv V1State
  VersionNegotiationPB pbToPqRatchetState spqrAuthApi spqrPolyApi spqrV1Recv)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeState spqrDecodeState)
open CryptoVerification.LibsignalTripleRatchet (SendCall VecArg sessionMemmoveSpec)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost SignalMessageGhost)
open CryptoVerification.RecordCodecs.Placed (lsProg_65 lsProg_595)
open CryptoVerification.RustHeap (RustAlloc vecU8)
open CryptoVerification.SignalSession (CliHooks cliBcmpHook cliElfBytes cliElfImage cliExternsPlaced
  cliHookTablePlaced libsignalSessionLib lsDropOffPlaced_eq lsReadFileSym lsReadStdinSym
  lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
  lsRustReallocSymCli lsStringCloneSym)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule cliBcmpName cliBcmpSpec dirAt getResultAt)
open CryptoVerification.SignalSession.Cli.KitInst (cliSessionKitSpecPlaced)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit (cliIdentityKitSpecPlaced savePollNeedPlaced
  saveShimNeedPlaced trustPollNeedPlaced trustShimNeedPlaced)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit (loadPollNeedPlaced loadShimNeedPlaced
  storePollNeedXPlaced storeShimNeedPlaced)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_565 blkPl_565 blkPl_589 lsProg_553 lsProg_565
  lsProg_569 lsProg_570 lsProg_571 lsProg_573 lsProg_575 lsProg_576 lsProg_578 lsProg_589 lsProg_597)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliExternsPlaced_row cliGhostExterns
  cliGhostExterns_bcmp cliGhostExterns_other cliGhostExterns_shim hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (cliKitStk cliPollKpkKitPlaced
  cliPollPkKitPlaced cliPollSpkKitPlaced dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot RunBudgets pathNeed)
open CryptoVerification.SignalSession.Cli.Slots (blackBox_row_placed cliGhostExterns_sat_of_cliExternsPlaced
  compress256_row_placed scopeIn scopeKit trTrapExternsPlaced)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_cl_to_lscro ls_transfer_lscro)
open CryptoVerification.SpqrV1.Alloc (growOneStack)
open CryptoVerification.SpqrV1.ChainProofs (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost
  ChainRecvKeyGhost bytesAt)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost V1InnerHeapPred canonicalV1InnerHeap)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.Recv (spqrRecvPlacedProg)
open CryptoVerification.SpqrV1.Top.StateSize (rawV1State)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open CryptoVerification.SpqrV1Sync.Codec (spqrDecodeState_encodeState)
open CryptoVerification.SpqrV1Sync.SendTotal (BOkTight isEkSide st_bCodec st_bRecvCt_tight
  st_bRecvEk_tight st_bSize_tight)
open CryptoVerification.SpqrV1Sync.TopSync (topPb)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Heap.SpecBudget (aesDecBudgetSpec libcruxHmacBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd
  (kpkKitFds_toWithFds pkKitFds_toWithFds spkKitFds_toWithFds)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget
  (OverVerNe1e04CliAtFrozenPlacedBody)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
  (StageP3Prev1Env)
open LibsignalBinary.Proofs.CliCBudget (signedHooksPlaced_of_codecHooks signedPortDepsPlaced_ok)
open LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridgeX
  (dpx_deserEnv dpx_p2OverErrEnv dpx_p2OverOkEnv)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux
  (spqrRecvPlacedInnerSpecXTOfEnv_of_placedSpecXT)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk (cliEncodeRawPrealloc_placed_ok)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec (StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv (SpqrRecvTightLinkedEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness (spqrRecvTightLinkedEnv_nil_exists)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitnessAux (spqrRecvBranchHyps_tightLinked)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired (StatesRecvExactTightEnv
  StatesRecvProtoEnv' statesRecvExactTightEnv_sub_statesRecvProtoEnv' states_recv_placed_ok_x_exactTight)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (ValidV1PtsAt)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges (tlb_DecodeStateGuardedEnv
  tlb_DecodeStateTightEnvOf tlb_V1StateMergeBlk325TightOkOf
  tlb_decodeStateGuardedEnv_sub_tight_of_topStateTight)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (TopStateTight topStateTight_decode_props
  topStateTight_to_tightValid640)
open LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf (SpqrRecvC07C09aTightLinkedEnvOf)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs (VerNeTightTopRawEnv)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
  (cliDecPkCanonSlotEnvExact' cliDecPkCanonSlotEnvExact'_eq_dom0'Prev0GuardedFixed)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (EncodeRawPreallocPlacedOkX)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (IdentityStoreKitPlacedOkI
  SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget (preKeyRecord_deserialize_placed_ok_of_hooks)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (preKeyDeserializePlacedSpec preKeyDeserializeRawSpec)
open LibsignalBinary.Proofs.RecordCodecs.SignedAssemblyBudget
  (decodeKyberPreKey_placed_ok decodeSignedPreKey_placed_ok)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (decodeKyberPreKeyPlacedSpec
  decodeKyberPreKeyRawSpec decodeSignedPreKeyPlacedSpec decodeSignedPreKeyRawSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (serializeCanonSpecX)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (sessDeserEvents_mem_recordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsSelfPlacedBudgetFd
  (cliPollSelf_kitPlacedOk_of_dirGet)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.StageP3RawBodyPlacedBudget
  (cliVerNe1e04_full_placed_ok_raw)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed ReadFileRuleEnvFixed extract_withFdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (cliGhostAllocHooks_withFds cliGhostExterns_libcruxHmac_withFds_hookSat
   fineAesDec_budget_withFds_hookOk withFds withFds_pool_enforced withFds_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliDirPutStr_placed_ok cliIdKitOkIE_placed_of_polls cliIdentityKitDefaultBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberPreKeyKitFdsPlacedBudget
  (cliKpkKitPlacedOkFds_full_of_polls)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeyKitFdsPlacedBudget
  (cliPkKitPlacedOkFds_of_polls)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (SessKitHooksPlaced cliAddrText_placed_ok_of_sessHooks cliDecimal_placed_ok_of_sessHooks
   cliDirPut_placed_ok_of_sessHooks cliSessFutDrop_rocl_placed_ok cliSessLoadPoll_rocl_placed_ok
   cliSessLoadShim_rocl_placed_ok cliSessStorePoll_rocl_placed_ok cliSessStoreShim_rocl_placed_ok
   cliSessionKitDefaultBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SignedPreKeyKitFdsPlacedBudget
  (cliSpkKitPlacedOkFds_of_poll)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPlacedBudgetFd
  (CanonPollKitsPlacedOk GuardSlotIncl decPk_d2c_canon_slot520_preFd_of_kits guardIncl_of_guarded_sub)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage3Prev1PlacedBudgetFd
  (CanonSessionGhostValid DecPkD2cCanonPollGvSeqFreeEnv cliPollStageP4Prev1SeqFreeEnvsAt wideM3PathCP3Envs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
  (cliIdKitPlacedOkI_full serContractsX_of_runHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
  (cliPollKpkFullBudgetEnv cliPollPkFullBudgetEnv cliPollSpkFullBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks cliExternsPlaced_alloc_budget_sat
   cliExternsPlaced_exactMemcpy_sat cliExternsPlaced_realloc_budget_sat
   cliExternsPlaced_sessionMemsetRegion_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced decimalSpecPlaced dirGetSpecPlaced dirPutSpecPlaced dropSpeWordSpecPlaced
   idSavePollSpecPlaced pathSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget (cliV1StateMerge_closed_cl)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
  (chainParamsMerge_decodeState_of_prost cliChainParams_294_cl cliDeallocBudget_at_block
   cliDrop_267_cl cliDrop_270_cl cliEpochDir_299_cl cliFrom_261_cl cliGrowOne_356_cl
   cliLibcMemcpyBudget_at_block cliPushMerge_257_cl cliSessionMemcpyBudget_at_block
   cliSkipBudget_263_cl cliVarint_291_cl decodeErrorPush_of_merge epochDirectionMerge_decodeState_of_prost)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInstBudget (cliBytesExact_290_cro)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
  (cliExternsPlaced_mlkemDecaps_budget_sat cliExternsPlaced_mlkemEncaps2_budget_sat
   cliExternsPlaced_mlkemValidatePk_budget_sat cliExternsPlaced_sessionMemmove_allocVm_sat
   cliRecvCt2PlacedAllocExt)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesFromPbGateU2Bridge
  (gu2b_SpqrSendCoinsExactFromPbLinkedEnv gu2b_StatesFromPbGuardedEnv
   gu2b_cliSpqrRecv_statesFromPb_fromPbGuard_ok gu2b_spqrV1PlacedSeams_exactFromPb_of_hmac)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
  (SpqrV1PlacedSeamsOfEnv spqrRecvPlacedInnerSpecXTOfEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudgetInst
  (cliSpqrRecvPlacedContracts_exact trTrapExternsPlaced_isPanic)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWordPlacedBudget (dropSpeWord_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudget
  (CliIdSavePollEnv publicKeySerialize_lscro_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.SymPlacedBudget (idSavePoll_placed_ok_of_deps_core)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget
  (idTrustPoll_placed_ok_of_deps identityKey_decode_placed_ok publicKeyEq_placed_ok_of_bb)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPollPlacedBudgetFd (kpkGetPoll_placed_fs_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlacedBudgetFd (kpkMarkPoll_placed_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
  (allocContractsBudgetPlaced_cli sessDeserialize_of_sessDeserEvents_caller_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPollPlacedBudgetFd (pkGetPoll_placed_fs_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePollPlacedBudgetFd (pkRemovePoll_placed_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget (serContractsX_cli_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget (serializeCanonX_placed_ok_of_serContractsX)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPollPlacedBudgetFd (spkGetPoll_placed_fs_ok_of_deps_fd)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm (h2asm_Branch2HookReplaysK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
  (h2kb_hole2_hG h2kb_hole2_runHooksPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit
  (dirGet_placed_ok_of_h2k_fd h2k_hole2_hReadSatK_withFds)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (h2k_ghFixedK h2k_readFileSpecK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (DecPkD2cSlotOkFrozenPlacedAtPreFd h2ki_W4DecPkCanonSlot520OkK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
  (h2kb_hole2_hGSpqr_withFds h2kb_runHooksPlaced_withFds)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
  (F3CliElfGhostWitnessK mkF3CliElfGhostWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2LsRetAddrKeep
  (h2lr_lsRetAddr624_keepSub_false)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup hole2_keepSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkClosePostBob (w4s2_pollGv_sub_canonPostBob)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkFresh (w4f_not_fitsEnv_top)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkR2
  (W4r2PollCustomP3GvSeqFreeEnv W4r2SessionGhostValid w4r2_cliPollStageP4Prev1SeqFreeEnvsAt
   w4r2_wideM3PathCP3Envs)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWire
  (w4wire_hp3Fits_wideM3 w4wire_libsignalFullPlacementOf w4wire_overPrevEncOK_of_scopeIn_v4)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
  (w4s2_SpqrRecvTopStateGuardedBytesEnv w4s2_TryDecryptTopStateGuardedEnv
   w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty w4s2_trTrap_hExt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.V1MergeBlk325Cli (v1StateMergeBlk325_cli_of_hExt)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget (StatesIntoPbExactEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlacedTightBudgetR
  (statesIntoPbExactEnv_tight statesIntoPbTightDom_of_bokTight)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudgetSat (statesRecvPlacedContracts_of_ro_leaves_sat)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesCountedR
  (e2ar_epochDirectionMerge_blk325_cl_ok_tight)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStatePlacedBudget
  (e2a_decodeState_cl_placed_ok_of_v1Merge_109)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget (DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (spqrDecodeStatePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeStateClPlacedBudget (mkDecodeStateCalleeContractsClPlacedX_of_blocks)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (InitInnerEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContractsOfEnv decodeStatePlacedSpecXOfEnv statesRecvPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudget
  (spqr_recv_placed_ok_blockProgram_ext_of_contracts_ofEnv)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
  (HkdfPlacedHooksExactBudgetSat hookSatExactMemcpy_of_sym_eq)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open VerifiedLibraries (mallocngLib)

/-! ## Seam Helpers (`growOneVecU8`, `dirGet`, `CanonPollKitsPlacedOk`, `SpqrTopStateGuarded`) -/

section LocalSeamHelpers

private theorem growOneVecU8_lsProg51_withLsCl_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)) :=
  LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlacedBudget.growOneVecU8_caller_withLsCl_ok
    (callerProg := lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 51)
    ((show CryptoVerification.lsHandleErrorSym =
          CryptoVerification.SpqrV1.Alloc.spqrHandleErrorSym by decide) ▸
      ((cliGhostExterns_other gh (cliExternsPlaced mmpl W) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (CryptoVerification.SignalSession.Cli.Slots.cliExternsPlaced_panic_handle_error mmpl W)))
    ((show lsRustNoAllocShimSymCli = CryptoVerification.SpqrV1.Alloc.spqrRustNoAllocShimSym by decide) ▸
      (⟨ProofLib.hookNoop, (cliGhostExterns_shim gh _).trans (congrArg some hG.shim_eq),
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShim_hookOk⟩ :
        HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsRustNoAllocShimSymCli
          LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimSpec))
    ((show lsRustAllocSymCli = CryptoVerification.SpqrV1.Alloc.spqrRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
    ((show lsRustReallocSymCli = CryptoVerification.SpqrV1.Alloc.spqrRustReallocSym by decide) ▸
      cliExternsPlaced_realloc_budget_sat mmpl gh W hG)

private theorem withFds_pool_eq_of_fds {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {s : State} (henf : lim.enforced = true) (hFds : FdsGe3Closed s.fs) (st : M.σ) :
    (withFds A).pool lim st s = A.pool lim st s := by
  have hTrue : FdsGe3Closed s.fs = True := propext ⟨fun _ => trivial, fun _ => hFds⟩
  rw [withFds_pool_enforced A henf, hTrue, ProofLib.pure_true, emp_sepConj]

private theorem fds_of_evs_right4 {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Q1 : List AllocEvent → SepProp} {P2 P3 R : SepProp} {st : M.σ} {sf : State}
    (henf : lim.enforced = true)
    (h : sf.mem ⊨ (∃∗ evs, Q1 evs ∗ P2 ∗ P3 ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗ R) :
    FdsGe3Closed sf.fs := by
  rw [sepExists_sepConj_left, satisfies_sepExists] at h; rcases h with ⟨evs, h⟩
  rw [withFds_pool_enforced A henf] at h
  have hEq : (Q1 evs ∗ P2 ∗ P3 ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf)) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗ ((Q1 evs ∗ P2 ∗ P3 ∗ A.pool lim (M.stepEvents evs st) sf) ∗ R) := by sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj] at h; exact h.1

private theorem fds_of_evs_right6 {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Q1 : List AllocEvent → SepProp} {P2 P3 P4 P5 R : SepProp} {st : M.σ} {sf : State}
    (henf : lim.enforced = true)
    (h : sf.mem ⊨ (∃∗ evs, Q1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗ R) :
    FdsGe3Closed sf.fs := by
  rw [sepExists_sepConj_left, satisfies_sepExists] at h; rcases h with ⟨evs, h⟩
  rw [withFds_pool_enforced A henf] at h
  have hEq : (Q1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf)) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗ ((Q1 evs ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ A.pool lim (M.stepEvents evs st) sf) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj] at h; exact h.1

private theorem fds_of_codec_post {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P1 Tail R : SepProp} {Q : List AllocEvent → SepProp} {st : M.σ} {sf : State}
    (henf : lim.enforced = true)
    (h : sf.mem ⊨ (P1 ∗ (∃∗ evs, Q evs ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗ Tail) ∗ R) :
    FdsGe3Closed sf.fs := by
  have hEq1 : (P1 ∗ (∃∗ evs, Q evs ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗ Tail) ∗ R =
      (∃∗ evs, Q evs ∗ (withFds A).pool lim (M.stepEvents evs st) sf) ∗ (P1 ∗ Tail ∗ R) := by sep_ac_rfl
  rw [hEq1, sepExists_sepConj_left, satisfies_sepExists] at h; rcases h with ⟨evs, h⟩
  rw [withFds_pool_enforced A henf] at h
  have hEq2 : (Q evs ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf)) ∗ (P1 ∗ Tail ∗ R) =
      ⌜FdsGe3Closed sf.fs⌝ ∗ ((Q evs ∗ A.pool lim (M.stepEvents evs st) sf) ∗ (P1 ∗ Tail ∗ R)) := by sep_ac_rfl
  rw [hEq2, satisfies_pure_sepConj] at h; exact h.1

private theorem fds_of_dropSpe_post {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P1 P2 P3 R : SepProp} {st : M.σ} {sf : State} (henf : lim.enforced = true)
    (h : sf.mem ⊨ (P1 ∗ P2 ∗ (withFds A).pool lim st sf ∗ P3) ∗ R) : FdsGe3Closed sf.fs := by
  rw [withFds_pool_enforced A henf] at h
  have hEq : (P1 ∗ P2 ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim st sf) ∗ P3) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗ ((P1 ∗ P2 ∗ A.pool lim st sf ∗ P3) ∗ R) := by sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj] at h; exact h.1

private theorem subroutine_ok_path_withFds_of_withFds [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} (A : RustCliAllocBudget M) {lim : BudgetLimits}
    (henf : lim.enforced = true) {PathEnv₀ : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {stk : Nat} (hok : subroutine_ok prog entry (pathSpecPlaced (withFds A) lim PathEnv₀ stk)) :
    subroutine_ok prog entry (withFdsGe3Closed (pathSpecPlaced A lim PathEnv₀ stk)) := by
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hpre => ?_) (fun ⟨x, st⟩ R s0 sf hpost => ?_)
  · obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    simpa only [pathSpecPlaced, withLsCodeRoLoaded, withFds_pool_eq_of_fds henf hClosed0,
      withFds_repAlloc] using hpreA
  · dsimp only [withFdsGe3Closed, pathSpecPlaced, withLsCodeRoLoaded] at hpost ⊢
    have hClosedF : FdsGe3Closed sf.fs := fds_of_evs_right6 henf hpost
    simp only [withFds_pool_eq_of_fds henf hClosedF, withFds_repAlloc] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hClosedF, hpost⟩

private theorem subroutine_ok_dirGet_withFds [LibsignalPlacement] {M : AllocCostModel}
    {P : Program} {entry : BitVec 64} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop} {stk : Nat}
    (henf : lim.enforced = true)
    (hGet : subroutine_ok P entry (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv stk))) :
    subroutine_ok P entry (dirGetSpecPlaced rd pathOk (withFds A) lim GetEnv stk) := by
  refine subroutine_ok_mono hGet (fun ⟨x, st⟩ R s0 hpre => ?_) (fun ⟨x, st⟩ R s0 sf hpost => ?_)
  · dsimp only [withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded, withFds_repAlloc] at hpre ⊢
    rw [withFds_pool_enforced A henf] at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · dsimp only [withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded, withFds_repAlloc] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hClosedF, hpostRest⟩
    simpa only [withFds_pool_eq_of_fds henf hClosedF] using hpostRest

private theorem cliBcmp_keepsFs_sat (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hBcmp : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliBcmpName (withVmPreserved cliBcmpSpec)) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs := by
  rcases hBcmp with ⟨f, hf, hok⟩
  cases Option.some.inj (hf.symm.trans (cliGhostExterns_bcmp mmpl gh W))
  exact ⟨cliBcmpHook W.bcmp, hf, hok.keepsFs fun _ => rfl⟩

private theorem dirGet_fd_ok [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true) {H : LibsignalHooks}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) (hAllocFs : AllocContractsFsPlaced A lim H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    (hhWithFds : RunHooksPlaced (withFds A) lim H)
    (hReadSatFd : HookSat H lsReadFileSym (withFdsGe3Closed
      (h2k_readFileSpecK cliIo.rd cliWrOk A lim cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))) :
    subroutine_ok (lsProg_589 H) (lsmpl.base 589) (withFdsGe3Closed
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        (RunBudgets.dirGetNeed ⟨cliRunBudgets.readFile⟩))) := by
  have hsh := SessKitHooksPlaced.of_runHooks hhWithFds
  exact dirGet_placed_ok_of_h2k_fd (pathProg := lsProg_589 H) (jPath := 589)
    (fun _ hp => hp.2) hAllocFs hBcmp (by decide) (by decide)
    (subroutine_ok_path_withFds_of_withFds A henf
      (hsh.path (callerProg := lsProg_589 H) (i := 589) (Nat.le_refl pathNeed) (by decide)))
    hReadSatFd
    (h2lr_lsRetAddr624_keepSub_false hLs (lsRetAddr624_blockPlacement_base_add 589 336#64 (by decide) (by decide)))
    (hhWithFds.fs (lsProg_589 H) 589) (Nat.le_refl (RunBudgets.dirGetNeed ⟨cliRunBudgets.readFile⟩))
    (fun _ _ _ _ h => h)

private theorem subroutine_ok_decimal_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {DecEnv : BitVec 32 → List AllocEvent → Prop} {stk : Nat}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (decimalSpecPlaced (withFds A) lim DecEnv stk)) :
    subroutine_ok P entry (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv stk)) := by
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hpre => ?_) (fun ⟨x, st⟩ R s0 sf hpost => ?_)
  · obtain ⟨h0, hp⟩ := extract_withFdsGe3Closed hpre
    simpa only [decimalSpecPlaced, withLsCodeRoLoaded, withFds_pool_eq_of_fds henf h0, withFds_repAlloc] using hp
  · dsimp only [withFdsGe3Closed, decimalSpecPlaced, withLsCodeRoLoaded] at hpost ⊢
    have hF : FdsGe3Closed sf.fs := fds_of_evs_right4 henf hpost
    simp only [withFds_pool_eq_of_fds henf hF, withFds_repAlloc] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hF, hpost⟩

private theorem subroutine_ok_dirPut_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop} {stk : Nat}
    (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (dirPutSpecPlaced (withFds A) lim PutEnv stk)) :
    subroutine_ok P entry (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv stk)) := by
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hpre => ?_) (fun ⟨x, st⟩ R s0 sf hpost => ?_)
  · obtain ⟨h0, hp⟩ := extract_withFdsGe3Closed hpre
    simpa only [dirPutSpecPlaced, withLsCodeRoLoaded, withFds_pool_eq_of_fds henf h0, withFds_repAlloc] using hp
  · dsimp only [withFdsGe3Closed, dirPutSpecPlaced, withLsCodeRoLoaded] at hpost ⊢
    have hF : FdsGe3Closed sf.fs := fds_of_evs_right6 henf hpost
    simp only [withFds_pool_eq_of_fds henf hF, withFds_repAlloc] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hF, hpost⟩

private theorem subroutine_ok_dropSpeWord_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (dropSpeWordSpecPlaced (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (dropSpeWordSpecPlaced A lim)) := by
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hpre => ?_) (fun ⟨x, st⟩ R s0 sf hpost => ?_)
  · obtain ⟨h0, hp⟩ := extract_withFdsGe3Closed hpre
    dsimp only [dropSpeWordSpecPlaced, withLsCodeRoLoaded] at hp ⊢; rwa [withFds_pool_eq_of_fds henf h0]
  · dsimp only [withFdsGe3Closed, dropSpeWordSpecPlaced, withLsCodeRoLoaded] at hpost ⊢
    have hF : FdsGe3Closed sf.fs := fds_of_dropSpe_post henf hpost
    rw [withFds_pool_eq_of_fds henf hF] at hpost; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hF, hpost⟩

private theorem subroutine_ok_preKeyDeserialize_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (preKeyDeserializePlacedSpec (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (preKeyDeserializePlacedSpec A lim)) := by
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hpre => ?_) (fun ⟨x, st⟩ R s0 sf hpost => ?_)
  · obtain ⟨h0, hp⟩ := extract_withFdsGe3Closed hpre
    dsimp only [preKeyDeserializePlacedSpec, CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      preKeyDeserializeRawSpec] at hp ⊢; rwa [withFds_pool_eq_of_fds henf h0]
  · dsimp only [withFdsGe3Closed, preKeyDeserializePlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded, preKeyDeserializeRawSpec] at hpost ⊢
    have hF : FdsGe3Closed sf.fs := fds_of_codec_post (Tail := _ ∗ _ ∗ _) henf (by simpa only [sepConj_assoc] using hpost)
    simp only [withFds_pool_eq_of_fds henf hF, withFds_repAlloc] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hF, hpost⟩

private theorem subroutine_ok_decodeKyberPreKey_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (decodeKyberPreKeyPlacedSpec (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (decodeKyberPreKeyPlacedSpec A lim)) := by
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hpre => ?_) (fun ⟨x, st⟩ R s0 sf hpost => ?_)
  · obtain ⟨h0, hp⟩ := extract_withFdsGe3Closed hpre
    dsimp only [decodeKyberPreKeyPlacedSpec, CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeKyberPreKeyRawSpec] at hp ⊢; rwa [withFds_pool_eq_of_fds henf h0]
  · dsimp only [withFdsGe3Closed, decodeKyberPreKeyPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded, decodeKyberPreKeyRawSpec] at hpost ⊢
    have hF : FdsGe3Closed sf.fs := fds_of_codec_post (Tail := _ ∗ _ ∗ _) henf (by simpa only [sepConj_assoc] using hpost)
    simp only [withFds_pool_eq_of_fds henf hF, withFds_repAlloc] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hF, hpost⟩

private theorem subroutine_ok_decodeSignedPreKey_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true) {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (decodeSignedPreKeyPlacedSpec (withFds A) lim)) :
    subroutine_ok P entry (withFdsGe3Closed (decodeSignedPreKeyPlacedSpec A lim)) := by
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hpre => ?_) (fun ⟨x, st⟩ R s0 sf hpost => ?_)
  · obtain ⟨h0, hp⟩ := extract_withFdsGe3Closed hpre
    dsimp only [decodeSignedPreKeyPlacedSpec, CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeSignedPreKeyRawSpec] at hp ⊢; rwa [withFds_pool_eq_of_fds henf h0]
  · dsimp only [withFdsGe3Closed, decodeSignedPreKeyPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded, decodeSignedPreKeyRawSpec] at hpost ⊢
    have hF : FdsGe3Closed sf.fs := fds_of_codec_post (Tail := _ ∗ _ ∗ _) henf (by simpa only [sepConj_assoc] using hpost)
    simp only [withFds_pool_eq_of_fds henf hF, withFds_repAlloc] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hF, hpost⟩

private theorem cliSessKitOkSE_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String} {deserProg serProg : Program} {deserBlk serBlk : Nat}
    [IsLsBlockProg deserProg deserBlk H] [IsLsBlockProg serProg serBlk H]
    (hDropNz : lsmpl.base 547 ≠ 0#64) (hh : SessKitHooksPlaced A lim H)
    (hGet : subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim (DirGetEnv PathEnv ReadEnv rd) (RunBudgets.dirGetNeed ⟨readStk⟩)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46) (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hSer : subroutine_ok serProg (lsmpl.base 52) (withLsCodeLoaded lsmpl (serializeCanonSpecX M A lim)))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hDeserBlk : deserBlk < 619 := by decide) (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide) (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord H :=
  let hAddr := cliAddrText_placed_ok_of_sessHooks hh
  { loadShim := fun hblk => cliSessLoadShim_rocl_placed_ok hh.alloc hs1 hblk
    loadPoll := fun hblk => cliSessLoadPoll_rocl_placed_ok hh.alloc hAddr hGet hDeser
      (hh.fs (lsProg_569 H) 569) hs2 hblk (by decide) (by decide) (by decide) (by decide) hDeserBlk hDeserUnmut
    loadFutDrop := fun hblk => by
      dsimp only [cliSessionKitSpecPlaced]; rw [lsDropOffPlaced_eq hDropNz]; exact cliSessFutDrop_rocl_placed_ok hblk
    storeShim := fun hblk => cliSessStoreShim_rocl_placed_ok hh.alloc hs3 hblk
    storePoll := fun hblk => cliSessStorePoll_rocl_placed_ok hh.alloc hAddr hSer
      (cliDirPut_placed_ok_of_sessHooks hh) hs4 hblk (by decide) (by decide) hSerBlk hSerUnmut (by decide) (by decide)
    storeFutDrop := fun hblk => by
      dsimp only [cliSessionKitSpecPlaced]; rw [lsDropOffPlaced_eq hDropNz]; exact cliSessFutDrop_rocl_placed_ok hblk }

private theorem cliIdKitOkIE_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64) (hh : RunHooksPlaced A lim H)
    (hGet : subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim (DirGetEnv PathEnv ReadEnv rd) (RunBudgets.dirGetNeed ⟨readStk⟩)))
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (hs1 : trustShimNeedPlaced ≤ s1) (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hs3 : saveShimNeedPlaced ≤ s3) (hs4 : savePollNeedPlaced readStk ≤ s4) :
    IdentityStoreKitPlacedOkI A lim (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
      (cliIdentityKitDefaultBudgetEnv A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym ReadEnv) H := by
  have hEq := publicKeyEq_placed_ok_of_bb h_bb
  have h566 := idTrustPoll_placed_ok_of_deps hh.alloc hGet (identityKey_decode_placed_ok (A := A) H) hEq hs2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h565 : subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd (DirGetEnv PathEnv ReadEnv rd) DirPutStrEnv) s4) :=
    idSavePoll_placed_ok_of_deps_core hh.alloc
      (publicKeySerialize_lscro_of_cli (callerProg := (blkPC_565).rebase (blkPl_565).base H) hh.alloc (by decide))
      (ls_transfer_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H) hGet (by decide) (by decide) (by decide))
      (ls_transfer_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
        (cliDirPutStr_placed_ok hh) (by decide) (by decide) (by decide))
      (ls_transfer_cl_to_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
        (identityKey_decode_placed_ok (A := A) H) (by decide) (by decide) (by decide))
      (ls_transfer_cl_to_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H) hEq
        (by decide) (by decide) (by decide)) hs4
  exact cliIdKitOkIE_placed_of_polls hDropNz hh.alloc h566 h565 hs1 hs3

private theorem canonPollKitsPlacedOk_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hAllocFs : AllocContractsFsPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hh : RunHooksPlaced (withFds A) lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGetFd : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed)))
    (hGetPool : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk (withFds A) lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit (withFds A) lim DeserEnv)) :
    CanonPollKitsPlacedOk (withFds A) lim B ReadEnv DeserEnv (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hsh := SessKitHooksPlaced.of_runHooks hh; have hc := hh.codecHooks
  have hBb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook :=
    (cliGhostExterns_other gh (cliExternsPlaced mmpl W) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W))
  have hDec597 := subroutine_ok_decimal_fd henf (cliDecimal_placed_ok_of_sessHooks hsh)
  have hPut542 := subroutine_ok_dirPut_fd henf (cliDirPut_placed_ok_of_sessHooks hsh)
  have hDrop553 := subroutine_ok_dropSpeWord_fd henf (dropSpeWord_placed_ok hsh.alloc)
  have hPkDec65 := subroutine_ok_preKeyDeserialize_fd henf (preKeyRecord_deserialize_placed_ok_of_hooks hc)
  have hSpkDec595 := subroutine_ok_decodeSignedPreKey_fd henf
    (decodeSignedPreKey_placed_ok (signedHooksPlaced_of_codecHooks hc) (signedPortDepsPlaced_ok hc))
  have hKpkDec595 := subroutine_ok_decodeKyberPreKey_fd henf
    (decodeKyberPreKey_placed_ok (signedHooksPlaced_of_codecHooks hc) (signedPortDepsPlaced_ok hc))
  have h571 := spkGetPoll_placed_fs_ok_of_deps_fd (decProg := lsProg_597 H) (decBlk := 597)
    (getProg := lsProg_589 H) (getBlk := 589) (spkDecProg := lsProg_595 H) (spkDecBlk := 595)
    (dropProg := lsProg_553 H) (dropBlk := 553) hAllocFs hDec597 hGetFd hSpkDec595 hDrop553
    (hh.fs (lsProg_571 H) 571) (Nat.le_refl (cliKitStk B).spkGetPoll) (fun _ _ => Or.inl) (fun _ _ => Or.inr)
  have h576 := kpkGetPoll_placed_fs_ok_of_deps_fd (decProg := lsProg_597 H) (decBlk := 597)
    (getProg := lsProg_589 H) (getBlk := 589) (decodeProg := lsProg_595 H) (decodeBlk := 595)
    hAllocFs hDec597 hGetFd hKpkDec595 (hh.fs (lsProg_576 H) 576) (Nat.le_refl (cliKitStk B).kpkGetPoll)
    (fun _ _ => Or.inl) (fun _ _ => Or.inr)
  have h578 := kpkMarkPoll_placed_ok_of_deps_fd (decProg := lsProg_597 H) (decBlk := 597)
    (getProg := lsProg_589 H) (getBlk := 589) (putProg := lsProg_570 H) (putBlk := 570)
    hAllocFs hh.panics (cliBcmp_keepsFs_sat mmpl gh W hsh.bcmp) hDec597 hGetFd hPut542
    (hh.fs (lsProg_578 H) 578) (Nat.le_refl (cliKitStk B).kpkMarkPoll)
  have h573 := pkGetPoll_placed_fs_ok_of_deps_fd (decProg := lsProg_597 H) (decBlk := 597)
    (getProg := lsProg_589 H) (getBlk := 589) (pkDecProg := lsProg_65 H) (pkDecBlk := 65)
    (dropProg := lsProg_553 H) (dropBlk := 553) hAllocFs hDec597 hGetFd hPkDec65 hDrop553
    (hh.fs (lsProg_573 H) 573) (Nat.le_refl (cliKitStk B).pkGetPoll) (fun _ _ => Or.inl) (fun _ _ => Or.inr)
  have h575 := pkRemovePoll_placed_ok_of_deps_fd (decProg := lsProg_597 H) (decBlk := 597)
    (getProg := lsProg_589 H) (getBlk := 589) (putProg := lsProg_570 H) (putBlk := 570)
    hAllocFs hDec597 hGetFd hPut542 (hh.fs (lsProg_575 H) 575) (Nat.le_refl (cliKitStk B).pkRemovePoll)
  haveI : IsLsBlockProg (dpPollProgPlaced H) 518 H := inferInstance
  exact
    { sessOk := fun F0 peer => cliSessKitOkSE_of_dirGet (deserProg := dpPollProgPlaced H) (deserBlk := 518)
        (serProg := lsProg_52 H) (serBlk := 52) hDropNz hsh hGetPool hDeser
        (serializeCanonX_placed_ok_of_serContractsX (serContractsX_of_runHooks mmpl gh W hh))
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by decide) (by decide) (by decide) (by decide)
      idOk := fun F0 peer => cliIdKitPlacedOkI_full
        (cliIdKitOkIE_of_dirGet hDropNz hh hGetPool hBb (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      selfOk := fun F0 peer => cliPollSelf_kitPlacedOk_of_dirGet mmpl gh W B F0 peer hDropNz hh hGetPool
      spkOk := fun F0 sid => spkKitFds_toWithFds henf rfl
        (cliSpkKitPlacedOkFds_of_poll (kitEnv := cliPollSpkFullBudgetEnv A.repAlloc F0 sid (cliKitStk B) ReadEnv)
          hDropNz hAllocFs (fun _ _ _ _ _ hm => hm) h571 (Nat.le_refl _))
      kpkOk := fun F0 kid sid kbk => kpkKitFds_toWithFds henf rfl
        (cliKpkKitPlacedOkFds_full_of_polls (cliPollKpkFullBudgetEnv A.repAlloc F0 kid sid kbk (cliKitStk B) ReadEnv)
          hDropNz hAllocFs (Nat.le_refl _) (Nat.le_refl _) (fun _ _ _ _ _ hm => hm) (fun _ _ _ _ _ _ hm => hm) h576 h578)
      pkOk := fun F0 pid => pkKitFds_toWithFds henf rfl
        (cliPkKitPlacedOkFds_of_polls (kitEnv := cliPollPkFullBudgetEnv A.repAlloc F0 pid (cliKitStk B) ReadEnv)
          hDropNz hAllocFs (fun _ _ _ _ _ hm => hm) (fun _ _ _ _ _ hm => hm) h573 h575 (Nat.le_refl _) (Nat.le_refl _)) }

end LocalSeamHelpers

section SpqrTopStateGuarded

private theorem spqr_hExt_withPanics (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym := fun sym hne => by
  rw [← withPanics_cliGhostExterns mmpl gh W]; simp only [Rust.withPanics, hExt sym hne]

private theorem spqr_cliGhost_row_aux (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {sym : String} {f : State → State} (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (h1 : sym ≠ lsRustAllocSymCli := by decide) (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide) (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide) (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ lsReadFileSym := by decide) (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ CryptoVerification.SignalSession.lsMemsetSym := by decide)
    (h10 : sym ≠ CryptoVerification.SignalSession.lsMemcpySym := by decide) :
    cliGhostExterns g (cliExternsPlaced mmpl W) sym = some f :=
  (cliGhostExterns_other g _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).trans (cliExternsPlaced_row mmpl W hrow)

private def SpqrFromPbStateGuard (F : ShaCompress) (pb : V1State) : Prop :=
  (∃ st : States spqrPolyApi (spqrAuthApi F), BOkTight st ∧ pb = st.into_pb) ∧ rawV1State pb ≤ 46880 ∧ ValidV1PtsAt 640 pb

private def SpqrIntoPbStateGuard {F : ShaCompress} (st1 : States spqrPolyApi (spqrAuthApi F)) : Prop :=
  BOkTight st1 ∧ rawV1State st1.into_pb ≤ 46880

private def SpqrStatesRecvExactPairTightEnv {F : ShaCompress} (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) (evs : List AllocEvent) : Prop :=
  ∃ outA selfA msgA, StatesRecvExactTightEnv K ⟨outA, selfA, msgA, st, msg⟩ evs

private theorem spqr_topStateTight_fromPbStateGuard {F : ShaCompress} {K : MlKem} {stBytes : Bytes}
    (hTop : TopStateTight F K stBytes) {pre_pb : PqRatchetState} (hdec : spqrDecodeState stBytes = .ok pre_pb)
    {pb : V1State} (hinner : pre_pb.inner = some (.v1 pb)) : SpqrFromPbStateGuard F pb := by
  have hprops := (topStateTight_decode_props hTop hdec).2.2.1 pb hinner
  obtain ⟨_, _, hlt31⟩ := topStateTight_to_tightValid640 hTop
  have hsize : stBytes.length < 2 ^ 64 := Nat.lt_trans hlt31 (by decide)
  obtain ⟨_, _, _, st, _, _, _, vn?, ch?, _, hw⟩ := hTop
  have hdec_eq : spqrDecodeState stBytes = .ok (pbToPqRatchetState (topPb st vn? ch?)) := by
    have hbeq : stBytes = encodeState (pbToPqRatchetState (topPb st vn? ch?)) := hw.htop.hbytes
    rw [hbeq] at hsize ⊢; exact spqrDecodeState_encodeState (pbToPqRatchetState (topPb st vn? ch?)) hsize
  rw [hdec_eq] at hdec; cases hdec
  simp only [pbToPqRatchetState, topPb, Option.map, Option.some.injEq] at hinner; cases hinner
  exact ⟨⟨st, hw.hbok, rfl⟩, hprops⟩

private theorem spqr_topStateTight_intoPbStateGuard {F : ShaCompress} {K : MlKem} {stBytes : Bytes}
    (hTop : TopStateTight F K stBytes) {pre_pb : PqRatchetState} (hdec : spqrDecodeState stBytes = .ok pre_pb)
    {pb : V1State} (hinner : pre_pb.inner = some (.v1 pb)) {st0 : States spqrPolyApi (spqrAuthApi F)}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    {sckaMsg : Message spqrPolyApi} {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    (hrecv : States.recv K st0 sckaMsg = .ok v) : SpqrIntoPbStateGuard v.state := by
  obtain ⟨⟨st, hbok, rfl⟩, -⟩ := spqr_topStateTight_fromPbStateGuard hTop hdec hinner
  rw [st_bCodec F st hbok.1] at hfrom
  rw [← Except.ok.inj hfrom] at hrecv; rcases v with ⟨key, st1⟩
  have hbok1 : BOkTight st1 := by
    cases hek : isEkSide st
    · exact st_bRecvCt_tight F K hek hbok hrecv
    · exact st_bRecvEk_tight F K hek hbok hrecv
  exact ⟨hbok1, st_bSize_tight F st1 hbok1⟩

private theorem spqr_seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs) {evs : List AllocEvent}
    (h : SeqEnv E₁ E₂ evs) : SeqEnv E₁' E₂' evs := by
  rcases h with hp | ⟨e1, e2, rfl, he1, he2⟩
  · exact Or.inl (h1 evs hp)
  · exact Or.inr ⟨e1, e2, rfl, h1 e1 he1, h2 e2 he2⟩

private theorem spqr_recvTightLinkedEnv_imp_c07c09aOf109_of_topStateTight {F : ShaCompress} {K : MlKem}
    {FromPbEnv : V1State → List AllocEvent → Prop} {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hFromPb_sub : ∀ pb evs, SpqrFromPbStateGuard F pb → FromPbEnv pb evs → StatesFromPbTightEnv evs)
    (hIntoPb_sub : ∀ g evs, SpqrIntoPbStateGuard g.st → IntoPbEnv g evs → StatesIntoPbTightEnv evs)
    {stBytes : Bytes} (hTop : TopStateTight F K stBytes)
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi} {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xInit : InitInnerGhost} {xNew : ChainNewGhost} {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall} {evs : List AllocEvent}
    (h : SpqrRecvTightLinkedEnv F K (fun _ => tlb_DecodeStateTightEnvOf 109) FromPbEnv IntoPbEnv
      (SpqrStatesRecvExactPairTightEnv K) stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    SpqrRecvC07C09aTightLinkedEnvOf 109 F K stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs := by
  rcases h with ⟨hTight, hLink⟩; refine ⟨?_, hLink⟩
  rcases hTight with hfree | hseq
  · exact Or.inl hfree
  · refine Or.inr (spqr_seqEnv_mono (fun _ hd => hd) (fun _ hafter => ?_) hseq)
    rcases hafter with hfree1 | ⟨hdec, hless | hgt | ⟨hinner, heq⟩⟩
    · exact Or.inl hfree1
    · exact Or.inr ⟨hdec, Or.inl hless⟩
    · exact Or.inr ⟨hdec, Or.inr (Or.inl hgt)⟩
    · refine Or.inr ⟨hdec, Or.inr (Or.inr ⟨hinner, ?_⟩)⟩
      have hPbG := spqr_topStateTight_fromPbStateGuard hTop hdec hinner
      refine spqr_seqEnv_mono (fun _ hf => hf) (fun _ hmd => ?_) heq
      rcases hmd with hfree2 | hfromSeq
      · exact Or.inl hfree2
      · refine Or.inr (spqr_seqEnv_mono (fun evsF hf => hFromPb_sub pb evsF hPbG hf) (fun _ haf => ?_) hfromSeq)
        rcases haf with hfree3 | ⟨hfrom, hrecvSeq⟩
        · exact Or.inl hfree3
        · refine Or.inr ⟨hfrom, spqr_seqEnv_mono
            (fun _ ⟨outA, selfA, msgA, hr⟩ =>
              statesRecvExactTightEnv_sub_statesRecvProtoEnv' K ⟨outA, selfA, msgA, st0, sckaMsg⟩ hfrom hr)
            (fun _ har => ?_) hrecvSeq⟩
          rcases har with hfree4 | ⟨hrecv, hxS, hv1c⟩
          · exact Or.inl hfree4
          · have hIntoG : SpqrIntoPbStateGuard xSInto.st :=
              hxS.symm ▸ spqr_topStateTight_intoPbStateGuard hTop hdec hinner hfrom hrecv
            refine Or.inr ⟨hrecv, hxS, spqr_seqEnv_mono (fun _ hc => hc) (fun _ he1 => ?_) hv1c⟩
            rcases he1 with hfree5 | ⟨hc1, hc2, haddSeq⟩
            · exact Or.inl hfree5
            · refine Or.inr ⟨hc1, hc2, spqr_seqEnv_mono (fun _ ha => ha) (fun _ he2 => ?_) haddSeq⟩
              rcases he2 with hfree6 | hrkSeq
              · exact Or.inl hfree6
              · refine Or.inr (spqr_seqEnv_mono (fun _ hrk => hrk) (fun _ he3 => ?_) hrkSeq)
                rcases he3 with hfree7 | ⟨hrkOk, hintoSeq⟩
                · exact Or.inl hfree7
                · exact Or.inr ⟨hrkOk, spqr_seqEnv_mono (fun evsI hi => hIntoPb_sub xSInto evsI hIntoG hi)
                    (fun _ ht => ht) hintoSeq⟩

private theorem spqr_recv_topStateGuarded_seam_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop} {IntoPbEnv : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    (hDecPre_sub : ∀ g evs, TopStateTight W.C.F W.Q.K g.st.bytes → DecodePreEnv g evs → tlb_DecodeStateTightEnvOf 109 evs)
    (hDecPost_sub : ∀ g evs, TopStateTight W.C.F W.Q.K g.st.bytes → DecodePostEnv g evs → tlb_DecodeStateTightEnvOf 109 evs)
    (hFromPb_sub : ∀ pb evs, SpqrFromPbStateGuard W.C.F pb → FromPbEnv pb evs → StatesFromPbTightEnv evs)
    (hIntoPb_sub : ∀ (g : StatesIntoPbGhost W.C.F) evs, SpqrIntoPbStateGuard g.st → IntoPbEnv g evs → StatesIntoPbTightEnv evs)
    (hRecvC : SpqrRecvPlacedContractsOfEnv H_inner A lim W.C.F W.Q.K DecodePreEnv DecodePostEnv
      (InitInnerEnv W.C.F) FromPbEnv (fun g => SpqrStatesRecvExactPairTightEnv W.Q.K g.self g.msg) IntoPbEnv
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))) (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
        (fun st msg => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes))) := by
  refine spqrRecvPlacedInnerSpecXTOfEnv_of_placedSpecXT
    (spqr_recv_placed_ok_blockProgram_ext_of_contracts_ofEnv
      (fun (st msg : VecArg) => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
      (trTrapExternsPlaced_isPanic mmpl gh W) hRecvC
      (fun st _ _ _ _ _ => spqrRecvTightLinkedEnv_nil_exists W.C.F W.Q.K (fun _ => tlb_DecodeStateTightEnvOf 109)
        (fun _ => StatesFromPbTightEnv) (fun _ => StatesIntoPbTightEnv) (StatesRecvProtoEnv' W.Q.K) st.bytes)
      (fun st msg s0 st_cost _ _ _ _ hfit => ?_))
  by_cases hTop : TopStateTight W.C.F W.Q.K st.bytes
  · exact spqrRecvBranchHyps_tightLinked (DecodeStateEnv' := fun _ => tlb_DecodeStateTightEnvOf 109)
      (StatesFromPbEnv' := FromPbEnv) (StatesIntoPbEnv' := IntoPbEnv)
      (StatesRecvEnv' := SpqrStatesRecvExactPairTightEnv W.Q.K) st msg s0 st_cost
      (fun evs hpre => hDecPre_sub ⟨st, s0.sp - 3056#64⟩ evs hTop hpre)
      (fun evs hpost => hDecPost_sub ⟨st, s0.sp - 3056#64⟩ evs hTop hpost)
      (fun _ _ h => h) (fun _ _ _ h => h) (fun _ _ h => h)
      (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto =>
        FitsEnv.mono (fun evs hevs _ => ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto,
          spqr_recvTightLinkedEnv_imp_c07c09aOf109_of_topStateTight hFromPb_sub hIntoPb_sub hTop hevs⟩) hfit)
      (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs hevs _ =>
        ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto,
          spqr_recvTightLinkedEnv_imp_c07c09aOf109_of_topStateTight hFromPb_sub hIntoPb_sub hTop hevs⟩)
  · exact False.elim (w4f_not_fitsEnv_top (FitsEnv.mono (fun _ _ h => False.elim (hTop h)) hfit))

private theorem spqr_hookSat_withAllocVmPreserved_memmove_of_zero
    {H : String → Option (State → State)} {sym : String} (hookStack : Nat)
    (h : HookSat H sym (withAllocVmPreserved (sessionMemmoveSpec 0))) :
    HookSat H sym (withAllocVmPreserved (sessionMemmoveSpec hookStack)) := by
  refine ProofLib.HookSat.mono h fun ⟨base, buf, dst, src, len⟩ R s0 hpre =>
    ⟨(base, buf, dst, src, len), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withAllocVmPreserved, sessionMemmoveSpec, libcMemmoveSpec, stackAt] at hpre ⊢
    simp only [ProofLib.memRegion_zero, sepConj_emp]; ac_nf at hpre ⊢
  · dsimp only [withAllocVmPreserved, sessionMemmoveSpec, libcMemmoveSpec, stackAt] at hpost ⊢
    simp only [ProofLib.memRegion_zero, sepConj_emp] at hpost; ac_nf at hpost ⊢

private theorem spqr_statesRecv_recv_exactTight_ok [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 332) (withLsCodeRoLoaded lsmpl
        (statesRecvPlacedSpecOfEnv M A lim W.C.F W.Q.K (fun g => SpqrStatesRecvExactPairTightEnv W.Q.K g.self g.msg))) := by
  let ext := trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
  have hExt := w4s2_trTrap_hExt mmpl gh W
  have hExt_wp := spqr_hExt_withPanics mmpl gh W hExt
  have hmemset_wp :=
    hookSat_of_eq (hExt_wp "memset" (by decide))
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl gh W hA.toCliGhostAllocHooks)
  letI : HkdfPlacedHooksExactBudgetSat W.C.F (Rust.withPanics ext) :=
    { memset := hmemset_wp
      memcpy := hookSatExactMemcpy_of_sym_eq (hExt_wp "memcpy" (by decide))
        (cliExternsPlaced_exactMemcpy_sat mmpl gh W hA.toCliGhostAllocHooks)
      compress256 := (hExt_wp _ (by decide)).trans
        (spqr_cliGhost_row_aux mmpl gh W (compress256_row_placed mmpl W)) }
  have hC := statesRecvPlacedContracts_of_ro_leaves_sat (cliRecvCt2PlacedAllocExt mmpl gh W hA hExt)
    (spqr_hookSat_withAllocVmPreserved_memmove_of_zero growOneStack
      (hookSat_of_eq (hExt_wp _ (by decide)) (cliExternsPlaced_sessionMemmove_allocVm_sat mmpl gh W)))
    hmemset_wp
    (hookSat_of_eq (hExt_wp _ (by decide)) (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_mlkemValidatePk_budget_sat mmpl W)))
    (hookSat_of_eq (hExt_wp _ (by decide)) (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_mlkemEncaps2_budget_sat mmpl W)))
    (hookSat_of_eq (hExt_wp _ (by decide)) (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_mlkemDecaps_budget_sat mmpl W)))
    (hookSat_of_eq (hExt_wp _ (by decide)) hHmac)
  have h0 := LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget.ls_subroutine_ok_of_blockProgram_cro
    (callerProg := spqrRecvPlacedProg ext) (i := 329) (states_recv_placed_ok_x_exactTight A lim W.C.F W.Q.K ext hC)
  exact subroutine_ok_mono h0
    (fun (g, _) _ _ hpre => by
      dsimp only [withLsCodeRoLoaded, statesRecvPlacedSpecOfEnv,
        LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget.statesRecvPlacedSpecOfEnv] at hpre ⊢
      exact Satisfies.mono (sepConj_mono_left (sepConj_mono_left (sepConj_mono_left
        (Entails.pure_mono fun ⟨h1, h2, h3, h4, hfit, hlr⟩ =>
          ⟨h1, h2, h3, h4, hfit.mono (fun evs hevs => ⟨g.outA, g.selfA, g.msgA, hevs⟩), hlr⟩)))) hpre)
    (fun (g, _) _ _ _ hpost => by
      dsimp only [withLsCodeRoLoaded, statesRecvPlacedSpecOfEnv,
        LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget.statesRecvPlacedSpecOfEnv] at hpost ⊢
      exact Satisfies.mono (sepConj_mono_left (Entails.sepExists_mono fun _ =>
        sepConj_mono_left (Entails.pure_mono fun ⟨h1, hevs⟩ => ⟨h1, ⟨g.outA, g.selfA, g.msgA, hevs⟩⟩))) hpost)
    (fun _ _ _ _ hp => hp)

private theorem spqr_decodeStateCalleeContractsClPlacedX_cliExt [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    DecodeStateCalleeContractsClPlacedX canonicalV1InnerHeap A lim ext := by
  have hExt_wp := spqr_hExt_withPanics mmpl gh W hExt
  exact mkDecodeStateCalleeContractsClPlacedX_of_blocks
    (cliDeallocBudget_at_block mmpl gh W hA hExt_wp (i := 325))
    (fun stk _ _ => cliLibcMemcpyBudget_at_block mmpl gh W hA hExt_wp stk (i := 325))
    (fun stk _ _ => cliSessionMemcpyBudget_at_block mmpl gh W hA hExt_wp stk (i := 325))
    (cliFrom_261_cl mmpl gh W hA hExt) (decodeErrorPush_of_merge (cliPushMerge_257_cl mmpl gh W hA hExt))
    (cliVarint_291_cl mmpl gh W hA hExt) (cliSkipBudget_263_cl mmpl gh W hA hExt)
    (chainParamsMerge_decodeState_of_prost (cliChainParams_294_cl mmpl gh W hA hExt))
    (cliGrowOne_356_cl mmpl gh W hA hExt) (cliDrop_267_cl mmpl gh W hA hExt) (cliDrop_270_cl mmpl gh W hA hExt)
    (cliBytesExact_290_cro mmpl gh W hA hExt)
    (epochDirectionMerge_decodeState_of_prost (cliEpochDir_299_cl mmpl gh W hA hExt))
    (cliV1StateMerge_closed_cl mmpl gh W hA hExt)

private theorem spqr_decodeState_recv_tight109_ok [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    (hV1Merge : tlb_V1StateMergeBlk325TightOkOf A lim 80
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325) (withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecXOfEnv canonicalV1InnerHeap A lim
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K) (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) := by
  let ext := trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
  have hc := spqr_decodeStateCalleeContractsClPlacedX_cliExt mmpl gh W hA (w4s2_trTrap_hExt mmpl gh W)
  have h0 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext)) (blkPl_325).base
      (withLsCodeRoLoaded lsmpl (spqrDecodeStatePlacedSpecOfEnv canonicalV1InnerHeap A lim
        (tlb_DecodeStateGuardedEnv W.C.F W.Q.K) (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) :=
    e2a_decodeState_cl_placed_ok_of_v1Merge_109 (F := W.C.F) (K := W.Q.K) hc
      (e2ar_epochDirectionMerge_blk325_cl_ok_tight hc) hV1Merge
  rw [IsLsBlockProg.eq_blockProgram (prog := (blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 325)] at h0
  exact LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget.ls_subroutine_ok_of_blockProgram_cro
    (callerProg := spqrRecvPlacedProg ext) (i := 329) h0

private theorem spqrSeams_topStateGuarded_of_hmac [LibsignalPlacement]
    (mmpl : MultiPlacement) (ghFixed : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hGSpqr : CliGhostSpqrAllocHooks M A lim ghFixed)
    (hHmac : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    SpqrV1PlacedSeamsOfEnv M A lim mmpl ghFixed W (InitialStateEnv W.C.F)
      (fun st msg => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
      (gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K) := by
  have hBase := gu2b_spqrV1PlacedSeams_exactFromPb_of_hmac mmpl ghFixed W hGSpqr hHmac
  have hRecvBase := cliSpqrRecvPlacedContracts_exact mmpl ghFixed W hGSpqr hHmac
  have hDec := spqr_decodeState_recv_tight109_ok mmpl ghFixed W hGSpqr.toCliGhostAllocHooks
    (v1StateMergeBlk325_cli_of_hExt mmpl ghFixed W (w4s2_trTrap_hExt mmpl ghFixed W) hGSpqr.toCliGhostAllocHooks)
  have hFromPb := gu2b_cliSpqrRecv_statesFromPb_fromPbGuard_ok mmpl ghFixed W hGSpqr
  have hRecv := spqr_statesRecv_recv_exactTight_ok mmpl ghFixed W hGSpqr hHmac
  exact
    { spqrInitialState := hBase.spqrInitialState
      spqrRecv := spqr_recv_topStateGuarded_seam_of_contracts mmpl ghFixed W
        (DecodePreEnv := tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
        (DecodePostEnv := tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
        (FromPbEnv := gu2b_StatesFromPbGuardedEnv W.C.F) (IntoPbEnv := StatesIntoPbExactEnv)
        (fun _ _ hTop h => tlb_decodeStateGuardedEnv_sub_tight_of_topStateTight hTop h)
        (fun _ _ hTop h => tlb_decodeStateGuardedEnv_sub_tight_of_topStateTight hTop h)
        (fun _ _ hG hf => hf hG)
        (fun _ _ hG hEnv => statesIntoPbExactEnv_tight (statesIntoPbTightDom_of_bokTight hG.1) hEnv)
        { hRecvBase with decodeState_ok := hDec, statesFromPb_ok := hFromPb, statesRecv_ok := hRecv }
      spqrSendCoins := hBase.spqrSendCoins }

private theorem spqrSeams_topStateGuarded_withFds [LibsignalPlacement]
    (mmpl : MultiPlacement) (ghFixed : CliGhostHooks) (hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks) (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits} (henf : lim.enforced = true)
    (hGSpqrWithFds : CliGhostSpqrAllocHooks fineCostModel
      (withFds (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim ghFixed) :
    SpqrV1PlacedSeamsOfEnv fineCostModel (withFds (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim mmpl ghFixed W
      (InitialStateEnv W.C.F) (fun st msg => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
      (gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K) :=
  spqrSeams_topStateGuarded_of_hmac mmpl ghFixed W hGSpqrWithFds
    (cliGhostExterns_libcruxHmac_withFds_hookSat γ mmpl tp brkStart henf ghFixed W hPl_mng)

end SpqrTopStateGuarded

/-! ## Spine-C Slot `520` `canon'` Interface and Envelope Inclusion -/

/-- Explicit-argument Spine-C Slot `520` (`decryptPrekey`, `canon'`) pre-only `FdsGe3Closed`
interface. -/
def h2k520c_W4DecPkCanonSlot520OkAt {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup) (ghFixed : CliGhostHooks) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    DecPkD2cSlotOkFrozenPlacedAtPreFd (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) X W
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits (cliDecPkCanonSlotEnvExact' X W)

private theorem slotWithPreFdsGe3Closed_eq (σ : CalleeSlot) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd.slotWithPreFdsGe3Closed σ =
      ElfSlicesPqOomH2KIfaces.slotWithPreFdsGe3Closed σ := rfl

private theorem decPkD2cSlotOkFrozenPlacedAtPreFd_of_canon [LibsignalPlacement]
    {M : AllocCostModel} {H : LibsignalHooks} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (h : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPlacedBudgetFd.DecPkD2cSlotOkFrozenPlacedAtPreFd
      H X W A lim DecPkEnv) :
    DecPkD2cSlotOkFrozenPlacedAtPreFd H X W A lim DecPkEnv :=
  fun S needs sEnvs hsEnv hfOk hdPk hdOk hneed =>
    slotWithPreFdsGe3Closed_eq _ ▸ h S needs sEnvs hsEnv hfOk hdPk hdOk hneed

private theorem hp3Fits_wideM3 {M : AllocCostModel} {lim : BudgetLimits}
    {tdEnvW : TryDecryptEnvArgs → List AllocEvent → Prop} {verNeDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    (st_b : M.σ) (recG : SessionGhost) (st : SessionState (List (BitVec 8))) (rem loc : AddrGhost)
    (msgG : SignalMessageGhost) (msg : SignalMessage) (msgVer : BitVec 32) (enc rest : List (BitVec 8))
    (hf : FitsEnv M lim st_b (fun evs =>
      (∃ G₁, CloneRel recG G₁ ∧ (wideM3PathCP3Envs tdEnvW verNeDecEnv).errEnv recG G₁ st rem loc msgG msg rest evs) ∨
      (wideM3PathCP3Envs tdEnvW verNeDecEnv).verNeEnv recG st enc evs ∨
      ∃ G₁, CloneRel recG G₁ ∧ (wideM3PathCP3Envs tdEnvW verNeDecEnv).okPrefixEnv recG G₁ st rem loc msgG msg rest evs)) :
    FitsEnv M lim st_b (StageP3Prev1Env tdEnvW verNeDecEnv recG st rem loc msgG msg msgVer enc rest) :=
  w4wire_hp3Fits_wideM3 st_b recG st rem loc msgG msg msgVer enc rest hf

private theorem canonPollGvSeqFreeEnv_eq_w4r2 [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (X' : UnreachedPqxdhPrimitives)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv : DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (verNeDecEnv : List (BitVec 8) → List AllocEvent → Prop) :
    DecPkD2cCanonPollGvSeqFreeEnv A W X' ReadEnv DeserEnv P2OverErrEnv P2OverOkEnv tdEnv
      (fun W' => wideM3PathCP3Envs (tdEnv W') verNeDecEnv) =
    W4r2PollCustomP3GvSeqFreeEnv A W X' ReadEnv DeserEnv P2OverErrEnv P2OverOkEnv tdEnv
      (fun W' => w4r2_wideM3PathCP3Envs (tdEnv W') verNeDecEnv) := by
  funext g evs
  dsimp only [DecPkD2cCanonPollGvSeqFreeEnv, W4r2PollCustomP3GvSeqFreeEnv, wideM3PathCP3Envs, w4r2_wideM3PathCP3Envs,
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage3Prev1PlacedBudgetFd.CliDpPollTrustedGvSeqFreeEnv,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkR2.CliDpPollTrustedGvSeqFreeEnv,
    CanonSessionGhostValid, W4r2SessionGhostValid, cliPollStageP4Prev1SeqFreeEnvsAt, w4r2_cliPollStageP4Prev1SeqFreeEnvsAt]

/-- Post-Bob guarded slot-envelope inclusion into `cliDecPkCanonSlotEnvExact' X W`. -/
theorem h2k520c_guardIncl_canonPostBob [LibsignalPlacement]
    (A : RustAlloc) (X' X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    GuardSlotIncl (M := fineCostModel) cliBudgetLimits W scopeIn
      (DecPkD2cCanonPollGvSeqFreeEnv A W X' (ReadFileRuleEnvFixed cliIo.rd) dpx_deserEnv
        (dpx_p2OverErrEnv A X' W) (dpx_p2OverOkEnv A X' W) w4s2_TryDecryptTopStateGuardedEnv
        (fun W' => wideM3PathCP3Envs (w4s2_TryDecryptTopStateGuardedEnv W') VerNeTightTopRawEnv))
      (cliDecPkCanonSlotEnvExact' X W) := by
  rw [canonPollGvSeqFreeEnv_eq_w4r2, cliDecPkCanonSlotEnvExact'_eq_dom0'Prev0GuardedFixed]
  exact guardIncl_of_guarded_sub fun g hfPeer hdecOk hTight evs hPoll hPrev0 =>
    w4s2_pollGv_sub_canonPostBob A X' X W g evs hfPeer hdecOk hTight hPrev0 hPoll

/-! ## Slot-`520` `canon'` Closers -/

/-- Explicit-seam Spine-C Slot-`520` `canon'` closer (`h2k520c_W4DecPkCanonSlot520OkAt`). -/
theorem h2k520c_w4DecPkCanonSlot520OkAt_of_seams {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks) (hPl_mng : mallocngLib.Placeable mmpl)
    {SendEnv : CliHooks → SendCall → List AllocEvent → Prop}
    (hG : letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hAllocFs : letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hReadSatFd : letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
          (withFdsGe3Closed (h2k_readFileSpecK cliIo.rd cliWrOk
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))))
    (hhWithFds : letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        RunHooksPlaced (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hSpqrWithFds : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
        (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits mmpl ghFixed W
        (InitialStateEnv W.C.F) (fun st msg => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
        (SendEnv W)) :
    h2k520c_W4DecPkCanonSlot520OkAt (mmpl := mmpl) hblk hext_nodup ghFixed := by
  intro h547 X W γ tp
  letI : LibsignalFullPlacement := w4wire_libsignalFullPlacementOf mpl hLs hblk hext_nodup
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  let H := cliGhostExterns ghFixed (cliExternsPlaced mmpl W)
  have hGWf : CliGhostAllocHooks fineCostModel (withFds A) cliBudgetLimits ghFixed :=
    cliGhostAllocHooks_withFds (hG γ tp)
  have hhP := hhWithFds W γ tp
  have hGetFd := dirGet_fd_ok rfl hLs (hAllocFs W γ tp) (cliBcmp_keepsFs_sat mmpl ghFixed W hhP.bcmp)
    hhP (hReadSatFd W γ tp)
  have hGetPool : subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk (withFds A) cliBudgetLimits
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd) cliRunBudgets.dirGetNeed) :=
    subroutine_ok_dirGet_withFds rfl hGetFd
  have hDeserDpxPool : subroutine_ok (dpPollProgPlaced H) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit (withFds A) cliBudgetLimits dpx_deserEnv) := by
    dsimp only [dpPollProgPlaced, stageP1ProgPlaced]
    exact sessDeserialize_of_sessDeserEvents_caller_ok (callerBlk := 518)
      (allocContractsBudgetPlaced_cli mmpl ghFixed W hGWf) (fun _ h => h)
      (fun _ hr => sessDeserEvents_mem_recordDeserializeCancelEnv hr)
  have hKitsCanon : CanonPollKitsPlacedOk (withFds A) cliBudgetLimits cliRunBudgets
      (ReadFileRuleEnvFixed cliIo.rd) dpx_deserEnv H :=
    canonPollKitsPlacedOk_of_dirGet rfl mmpl ghFixed W cliRunBudgets h547 (hAllocFs W γ tp) hhP
      hGetFd hGetPool hDeserDpxPool
  exact decPkD2cSlotOkFrozenPlacedAtPreFd_of_canon
    (decPk_d2c_canon_slot520_preFd_of_kits A cliBudgetLimits rfl
      (ReadEnv := ReadFileRuleEnvFixed cliIo.rd) (DeserEnv := dpx_deserEnv)
      (P2OverErrEnv := fun X' => dpx_p2OverErrEnv A.repAlloc X' W)
      (P2OverOkEnv := fun X' => dpx_p2OverOkEnv A.repAlloc X' W)
      (RecvBytesEnv := w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K)
      (SendEnv := SendEnv W) (tdEnv := w4s2_TryDecryptTopStateGuardedEnv)
      (verNeDecEnv := VerNeTightTopRawEnv)
      (p3c := fun W' => wideM3PathCP3Envs (w4s2_TryDecryptTopStateGuardedEnv W') VerNeTightTopRawEnv)
      (SlotEnv := cliDecPkCanonSlotEnvExact' X W) mmpl ghFixed W X
      h547 hGWf hhP hGetPool hDeserDpxPool hKitsCanon
      (cliEncodeRawPrealloc_placed_ok (serContractsX_cli_placed mmpl ghFixed W (hG γ tp)))
      (growOneVecU8_lsProg51_withLsCl_ok mmpl ghFixed W hGWf)
      (fineAesDec_budget_withFds_hookOk γ tp cliElfImage.brkStart cliBudgetLimits hPl_mng W.C.D)
      (hSpqrWithFds W γ tp) (w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty W.C.F W.Q.K)
      (fun _ _ h => h) w4wire_overPrevEncOK_of_scopeIn_v4
      (cliVerNe1e04_full_placed_ok_raw mmpl ghFixed W hGWf)
      (fun _ _ _ _ _ _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ _ _ _ _ _ h => h)
      hp3Fits_wideM3 (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (fun X' => h2k520c_guardIncl_canonPostBob A.repAlloc X' X W))

/-- Closes `h2ki_W4DecPkCanonSlot520OkK w` at `w.ghFixed = h2k_ghFixedK mpl mmpl`. -/
theorem h2k520c_w4DecPkCanonSlot520OkK_of_ghFixed {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hgh : letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      w.ghFixed = h2k_ghFixedK mpl mmpl) :
    h2ki_W4DecPkCanonSlot520OkK w := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hgh' : w.ghFixed = h2k_ghFixedK mpl mmpl := hgh
  unfold h2ki_W4DecPkCanonSlot520OkK
  change h2k520c_W4DecPkCanonSlot520OkAt (mmpl := mmpl) (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs) w.ghFixed
  rw [hgh']
  exact h2k520c_w4DecPkCanonSlot520OkAt_of_seams hLs (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    (h2k_ghFixedK mpl mmpl) w.hPl_mng
    (fun γ tp => h2kb_hole2_hG mpl mmpl hLs hMm γ tp)
    (fun W γ tp => (h2kb_hole2_runHooksPlaced mpl mmpl hLs hMm W γ tp).allocFs)
    (fun W γ tp => h2k_hole2_hReadSatK_withFds mpl mmpl hLs hMm W γ tp)
    (fun W γ tp => h2kb_runHooksPlaced_withFds mpl mmpl hLs hMm W γ tp)
    (fun W γ tp => spqrSeams_topStateGuarded_withFds mmpl (h2k_ghFixedK mpl mmpl) w.hPl_mng W γ tp
      cliElfImage.brkStart rfl (h2kb_hole2_hGSpqr_withFds mpl mmpl hLs hMm γ tp))

/-- Unconditional `h2ki_W4DecPkCanonSlot520OkK` closer at
`mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2`. -/
theorem h2k520c_w4DecPkCanonSlot520OkK_mkWitness {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 : letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    h2ki_W4DecPkCanonSlot520OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) :=
  h2k520c_w4DecPkCanonSlot520OkK_of_ghFixed (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) hLs hMm rfl

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520Canon
