/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.AssemblyPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.CmDropPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrPreKeyEncryptPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrSignalEncryptPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrStoreHookPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailDropRecordPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailDropRecordStepsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailDropRecordStepsPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFreePrevSessionsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFreePrevSessionsPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFromSessionStateErrPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailWriteResultPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg3PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.FinalPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.RootPlacedBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendTightBuckets
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendTightHelpers
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.CmDropBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.KyberMapBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItemsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.ComposeBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.CommonPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrCommon
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrSignalEncrypt
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrStoreHook
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecord
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordSteps
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordStepsPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordStepsPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessions
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessionsPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessionsPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteErr
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteErrPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteResultPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCallees
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetUuid
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.WritePaths
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SpqrV1Empty
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrAuthMergePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesIntoPbPlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrUnchunkedMergePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.TopPlacedTightBudgetR
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeStateClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializePlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeysBudget
public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.NextChainKey
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.CoreStepEnvBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceIdBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget
public import LibsignalBinary.Proofs.TripleRatchet.Mac.AddressesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.ApplyBudget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.FromBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLenBudget
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewBudget
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
public import ProofLib.SepLogic.WP.Apply
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopRegionsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
import LibsignalBinary.Proofs.PeakBudget.SpqrSendTieLemmas
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Top
import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopPhase3
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
import ProofLib.SepLogic.Entry
import ProofLib.SepLogic.WPp

/-!
# Guarded-Tight Block-464 `encrypt` (`W1`) Slot Bridge

**Checked by Lean.**

Proves the block-464 `encrypt` (`W1`) slot contract at `cliEncryptBinaryKitSlotEnvExact`
(`maxOps = 109`), assembling the block-427 `spqr::send::<Coins>` seam, hook-only
`EncTailsVTPlaced`, and the `PeerSpqrStateTight640` guard lift.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W1InnerTight

/-! ## Block-427 `spqr::send::<Coins>` Guarded-Tight Seam -/

section W1T_SendCoins

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement libsignalSessionLib lsmpl withLsCodeLoaded)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter cliTapeAt)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (ls_subroutine_ok_of_blockProgram_cro spqrCoinsAfterPlaced spqrCoinsAtPlaced
   spqrLogLevelZeroPlacedAt spqrSendDropJumpTablePlacedAt spqrSendEncodeJumpTablePlacedAt
   spqrSendFullRoPlacedAt spqrSendRoPlacedAt statesFromPbJumpTablePlacedAt)
open CryptoVerification.CliRatchet.SendPlaced (blkPC_427 blkPl_427)
open CryptoVerification.E2E (pqxdhSpqrModel)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainPB Error MlKem PqRatchetState States StatesResult V1Send V1State
   pbToPqRatchetState pqRatchetStateToPb spqrAuthApi spqrDecodeState spqrHkdfWith spqrPolyApi
   spqrV1)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded SendCall VecArg keys_ls_subroutine_ok_of_block_cro
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SpqrV1.ChainProofs (hkdfToSliceSpqrSpec)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (pqRatchetStatePBEncodedLen)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt optVersionNegotiationPBAt)
open CryptoVerification.SpqrV1.States.FromPb
  (StatesFromPbGhost resultChunkedStatesAt statesFromPbStackX v1StatePtsBound)
open CryptoVerification.SpqrV1.States.IntoPb (statesIntoPbJumpTablePlacedAt)
open CryptoVerification.SpqrV1.States.Leaves
  (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost V1InnerHeapPred canonicalV1InnerHeap decodeStateResultAt decodeStateStackX
   optProtoInnerStateAt_canonical_eq_drop optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.MessageSerialize
  (MessageSerializeGhost messageAt messageSerializeStackX)
open CryptoVerification.SpqrV1.Top.Send
  (chunkedStatesAt_entails_polyEncoderValid chunkedStatesWord0
   decodeState_spqrDeps_of_spqrDecodeState_ok headerReceived_rootKey_le_rawV1State
   optEpochSecretRegSlotAt optVN_30_to_proto post_3196_regions_eq
   pqRatchetStatePBEncodedLen_lt_of_send pre_309cc_regions_eq
   sendPanics_of_sendChainPhase_panic sendPanics_of_statesSend_panic
   send_and_draws_of_sendChainPhase_error send_and_draws_of_sendChainPhase_ok
   spqrSendCalleeStack spqrSendSavedRegs stackRestA stackRestB0_950
   stackRestC stackRestCF0_1F20 statesPolyEncoderValid statesSendArmOffset
   statesSendPostArmScratch statesSendPreArmScratch
   statesSend_ok_or_headerReceived_encaps1_of_le_64)
open CryptoVerification.SpqrV1.Top.StateSize
  (decodeState_spqrDeps_raw_le optRaw optRaw_some rawChain rawPqInner rawPqState rawV1State rawVN)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FreeOnlyEvs
   MallocngCostModelIface MallocngCostModelSound RustCliAllocBudget SeqEnv fitsEvents_append
   rustAllocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq smallAllocCost_le_738_of_le_44)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ChainEpochPlacedBudget
  (drop_chain_epoch_slice_local1_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlacedBudget
  (drop_chain_epoch_slice_local1_placed_ok_x drop_proto_spqr_chain_placed_ok_x
   ls_subroutine_ok_of_blockProgram_plain)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced CoinsFillPlacedOkX SpqrSendPlacedContractsOfEnv spqrSendPlacedEntry
   spqrSendPlacedProg spqrSendStatesJumpTablePlacedAt)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.FinalPlacedBudget
  (SpqrSendBudgetActiveContinuationPlaced
   spqrSendCoins_placed_ok_of_contracts_and_continuation_ofEnv spqrSendPhase1Rest0)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (decodeStatePlacedSpecXOfEnv messageSerializeSpecXOfEnv spqrSendCoinsPlacedSpecOfEnv
   spqrSendCoinsPlacedSpecTOfEnv statesFromPbPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudget
  (step_send_statesSend_tight_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudgetAux
  (StatesSendEnvOfEnv StatesSendTightEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget
  (HeaderReceived1aEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3PlacedBudget
  (SendPhase3EnvOfEnv step_send_from_314d8_ofEnv_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPlacedBudget (SpqrSendExtraContractsPlaced)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopRegionsPlacedBudget
  (step_send_arm_headerReceived_encaps1_none_ofEnv_placed)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (fineHookRustCliAllocBudget mallocngHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (DecodeStateTightEnv StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightBuckets
  (FineSmallEvs fineSmallEventCost fineSmallRealloc_80 fineSmallTraceCost)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightHelpers (MessageSerializeTightEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudget
  (cliSpqrSend_chainFromPb_ok cliSpqrSend_chainFromVn_ok cliSpqrSend_chainIntoPb_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget
  (cliSpqrSend_decodeState_closed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
  (CliSpqrRecvTightLinkedEnv DecodeStateBytesEnv SpqrSendCoinsTightBytesEnv
   SpqrSendCoinsTightLinkedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget
  (hpo_cliLibcruxHmac_budget_hookSat hpo_cliLibcruxHmac_mallocngHook_budget_hookSat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
  (cliExternsPlaced_noAllocShimBudget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
  (cliAuthMacHdr_placed_ok cliAuthUpdate_placed_ok cliChainAddEpoch_placed_ok
   cliChainSendKey_placed_ok cliEncodeBytesPlacedOkX cliEncodeVarintPlacedOkX
   cliEncodeVarint_placed_ok cliHkdfToVec_placed_ok cliPolyNextChunkPlacedOkX
   cliSpqrSendAllocContractsPlaced cliSpqrSendAllocContractsPlacedExt
   cliSpqrSend_coinsFill_ok_cli cliStatesPlacedSeams spqrSendExtraContractsPlaced_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesIntoPbPlacedInstBudget
  (cliStatesIntoPb_sendCoins_exact_ok)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget (chainAddEpochSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget (chainSendKeySpecX)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget (StatesIntoPbExactEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (spqrDecodeStatePlacedSpec spqrDecodeStatePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget (spqrEncodeVarintSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (statesIntoPbPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
  (MessageSerializeEnv messageSerializeEvents)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializePlacedBudget
  (messageSerialize_placed_ok_of_hooks)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)

open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_DecodeStateGuardedEnv tlb_DecodeStateTightEnv
   tlb_EpochDirectionMergeBlk325TightOkOf tlb_V1StateMergeBlk325TightOkOf
   tlb_V1StateMergePlacedTightOkOf tlb_decodeStateGuardedEnv_sub_tight_of_spqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (SpqrStateTight640)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
  (chainParamsMerge_decodeState_of_prost cliChainParams_294_cl cliDrop_267_cl cliDrop_270_cl
   cliEpochDir_299_cl cliFrom_261_cl cliGrowOne_356_cl cliLibcMemcpyBudget_at_block
   cliPushMerge_257_cl cliSessionMemcpyBudget_at_block cliSkipBudget_263_cl cliVarint_291_cl
   decodeErrorPush_of_merge epochDirectionMerge_decodeState_of_prost)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInstBudget
  (cliBytesExact_290_cro)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget
  (cliV1StateMerge_closed_cl)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudget
  (cliDeallocBudget_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
  (cliExternsPlaced_sessionMemmove_allocVm_sat cliRecvCt2PlacedAllocExt)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStatePlacedOkOfEnv spqrDecodeStatePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeStateClPlacedBudget
  (mkDecodeStateCalleeContractsClPlacedX_of_blocks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.TopPlacedTightBudgetR
  (e2b_StatesFromPbExactEnv e2b_statesFromPbExactEnv_sub_tight
   e2b_statesFromPbTightDom_of_spqrStateTight640 e2b_states_from_pb_ok_x_placed_exact)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget)
open CryptoVerification.SpqrV1.Alloc (spqrMemmoveSym)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open CryptoVerification (ls_blockPlacement_base)

theorem w1t_s427_not_fitsEnv_true (M : AllocCostModel) (lim : BudgetLimits) (st0 : M.σ) :
    ¬ FitsEnv M lim st0 (fun _ => True) :=
  fun h => absurd (h [AllocEvent.alloc (2 ^ 64)] trivial).1.1 (by decide)

/-- No allocator envelope containing `AllocEvent.alloc (2 ^ 64)` satisfies `FitsEnv`. -/
theorem w1t_s427_not_fitsEnv_of_univ {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {Env : List AllocEvent → Prop} (hUniv : ∀ evs, Env evs) :
    ¬ FitsEnv M lim st0 Env :=
  fun h => absurd (h [AllocEvent.alloc (2 ^ 64)] (hUniv _)).1.1 (by decide)

/-- Every trace in `MessageSerializeEnv spqrPolyApi x` satisfies `MessageSerializeTightEnv`. -/
theorem w1t_s427_messageSerializeEnv_to_tight
    (x : MessageSerializeGhost spqrPolyApi) {evs : List AllocEvent}
    (h : MessageSerializeEnv spqrPolyApi x evs) :
    MessageSerializeTightEnv evs := by
  subst h
  have h40 : FineSmallEvs 1 738 80 (rustAllocEvents 40 1) :=
    FineSmallEvs.rustAlloc (by decide) (by decide) (smallAllocCost_le_738_of_le_44 (by decide))
  have h80 : FineSmallEvs 1 8397 80 (rustReallocEvents 40 80 1) := by
    refine ⟨by decide, ?_, ?_⟩
    · simp only [rustReallocEvents]
      exact Nat.le_refl 8397
    · simp [rustReallocEvents, eventStepReq, eventStepAlign]
  have halloc : MessageSerializeTightEnv (rustAllocEvents 40 1) :=
    h40.mono (by decide) (by decide) (by decide)
  have hboth : MessageSerializeTightEnv (rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1) :=
    (h40.append h80).mono (by decide) (by decide) (by decide)
  unfold messageSerializeEvents
  cases x.msg.payload <;> dsimp only <;>
    first | exact halloc | (split <;> [exact halloc; exact hboth])

/-- Block-427 `SpqrSendBudgetEnv` parameterized by `DecBytesEnv` (`spqr::decode_state`) and
`FromPbValEnv` (`<States>::from_pb`), with exact `StatesSendTightEnv`,
`MessageSerializeEnv`, and `StatesIntoPbExactEnv`. -/
def w1t_s427_SpqrSendCoinsOfDecodeFromPbBytesEnv (F : ShaCompress) (K : MlKem)
    (DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop)
    (FromPbValEnv : V1State → List AllocEvent → Prop) : SpqrSendBudgetEnv :=
  fun stBs rest evs =>
    let decEnv : List AllocEvent → Prop := DecBytesEnv stBs
    let fpbEnv (v1 : V1State) : List AllocEvent → Prop := FromPbValEnv v1
    match spqrDecodeState stBs with
    | .error _ => decEnv evs
    | .ok pq =>
      match pq.inner with
      | none => SeqEnv decEnv FreeOnlyEvs evs
      | some (.v1 v1) =>
        SeqEnv decEnv
          (match States.from_pb spqrPolyApi (spqrAuthApi F) v1 with
           | .error (.panic _) => fpbEnv v1
           | .error (.err _) => SeqEnv (fpbEnv v1) FreeOnlyEvs
           | .ok st_states =>
             SeqEnv (fpbEnv v1)
               (SeqEnv (StatesSendTightEnv F K st_states rest)
                 (match st_states.send K rest with
                  | .ok (sOut, _) =>
                    SendPhase3EnvOfEnv (MessageSerializeEnv spqrPolyApi) StatesIntoPbExactEnv
                      0#64 pq sOut
                  | .error (.err _) => FreeOnlyEvs
                  | .error (.panic _) => HeaderReceived1aEnv)))
          evs

abbrev w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv (F : ShaCompress) (K : MlKem)
    (DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop)
    (FromPbValEnv : V1State → List AllocEvent → Prop)
    (x : SendCall) (evs : List AllocEvent) : Prop :=
  w1t_s427_SpqrSendCoinsOfDecodeFromPbBytesEnv F K DecBytesEnv FromPbValEnv x.st.bytes x.rest evs

private theorem w1t_s427_seqEnv_mono_left
    {P P' Q : List AllocEvent → Prop} {evs : List AllocEvent}
    (hP : ∀ e, P e → P' e) (h : SeqEnv P Q evs) :
    SeqEnv P' Q evs :=
  h.imp (hP evs) fun ⟨e1, e2, heq, h1, h2⟩ => ⟨e1, e2, heq, hP e1 h1, h2⟩

private theorem w1t_s427_hExt_withPanics_id
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym =
        cliGhostExterns gh (cliExternsPlaced mmpl W) sym := by
  intro sym _
  exact congrFun (withPanics_cliGhostExterns mmpl gh W) sym

private theorem w1t_s427_cliGhostExterns_isPanic
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym, Rust.isPanicSymbol sym = true →
      cliGhostExterns gh (cliExternsPlaced mmpl W) sym = some Rust.panicked := by
  intro sym hsym
  have h := congrFun (withPanics_cliGhostExterns mmpl gh W) sym
  simp only [Rust.withPanics, hsym, ↓reduceIte] at h
  exact h.symm

/-- Block-352 `<Message>::serialize` contract at `MessageSerializeEnv spqrPolyApi` on `blockProgram lsmpl 352`. -/
theorem w1t_s427_cliMessageSerialize_exact_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 352
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl
        (messageSerializeSpecXOfEnv spqrPolyApi M A lim (MessageSerializeEnv spqrPolyApi))) := by
  have hc := cliSpqrSendAllocContractsPlacedExt mmpl gh W hA.toCliGhostAllocHooks (fun _ _ => rfl)
  have hraw := messageSerialize_placed_ok_of_hooks spqrPolyApi A lim
    (cliGhostExterns gh (cliExternsPlaced mmpl W))
    hc.handle_error
    (hookSat_of_eq (w1t_s427_hExt_withPanics_id mmpl gh W _ (by decide))
      (cliExternsPlaced_noAllocShimBudget_sat mmpl gh W hA.shim_eq))
    hc.alloc hc.realloc
    (cliEncodeVarintPlacedOkX mmpl gh W hA (fun _ _ => rfl))
  have hcro := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hraw
  exact subroutine_ok_mono hcro
    (fun _ _ _ hpre => hpre)
    (fun (x, stB) R s0 sf hpost => by
      dsimp only [withLsCodeRoLoaded, messageSerializeSpecXOfEnv,
        LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget.messageSerializeSpecX] at hpost ⊢
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
      rcases hpost with ⟨evs, hpost⟩
      refine ⟨evs, ?_⟩
      have hpost' : sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗
          (⌜MessageSerializeEnv spqrPolyApi x evs⌝ ∗
            ((messageAt spqrPolyApi x.msgA x.msg ∗
                vecU8 A.repAlloc x.ret (x.msg.serialize x.index) ∗
                A.pool lim (M.stepEvents evs stB) sf ∗
                stackAt s0.sp messageSerializeStackX) ∗ R)) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost'
      rcases hpost' with ⟨htr, hevs, hrest⟩
      have hgoal : sf.mem ⊨ ⌜sf.trace = s0.trace ∧ MessageSerializeEnv spqrPolyApi x evs⌝ ∗
          ((messageAt spqrPolyApi x.msgA x.msg ∗
              vecU8 A.repAlloc x.ret (x.msg.serialize x.index) ∗
              A.pool lim (M.stepEvents evs stB) sf ∗
              stackAt s0.sp messageSerializeStackX) ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨htr, hevs⟩, hrest⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hgoal)
    (fun _ _ _ _ hp => hp)

/-- Lifts `w1t_s427_cliMessageSerialize_exact_placed_ok` onto `spqrSendPlacedProg`. -/
theorem w1t_s427_cliSpqrSend_messageSerialize_exact_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl
        (messageSerializeSpecXOfEnv spqrPolyApi M A lim (MessageSerializeEnv spqrPolyApi))) :=
  ls_subroutine_ok_of_blockProgram_cro
    (w1t_s427_cliMessageSerialize_exact_placed_ok mmpl gh W hA)

private theorem w1t_s427_cliSpqrSend_chainAddEpoch_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 368)
      (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith W.C.F) M A lim)) :=
  keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 368)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv
      (cliChainAddEpoch_placed_ok mmpl gh W hA (w1t_s427_hExt_withPanics_id mmpl gh W)))

private theorem w1t_s427_cliSpqrSend_chainSendKey_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 367)
      (withLsCodeRoLoaded lsmpl (chainSendKeySpecX (spqrHkdfWith W.C.F) M A lim)) :=
  keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 367)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv
      (cliChainSendKey_placed_ok mmpl gh W hA (w1t_s427_hExt_withPanics_id mmpl gh W)))

private theorem w1t_s427_cliSpqrSend_coinsFill_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    CoinsFillPlacedOkX (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  ls_subroutine_ok_of_blockProgram_plain (cliSpqrSend_coinsFill_ok_cli mmpl gh W hA)

private theorem w1t_s427_cliSpqrSend_encodeVarint_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 326)
      (withLsCodeRoLoaded lsmpl (spqrEncodeVarintSpecX A lim)) :=
  ls_subroutine_ok_of_blockProgram_cro
    (cliEncodeVarint_placed_ok mmpl gh W hA (fun _ _ => rfl))

set_option maxHeartbeats 800000 in
/-- Active continuation for block 427 composing `StatesSendTightEnv`, `MessageSerializeEnv`, and `StatesIntoPbExactEnv`. -/
theorem w1t_s427_spqrSendBudgetActiveContinuation_placed_ok_tight [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {EnvDecode : DecodeStateGhost → List AllocEvent → Prop}
    {EnvFromPb : StatesFromPbGhost → List AllocEvent → Prop}
    {Env : SendCall → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hC : SpqrSendPlacedContractsOfEnv M H_inner A lim ctl C K
      EnvDecode EnvFromPb StatesIntoPbExactEnv (MessageSerializeEnv spqrPolyApi)
      (fun x => LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.EncodeBytesEnv x.msg.length)
      (fun x => LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.EncodeBytesEnv x.msg.length)
      LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget.PolyNextChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.HeaderSentSendEkChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct1ReceivedSendEkChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct1SampledSendCt1ChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.EkReceivedCt1SampledSendCt1ChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct2SampledSendCt2ChunkEnv
      ext)
    (hEx : SpqrSendExtraContractsPlaced M A lim ctl C K ext)
    (hfits_ss : ∀ (x : SendCall) (s0 : State) (st0 : M.σ)
        (pq : PqRatchetState) (v1 : V1State)
        (st_states : States spqrPolyApi (spqrAuthApi C.F))
        (evs_dec evs_fpb : List AllocEvent),
      x.st.bytes.length < 2 ^ 32 → 64 ≤ x.rest.length →
      FitsEnv M lim st0 (Env x) →
      spqrDecodeState x.st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 = .ok st_states →
      EnvDecode { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      FitsEnv M lim (M.stepEvents (evs_dec ++ evs_fpb) st0)
        (SeqEnv (StatesSendTightEnv C.F K st_states x.rest)
          (match st_states.send K x.rest with
           | .ok (sOut, _) =>
             SendPhase3EnvOfEnv (MessageSerializeEnv spqrPolyApi) StatesIntoPbExactEnv 0#64 pq sOut
           | .error (.err _) => FreeOnlyEvs
           | .error (.panic _) => HeaderReceived1aEnv)))
    (henv_active : ∀ (x : SendCall) (s0 : State)
        (pq : PqRatchetState) (v1 : V1State)
        (st_states : States spqrPolyApi (spqrAuthApi C.F))
        (evs_dec evs_fpb evs_tail : List AllocEvent),
      x.st.bytes.length < 2 ^ 32 → 64 ≤ x.rest.length →
      spqrDecodeState x.st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 = .ok st_states →
      EnvDecode { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      (match st_states.send K x.rest with
       | .ok (sOut, _) =>
         SeqEnv (StatesSendTightEnv C.F K st_states x.rest)
           (SendPhase3EnvOfEnv (MessageSerializeEnv spqrPolyApi) StatesIntoPbExactEnv 0#64 pq sOut)
           evs_tail
       | .error (.err _) =>
         SeqEnv (StatesSendTightEnv C.F K st_states x.rest)
           FreeOnlyEvs evs_tail
       | .error (.panic _) => False) →
      Env x (evs_dec ++ evs_fpb ++ evs_tail)) :
    SpqrSendBudgetActiveContinuationPlaced M A lim ctl C.F K
      EnvDecode EnvFromPb Env ext := by
  intro x s0 st0 R hlen hrest_len hfits0 hsp_align pq v1 st_states evs_dec evs_fpb
    hdec hinner hfrom hevs_dec hevs_fpb w0 w1 hw0 sf hcrlf hpcf hrunf hspf htrf
    hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hvregsf
  rw [← M.stepEvents_append evs_dec evs_fpb st0]
  let sp : BitVec 64 := s0.sp - 0x1f80#64
  let bSt : M.σ := M.stepEvents (evs_dec ++ evs_fpb) st0
  have hfsp_align : (sp &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp_align (by decide)
  have hfit_tail :=
    hfits_ss x s0 st0 pq v1 st_states evs_dec evs_fpb hlen hrest_len hfits0
      hdec hinner hfrom hevs_dec hevs_fpb
  dsimp only [spqrSendPhase1Rest0]
  let RestPre : SepProp :=
    (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
      ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
      optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
      memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
      memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
      memRegion x.ret 72 ∗ A.pool lim bSt sf ∗
      statesFromPbJumpTablePlacedAt ∗
      spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
     (x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗
      (spqrCoinsAtPlaced ctl x.cur x.rest ∗ tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
       spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
       statesIntoPbJumpTablePlacedAt ∗ reduceTablePlacedAt))
  have hpull_valid :
      (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
        ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
        optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
        memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗
        memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool lim bSt sf ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
       (x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗
        (spqrCoinsAtPlaced ctl x.cur x.rest ∗ tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         statesIntoPbJumpTablePlacedAt ∗ reduceTablePlacedAt)) ⊢
      ⌜statesPolyEncoderValid st_states⌝ ∗
      ((stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
        ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
        optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
        memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗
        memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool lim bSt sf ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
       (x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗
        (spqrCoinsAtPlaced ctl x.cur x.rest ∗ tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         statesIntoPbJumpTablePlacedAt ∗ reduceTablePlacedAt))) := by
    have hv0 := chunkedStatesAt_entails_polyEncoderValid A.repAlloc (sp + 0x950#64) st_states
    refine Entails.trans (Entails.of_eq (show _ =
        chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗ RestPre by
      dsimp only [RestPre]; sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hv0) ?_
    exact Entails.of_eq (by dsimp only [RestPre]; sep_ac_rfl)
  refine SepWPp.weaken_pre hpull_valid (ProofLib.SepWPp.pure_elim fun hv => ?_)
  rcases statesSend_ok_or_headerReceived_encaps1_of_le_64 K hlen hrest_len hdec hinner hfrom hv with
    ⟨sOut, rest', hsend0⟩ | ⟨st, rfl, hencaps, hsend_err⟩
  · rw [hsend0] at hfit_tail
    have hfit_ss : FitsEnv M lim bSt (StatesSendTightEnv C.F K st_states x.rest) :=
      hfit_tail.seq_left
    have hdec_deps := decodeState_spqrDeps_of_spqrDecodeState_ok C.F K hdec
    have hinner_pb : (pqRatchetStateToPb pq).inner = some v1 := by
      unfold pqRatchetStateToPb; simp [hinner]
    have hraw := decodeState_spqrDeps_raw_le hdec_deps
    have hraw' :
        optRaw rawVN pq.versionNegotiation + optRaw rawChain pq.chain + rawV1State v1 ≤
        201 * x.st.bytes.length := by
      simpa only [pbToPqRatchetState, pqRatchetStateToPb, rawPqState, rawPqInner,
        hinner, Option.map, optRaw_some] using hraw
    have hchain_raw : optRaw rawChain pq.chain + 296 ≤ 2 ^ 54 := by
      omega
    rcases CryptoVerification.SpqrV1.Top.StateSize.States.from_pb_raw_le hfrom with ⟨hst0_raw, _⟩
    have hroot_len : ∀ st, st_states = .headerReceived st → st.uc.auth.rootKey.length + 32 < 2 ^ 63 := by
      intro st hst; subst hst
      have hrk := headerReceived_rootKey_le_rawV1State st
      omega
    have hpq'_len : ∀ chainPb : Option ChainPB,
        optRaw rawChain chainPb ≤ optRaw rawChain pq.chain + 624 →
        pqRatchetStatePBEncodedLen
          { versionNegotiation := pq.versionNegotiation
            chain := chainPb
            inner := some (.v1 sOut.state.into_pb) } < 2 ^ 63 :=
      fun chainPb hch_le =>
        pqRatchetStatePBEncodedLen_lt_of_send C.F K hlen hdec_deps hinner_pb hfrom hsend0 hch_le
    let RestTail : SepProp :=
      statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
      x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt
    let FrameArm : SepProp :=
      optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
      memRegion x.ret 72 ∗
      (memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
       memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
       memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp) ∗
      spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
      spqrSendEncodeJumpTablePlacedAt ∗ statesIntoPbJumpTablePlacedAt ∗ RestTail
    have hpre_arm :
        (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
          ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
          optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
          chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗
          memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
          memRegion x.ret 72 ∗ A.pool lim bSt sf ∗
          statesFromPbJumpTablePlacedAt ∗
          spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
         (x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗
          (spqrCoinsAtPlaced ctl x.cur x.rest ∗ tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
           spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
           statesIntoPbJumpTablePlacedAt ∗ reduceTablePlacedAt)) ⊢
        (stackAt sp spqrSendCalleeStack ∗ A.pool lim bSt sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          spqrLogLevelZeroPlacedAt ∗ spqrCoinsAtPlaced ctl x.cur x.rest ∗
          optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
          memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
          memRegion (sp + 0x590#64) 920 ∗
          chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗
          statesSendPreArmScratch sp) ∗ FrameArm := by
      have hvn := optVN_30_to_proto A.repAlloc sp w0 w1 pq.versionNegotiation
      have hreg := pre_309cc_regions_eq sp
      dsimp only [FrameArm, RestTail]
      refine Entails.trans (Entails.of_eq (show _ =
        (((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation) ∗
        (memRegion sp 0x30 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
          memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0)) ∗
        (stackAt sp spqrSendCalleeStack ∗ A.pool lim bSt sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          spqrLogLevelZeroPlacedAt ∗ spqrCoinsAtPlaced ctl x.cur x.rest ∗
          optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗
          memRegion x.ret 72 ∗ spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
          spqrSendEncodeJumpTablePlacedAt ∗ statesIntoPbJumpTablePlacedAt ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt) by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hvn) ?_
      rw [hreg]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpre_arm ?_
    refine step_send_statesSend_tight_placed (ctl := ctl) A lim bSt ext hA
      hEx.allocZeroed_hook hC.coinsFill_ok hEx.mlkemFromSeed_hook hEx.mlkemPk1_hook hEx.mlkemPk2_hook
      hEx.mlkemEncaps1_hook hEx.fromSeed_pk1_slice hEx.fromSeed_pk2_slice
      hEx.macHdrPinned_ok hEx.doReserve2_ok hC.encodeBytes_ok hC.polyNextChunk_ok
      hC.hkdfToVec_ok hC.authUpdate_ok
      hC.headerSentSendEkChunk_ok hC.ct1ReceivedSendEkChunk_ok hC.ct1SampledSendCt1Chunk_ok
      hC.ct2SampledSendCt2Chunk_ok hC.ekReceivedCt1SampledSendCt1Chunk_ok
      (s0 := sf) (s := sf) sp x.cur x.rest rest' pq.chain st_states sOut hroot_len hsend0 hfit_ss
      hcrlf hpcf hrunf hspf hfsp_align rfl rfl hx20 hx24 hx25 hx26 hx28 rfl rfl rfl ?_
    intro sm evs_ss hevs_ss hcrl_m hpc_m hrun_m hsp_m htr_m hx19_m _ hx22_m hx25_m hx26_m
      hx28_m hx23_none_m hpstate_m hvregs_m
    rw [htrf] at htr_m
    rw [hx19] at hx19_m
    rw [hx28] at hx28_m
    have hfit_p3 : FitsEnv M lim (M.stepEvents evs_ss bSt)
        (SendPhase3EnvOfEnv (MessageSerializeEnv spqrPolyApi) StatesIntoPbExactEnv sp pq sOut) :=
      hfit_tail.seq_right hevs_ss
    let Rest314d8 : SepProp :=
      spqrCoinsAfterPlaced ctl x.cur x.rest (x.rest.length - rest'.length) ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      spqrLogLevelZeroPlacedAt ∗ RestTail
    have hP3196_eq :
        (optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          chunkedStatesAt A.repAlloc (sp + 0x190#64) sOut.state ∗
          memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
          memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
          memRegion (sp + 0x950#64) 928 ∗
          optEpochSecretRegSlotAt A.repAlloc sp (sm.readReg64 .x21) (sm.readReg64 .x27) sOut.key ∗
          messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗
          statesSendPostArmScratch sp ∗
          spqrCoinsAfterPlaced ctl x.cur x.rest (x.rest.length - rest'.length) ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          spqrLogLevelZeroPlacedAt ∗ A.pool lim (M.stepEvents evs_ss bSt) sm ∗
          stackAt sp spqrSendCalleeStack) ∗ FrameArm =
        (optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
          optEpochSecretRegSlotAt A.repAlloc sp (sm.readReg64 .x21) (sm.readReg64 .x27) sOut.key ∗
          memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
          memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗
          memRegion (sp + 0xd40#64) 80 ∗ memRegion (sp + 0xde0#64) 80 ∗
          memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x28#64) 8 ∗
          memRegion (sp + 0x8#64) 8 ∗ memRegion x.ret 72 ∗
          chunkedStatesAt A.repAlloc (sp + 0x190#64) sOut.state ∗
          A.pool lim (M.stepEvents evs_ss bSt) sm ∗ stackAt sp spqrSendCalleeStack ∗
          memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
          memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
          memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
          messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗
          stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
          spqrSendEncodeJumpTablePlacedAt ∗ statesIntoPbJumpTablePlacedAt ∗ Rest314d8) := by
      have hreg := post_3196_regions_eq sp
      calc
        _ = (memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
              memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
              statesSendPostArmScratch sp ∗
              memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
              memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
              memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp) ∗
            (optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
              optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
              optEpochSecretRegSlotAt A.repAlloc sp (sm.readReg64 .x21) (sm.readReg64 .x27) sOut.key ∗
              memRegion x.ret 72 ∗ chunkedStatesAt A.repAlloc (sp + 0x190#64) sOut.state ∗
              A.pool lim (M.stepEvents evs_ss bSt) sm ∗ stackAt sp spqrSendCalleeStack ∗
              memRegion (sp + 0x950#64) 928 ∗
              messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗
              spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
              spqrSendEncodeJumpTablePlacedAt ∗ statesIntoPbJumpTablePlacedAt ∗ Rest314d8) := by
          dsimp only [FrameArm, Rest314d8]; sep_ac_rfl
        _ = _ := by rw [hreg]; sep_ac_rfl
    rw [hP3196_eq]
    refine step_send_from_314d8_ofEnv_placed (M.stepEvents evs_ss bSt) hA
      hEx.panic_hook hEx.panicSubOverflow_hook
      hEx.dropChainEpochSlice_raw_ok hEx.dropChunkedStates_ok hC.chainFromPb_ok hC.chainFromVn_ok
      hC.chainAddEpoch_ok hC.chainSendKey_ok hC.chainIntoPb_ok hC.messageSerialize_ok
      hC.statesIntoPb_ok s0 sm sp x.ret (sm.readReg64 .x21) (sm.readReg64 .x27) (sm.readReg64 .x23)
      pq sOut hfit_p3 Rest314d8 R _ hsp_align rfl hchain_raw hpq'_len hcrl_m
      hpc_m hrun_m hsp_m htr_m hx19_m rfl hx22_m rfl hx25_m hx26_m rfl hx28_m hx23_none_m hpstate_m
      ?hφ ?herr ?hok (hvregs_m.trans hvregsf)
    case hφ =>
      rintro s_pan ⟨hch_pan, htr_p⟩
      exact ⟨sendPanics_of_sendChainPhase_panic hdec hinner hfrom hsend0 hch_pan,
        htr_p ▸ List.prefix_refl s0.trace⟩
    case herr =>
      intro err evs_p3 hch hevs_p3 sf' Pf' _ _ hPf' hsp_f hcs_f htr_f
      have ⟨hsend_eq, hdraws_eq, hnp⟩ :=
        send_and_draws_of_sendChainPhase_error hdec hinner hfrom hsend0 hch
      have hevs_all : Env x (evs_dec ++ evs_fpb ++ (evs_ss ++ evs_p3)) :=
        henv_active x s0 pq v1 st_states evs_dec evs_fpb (evs_ss ++ evs_p3)
          hlen hrest_len hdec hinner hfrom hevs_dec hevs_fpb
          (by rw [hsend0]; exact SeqEnv.append hevs_ss hevs_p3)
      refine ⟨hsp_f, hcs_f, evs_dec ++ evs_fpb ++ (evs_ss ++ evs_p3), hevs_all, ?_⟩
      have hstep_eq :
          M.stepEvents (evs_dec ++ evs_fpb ++ (evs_ss ++ evs_p3)) st0 =
            M.stepEvents evs_p3 (M.stepEvents evs_ss bSt) := by
        rw [M.stepEvents_append, M.stepEvents_append]
      rw [hsend_eq, hdraws_eq, hstep_eq]
      refine Entails.pure_right ⟨Nat.sub_le _ _, htr_f, hnp⟩ (Entails.trans hPf' ?_)
      dsimp only [Rest314d8, RestTail, spqrSendFullRoPlacedAt, spqrSendRoPlacedAt]
      have hinto_eq :
          CryptoVerification.Cli.SpqrV1.Top.Send.statesIntoPbJumpTablePlacedAt =
            statesIntoPbJumpTablePlacedAt := rfl
      rw [hinto_eq]
      exact Entails.of_eq (by sep_ac_rfl)
    case hok =>
      intro idx msgKey chainPb salt evs_p3 hch hsalt hevs_p3 sf' Pf' _ _ hPf' hsp_f hcs_f htr_f
      have ⟨hsend_eq, hdraws_eq, hnp⟩ :=
        send_and_draws_of_sendChainPhase_ok hdec hinner hfrom hsend0 hch hsalt
      have hevs_all : Env x (evs_dec ++ evs_fpb ++ (evs_ss ++ evs_p3)) :=
        henv_active x s0 pq v1 st_states evs_dec evs_fpb (evs_ss ++ evs_p3)
          hlen hrest_len hdec hinner hfrom hevs_dec hevs_fpb
          (by rw [hsend0]; exact SeqEnv.append hevs_ss hevs_p3)
      refine ⟨hsp_f, hcs_f, evs_dec ++ evs_fpb ++ (evs_ss ++ evs_p3), hevs_all, ?_⟩
      have hstep_eq :
          M.stepEvents (evs_dec ++ evs_fpb ++ (evs_ss ++ evs_p3)) st0 =
            M.stepEvents evs_p3 (M.stepEvents evs_ss bSt) := by
        rw [M.stepEvents_append, M.stepEvents_append]
      rw [hsend_eq, hdraws_eq, hstep_eq]
      refine Entails.pure_right ⟨Nat.sub_le _ _, htr_f, hnp⟩ (Entails.trans hPf' ?_)
      dsimp only [Rest314d8, RestTail, spqrSendFullRoPlacedAt, spqrSendRoPlacedAt]
      have hinto_eq :
          CryptoVerification.Cli.SpqrV1.Top.Send.statesIntoPbJumpTablePlacedAt =
            statesIntoPbJumpTablePlacedAt := rfl
      rw [hinto_eq]
      exact Entails.of_eq (by sep_ac_rfl)
  · rw [hsend_err] at hfit_tail
    have hct1_err : ∀ v, st.send_ct1_chunk K x.rest ≠ .ok v := by
      intro ⟨outSt, chunk, ek, tape1⟩ hok
      simp [States.send, StatesResult.ofPanic, hok, Bind.bind, Except.bind] at hsend_err
    have hss_nil : StatesSendTightEnv C.F K (.headerReceived st) x.rest [] := by
      dsimp only [StatesSendTightEnv, StatesSendEnvOfEnv]
      cases h : st.send_ct1_chunk K x.rest with
      | ok v => exact False.elim (hct1_err v h)
      | error _ => rfl
    have hfit_hr : FitsEnv M lim bSt HeaderReceived1aEnv :=
      hfit_tail.seq_right hss_nil
    have hpan : (spqrV1 C.F K).sendPanics x.st.bytes x.rest :=
      sendPanics_of_statesSend_panic hdec hinner hfrom hsend_err
    let FramePan : SepProp :=
      ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
      optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
      (memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
       memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
       memRegion (sp + 0x590#64) 920 ∗
       (memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
        memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp)) ∗
      memRegion x.ret 72 ∗ statesFromPbJumpTablePlacedAt ∗
      spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0 ∗
      x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗
      tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
      spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
      statesIntoPbJumpTablePlacedAt ∗ reduceTablePlacedAt
    have hpre_pan :
        (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
          ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
          optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
          chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerReceived st) ∗
          memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
          memRegion x.ret 72 ∗ A.pool lim bSt sf ∗
          statesFromPbJumpTablePlacedAt ∗
          spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
         (x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗
          (spqrCoinsAtPlaced ctl x.cur x.rest ∗ tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
           spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
           statesIntoPbJumpTablePlacedAt ∗ reduceTablePlacedAt)) ⊢
        (stackAt sp spqrSendCalleeStack ∗ A.pool lim bSt sf ∗ spqrCoinsAtPlaced ctl x.cur x.rest ∗
          chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerReceived st) ∗
          statesSendPreArmScratch sp) ∗ FramePan := by
      have hreg := pre_309cc_regions_eq sp
      refine Entails.of_eq ?_
      calc
        _ = (memRegion sp 0x30 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
              memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0)) ∗
            (stackAt sp spqrSendCalleeStack ∗ A.pool lim bSt sf ∗
              spqrCoinsAtPlaced ctl x.cur x.rest ∗
              chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerReceived st) ∗
              ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
              optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
              optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
              memRegion x.ret 72 ∗ statesFromPbJumpTablePlacedAt ∗
              spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0 ∗
              x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗
              tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
              spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
              statesIntoPbJumpTablePlacedAt ∗ reduceTablePlacedAt) := by sep_ac_rfl
        _ = _ := by dsimp only [FramePan]; rw [hreg]; sep_ac_rfl
    exact SepWPp.weaken_pre hpre_pan
      (step_send_arm_headerReceived_encaps1_none_ofEnv_placed
        (R := R) (Frame := FramePan)
        hA hEx.allocZeroed_hook hC.coinsFill_ok hEx.mlkemEncaps1_hook hEx.unwrapFailed_hook
        sp x.cur x.rest (by omega) st hencaps hfit_hr hpan hcrlf hpcf hrunf hspf hfsp_align
        htrf hx24 hx26 hx28 rfl)

/-- Block-427 `subroutine_ok` on `spqrSendPlacedProg` at `w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv`. -/
theorem w1t_s427_spqrSendCoins_placed_ok_of_contracts_tight [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    {FromPbValEnv : V1State → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hC : SpqrSendPlacedContractsOfEnv M H_inner A lim ctl C K
      (fun g => DecBytesEnv g.st.bytes)
      (fun g => FromPbValEnv g.pb)
      StatesIntoPbExactEnv (MessageSerializeEnv spqrPolyApi)
      (fun x => LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.EncodeBytesEnv x.msg.length)
      (fun x => LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.EncodeBytesEnv x.msg.length)
      LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget.PolyNextChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.HeaderSentSendEkChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct1ReceivedSendEkChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct1SampledSendCt1ChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.EkReceivedCt1SampledSendCt1ChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct2SampledSendCt2ChunkEnv
      ext)
    (hEx : SpqrSendExtraContractsPlaced M A lim ctl C K ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim ctl (spqrV1 C.F K)
          (w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv C.F K DecBytesEnv FromPbValEnv))) := by
  refine spqrSendCoins_placed_ok_of_contracts_and_continuation_ofEnv hC ?_ ?_ ?_ ?_ ?_
    (w1t_s427_spqrSendBudgetActiveContinuation_placed_ok_tight hA hC hEx ?_ ?_)
  · intro x _ st0 _ _ hfits0 evs hevs
    apply hfits0 evs
    dsimp only [w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv, w1t_s427_SpqrSendCoinsOfDecodeFromPbBytesEnv]
    cases spqrDecodeState x.st.bytes with
    | error _ => exact hevs
    | ok pq =>
      dsimp only
      cases pq.inner with
      | none => exact Or.inl hevs
      | some inner =>
        cases inner with
        | v1 _ => exact Or.inl hevs
  · intro x _ st0 pq v1 evs_dec _ _ hfits0 hdec hinner hevs_dec evs_fpb hevs_fpb
    refine ((fitsEvents_append M lim evs_dec evs_fpb st0).mp
      (hfits0 (evs_dec ++ evs_fpb) ?_)).2
    simp only [w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv, w1t_s427_SpqrSendCoinsOfDecodeFromPbBytesEnv,
      hdec, hinner]
    cases States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 with
    | error err =>
      cases err with
      | panic _ => exact SeqEnv.append hevs_dec hevs_fpb
      | err _ => exact SeqEnv.append hevs_dec (SeqEnv.inl hevs_fpb)
    | ok _ => exact SeqEnv.append hevs_dec (SeqEnv.inl hevs_fpb)
  · intro x _ _ evs_dec _ hdec hevs_dec
    simp only [w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv, w1t_s427_SpqrSendCoinsOfDecodeFromPbBytesEnv, hdec]
    exact hevs_dec
  · intro x _ pq evs_dec evs_drop _ hdec hinner hevs_dec hevs_drop
    simp only [w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv, w1t_s427_SpqrSendCoinsOfDecodeFromPbBytesEnv,
      hdec, hinner]
    exact SeqEnv.append hevs_dec hevs_drop
  · intro x _ pq v1 _ evs_dec evs_fpb evs_drop _ hdec hinner hfrom hevs_dec hevs_fpb hevs_drop
    simp only [w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv, w1t_s427_SpqrSendCoinsOfDecodeFromPbBytesEnv,
      hdec, hinner, hfrom]
    rw [List.append_assoc]
    exact SeqEnv.append hevs_dec (SeqEnv.append hevs_fpb hevs_drop)
  · intro x _ st0 pq v1 st_states evs_dec evs_fpb _ _ hfits0 hdec hinner hfrom
      hevs_dec hevs_fpb evs_tail
    cases h : st_states.send K x.rest with
    | ok val =>
      rcases val with ⟨sOut, _⟩
      intro htail
      refine ((fitsEvents_append M lim (evs_dec ++ evs_fpb) evs_tail st0).mp
        (hfits0 ((evs_dec ++ evs_fpb) ++ evs_tail) ?_)).2
      simp only [w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv, w1t_s427_SpqrSendCoinsOfDecodeFromPbBytesEnv,
        hdec, hinner, hfrom, h]
      rw [List.append_assoc]
      exact SeqEnv.append hevs_dec (SeqEnv.append hevs_fpb htail)
    | error err =>
      cases err with
      | err _ =>
        intro htail
        refine ((fitsEvents_append M lim (evs_dec ++ evs_fpb) evs_tail st0).mp
          (hfits0 ((evs_dec ++ evs_fpb) ++ evs_tail) ?_)).2
        simp only [w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv, w1t_s427_SpqrSendCoinsOfDecodeFromPbBytesEnv,
          hdec, hinner, hfrom, h]
        rw [List.append_assoc]
        exact SeqEnv.append hevs_dec (SeqEnv.append hevs_fpb htail)
      | panic _ =>
        intro htail
        refine ((fitsEvents_append M lim (evs_dec ++ evs_fpb) evs_tail st0).mp
          (hfits0 ((evs_dec ++ evs_fpb) ++ evs_tail) ?_)).2
        simp only [w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv, w1t_s427_SpqrSendCoinsOfDecodeFromPbBytesEnv,
          hdec, hinner, hfrom, h]
        rw [List.append_assoc]
        exact SeqEnv.append hevs_dec (SeqEnv.append hevs_fpb htail)
  · intro x _ pq v1 st_states evs_dec evs_fpb evs_tail _ _ hdec hinner hfrom
      hevs_dec hevs_fpb htail
    simp only [w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv, w1t_s427_SpqrSendCoinsOfDecodeFromPbBytesEnv,
      hdec, hinner, hfrom]
    rw [List.append_assoc]
    refine SeqEnv.append hevs_dec (SeqEnv.append hevs_fpb ?_)
    cases h : st_states.send K x.rest with
    | ok val =>
      rcases val with ⟨sOut, _⟩
      rw [h] at htail
      exact htail
    | error err =>
      cases err with
      | err _ =>
        rw [h] at htail
        exact htail
      | panic _ =>
        rw [h] at htail
        exact False.elim htail

/-- Instantiates `DecodeStateCalleeContractsClPlacedX` on `cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem w1t_decodeStateCalleeContractsClPlacedX_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    DecodeStateCalleeContractsClPlacedX canonicalV1InnerHeap A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
    cliGhostExterns gh (cliExternsPlaced mmpl W) sym =
      cliGhostExterns gh (cliExternsPlaced mmpl W) sym :=
    fun _ _ => rfl
  have hExt_wp := w1t_s427_hExt_withPanics_id mmpl gh W
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

/-- Lifts `tlb_V1StateMergePlacedTightOkOf` from `blockProgram lsmpl 298` onto block 325's rebased callee program. -/
theorem w1t_v1StateMergeBlk325_of_own [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxOps : Nat} {ext : String → Option (State → State)}
    (hOwn : tlb_V1StateMergePlacedTightOkOf A lim maxOps ext) :
    tlb_V1StateMergeBlk325TightOkOf A lim maxOps ext :=
  keys_ls_subroutine_ok_of_block_cro
    (callerProg := (blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (hcallee_prog := ⟨rfl, IsLsBlockProg.externs_eq (prog :=
      (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_298).rebase
        (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_298).base (fun _ => none))⟩)
    (bi := 619) (bj := 619) hOwn (by decide) (by decide) (by decide)

/-- Byte-slice projection of `tlb_DecodeStateGuardedEnv F K`. -/
def w1t_DecGuardedBytes (F : ShaCompress) (K : MlKem) (bs : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  tlb_DecodeStateGuardedEnv F K ⟨⟨0#64, 0#64, 0#64, bs⟩, 0#64⟩ evs

private theorem w1t_hookSat_allocMemcpyVm_of_framelessAcp
    {hooks : String → Option (State → State)} {name : String}
    (h : HookSat hooks name
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec) :
    HookSat hooks name LibsignalBinary.Heap.allocMemcpyVmSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  dsimp only [LibsignalBinary.Heap.allocMemcpyVmSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_bv, hlt⟩, hm⟩
  have hx2 : (s0.readReg64 .x2).toNat = bs.length := by
    rw [hx2_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hpre' : s0.mem ⊨
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec.pre
        (dst, src, bs) s0 ∗ R := by
    dsimp only [LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  rcases hsat (dst, src, bs) R s0 hrun hpre' hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalBinary.Heap.allocMemcpyVmSpec,
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr hrest

private theorem w1t_cliSpqrSend_decodeState_guarded_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h325 : DecodeStatePlacedOkOfEnv canonicalV1InnerHeap A lim
      (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
      (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
      (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecXOfEnv canonicalV1InnerHeap M A lim
          (fun g => w1t_DecGuardedBytes W.C.F W.Q.K g.st.bytes))) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hblk : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics H))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (spqrDecodeStatePlacedSpecOfEnv canonicalV1InnerHeap A lim
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) := by
    have h0 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics H))
        (blkPl_325).base
        (withLsCodeRoLoaded lsmpl
          (spqrDecodeStatePlacedSpecOfEnv canonicalV1InnerHeap A lim
            (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
            (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) := h325
    rwa [IsLsBlockProg.eq_blockProgram
          (prog := (blkPC_325).rebase (blkPl_325).base (Rust.withPanics H)),
        ls_blockPlacement_base (i := 325)] at h0
  have hok : subroutine_ok (spqrSendPlacedProg H) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (spqrDecodeStatePlacedSpecOfEnv canonicalV1InnerHeap A lim
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) :=
    ls_subroutine_ok_of_blockProgram_cro hblk
  exact subroutine_ok_mono hok
    (fun (g, stB) R s0 hpre => by
      dsimp only [withLsCodeRoLoaded, spqrDecodeStatePlacedSpecOfEnv,
        decodeStatePlacedSpecXOfEnv] at hpre ⊢
      have hpre' : s0.mem ⊨
          ⌜s0.readReg64 .x8 = g.outPtr ∧ s0.readReg64 .x0 = g.st.v ∧
            g.st.bytes.length < 2 ^ 32 ∧
            FitsEnv M lim stB (w1t_DecGuardedBytes W.C.F W.Q.K g.st.bytes)⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
            (v1StateJumpTablesPlacedAt ∗ g.st.at A.repAlloc ∗ memRegion g.outPtr 352 ∗
              A.pool lim stB s0 ∗ stackAt s0.sp decodeStateStackX ∗ R)) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
      rw [satisfies_pure_sepConj] at hpre'
      rcases hpre' with ⟨⟨hx8, hx0, hlen, hfit⟩, hrest⟩
      have hgoal : s0.mem ⊨
          ⌜s0.readReg64 .x8 = g.outPtr ∧ s0.readReg64 .x0 = g.st.v ∧
            g.st.bytes.length < 2 ^ 32 ∧
            FitsEnv M lim stB (tlb_DecodeStateGuardedEnv W.C.F W.Q.K g)⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
            (v1StateJumpTablesPlacedAt ∗ g.st.at A.repAlloc ∗ memRegion g.outPtr 352 ∗
              A.pool lim stB s0 ∗ stackAt s0.sp decodeStateStackX ∗ R)) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx8, hx0, hlen, hfit⟩, hrest⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hgoal)
    (fun (g, stB) R s0 sf hpost => by
      dsimp only [withLsCodeRoLoaded, spqrDecodeStatePlacedSpecOfEnv,
        decodeStatePlacedSpecXOfEnv] at hpost ⊢
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
      rcases hpost with ⟨evs, hpost⟩
      refine ⟨evs, ?_⟩
      have hpost' : sf.mem ⊨
          ⌜sf.trace = s0.trace ∧ tlb_DecodeStateGuardedEnv W.C.F W.Q.K g evs⌝ ∗
          (v1StateJumpTablesPlacedAt ∗ g.st.at A.repAlloc ∗
            decodeStateResultAt canonicalV1InnerHeap A.repAlloc g.outPtr
              (spqrDecodeState g.st.bytes) ∗
            A.pool lim (M.stepEvents evs stB) sf ∗ stackAt s0.sp decodeStateStackX ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost'
      rcases hpost' with ⟨⟨htr, hevs⟩, hrest⟩
      have hgoal : sf.mem ⊨
          ⌜sf.trace = s0.trace ∧ w1t_DecGuardedBytes W.C.F W.Q.K g.st.bytes evs⌝ ∗
          (v1StateJumpTablesPlacedAt ∗ g.st.at A.repAlloc ∗
            decodeStateResultAt canonicalV1InnerHeap A.repAlloc g.outPtr
              (spqrDecodeState g.st.bytes) ∗
            A.pool lim (M.stepEvents evs stB) sf ∗ stackAt s0.sp decodeStateStackX ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨htr, hevs⟩, hrest⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hgoal)
    (fun _ _ _ _ hp => hp)

private theorem w1t_cliSpqrSend_statesFromPb_exact_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (statesFromPbPlacedSpecXOfEnv M A lim W.C.F
          (fun g => e2b_StatesFromPbExactEnv W.C.F g.pb))) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hRecv := cliRecvCt2PlacedAllocExt mmpl gh W hA (fun _ _ => rfl)
  have hFromPbHooks : FromPbAllocHooksBudget M A lim H :=
    {
      panic_ok := hRecv.handleError
      shim := hRecv.shim
      alloc := hRecv.alloc
      dealloc := hRecv.dealloc
      memcpy := w1t_hookSat_allocMemcpyVm_of_framelessAcp hRecv.memcpy
    }
  have hmemmove0 : HookSat (Rust.withPanics H) spqrMemmoveSym
      (withAllocVmPreserved (CryptoVerification.LibsignalTripleRatchet.sessionMemmoveSpec 0)) :=
    hookSat_of_eq (w1t_s427_hExt_withPanics_id mmpl gh W _ (by decide))
      (cliExternsPlaced_sessionMemmove_allocVm_sat mmpl gh W)
  have hok333 := e2b_states_from_pb_ok_x_placed_exact (F := W.C.F) hFromPbHooks hmemmove0
  have hok : subroutine_ok (spqrSendPlacedProg H) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.statesFromPbPlacedSpecXOfEnv
          M A lim W.C.F (e2b_StatesFromPbExactEnv W.C.F))) :=
    ls_subroutine_ok_of_blockProgram_cro hok333
  have hjt_eq :
      CryptoVerification.SpqrV1.States.FromPb.statesFromPbJumpTablePlacedAt =
        statesFromPbJumpTablePlacedAt := rfl
  exact subroutine_ok_mono hok
    (fun (g, stB) R s0 hpre => by
      dsimp only [withLsCodeRoLoaded,
        LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.statesFromPbPlacedSpecXOfEnv,
        LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv,
        statesFromPbPlacedSpecXOfEnv] at hpre ⊢
      rw [hjt_eq]
      have hpre' : s0.mem ⊨
          ⌜s0.readReg64 .x8 = g.out ∧ s0.readReg64 .x0 = g.pbA ∧
            v1StatePtsBound g.pb ∧
            FitsEnv M lim stB (e2b_StatesFromPbExactEnv W.C.F g.pb)⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
            (memRegion g.out chunkedStatesSize ∗
              optProtoInnerStateAt A.repAlloc g.pbA g.pb.innerState ∗
              statesFromPbJumpTablePlacedAt ∗ A.pool lim stB s0 ∗
              stackAt s0.sp statesFromPbStackX ∗ R)) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre')
    (fun (g, stB) R s0 sf hpost => by
      dsimp only [withLsCodeRoLoaded,
        LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.statesFromPbPlacedSpecXOfEnv,
        LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv,
        statesFromPbPlacedSpecXOfEnv] at hpost ⊢
      rw [hjt_eq] at hpost
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
      rcases hpost with ⟨evs, hpost⟩
      refine ⟨evs, ?_⟩
      have hpost' : sf.mem ⊨
          ⌜sf.trace = s0.trace ∧ e2b_StatesFromPbExactEnv W.C.F g.pb evs⌝ ∗
          (resultChunkedStatesAt A.repAlloc (F := W.C.F) g.out
              (States.from_pb spqrPolyApi (spqrAuthApi W.C.F) g.pb) ∗
            memRegion g.pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs stB) sf ∗
            stackAt s0.sp statesFromPbStackX ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost')
    (fun _ _ _ _ hp => hp)

private theorem w1t_spqrSendPlacedContracts_tight_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h325 : DecodeStatePlacedOkOfEnv canonicalV1InnerHeap A lim
      (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
      (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    SpqrSendPlacedContractsOfEnv M canonicalV1InnerHeap A lim 0#64 W.C W.Q.K
      (fun g => w1t_DecGuardedBytes W.C.F W.Q.K g.st.bytes)
      (fun g => e2b_StatesFromPbExactEnv W.C.F g.pb)
      StatesIntoPbExactEnv
      (MessageSerializeEnv spqrPolyApi)
      (fun x => LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.EncodeBytesEnv x.msg.length)
      (fun x => LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.EncodeBytesEnv x.msg.length)
      LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget.PolyNextChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.HeaderSentSendEkChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct1ReceivedSendEkChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct1SampledSendCt1ChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.EkReceivedCt1SampledSendCt1ChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct2SampledSendCt2ChunkEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have hAlloc := cliSpqrSendAllocContractsPlaced mmpl gh W hA.toCliGhostAllocHooks
  have hS := cliStatesPlacedSeams mmpl gh W hA hHmac
  exact
    {
      h_inner_eq := optProtoInnerStateAt_canonical_eq_drop A.repAlloc
      alloc := hAlloc
      coinsFill_ok := w1t_s427_cliSpqrSend_coinsFill_on mmpl gh W hA.toCliGhostAllocHooks
      decodeState_ok := w1t_cliSpqrSend_decodeState_guarded_on mmpl gh W h325
      statesFromPb_ok := w1t_cliSpqrSend_statesFromPb_exact_on mmpl gh W hA
      statesIntoPb_ok := cliStatesIntoPb_sendCoins_exact_ok mmpl gh W hA.toCliGhostAllocHooks
      chainFromPb_ok := cliSpqrSend_chainFromPb_ok mmpl gh W hA.toCliGhostAllocHooks
      chainFromVn_ok := cliSpqrSend_chainFromVn_ok mmpl gh W hA.toCliGhostAllocHooks
      chainAddEpoch_ok := w1t_s427_cliSpqrSend_chainAddEpoch_on mmpl gh W hA.toCliGhostAllocHooks
      chainSendKey_ok := w1t_s427_cliSpqrSend_chainSendKey_on mmpl gh W hA.toCliGhostAllocHooks
      chainIntoPb_ok := cliSpqrSend_chainIntoPb_ok mmpl gh W hA.toCliGhostAllocHooks
      messageSerialize_ok := w1t_s427_cliSpqrSend_messageSerialize_exact_on mmpl gh W hA
      encodeVarint_ok := w1t_s427_cliSpqrSend_encodeVarint_on mmpl gh W hA
      authMacHdr_ok := cliAuthMacHdr_placed_ok mmpl gh W hA hHmac
      authUpdate_ok := cliAuthUpdate_placed_ok mmpl gh W hA
      hkdfToVec_ok := cliHkdfToVec_placed_ok mmpl gh W hA
      encodeBytes_ok := cliEncodeBytesPlacedOkX mmpl gh W hA.toCliGhostAllocHooks
      polyNextChunk_ok := cliPolyNextChunkPlacedOkX mmpl gh W hA.toCliGhostAllocHooks
      headerSentSendEkChunk_ok := hS.headerSentSendEkChunk_on
      ct1ReceivedSendEkChunk_ok := hS.ct1ReceivedSendEkChunk_on
      ct1SampledSendCt1Chunk_ok := hS.ct1SampledSendCt1Chunk_on
      ekReceivedCt1SampledSendCt1Chunk_ok := hS.ekReceivedCt1SampledSendCt1Chunk_on
      ct2SampledSendCt2Chunk_ok := hS.ct2SampledSendCt2Chunk_on
      dropProtoChain_ok := drop_proto_spqr_chain_placed_ok_x hAlloc
      dropChainEpochSlice_ok := drop_chain_epoch_slice_local1_placed_ok_x hAlloc
    }

/-- Tight `SpqrSendBudgetEnv` at `(tlb_DecodeStateTightEnv, StatesFromPbTightEnv)` (`maxOps = 109`). -/
def w1t_SendTightBytesEnv (F : ShaCompress) (K : MlKem) : SpqrSendBudgetEnv :=
  w1t_s427_SpqrSendCoinsOfDecodeFromPbBytesEnv F K
    (fun _ => tlb_DecodeStateTightEnv)
    (fun _ => StatesFromPbTightEnv)

/-- `SpqrStateTight640 F K`-guarded wrapper around `w1t_SendTightBytesEnv F K`. -/
def w1t_SendGuardedBytesEnv (F : ShaCompress) (K : MlKem) : SpqrSendBudgetEnv :=
  fun stBs rest evs => SpqrStateTight640 F K stBs → w1t_SendTightBytesEnv F K stBs rest evs

def w1t_SendGuardedEnv (F : ShaCompress) (K : MlKem) (sc : SendCall) (evs : List AllocEvent) : Prop :=
  w1t_SendGuardedBytesEnv F K sc.st.bytes sc.rest evs

private theorem w1t_sendOfDecodeFromPb_sub_tight
    {F : ShaCompress} {K : MlKem} {x : SendCall} {evs : List AllocEvent}
    (hG : SpqrStateTight640 F K x.st.bytes)
    (hevs : w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv F K
      (w1t_DecGuardedBytes F K) (e2b_StatesFromPbExactEnv F) x evs) :
    w1t_SendTightBytesEnv F K x.st.bytes x.rest evs := by
  have hDec : ∀ e, w1t_DecGuardedBytes F K x.st.bytes e → tlb_DecodeStateTightEnv e :=
    fun _ he => tlb_decodeStateGuardedEnv_sub_tight_of_spqrStateTight640 hG he
  have hFromPb : ∀ pq v1 e,
      spqrDecodeState x.st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      e2b_StatesFromPbExactEnv F v1 e → StatesFromPbTightEnv e :=
    fun _ _ _ hdec hinner he =>
      e2b_statesFromPbExactEnv_sub_tight
        (e2b_statesFromPbTightDom_of_spqrStateTight640 hG hdec hinner) he
  dsimp only [w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv, w1t_SendTightBytesEnv,
    w1t_s427_SpqrSendCoinsOfDecodeFromPbBytesEnv] at hevs ⊢
  cases hdec : spqrDecodeState x.st.bytes with
  | error _ =>
    rw [hdec] at hevs
    exact hDec evs hevs
  | ok pq =>
    rw [hdec] at hevs
    dsimp only at hevs ⊢
    cases hinner : pq.inner with
    | none =>
      rw [hinner] at hevs
      exact w1t_s427_seqEnv_mono_left hDec hevs
    | some inner =>
      cases inner with
      | v1 v1 =>
        rw [hinner] at hevs
        dsimp only at hevs ⊢
        rcases hevs with h1 | ⟨e1, e2, rfl, h1, h2⟩
        · exact Or.inl (hDec evs h1)
        · refine SeqEnv.append (hDec e1 h1) ?_
          cases hfpb : States.from_pb spqrPolyApi (spqrAuthApi F) v1 with
          | error err =>
            cases err with
            | panic _ =>
              rw [hfpb] at h2
              exact hFromPb pq v1 e2 hdec hinner h2
            | err _ =>
              rw [hfpb] at h2
              exact w1t_s427_seqEnv_mono_left (hFromPb pq v1 · hdec hinner) h2
          | ok st_states =>
            rw [hfpb] at h2
            exact w1t_s427_seqEnv_mono_left (hFromPb pq v1 · hdec hinner) h2

/-- Block-427 `spqr::send::<Coins>` contract at `w1t_SendGuardedEnv` from `DecodeStatePlacedOkOfEnv`. -/
theorem w1t_cliSpqrSendCoins_placed_ok_guarded_of_decodeState [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl_mng : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim gh)
    (h325 : DecodeStatePlacedOkOfEnv canonicalV1InnerHeap
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
      (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
      (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv
          fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) (w1t_SendGuardedEnv W.C.F W.Q.K))) := by
  let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hHmac := hpo_cliLibcruxHmac_budget_hookSat γ mmpl tp brkStart lim gh W hPl_mng
  have hraw := w1t_s427_spqrSendCoins_placed_ok_of_contracts_tight
    (cliSpqrSendAllocContractsPlaced mmpl gh W hGSpqr.toCliGhostAllocHooks)
    (w1t_spqrSendPlacedContracts_tight_cli mmpl gh W h325 hGSpqr hHmac)
    (spqrSendExtraContractsPlaced_of_cli mmpl gh W hGSpqr hHmac)
  have hblk_wp : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 427 (Rust.withPanics H))
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv fineCostModel A lim 0#64 (spqrV1 W.C.F W.Q.K)
          (w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv W.C.F W.Q.K
            (w1t_DecGuardedBytes W.C.F W.Q.K) (e2b_StatesFromPbExactEnv W.C.F)))) := by
    rwa [← IsLsBlockProg.eq_blockProgram (prog := spqrSendPlacedProg H)]
  have hwp_eq : Rust.withPanics H = H := by
    funext sym; unfold Rust.withPanics; split
    · next hp => exact (w1t_s427_cliGhostExterns_isPanic mmpl gh W sym hp).symm
    · rfl
  have hblk_ext : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 427 H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv fineCostModel A lim 0#64 (spqrV1 W.C.F W.Q.K)
          (w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv W.C.F W.Q.K
            (w1t_DecGuardedBytes W.C.F W.Q.K) (e2b_StatesFromPbExactEnv W.C.F)))) := by
    simpa only [hwp_eq] using hblk_wp
  have hok0 : subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv fineCostModel A lim 0#64 (spqrV1 W.C.F W.Q.K)
          (w1t_s427_SpqrSendCoinsOfDecodeFromPbEnv W.C.F W.Q.K
            (w1t_DecGuardedBytes W.C.F W.Q.K) (e2b_StatesFromPbExactEnv W.C.F)))) :=
    ls_subroutine_ok_of_blockProgram_cro
      (callerProg := (blkPC_427).rebase (blkPl_427).base H) hblk_ext (by decide)
  have heq_cro (m : Memory) :
      CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl m =
        LibsignalCodeRoLoaded lsmpl m :=
    propext ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  have hmod : pqxdhSpqrModel ⟨W.C, W.Q⟩ = spqrV1 W.C.F W.Q.K := rfl
  rw [hmod]
  have hcoinsAt : spqrCoinsAtPlaced = cliTapeAt := rfl
  have hcoinsAfter : spqrCoinsAfterPlaced = cliTapeAfter := rfl
  exact subroutine_ok_mono hok0
    (fun (sc, stB) _ s hpre => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget.spqrSendCoinsPlacedSpec,
        withLsCodeRoLoaded, spqrSendCoinsPlacedSpecTOfEnv, spqrSendCoinsPlacedSpecOfEnv]
        at hpre ⊢
      rw [heq_cro s.mem] at hpre
      rw [hcoinsAt]
      refine Satisfies.mono ?_ hpre
      refine sepConj_mono_left ?_
      refine sepConj_mono_left ?_
      refine sepConj_mono_right ?_
      refine sepConj_mono_right ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨h1, h2, hfit⟩ => by
        by_cases hG : SpqrStateTight640 W.C.F W.Q.K sc.st.bytes
        · exact ⟨h1, h2, hfit.mono fun evs hevs =>
            fun _ => w1t_sendOfDecodeFromPb_sub_tight hG hevs⟩
        · exact False.elim
            (w1t_s427_not_fitsEnv_of_univ (fun _ hp => False.elim (hG hp)) hfit))
    (fun (sc, stB) _ _ _ hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget.spqrSendCoinsPlacedSpec,
        withLsCodeRoLoaded, spqrSendCoinsPlacedSpecTOfEnv, spqrSendCoinsPlacedSpecOfEnv]
        at hpost ⊢
      rw [hcoinsAfter] at hpost
      refine Satisfies.mono ?_ hpost
      refine sepConj_mono_left ?_
      refine sepConj_mono_right ?_
      refine Entails.sepExists_mono fun evs => ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨hd, htr, hnp, hevs⟩ =>
        ⟨fun hG => w1t_sendOfDecodeFromPb_sub_tight hG hevs, hd, htr, hnp⟩)
    (fun _ _ _ _ hp => hp)

theorem w1t_sendGuardedBytes_empty (F : ShaCompress) (K : MlKem) (rest : List (BitVec 8)) :
    w1t_SendGuardedBytesEnv F K [] rest [] := by
  intro _
  have hdec : spqrDecodeState ([] : List (BitVec 8)) = .ok ⟨none, none, none⟩ := rfl
  dsimp only [w1t_SendTightBytesEnv, w1t_s427_SpqrSendCoinsOfDecodeFromPbBytesEnv]
  rw [hdec]
  exact Or.inl (SpqrTightEvs.nil 109 1307216 79236)

end W1T_SendCoins

/-! ## Hook-Only `EncTailsVTPlaced` -/

section W1T_EncTails

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  FreeOnlyEvs rustDeallocEvents rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync LibsignalBinary.Proofs.Placed.BudgetVmSteps
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget (
  call_nopanic_placed call_rocl_nopanic_placed
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins (
  SeamBudget freeOnlyEvs_rustDeallocEvents retagSessionStore retagIdentityStore
  SpqrSendBudgetEnv SessionStoreBudgetEnv IdentityStoreBudgetEnv
  WithStoresEncEnv withStoresEncBudgetSpecV EncTailVBudget SegExitBudget
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins (
  dropSessionStructureLocal2BudgetSpec
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFreePrevSessionsPlacedBudget (
  freePrevSessions_zero_placed_sepWP freePrevSessions_nz_placed_step_pre
  tailWriteErr_placed_ok
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailDropRecordStepsPlacedBudget (
  dropRecordDropSs_placed_step_pre
  dropRecordCur_none_placed_sepWP dropRecordCur_some_placed_sepWP
  dropRecordAfterDealloc_none_placed_sepWP dropRecordAfterDealloc_some_placed_sepWP
  dropRecord_otr_none_placed_sepWP dropRecord_otr_zero_placed_sepWP
  dropRecord_otr_nz_placed_step_pre
)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (
  WithStoresEncGhost withStoresEncStack withStoresEncStackV
  encSubStack encSpillsAtV encSavedRegs nowAt curScratch cmScratch
)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt (
  encEntryPlaced encCommonPlaced encStoreExtraPlaced withStoresEncStack_join_extra_placed
)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon (
  words64At SpeStaged ResStaged pollWith tailRegs TailModel dropRecordSlots otrSlotAt cmSlotAt
  unpack64List exists_unpack64List words64At_eq_pointsToBytes
  words64At_entails_memRegion writeResult_frame_entails_stackAtV
)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions (
  stackAt_encSubStack_alloc mul24_shift_toNat
  vecHeader_prev_weaken vecAt_prev_zero_eq vecAt_prev_nz_eq
)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps (
  cap_add_one_beq_zero_eq_false cap_add_one_ne_zero
  scratch_has_50 stackAt_encSubStack_dropSs
  cur_none_weaken flag_memRegion_weaken
  sessionStateAt_unfold_cap sessionStateAfterLocalIk
  otr_none_slots_eq otrAt_weaken_vecU8At vecU8At_zero_weaken
  otr_zero_post_weaken vecU8At_nz_weaken otr_nz_post_weaken
)

private theorem w1t_tfp_bv_sub_add_lit_local (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] w1t_tfp_bv_sub_add_lit_local BitVec.toNat_zero

/-! ### `SeamBudget` Step Helpers -/

private theorem w1t_tfp_seamBudget_step_freeOnly {M : AllocCostModel} {lim : BudgetLimits}
    {TopEnv : List AllocEvent → Prop} {st_init st : M.σ} {evs_step : List AllocEvent}
    (h : SeamBudget lim TopEnv st_init st FreeOnlyEvs) (hstep : FreeOnlyEvs evs_step) :
    SeamBudget lim TopEnv st_init (M.stepEvents evs_step st) FreeOnlyEvs :=
  (h.narrow (by rintro _ (h1 | ⟨_, _, rfl, h1, h2⟩); exact h1; exact h1.append h2)).advance hstep

private theorem w1t_tfp_protocolAddressAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    protocolAddressAt (A.atState lim st s) = protocolAddressAt A.repAlloc := rfl

private theorem w1t_tfp_storeFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs, (retagSessionStore (A' := A') kit).storeFinal st0 ans cs = kit.storeFinal st0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact w1t_tfp_storeFinal_retag kit _ ans cs

private theorem w1t_tfp_idFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs, (retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs = ikit.idFinal ist0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact w1t_tfp_idFinal_retag ikit _ ans cs

private theorem w1t_tfp_encStoreExtraPlaced_final_retag [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8))))
    (x : WithStoresEncGhost) (s0 : State) :
    encStoreExtraPlaced (retagSessionStore (A' := A') kit)
      ((retagSessionStore (A' := A') kit).storeFinal st0 ans cs)
      (retagIdentityStore (A' := A') ikit)
      ((retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs) x s0 =
    encStoreExtraPlaced kit (kit.storeFinal st0 ans cs)
      ikit (ikit.idFinal ist0 ans cs) x s0 := by
  have hs := w1t_tfp_storeFinal_retag (A' := A') kit st0 ans cs
  have hi := w1t_tfp_idFinal_retag (A' := A') ikit ist0 ans cs
  have hfn :
      ∀ (st : kit.StoreState) (ist : ikit.IdState),
        encStoreExtraPlaced (retagSessionStore (A' := A') kit) st
          (retagIdentityStore (A' := A') ikit) ist x s0 =
        encStoreExtraPlaced kit st ikit ist x s0 := fun _ _ => rfl
  exact (hfn _ _).trans (by rw [hs, hi])

private theorem w1t_tfp_encTail_mem_retag_eq [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (S : SpqrModel)
    (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (slotsP : SepProp) (R0 : SepProp) (s0 : State) :
    (slotsP ∗
      encSpillsAtV (retagSessionStore (A' := A') kit).ss_vt
        (retagIdentityStore (A' := A') ikit).id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced (retagSessionStore (A' := A') kit)
        ((retagSessionStore (A' := A') kit).storeFinal st0 answers (x.model C S uuidTryParse answers).2)
        (retagIdentityStore (A' := A') ikit)
        ((retagIdentityStore (A' := A') ikit).idFinal ist0 answers (x.model C S uuidTryParse answers).2)
        x s0 ∗ R0)) =
    (slotsP ∗
      encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced kit
        (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
        ikit
        (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2)
        x s0 ∗ R0)) := by
  have hext := w1t_tfp_encStoreExtraPlaced_final_retag (A' := A') kit st0 ikit ist0 answers
    (x.model C S uuidTryParse answers).2 x s0
  have hvt :
      encSpillsAtV (retagSessionStore (A' := A') kit).ss_vt
        (retagIdentityStore (A' := A') ikit).id_vt =
      encSpillsAtV kit.ss_vt ikit.id_vt := rfl
  exact congrArg (slotsP ∗ ·)
    (congrArg₂ sepConj (congrFun (congrFun hvt _) _)
      (congrArg (memRegion x.ret 248 ∗ ·)
        (congrArg (encCommonPlaced A' ctl x (x.draws S answers) s0 ∗ ·)
          (congrArg (· ∗ R0) hext))))

private theorem w1t_tfp_encCommonPlaced_vmPreserved [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (draws : Nat) (s0 s1 s2 : State)
    (hvm : VmPreserved s1 s2) :
    encCommonPlaced (A.atState lim st s1) ctl x draws s0 =
      encCommonPlaced (A.atState lim st s2) ctl x draws s0 := by
  rw [(A.atState_eq_of_vmPreserved lim st hvm).symm]

/-! ### `VmPreserved`-Threaded `SepWP` Steppers (`+0x564..+0x660`) -/

private theorem w1t_tfp_sessionRecordAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    sessionRecordAt (A.atState lim st s) = sessionRecordAt A.repAlloc := rfl

private theorem w1t_tfp_sessionStateAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    sessionStateAt (A.atState lim st s) = sessionStateAt A.repAlloc := rfl

private theorem w1t_tfp_pool_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    (A.atState lim st s).pool = A.pool lim st s := rfl

private theorem w1t_sat_of_eq {m : Memory} {P Q : SepProp} (h : m ⊨ P) (heq : P = Q) : m ⊨ Q :=
  heq ▸ h

private theorem w1t_tailFreePrevSessions [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    (hdealloc : subroutine_ok (lsProg_464 Hk) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (prevCap prevPtr : BitVec 64)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      x st_init st answers (encEntryPlaced + 0x564#64) (tailRegs w0 w1 w2)
      (fun sp => memRegion sp 0x58 ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) := by
  let R := encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hbud, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (w1t_tfp_encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) hmem
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (memRegion sp 0x58 ∗
      vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      memRegion (sp + 0x128#64) 0x158 ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R at hmem
  by_cases hcap : prevCap = 0#64
  · subst hcap
    rw [vecAt_prev_zero_eq A.repAlloc sp prevPtr] at hmem
    let F := memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x158 ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0
    have hmem_re : s.mem ⊨
        ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
        ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ (F ∗ R)) := by
      have heq :
          ((memRegion sp 0x58 ∗
            (⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
              (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))) ∗
            memRegion (sp + 0x128#64) 0x158 ∗ memRegion (sp + 0x280#64) 0x1ea ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          (⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
           ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ (F ∗ R))) := by
        dsimp only [F]; sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hmem_re
    have hwp := freePrevSessions_zero_placed_sepWP (Hk := Hk) (prevPtr := prevPtr) hpc hrun hsp_al hsp
    refine SegExitBudget.of_sepWP (R0 := R0) hmem_re.2 hwp ?_
    intro s1 P_f _ hsteps1 hpc1 hrun1 hmf1
      ⟨hvm1, hsp1, hsp1_al, htr1, _hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, _, hvregs1, hPf⟩
    subst hPf
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine tailWriteErr_placed_ok x st_init st R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H hm1 hst ⟨hbud, ?_⟩
    refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hcrl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1.trans hvregs⟩,
      ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    refine Eq.mpr (congrArg (s1.mem ⊨ ·)
      (w1t_tfp_encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
    have hmf2 : s1.mem ⊨
        (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea) ∗
        (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ (F ∗ R)) =
          ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
            memRegion (sp + 0x280#64) 0x1ea) ∗
           (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) := by
        dsimp only [F]
        rw [w1t_tfp_encCommonPlaced_vmPreserved A lim st ctl x (x.draws S answers) s0 s s1 hvm1]
        sep_ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (vecHeader_prev_weaken sp 0#64 prevPtr)) hmf2
    have heq2 :
        (memRegion (sp + 0x110#64) 0x35a ∗
         (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
    rwa [← heq2]
  · rw [vecAt_prev_nz_eq A.repAlloc sp prevCap prevPtr hcap] at hmem
    let F_core := memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x158 ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
      nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ FromRecordCallees.lsLogOff ∗
      memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - allocHookStack) ∗
      encSavedRegs s0.sp s0
    have hmem_re :
        s.mem ⊨ ⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
          ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗
           ((A.pool lim st s ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
             memRegion prevPtr (prevCap.toNat * 24) ∗ stackAt sp allocHookStack ∗ F_core) ∗ R)) := by
      have heq :
          ((memRegion sp 0x58 ∗
            (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
              (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
               ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
               memRegion prevPtr (prevCap.toNat * 24))) ∗
            memRegion (sp + 0x128#64) 0x158 ∗
            memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
           ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗
            ((A.pool lim st s ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
              memRegion prevPtr (prevCap.toNat * 24) ∗ stackAt sp allocHookStack ∗ F_core) ∗ R))) := by
        unfold encCommonPlaced
        rw [w1t_tfp_protocolAddressAt_atState]
        change ((memRegion sp 0x58 ∗
          (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
            (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
             ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
             memRegion prevPtr (prevCap.toNat * 24))) ∗
          memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
          nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ FromRecordCallees.lsLogOff ∗
          stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st s) ∗ R) = _
        rw [stackAt_encSubStack_alloc sp]
        dsimp only [F_core]
        sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hmem_re
    rcases hmem_re with ⟨⟨_, hcap_lt, _⟩, hmem2⟩
    have hwp := freePrevSessions_nz_placed_step_pre (Hk := Hk) (prevPtr := prevPtr)
      hcap hcap_lt hpc hrun hsp_al hsp
    refine SegExitBudget.of_sepWP (R0 := R0) hmem2 hwp ?_
    intro s_pre P_pre _ hsteps_pre hpc_pre hrun_pre hmf_pre
      ⟨hvm_pre, hsp_pre, hsp_pre_al, htr_pre, hx0_pre, hx1_pre, hx2_pre, hlr_pre,
        hx19_pre, hx21_pre, hx23_pre, _hx25_pre, hx26_pre, hx27_pre, hx28_pre, hx29_pre, hvregs_pre, hP_pre⟩
    subst hP_pre
    have hm_dealloc : s_pre.mem ⊨
        (rustCliDeallocBudgetSpec M A lim).pre (prevPtr, prevCap.toNat * 24, 8, st) s_pre ∗
        ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ F_core) ∗ R) := by
      dsimp only [rustCliDeallocBudgetSpec]
      rw [hsp_pre]
      rw [← A.pool_transport lim st s s_pre hvm_pre] at hmf_pre
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0_pre, hx1_pre, hx2_pre,
        by rw [hlr_pre]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 464 0x5b4#64 (by decide) (by decide)⟩,
        w1t_sat_of_eq hmf_pre (by dsimp only [sp]; sep_ac_rfl)⟩
    refine call_nopanic_placed (R0 := R0) hdealloc
      (prevPtr, prevCap.toNat * 24, 8, st) hpc_pre hrun_pre hsp_pre_al hlr_pre hm_dealloc ?_
    intro s1 hsteps_call hpc1 hrun1 hsp1_pre hsp1_al hcs1 hmf1
    obtain ⟨hx19_c, _, hx21_c, _, hx23_c, _, _, hx26_c, hx27_c, hx28_c, hx29_c, hvregs_c⟩ := hcs1
    dsimp only [rustCliDeallocBudgetSpec] at hmf1
    rw [hsp_pre] at hmf1
    have hsp1 : s1.sp = sp := hsp1_pre.trans hsp_pre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf1
    obtain ⟨⟨hacp1, _⟩, hmf1⟩ := hmf1
    have htr_call : s1.trace = s_pre.trace := hacp1.2.1
    have hbud1 := w1t_tfp_seamBudget_step_freeOnly hbud (freeOnlyEvs_rustDeallocEvents (prevCap.toNat * 24) 8)
    set st1 := M.stepEvents (rustDeallocEvents (prevCap.toNat * 24) 8) st
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, (htr_call.trans htr_pre).trans hm.2⟩
    have hcrl1 : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem :=
      hcrl.of_keepsFrozen (hsteps_pre.trans hsteps_call).keepsFrozen
    refine tailWriteErr_placed_ok x st_init st1 R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H hm1 hst ⟨hbud1, ?_⟩
    refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al,
      (hx29_c.trans hx29_pre).trans hx29,
      (hx19_c.trans hx19_pre).trans hx19,
      hcrl1,
      (hvregs_c.trans hvregs_pre).trans hvregs⟩,
      ⟨(hx26_c.trans hx26_pre).trans hx26,
       (hx28_c.trans hx28_pre).trans hx28,
       (hx27_c.trans hx27_pre).trans hx27,
       (hx21_c.trans hx21_pre).trans hx21,
       (hx23_c.trans hx23_pre).trans hx23⟩,
      hstack_le, ?_⟩
    refine Eq.mpr (congrArg (s1.mem ⊨ ·)
      (w1t_tfp_encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
    have hmf2 : s1.mem ⊨
        (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea) ∗
        (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((A.pool lim st1 s1 ∗ stackAt sp allocHookStack) ∗
           ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
             ((sp + 0x120#64) ↦₆₄ 0#64) ∗ F_core) ∗ R)) =
          ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
            memRegion (sp + 0x280#64) 0x1ea) ∗
           (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R)) := by
        unfold encCommonPlaced
        rw [w1t_tfp_protocolAddressAt_atState]
        change _ = ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
            memRegion (sp + 0x280#64) 0x1ea) ∗
           (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
              nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ FromRecordCallees.lsLogOff ∗
              stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st1 s1) ∗ R))
        rw [stackAt_encSubStack_alloc sp]
        dsimp only [F_core]
        sep_ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (vecHeader_prev_weaken sp prevCap prevPtr)) hmf2
    have heq2 :
        (memRegion (sp + 0x110#64) 0x35a ∗
         (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
    rwa [← heq2]

private theorem w1t_tailDropRecordAt55c [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    (hdealloc : subroutine_ok (lsProg_464 Hk) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok (lsProg_464 Hk) (lsmpl.base 442)
      (StoreKit.withLsRoCl lsmpl (dropSessionStructureLocal2BudgetSpec M A lim)))
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch)
    (prevCap prevPtr : BitVec 64) (G : SessionGhost) (sess_st : SessionState (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv x st_init st answers
      (encEntryPlaced + 0x55c#64) (tailRegs w0 w1 w2)
      (fun sp => scratch sp ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateAt A.repAlloc (sp + 0x128#64) G sess_st ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 s
      (fun _ => False) := by
  let R := encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hbud, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  let sp := s0.sp - 0xbe0#64
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (w1t_tfp_encTail_mem_retag_eq (A' := A.atState lim st s) kit st0 ikit ist0 C ctl S x answers _ R0 s0)) hmem
  rcases scratch_has_50 hscr sp with ⟨S50, hscr_eq, hscr_weaken⟩
  change s.mem ⊨
    (scratch sp ∗
      vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      sessionStateAt A.repAlloc (sp + 0x128#64) G sess_st ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R at hmem
  rw [hscr_eq] at hmem
  let F := S50 ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
    nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ FromRecordCallees.lsLogOff ∗
    memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - FromRecordCallees.dropSessionStructureLocal2Stack) ∗
    encSavedRegs s0.sp s0
  have hmem_re : s.mem ⊨
      ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sessionStateAt A.repAlloc (sp + 0x128#64) G sess_st ∗
        A.pool lim st s ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ (F ∗ R)) := by
    have heq :
        (((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
          vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A.repAlloc (sp + 0x128#64) G sess_st ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
        (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
          ((sessionStateAt A.repAlloc (sp + 0x128#64) G sess_st ∗
            A.pool lim st s ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ (F ∗ R))) := by
      unfold encCommonPlaced
      rw [w1t_tfp_protocolAddressAt_atState]
      change (((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateAt A.repAlloc (sp + 0x128#64) G sess_st ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
        nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ FromRecordCallees.lsLogOff ∗
        stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st s) ∗ R) = _
      rw [stackAt_encSubStack_dropSs sp]
      dsimp only [F]
      sep_ac_rfl
    rwa [← heq]
  have hwp := dropRecordDropSs_placed_step_pre (Hk := Hk) hpc hrun hsp_al hsp
  refine SegExitBudget.of_sepWP (R0 := R0) hmem_re hwp ?_
  intro s_pre P_pre _ hsteps_pre hpc_pre hrun_pre hmf_pre
    ⟨hvm_pre, hsp_pre, hsp_pre_al, htr_pre, hx0_pre, hlr_pre,
      hx19_pre, hx21_pre, hx23_pre, _hx25_pre, hx26_pre, hx27_pre, hx28_pre, hx29_pre, hvregs_pre, hP_pre⟩
  subst hP_pre
  have hm_drop : s_pre.mem ⊨
      (dropSessionStructureLocal2BudgetSpec M A lim).pre (⟨sp + 0x128#64, G, sess_st⟩, st) s_pre ∗
      ((((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ F) ∗ R) := by
    dsimp only [dropSessionStructureLocal2BudgetSpec, FromRecordCallees.dropSessionStructureLocal2Spec]
    rw [w1t_tfp_sessionStateAt_atState, w1t_tfp_pool_atState, hsp_pre]
    rw [← A.pool_transport lim st s s_pre hvm_pre] at hmf_pre
    have hlr_ls : LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s_pre.readReg64 .lr) := by
      rw [hlr_pre]
      exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 464 0x564#64 (by decide) (by decide)
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hlr_ls, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0_pre, w1t_sat_of_eq hmf_pre (by dsimp only [sp]; sep_ac_rfl)⟩
  have hcrl_pre : StoreKit.LibsignalCodeRoLoaded lsmpl s_pre.mem :=
    hcrl.of_keepsFrozen hsteps_pre.keepsFrozen
  refine call_rocl_nopanic_placed (R0 := R0) hdrop
    (⟨sp + 0x128#64, G, sess_st⟩, st) hpc_pre hrun_pre hsp_pre_al hlr_pre hcrl_pre hm_drop ?_
  intro s1 hsteps_call hpc1 hrun1 hsp1_pre hsp1_al hcs1 hmf1
  obtain ⟨hx19_c, _, hx21_c, _, hx23_c, _, _, hx26_c, hx27_c, hx28_c, hx29_c, hvregs_c⟩ := hcs1
  dsimp only [dropSessionStructureLocal2BudgetSpec, FromRecordCallees.dropSessionStructureLocal2Spec] at hmf1
  rw [hsp_pre] at hmf1
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hmf1
  obtain ⟨evs, hmf1⟩ := hmf1
  rw [w1t_tfp_pool_atState] at hmf1
  have hmf1_pull : s1.mem ⊨ ⌜FreeOnlyEvs evs⌝ ∗ (⌜s1.trace = s_pre.trace⌝ ∗
      ((((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x128#64) 0x158 ∗
        A.pool lim (M.stepEvents evs st) s1 ∗
        stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ (F ∗ R))) := by
    change s1.mem ⊨ (⌜FreeOnlyEvs evs⌝ ∗
      (⌜s1.trace = s_pre.trace⌝ ∗ memRegion (sp + 0x128#64) 0x158 ∗
        A.pool lim (M.stepEvents evs st) s1 ∗
        stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack)) ∗
      ((((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ F) ∗ R) at hmf1
    exact Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) hmf1
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hmf1_pull
  rcases hmf1_pull with ⟨hevs, htr_call, hmf1'⟩
  have hsp1 : s1.sp = sp := hsp1_pre.trans hsp_pre
  have hbud1 := w1t_tfp_seamBudget_step_freeOnly hbud hevs
  set st1 := M.stepEvents evs st
  have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
    ⟨hm.1, (htr_call.trans htr_pre).trans hm.2⟩
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem :=
    hcrl.of_keepsFrozen (hsteps_pre.trans hsteps_call).keepsFrozen
  refine w1t_tailFreePrevSessions hdealloc x st_init st1 R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H
    prevCap prevPtr hm1 hst ⟨hbud1, ?_⟩
  refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al,
    (hx29_c.trans hx29_pre).trans hx29,
    (hx19_c.trans hx19_pre).trans hx19,
    hcrl1,
    (hvregs_c.trans hvregs_pre).trans hvregs⟩,
    ⟨(hx26_c.trans hx26_pre).trans hx26,
     (hx28_c.trans hx28_pre).trans hx28,
     (hx27_c.trans hx27_pre).trans hx27,
     (hx21_c.trans hx21_pre).trans hx21,
     (hx23_c.trans hx23_pre).trans hx23⟩,
    hstack_le, ?_⟩
  refine Eq.mpr (congrArg (s1.mem ⊨ ·)
    (w1t_tfp_encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
  have hmf2 : s1.mem ⊨
      (S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
      (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
       memRegion (sp + 0x128#64) 0x158 ∗
       memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R) := by
    have heq :
        ((((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          A.pool lim st1 s1 ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ (F ∗ R)) =
        ((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
         (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R)) := by
      unfold encCommonPlaced
      rw [w1t_tfp_protocolAddressAt_atState]
      change _ = ((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
        (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
         memRegion (sp + 0x128#64) 0x158 ∗
         memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
          nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ FromRecordCallees.lsLogOff ∗
          stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st1 s1) ∗ R))
      rw [stackAt_encSubStack_dropSs sp]
      dsimp only [F]
      sep_ac_rfl
    rwa [heq] at hmf1'
  have hmf3 := Satisfies.mono (sepConj_mono_left hscr_weaken) hmf2
  have heq2 :
      (memRegion sp 0x58 ∗
       (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R)) =
      ((memRegion sp 0x58 ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
  rwa [← heq2]

private theorem w1t_tailDropRecordCur [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    (hdealloc : subroutine_ok (lsProg_464 Hk) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok (lsProg_464 Hk) (lsmpl.base 442)
      (StoreKit.withLsRoCl lsmpl (dropSessionStructureLocal2BudgetSpec M A lim)))
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) (b469 : BitVec 8)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv x st_init st answers
      (encEntryPlaced + 0x54c#64) (tailRegs w0 w1 w2)
      (fun sp => scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 s
      (fun _ => False) := by
  let R := encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hbud, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  let sp := s0.sp - 0xbe0#64
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (w1t_tfp_encTail_mem_retag_eq (A' := A.atState lim st s) kit st0 ikit ist0 C ctl S x answers _ R0 s0)) hmem
  change s.mem ⊨
    (scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R at hmem
  unfold sessionRecordAt at hmem
  have h128 : sp + 0x110#64 + 0x18#64 = sp + 0x128#64 := by bv_omega
  have h130 : sp + 0x110#64 + 0x20#64 = sp + 0x130#64 := by bv_omega
  rcases g with ⟨prevCap, prevPtr, _ | G⟩ <;> rcases hcur : rec.currentSession with _ | sess
  · rw [hcur, h128, h130] at hmem
    rcases scratch_has_50 hscr sp with ⟨S50, hscr_eq, hscr_weaken⟩
    have hscr_mem : scratch sp ⊢ memRegion sp 0x58 := hscr_eq ▸ hscr_weaken
    let F := scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      memRegion (sp + 0x130#64) 336 ∗ memRegion (sp + 0x280#64) 0x1e9 ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0
    have hmem_re : s.mem ⊨ (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ (F ∗ R) := by
      have heq :
          ((scratch sp ∗
            (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
              (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336)) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          ((((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ (F ∗ R)) := by
        dsimp only [F]; sep_ac_rfl
      rwa [← heq]
    have hwp := dropRecordCur_none_placed_sepWP (Hk := Hk) (b469 := b469) hpc hrun hsp_al hsp
    refine SegExitBudget.of_sepWP (R0 := R0) hmem_re hwp ?_
    intro s1 P_f _ hsteps1 hpc1 hrun1 hmf1
      ⟨hvm1, hsp1, hsp1_al, htr1, _hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine w1t_tailFreePrevSessions hdealloc x st_init st R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H
      prevCap prevPtr hm1 hst ⟨hbud, ?_⟩
    refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hcrl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1.trans hvregs⟩,
      ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    refine Eq.mpr (congrArg (s1.mem ⊨ ·)
      (w1t_tfp_encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
    have hmf2 : s1.mem ⊨
        (scratch sp ∗
          (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336) ∗
          (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8))) ∗
        (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗ (F ∗ R)) =
          ((scratch sp ∗
            (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336) ∗
            (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8))) ∗
           (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) := by
        dsimp only [F]
        rw [w1t_tfp_encCommonPlaced_vmPreserved A lim st ctl x (x.draws S answers) s0 s s1 hvm1]
        sep_ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono
      (sepConj_mono_left (sepConj_mono hscr_mem
        (sepConj_mono (cur_none_weaken sp) (flag_memRegion_weaken sp 0#8)))) hmf2
    have heq2 :
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x158 ∗ memRegion (sp + 0x280#64) 0x1ea) ∗
         (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
           pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗
          vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
    rwa [← heq2]
  · rw [hcur] at hmem
    have hfalse : s.mem ⊨ ⌜False⌝ ∗
        (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((scratch sp ∗
            (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗ ⌜False⌝) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          (⌜False⌝ ∗
           (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R)) := by sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1.elim
  · rw [hcur] at hmem
    have hfalse : s.mem ⊨ ⌜False⌝ ∗
        (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((scratch sp ∗
            (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗ ⌜False⌝) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          (⌜False⌝ ∗
           (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R)) := by sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1.elim
  · rw [hcur] at hmem
    dsimp only at hmem
    unfold sessionStateReprAt at hmem
    rw [h128, sessionStateAt_unfold_cap A.repAlloc (sp + 0x128#64) G sess.state] at hmem
    let P_sess_pure : Prop :=
      PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
        G.alice.bytes = sess.aliceBaseKey ∧
        G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
        (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat
    let P_ik_pure : Prop :=
      G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0
    let F_some := scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      sessionStateAfterLocalIk A.repAlloc (sp + 0x128#64) G sess.state ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0
    have hmem_re : s.mem ⊨ ⌜P_sess_pure⌝ ∗ (⌜P_ik_pure⌝ ∗
        ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ (F_some ∗ R))) := by
      have heq :
          ((scratch sp ∗
            (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
              (⌜P_sess_pure⌝ ∗
                (⌜P_ik_pure⌝ ∗
                  (((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
                    sessionStateAfterLocalIk A.repAlloc (sp + 0x128#64) G sess.state)))) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          (⌜P_sess_pure⌝ ∗ (⌜P_ik_pure⌝ ∗
            ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ (F_some ∗ R)))) := by
        dsimp only [P_sess_pure, P_ik_pure, F_some]; sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hmem_re
    rcases hmem_re with ⟨_, h_ik, hmem2⟩
    have hcap_lt : G.localIk.cap.toNat < 2 ^ 63 := h_ik.2.1
    have hwp := dropRecordCur_some_placed_sepWP (Hk := Hk) (b469 := b469) hcap_lt hpc hrun hsp_al hsp
    refine SegExitBudget.of_sepWP (R0 := R0) hmem2 hwp ?_
    intro s1 P_f _ hsteps1 hpc1 hrun1 hmf1
      ⟨hvm1, hsp1, hsp1_al, htr1, _hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine w1t_tailDropRecordAt55c hdealloc hdrop x st_init st R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H scratch hscr
      prevCap prevPtr G sess.state hm1 hst ⟨hbud, ?_⟩
    refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hcrl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1.trans hvregs⟩,
      ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    refine Eq.mpr (congrArg (s1.mem ⊨ ·)
      (w1t_tfp_encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
    have hmf1' : s1.mem ⊨ ⌜P_ik_pure⌝ ∗
        ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗ (F_some ∗ R)) := by
      rw [satisfies_pure_sepConj]
      exact ⟨h_ik, hmf1⟩
    have hmf2 : s1.mem ⊨
        (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
        (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A.repAlloc (sp + 0x128#64) G sess.state ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          (⌜P_ik_pure⌝ ∗
            ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗ (F_some ∗ R))) =
          ((memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
           (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             sessionStateAt A.repAlloc (sp + 0x128#64) G sess.state ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) := by
        rw [sessionStateAt_unfold_cap A.repAlloc (sp + 0x128#64) G sess.state]
        dsimp only [P_ik_pure, F_some]
        rw [w1t_tfp_encCommonPlaced_vmPreserved A lim st ctl x (x.draws S answers) s0 s s1 hvm1]
        sep_ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (flag_memRegion_weaken sp 0#8)) hmf2
    have heq2 :
        (memRegion (sp + 0x280#64) 0x1ea ∗
         (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
           sessionStateAt A.repAlloc (sp + 0x128#64) G sess.state ∗
           pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) =
        ((scratch sp ∗
          vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A.repAlloc (sp + 0x128#64) G sess.state ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
    rwa [← heq2]

private theorem w1t_tailDropRecordAfterDealloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    (hdealloc : subroutine_ok (lsProg_464 Hk) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok (lsProg_464 Hk) (lsmpl.base 442)
      (StoreKit.withLsRoCl lsmpl (dropSessionStructureLocal2BudgetSpec M A lim)))
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) (b469 : BitVec 8)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      x st_init st answers (encEntryPlaced + 0x488#64) (tailRegs w0 w1 w2)
      (fun sp => scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) := by
  let R := encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hbud, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (w1t_tfp_encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) hmem
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R at hmem
  unfold sessionRecordAt at hmem
  have h128 : sp + 0x110#64 + 0x18#64 = sp + 0x128#64 := by bv_omega
  have h130 : sp + 0x110#64 + 0x20#64 = sp + 0x130#64 := by bv_omega
  rcases g with ⟨prevCap, prevPtr, _ | G⟩ <;> rcases hcur : rec.currentSession with _ | sess
  · rw [hcur, h128, h130] at hmem
    rcases scratch_has_50 hscr sp with ⟨S50, hscr_eq, hscr_weaken⟩
    have hscr_mem : scratch sp ⊢ memRegion sp 0x58 := hscr_eq ▸ hscr_weaken
    let F := scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      memRegion (sp + 0x130#64) 336 ∗ memRegion (sp + 0x280#64) 0x1e9 ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0
    have hmem_re : s.mem ⊨ (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ (F ∗ R) := by
      have heq :
          ((scratch sp ∗
            (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
              (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336)) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          ((((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ (F ∗ R)) := by
        dsimp only [F]; sep_ac_rfl
      rwa [← heq]
    have hwp := dropRecordAfterDealloc_none_placed_sepWP (Hk := Hk) (b469 := b469) hpc hrun hsp_al hsp
    refine SegExitBudget.of_sepWP (R0 := R0) hmem_re hwp ?_
    intro s1 P_f _ hsteps1 hpc1 hrun1 hmf1
      ⟨hvm1, hsp1, hsp1_al, htr1, _hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine w1t_tailFreePrevSessions hdealloc x st_init st R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H prevCap prevPtr hm1 hst ⟨hbud, ?_⟩
    refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hcrl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1.trans hvregs⟩,
      ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    refine Eq.mpr (congrArg (s1.mem ⊨ ·)
      (w1t_tfp_encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
    have hmf2 : s1.mem ⊨
        (scratch sp ∗
          (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336) ∗
          (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8))) ∗
        (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗ (F ∗ R)) =
          ((scratch sp ∗
            (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336) ∗
            (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8))) ∗
           (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) := by
        dsimp only [F]
        rw [w1t_tfp_encCommonPlaced_vmPreserved A lim st ctl x (x.draws S answers) s0 s s1 hvm1]
        sep_ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono
      (sepConj_mono_left (sepConj_mono hscr_mem
        (sepConj_mono (cur_none_weaken sp) (flag_memRegion_weaken sp 0#8)))) hmf2
    have heq2 :
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x158 ∗ memRegion (sp + 0x280#64) 0x1ea) ∗
         (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
           pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗
          vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
    rwa [← heq2]
  · rw [hcur] at hmem
    have hfalse : s.mem ⊨ ⌜False⌝ ∗
        (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((scratch sp ∗
            (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗ ⌜False⌝) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          (⌜False⌝ ∗
           (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R)) := by sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1.elim
  · rw [hcur] at hmem
    have hfalse : s.mem ⊨ ⌜False⌝ ∗
        (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((scratch sp ∗
            (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗ ⌜False⌝) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          (⌜False⌝ ∗
           (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R)) := by sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1.elim
  · rw [hcur] at hmem
    dsimp only at hmem
    unfold sessionStateReprAt at hmem
    rw [h128, sessionStateAt_unfold_cap A.repAlloc (sp + 0x128#64) G sess.state] at hmem
    let P_sess_pure : Prop :=
      PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
        G.alice.bytes = sess.aliceBaseKey ∧
        G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
        (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat
    let P_ik_pure : Prop :=
      G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0
    let F := scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      sessionStateAfterLocalIk A.repAlloc (sp + 0x128#64) G sess.state ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0
    have hmem_re : s.mem ⊨ ⌜P_sess_pure⌝ ∗ (⌜P_ik_pure⌝ ∗
        ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ (F ∗ R))) := by
      have heq :
          ((scratch sp ∗
            (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
              (⌜P_sess_pure⌝ ∗
                (⌜P_ik_pure⌝ ∗
                  (((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
                    sessionStateAfterLocalIk A.repAlloc (sp + 0x128#64) G sess.state)))) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          (⌜P_sess_pure⌝ ∗ (⌜P_ik_pure⌝ ∗
            ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ (F ∗ R)))) := by
        dsimp only [P_sess_pure, P_ik_pure, F]; sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hmem_re
    rcases hmem_re with ⟨_, h_ik, hmem2⟩
    have hcap_lt : G.localIk.cap.toNat < 2 ^ 63 := h_ik.2.1
    have hwp := dropRecordAfterDealloc_some_placed_sepWP (Hk := Hk) (b469 := b469) hcap_lt hpc hrun hsp_al hsp
    refine SegExitBudget.of_sepWP (R0 := R0) hmem2 hwp ?_
    intro s1 P_f _ hsteps1 hpc1 hrun1 hmf1
      ⟨hvm1, hsp1, hsp1_al, htr1, _hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine w1t_tailDropRecordAt55c hdealloc hdrop x st_init st R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H scratch hscr
      prevCap prevPtr G sess.state hm1 hst ⟨hbud, ?_⟩
    refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hcrl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1.trans hvregs⟩,
      ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    refine Eq.mpr (congrArg (s1.mem ⊨ ·)
      (w1t_tfp_encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
    have hmf1' : s1.mem ⊨ ⌜P_ik_pure⌝ ∗
        ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗ (F ∗ R)) := by
      rw [satisfies_pure_sepConj]
      exact ⟨h_ik, hmf1⟩
    have hmf2 : s1.mem ⊨
        (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
        (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A.repAlloc (sp + 0x128#64) G sess.state ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          (⌜P_ik_pure⌝ ∗
            ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗ (F ∗ R))) =
          ((memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
           (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             sessionStateAt A.repAlloc (sp + 0x128#64) G sess.state ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) := by
        dsimp only [F, P_ik_pure]
        rw [w1t_tfp_encCommonPlaced_vmPreserved A lim st ctl x (x.draws S answers) s0 s s1 hvm1,
            sessionStateAt_unfold_cap A.repAlloc (sp + 0x128#64) G sess.state]
        sep_ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (flag_memRegion_weaken sp 0#8)) hmf2
    have heq2 :
        (memRegion (sp + 0x280#64) 0x1ea ∗
         (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
           sessionStateAt A.repAlloc (sp + 0x128#64) G sess.state ∗
           pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) =
        ((scratch sp ∗
          vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A.repAlloc (sp + 0x128#64) G sess.state ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
    rwa [← heq2]

private theorem w1t_tailDropRecord_tt [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    (hdealloc : subroutine_ok (lsProg_464 Hk) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok (lsProg_464 Hk) (lsmpl.base 442)
      (StoreKit.withLsRoCl lsmpl (dropSessionStructureLocal2BudgetSpec M A lim)))
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      x st_init st answers (encEntryPlaced + 0x46c#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
      R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) := by
  let R := encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hbud, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (w1t_tfp_encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) hmem
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (dropRecordSlots A.repAlloc sp scratch g rec ot none (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R at hmem
  unfold dropRecordSlots at hmem
  rcases ot with _ | ⟨pqCap, pqPtr, otr⟩
  · let F := scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0
    have hmem_re : s.mem ⊨ ((sp + 0x469#64) ↦₈ 0#8) ∗ (F ∗ R) := by
      have heq :
          (((scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗ memRegion (sp + 0x280#64) 8 ∗
            otrSlotAt A.repAlloc sp none ∗ cmSlotAt A.repAlloc sp none ∗ pollWith sp 0x9d0 [w3, w4, w5]) ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          (((sp + 0x469#64) ↦₈ 0#8) ∗ (F ∗ R)) := by
        have hslots := otr_none_slots_eq A.repAlloc sp
        have hassoc :
            (scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗ memRegion (sp + 0x280#64) 8 ∗
              otrSlotAt A.repAlloc sp none ∗ cmSlotAt A.repAlloc sp none ∗ pollWith sp 0x9d0 [w3, w4, w5]) =
            scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
              (memRegion (sp + 0x280#64) 8 ∗ otrSlotAt A.repAlloc sp none ∗ cmSlotAt A.repAlloc sp none) ∗
              pollWith sp 0x9d0 [w3, w4, w5] := by sep_ac_rfl
        rw [hassoc, hslots]
        dsimp only [F]
        sep_ac_rfl
      rwa [← heq]
    have hwp := dropRecord_otr_none_placed_sepWP (Hk := Hk) hpc hrun hsp_al hsp
    refine SegExitBudget.of_sepWP (R0 := R0) hmem_re hwp ?_
    intro s1 P_f _ hsteps1 hpc1 hrun1 hmf1
      ⟨hvm1, hsp1, hsp1_al, htr1, _hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine w1t_tailDropRecordCur hdealloc hdrop x st_init st R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H scratch hscr g rec 0#8 hm1 hst ⟨hbud, ?_⟩
    refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hcrl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1.trans hvregs⟩,
      ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    refine Eq.mpr (congrArg (s1.mem ⊨ ·)
      (w1t_tfp_encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
    have heq2 :
        (((sp + 0x469#64) ↦₈ 0#8) ∗ (F ∗ R)) =
        ((scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by
      dsimp only [F]
      rw [w1t_tfp_encCommonPlaced_vmPreserved A lim st ctl x (x.draws S answers) s0 s s1 hvm1]
      sep_ac_rfl
    rwa [← heq2]
  · unfold otrSlotAt cmSlotAt at hmem
    have h2a0 : sp + 0x288#64 + 0x18#64 = sp + 0x2a0#64 := by bv_omega
    have hotr_w : otrAt A.repAlloc (sp + 0x288#64) pqCap pqPtr otr ⊢
        vecU8At A.repAlloc (sp + 0x288#64) pqCap pqPtr otr.pqrState ∗ memRegion (sp + 0x2a0#64) 176 := by
      have h := otrAt_weaken_vecU8At A.repAlloc (sp + 0x288#64) pqCap pqPtr otr
      rwa [h2a0] at h
    have hmem_otr : s.mem ⊨
        vecU8At A.repAlloc (sp + 0x288#64) pqCap pqPtr otr.pqrState ∗
        (memRegion (sp + 0x2a0#64) 176 ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
          scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
          memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) := by
      have hmem_pre : s.mem ⊨
          otrAt A.repAlloc (sp + 0x288#64) pqCap pqPtr otr ∗
          (((sp + 0x469#64) ↦₈ 1#8) ∗
            scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
            memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
            encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
            encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) := by
        have heq :
            (((scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗ memRegion (sp + 0x280#64) 8 ∗
              (otrAt A.repAlloc (sp + 0x288#64) pqCap pqPtr otr ∗ ((sp + 0x469#64) ↦₈ 1#8)) ∗
              memRegion (sp + 0x350#64) 0x119 ∗ pollWith sp 0x9d0 [w3, w4, w5]) ∗ H) ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
            (otrAt A.repAlloc (sp + 0x288#64) pqCap pqPtr otr ∗
             (((sp + 0x469#64) ↦₈ 1#8) ∗
               scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
               memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
               pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
               encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
               encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R)) := by sep_ac_rfl
        rwa [← heq]
      have h1 := Satisfies.mono (sepConj_mono_left hotr_w) hmem_pre
      have heq2 :
          ((vecU8At A.repAlloc (sp + 0x288#64) pqCap pqPtr otr.pqrState ∗ memRegion (sp + 0x2a0#64) 176) ∗
           (((sp + 0x469#64) ↦₈ 1#8) ∗
             scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
             memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R)) =
          (vecU8At A.repAlloc (sp + 0x288#64) pqCap pqPtr otr.pqrState ∗
           (memRegion (sp + 0x2a0#64) 176 ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
             scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
             memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R)) := by sep_ac_rfl
      rwa [← heq2]
    by_cases hpq : pqCap = 0#64
    · subst hpq
      have h290 : sp + 0x288#64 + 8#64 = sp + 0x290#64 := by bv_omega
      have hvec_w : vecU8At A.repAlloc (sp + 0x288#64) 0#64 pqPtr otr.pqrState ⊢
          ((sp + 0x288#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x290#64) 16 := by
        have h := vecU8At_zero_weaken A.repAlloc (sp + 0x288#64) pqPtr otr.pqrState
        rwa [h290] at h
      have hmem_z := Satisfies.mono (sepConj_mono_left hvec_w) hmem_otr
      let F := memRegion (sp + 0x290#64) 16 ∗ memRegion (sp + 0x2a0#64) 176 ∗
        scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0
      have hmem_re : s.mem ⊨ (((sp + 0x288#64) ↦₆₄ 0#64) ∗ ((sp + 0x469#64) ↦₈ 1#8)) ∗ (F ∗ R) := by
        have heq :
            ((((sp + 0x288#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x290#64) 16) ∗
             (memRegion (sp + 0x2a0#64) 176 ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
               scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
               memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
               pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
               encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
               encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R)) =
            ((((sp + 0x288#64) ↦₆₄ 0#64) ∗ ((sp + 0x469#64) ↦₈ 1#8)) ∗ (F ∗ R)) := by
          dsimp only [F]; sep_ac_rfl
        rwa [← heq]
      have hwp := dropRecord_otr_zero_placed_sepWP (Hk := Hk) hpc hrun hsp_al hsp
      refine SegExitBudget.of_sepWP (R0 := R0) hmem_re hwp ?_
      intro s1 P_f _ hsteps1 hpc1 hrun1 hmf1
        ⟨hvm1, hsp1, hsp1_al, htr1, _hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
      subst hPf
      have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
        ⟨hm.1, htr1.trans hm.2⟩
      refine w1t_tailDropRecordCur hdealloc hdrop x st_init st R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H scratch hscr g rec 1#8 hm1 hst ⟨hbud, ?_⟩
      refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
        hcrl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1.trans hvregs⟩,
        ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
        hstack_le, ?_⟩
      refine Eq.mpr (congrArg (s1.mem ⊨ ·)
        (w1t_tfp_encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
      have hmf2 : s1.mem ⊨
          (memRegion (sp + 0x280#64) 8 ∗ ((sp + 0x288#64) ↦₆₄ 0#64) ∗
            memRegion (sp + 0x290#64) 16 ∗ memRegion (sp + 0x2a0#64) 176 ∗
            memRegion (sp + 0x350#64) 0x119) ∗
          (scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
            ((sp + 0x469#64) ↦₈ 1#8) ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
            encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
            encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by
        have heq :
            ((((sp + 0x288#64) ↦₆₄ 0#64) ∗ ((sp + 0x469#64) ↦₈ 1#8)) ∗ (F ∗ R)) =
            ((memRegion (sp + 0x280#64) 8 ∗ ((sp + 0x288#64) ↦₆₄ 0#64) ∗
              memRegion (sp + 0x290#64) 16 ∗ memRegion (sp + 0x2a0#64) 176 ∗
              memRegion (sp + 0x350#64) 0x119) ∗
             (scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
               ((sp + 0x469#64) ↦₈ 1#8) ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
               encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
               encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) := by
          dsimp only [F]
          rw [w1t_tfp_encCommonPlaced_vmPreserved A lim st ctl x (x.draws S answers) s0 s s1 hvm1]
          sep_ac_rfl
        rwa [← heq]
      have hmf3 := Satisfies.mono (sepConj_mono_left (otr_zero_post_weaken sp)) hmf2
      have heq2 :
          (memRegion (sp + 0x280#64) 0x1e9 ∗
           (scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
             ((sp + 0x469#64) ↦₈ 1#8) ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) =
          ((scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
      rwa [← heq2]
    · have h290 : sp + 0x288#64 + 8#64 = sp + 0x290#64 := by bv_omega
      have h298 : sp + 0x288#64 + 16#64 = sp + 0x298#64 := by bv_omega
      have hvec_w : vecU8At A.repAlloc (sp + 0x288#64) pqCap pqPtr otr.pqrState ⊢
          ((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗
            memRegion (sp + 0x298#64) 8 ∗ A.live pqPtr pqCap.toNat 1 ∗
            memRegion pqPtr pqCap.toNat := by
        have h := vecU8At_nz_weaken A.repAlloc (sp + 0x288#64) pqCap pqPtr otr.pqrState hpq
        rwa [h290, h298] at h
      have hmem_nz := Satisfies.mono (sepConj_mono_left hvec_w) hmem_otr
      let F_core := memRegion (sp + 0x298#64) 8 ∗ memRegion (sp + 0x2a0#64) 176 ∗
        scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
        nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
        memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - allocHookStack) ∗
        encSavedRegs s0.sp s0
      have hmem_re : s.mem ⊨
          (((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ ((sp + 0x469#64) ↦₈ 1#8)) ∗
          ((A.pool lim st s ∗ A.live pqPtr pqCap.toNat 1 ∗
            memRegion pqPtr pqCap.toNat ∗ stackAt sp allocHookStack ∗ F_core) ∗ R) := by
        have heq :
            ((((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗
              memRegion (sp + 0x298#64) 8 ∗ A.live pqPtr pqCap.toNat 1 ∗
              memRegion pqPtr pqCap.toNat) ∗
             (memRegion (sp + 0x2a0#64) 176 ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
               scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
               memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
               pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
               encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
               encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R)) =
            ((((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ ((sp + 0x469#64) ↦₈ 1#8)) ∗
             ((A.pool lim st s ∗ A.live pqPtr pqCap.toNat 1 ∗
               memRegion pqPtr pqCap.toNat ∗ stackAt sp allocHookStack ∗ F_core) ∗ R)) := by
          unfold encCommonPlaced
          rw [w1t_tfp_protocolAddressAt_atState]
          change ((((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗
            memRegion (sp + 0x298#64) 8 ∗ A.live pqPtr pqCap.toNat 1 ∗
            memRegion pqPtr pqCap.toNat) ∗
           (memRegion (sp + 0x2a0#64) 176 ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
             scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
             memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
              nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
              stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st s) ∗ R)) = _
          rw [stackAt_encSubStack_alloc sp]
          dsimp only [F_core]
          sep_ac_rfl
        rwa [← heq]
      have hwp := dropRecord_otr_nz_placed_step_pre (Hk := Hk) (pqPtr := pqPtr) hpq hpc hrun hsp_al hsp
      refine SegExitBudget.of_sepWP (R0 := R0) hmem_re hwp ?_
      intro s_pre P_pre _ hsteps_pre hpc_pre hrun_pre hmf_pre
        ⟨hvm_pre, hsp_pre, hsp_pre_al, htr_pre, hx0_pre, hx1_pre, hx2_pre, hlr_pre,
          hx19_pre, hx21_pre, hx23_pre, _hx25_pre, hx26_pre, hx27_pre, hx28_pre, hx29_pre, hvregs_pre, hP_pre⟩
      subst hP_pre
      have hm_dealloc : s_pre.mem ⊨
          (rustCliDeallocBudgetSpec M A lim).pre (pqPtr, pqCap.toNat, 1, st) s_pre ∗
          ((((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗
            ((sp + 0x469#64) ↦₈ 1#8) ∗ F_core) ∗ R) := by
        dsimp only [rustCliDeallocBudgetSpec]
        rw [hsp_pre]
        rw [← A.pool_transport lim st s s_pre hvm_pre] at hmf_pre
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨hx0_pre, hx1_pre, hx2_pre,
          by rw [hlr_pre]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 464 0x488#64 (by decide) (by decide)⟩,
          w1t_sat_of_eq hmf_pre (by dsimp only [sp]; sep_ac_rfl)⟩
      refine call_nopanic_placed (R0 := R0) hdealloc
        (pqPtr, pqCap.toNat, 1, st) hpc_pre hrun_pre hsp_pre_al hlr_pre hm_dealloc ?_
      intro s1 hsteps_call hpc1 hrun1 hsp1_pre hsp1_al hcs1 hmf1
      obtain ⟨hx19_c, _, hx21_c, _, hx23_c, _, _, hx26_c, hx27_c, hx28_c, hx29_c, hvregs_c⟩ := hcs1
      dsimp only [rustCliDeallocBudgetSpec] at hmf1
      rw [hsp_pre] at hmf1
      have hsp1 : s1.sp = sp := hsp1_pre.trans hsp_pre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hmf1
      obtain ⟨⟨hacp1, _⟩, hmf1⟩ := hmf1
      have htr_call : s1.trace = s_pre.trace := hacp1.2.1
      have hbud1 := w1t_tfp_seamBudget_step_freeOnly hbud (freeOnlyEvs_rustDeallocEvents pqCap.toNat 1)
      set st1 := M.stepEvents (rustDeallocEvents pqCap.toNat 1) st
      have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
        ⟨hm.1, (htr_call.trans htr_pre).trans hm.2⟩
      have hcrl1 : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem :=
        hcrl.of_keepsFrozen (hsteps_pre.trans hsteps_call).keepsFrozen
      refine w1t_tailDropRecordAfterDealloc hdealloc hdrop x st_init st1 R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H
        scratch hscr g rec 1#8 hm1 hst ⟨hbud1, ?_⟩
      refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al,
        (hx29_c.trans hx29_pre).trans hx29,
        (hx19_c.trans hx19_pre).trans hx19,
        hcrl1,
        (hvregs_c.trans hvregs_pre).trans hvregs⟩,
        ⟨(hx26_c.trans hx26_pre).trans hx26,
         (hx28_c.trans hx28_pre).trans hx28,
         (hx27_c.trans hx27_pre).trans hx27,
         (hx21_c.trans hx21_pre).trans hx21,
         (hx23_c.trans hx23_pre).trans hx23⟩,
        hstack_le, ?_⟩
      refine Eq.mpr (congrArg (s1.mem ⊨ ·)
        (w1t_tfp_encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
      have hmf2 : s1.mem ⊨
          (memRegion (sp + 0x280#64) 8 ∗ ((sp + 0x288#64) ↦₆₄ pqCap) ∗
            ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ memRegion (sp + 0x298#64) 8 ∗
            memRegion (sp + 0x2a0#64) 176 ∗ memRegion (sp + 0x350#64) 0x119) ∗
          (scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
            ((sp + 0x469#64) ↦₈ 1#8) ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
            encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
            encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R) := by
        have heq :
            ((A.pool lim st1 s1 ∗ stackAt sp allocHookStack) ∗
             ((((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗
               ((sp + 0x469#64) ↦₈ 1#8) ∗ F_core) ∗ R)) =
            ((memRegion (sp + 0x280#64) 8 ∗ ((sp + 0x288#64) ↦₆₄ pqCap) ∗
              ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ memRegion (sp + 0x298#64) 8 ∗
              memRegion (sp + 0x2a0#64) 176 ∗ memRegion (sp + 0x350#64) 0x119) ∗
             (scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
               ((sp + 0x469#64) ↦₈ 1#8) ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
               encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
               encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R)) := by
          unfold encCommonPlaced
          rw [w1t_tfp_protocolAddressAt_atState]
          change _ = ((memRegion (sp + 0x280#64) 8 ∗ ((sp + 0x288#64) ↦₆₄ pqCap) ∗
              ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ memRegion (sp + 0x298#64) 8 ∗
              memRegion (sp + 0x2a0#64) 176 ∗ memRegion (sp + 0x350#64) 0x119) ∗
             (scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
               ((sp + 0x469#64) ↦₈ 1#8) ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
               encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
               ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
                nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
                stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st1 s1) ∗ R))
          rw [stackAt_encSubStack_alloc sp]
          dsimp only [F_core]
          sep_ac_rfl
        rwa [← heq]
      have hmf3 := Satisfies.mono (sepConj_mono_left (otr_nz_post_weaken sp pqCap pqPtr)) hmf2
      have heq2 :
          (memRegion (sp + 0x280#64) 0x1e9 ∗
           (scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
             ((sp + 0x469#64) ↦₈ 1#8) ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R)) =
          ((scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
      rwa [← heq2]

end W1T_EncTails

section W1T_EncTailsAssemble

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto OutgoingTripleRatchet)
open CryptoGames.LibsignalSessionApi (ApiError CiphertextMessage SessionRecord StoreAnswers)
open CryptoVerification (LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.CliRatchet.EncPlaced (lsProg_464)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt (
  encEntryPlaced encMidMetaPlaced
)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost sessionRecordAt)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (
  WithStoresEncGhost cmScratch curScratch
)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails (
  ResStaged SpeStaged TailModel cmSlotAt dropRecordSlots pollWith tailRegs words64At
)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr (
  dropRecordBase dropRecordSlots_eq memRegion_24_eq memRegion_46a_src
  pollWith_9d0_eq pollWith_9d0_eq' pollWith_b00_eq pollWith_src_eq words64At_three_entails
)
open CryptoVerification.LibsignalPublicApi.StoreKit (SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc vecAt)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudget (
  EncCalleesPlaced EncTailVPlaced PublicApiEncHooksPlaced SegExitPlaced
  toTempTwinsIkitEnv toTempTwinsKitEnv
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget (
  encTailVPlaced_eq_tempTwins segExitPlaced_eq_tempTwins
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlacedBudget (
  encTail_placed_run segExit_placed_of_run
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux (
  EncTailsVTPlaced h45_otrEncryptPlacedOkQ_false
)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)

attribute [local irreducible] Program.fetch Program.externAt?

private theorem w1t_bv_add_sub_local (x a b : BitVec 64) : x + a - b = x + (a - b) := by
  bv_omega

attribute [local arm64_norm] w1t_bv_add_sub_local BitVec.neg_neg

private theorem w1t_tails_dropRecordSlots_eq (A : RustAlloc) (sp : BitVec 64)
    (scratch : BitVec 64 → SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (cm : Option CiphertextMessage) (poll : SepProp) :
    dropRecordSlots A sp scratch g rec ot cm poll =
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.dropRecordSlots
        A sp scratch g rec ot cm poll :=
  rfl

private theorem w1t_tails_pollWith_3_eq (sp : BitVec 64) (off : Nat) (w3 w4 w5 : BitVec 64) :
    pollWith sp off [w3, w4, w5] =
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.pollWith
        sp off [w3, w4, w5] :=
  rfl

private theorem w1t_tails_words64At_3_eq (a w3 w4 w5 : BitVec 64) :
    words64At a [w3, w4, w5] =
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.words64At
        a [w3, w4, w5] :=
  rfl

private theorem w1t_tails_cmSlotAt_eq (A : RustAlloc) (sp : BitVec 64)
    (cm : Option CiphertextMessage) :
    cmSlotAt A sp cm =
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.cmSlotAt A sp cm :=
  rfl

private theorem w1t_signal_placed_run_vm [LibsignalPlacement] {Hk : LibsignalHooks}
    (w0 w1 w2 w3 w4 w5 sp : BitVec 64) (s : State)
    (hpc : s.pc = encEntryPlaced + 0xc14#64) (hrun : s.status = .Running)
    (hssp : s.sp = sp) (hal : (sp &&& 15#64 == 0#64) = true)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64)
    (hregs : tailRegs w0 w1 w2 sp s) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x46c#64) s
      (memRegion (sp + 0x9d0#64) 24 ∗ words64At (sp + 0xb00#64) [w3, w4, w5])
      (fun s' P => VmPreserved s s' ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧
        tailRegs w0 w1 w2 sp s' ∧
        ∀ m F, (m ⊨ P ∗ F) →
          (m ⊨ (words64At (sp + 0x9d0#64) [w3, w4, w5] ∗ memRegion (sp + 0xb00#64) 24) ∗ F)) := by
  obtain ⟨hx26, hx28, hx27, hx21, hx23⟩ := hregs
  unfold encEntryPlaced at hpc ⊢
  rw [memRegion_24_eq]
  simp only [sepExists_sepConj_left]
  refine SepWP.exists_elim fun u2 => SepWP.exists_elim fun u1 => SepWP.exists_elim fun u0 => ?_
  simp only [words64At, CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.words64At,
    sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
    · unfold tailRegs
      simp only [wp_norm, arm64_norm, *]
    · intro m F hm
      have h := words64At_three_entails (sp + 0xb00#64) w3 w4 w5
      simp only [CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.words64At,
        sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at h
      have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right h)))) hm
      simpa only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h2)

private theorem w1t_store_placed_run_vm [LibsignalPlacement] {Hk : LibsignalHooks}
    (w0 w1 w2 w3 w4 w5 sp : BitVec 64) (s : State) (pcOff src : Nat)
    (hsel : (pcOff, src) = (0xc20, 0x970) ∨ (pcOff, src) = (0xe28, 0x990) ∨
      (pcOff, src) = (0xf2c, 0x9b0))
    (hpc : s.pc = encEntryPlaced + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hssp : s.sp = sp) (hal : (sp &&& 15#64 == 0#64) = true)
    (hregs : tailRegs w0 w1 w2 sp s) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0xd40#64) s
      (memRegion (sp + 0x9d0#64) 24 ∗ words64At (sp + BitVec.ofNat 64 src) [w3, w4, w5])
      (fun s' P => VmPreserved s s' ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧
        tailRegs w0 w1 w2 sp s' ∧
        ∀ m F, (m ⊨ P ∗ F) →
          (m ⊨ (words64At (sp + 0x9d0#64) [w3, w4, w5] ∗
            memRegion (sp + BitVec.ofNat 64 src) 24) ∗ F)) := by
  obtain ⟨hx26, hx28, hx27, hx21, hx23⟩ := hregs
  unfold encEntryPlaced at hpc ⊢
  rw [memRegion_24_eq]
  simp only [sepExists_sepConj_left]
  refine SepWP.exists_elim fun u2 => SepWP.exists_elim fun u1 => SepWP.exists_elim fun u0 => ?_
  dsimp only [lsProg_464, ite_true]
  rcases hsel with h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
  · simp only [words64At, CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.words64At,
      sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    by_vm_steps (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
      · unfold tailRegs
        simp only [wp_norm, arm64_norm, *]
      · intro m F hm
        rw [memRegion_24_eq]
        simp only [CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.words64At,
          sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
          satisfies_sepExists, BitVec.add_assoc, BitVec.reduceAdd]
        exact ⟨w5, w4, w3, by simpa only [sepConj_assoc] using hm⟩)

/-- Assembles `EncTailsVTPlaced` from `PublicApiEncHooksPlaced`. -/
theorem w1t_encTailsVTPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState} {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv} {Hk : LibsignalHooks}
    (hhooks : PublicApiEncHooksPlaced A lim Hk) :
    EncTailsVTPlaced A lim ikit ikitEnv ist0 C ctl uuidTryParse S sendEnv encodeRecord Hk := by
  intro kit kitEnv st0 Scope
  have hC := EncCalleesPlaced.of_otrEnc hhooks
    (h45_otrEncryptPlacedOkQ_false (C := C) (ctl := ctl) (parse := uuidTryParse)
      (S := S) (sendEnv := sendEnv))
  have hdealloc := ls_hook_ok_ultra_of_mem (prog := lsProg_464 Hk) hhooks.dealloc
  have hDropRec :
      ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
        (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
        (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (scratch : BitVec 64 → SepProp),
        (scratch = curScratch ∨ scratch = cmScratch) →
        ∀ (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
          (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))),
          TailModel kit st0 ikit ist0 C S uuidTryParse encodeRecord x answers (.error e) s0 s →
          SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
          EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
            x st_init st answers (encEntryPlaced + 0x46c#64) (tailRegs w0 w1 w2)
            (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
              (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp) R s0 s →
          SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
            encodeRecord Hk x st_init R s0 s (fun _ => False) := by
    intro x st_init st R s0 s answers e w0 w1 w2 w3 w4 w5 Hp scratch hscr g rec ot hm hst hs
    rw [segExitPlaced_eq_tempTwins]
    rw [encTailVPlaced_eq_tempTwins] at hs
    exact w1t_tailDropRecord_tt hdealloc hC.toTempTwinsFull.dropSs x st_init st R s0 s answers e
      w0 w1 w2 w3 w4 w5 Hp scratch hscr g rec ot hm hst hs
  have hCmDrop :
      ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
        (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
        (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (scratch : BitVec 64 → SepProp),
        (scratch = curScratch ∨ scratch = cmScratch) →
        ∀ (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
          (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
          (m : CiphertextMessage),
          TailModel kit st0 ikit ist0 C S uuidTryParse encodeRecord x answers (.error e) s0 s →
          SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
          EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
            x st_init st answers (encEntryPlaced + 0xd40#64) (tailRegs w0 w1 w2)
            (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot (some m)
              (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp) R s0 s →
          SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
            encodeRecord Hk x st_init R s0 s (fun _ => False) := by
    intro x st_init st R s0 s answers e w0 w1 w2 w3 w4 w5 Hp scratch hscr g rec ot m hm hst hs
    exact LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.CmDropPlacedBudget.tailCmDrop_placed_ok
      hC.cmDrop hDropRec x st_init st R s0 s answers e w0 w1 w2 w3 w4 w5 Hp scratch hscr g rec ot m
      hm hst hs
  refine
    { tailDropRecord := hDropRec
      tailSignalEncryptErr := ?_
      tailCmDrop := hCmDrop
      tailStoreHookErr := ?_
      tailWriteResult := ?_
      tailWriteErr := ?_
      tailFreePrevSessions := ?_
      tailFromSessionStateErr := ?_
      tailPreKeyEncryptErr := ?_ }
  · intro x st_init st R s0 s answers e w0 w1 w2 w3 w4 w5 Hp scratch hscr g rec ot hm hst hs
    refine segExit_placed_of_run hm (fun hL => ?_) (fun s' hm' hs' =>
      hDropRec x st_init st R s0 s' answers e w0 w1 w2 w3 w4 w5 Hp scratch hscr g rec ot hm' hst hs')
    refine encTail_placed_run (C := C) (Hk := Hk)
      (Act := fun sp => memRegion (sp + 0x9d0#64) 24 ∗ words64At (sp + 0xb00#64) [w3, w4, w5])
      (Fr := fun sp => (memRegion (sp + 0x46a#64) 0x566 ∗ memRegion (sp + 0x9e8#64) 0x118 ∗
        memRegion (sp + 0xb18#64) 0x68) ∗ dropRecordBase A.repAlloc sp scratch g rec ot ∗
        cmSlotAt A.repAlloc sp none ∗ Hp)
      (Act' := fun sp => words64At (sp + 0x9d0#64) [w3, w4, w5] ∗ memRegion (sp + 0xb00#64) 24)
      hs ?_ ?_ ?_ hL
    · intro sp
      refine Entails.of_eq ?_
      rw [w1t_tails_dropRecordSlots_eq, w1t_tails_pollWith_3_eq, w1t_tails_cmSlotAt_eq,
        w1t_tails_words64At_3_eq, dropRecordSlots_eq, pollWith_b00_eq]
      sep_ac_rfl
    · intro sp
      refine Entails.of_eq ?_
      rw [w1t_tails_dropRecordSlots_eq, w1t_tails_pollWith_3_eq, w1t_tails_cmSlotAt_eq,
        w1t_tails_words64At_3_eq, dropRecordSlots_eq, pollWith_9d0_eq]
      sep_ac_rfl
    · intro sp hpc hmeta hregs hsp
      obtain ⟨hrun, hssp, _, hspal, hx29, -⟩ := hmeta
      have hal : (sp &&& 15#64 == 0#64) = true := by
        simpa [State.spAligned, hssp, hsp] using hspal
      exact w1t_signal_placed_run_vm w0 w1 w2 w3 w4 w5 sp s hpc hrun (hssp.trans hsp.symm) hal
        (by rw [hx29, hsp]; bv_omega) hregs
  · intro x st_init st R s0 s answers e w0 w1 w2 w3 w4 w5 Hp scratch hscr g rec ot m pcOff src hsel hm hst hs
    have hsrc : 0x46a ≤ src ∧ src + 24 ≤ 0x9d0 := by
      rcases hsel with h | h | h <;> cases h <;> decide
    refine segExit_placed_of_run hm (fun hL => ?_) (fun s' hm' hs' =>
      hCmDrop x st_init st R s0 s' answers e w0 w1 w2 w3 w4 w5 Hp scratch hscr g rec ot m hm' hst hs')
    refine encTail_placed_run (C := C) (Hk := Hk)
      (Act := fun sp => memRegion (sp + 0x9d0#64) 24 ∗ words64At (sp + BitVec.ofNat 64 src) [w3, w4, w5])
      (Fr := fun sp => (memRegion (sp + 0x46a#64) (src - 0x46a) ∗
          memRegion (sp + BitVec.ofNat 64 (src + 24)) (0x9d0 - (src + 24)) ∗
          memRegion (sp + 0x9e8#64) 0x198) ∗ dropRecordBase A.repAlloc sp scratch g rec ot ∗
          cmSlotAt A.repAlloc sp (some m) ∗ Hp)
      (Act' := fun sp => words64At (sp + 0x9d0#64) [w3, w4, w5] ∗
        memRegion (sp + BitVec.ofNat 64 src) 24)
      hs ?_ ?_ ?_ hL
    · intro sp
      refine Entails.of_eq ?_
      rw [w1t_tails_dropRecordSlots_eq, w1t_tails_pollWith_3_eq, w1t_tails_cmSlotAt_eq,
        w1t_tails_words64At_3_eq, dropRecordSlots_eq, pollWith_src_eq sp w3 w4 w5 src hsrc.2]
      sep_ac_rfl
    · intro sp
      refine Entails.of_eq ?_
      rw [w1t_tails_dropRecordSlots_eq, w1t_tails_pollWith_3_eq, w1t_tails_cmSlotAt_eq,
        w1t_tails_words64At_3_eq, dropRecordSlots_eq, pollWith_9d0_eq', memRegion_46a_src sp src hsrc.1 hsrc.2]
      sep_ac_rfl
    · intro sp hpc hmeta hregs hsp
      obtain ⟨hrun, hssp, _, hspal, -⟩ := hmeta
      have hal : (sp &&& 15#64 == 0#64) = true := by
        simpa [State.spAligned, hssp, hsp] using hspal
      exact w1t_store_placed_run_vm w0 w1 w2 w3 w4 w5 sp s pcOff src hsel hpc hrun
        (hssp.trans hsp.symm) hal hregs
  · intro x st_init st R s0 s answers res w0 w1 w2 w3 bs Hp hm hres hs
    exact LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailWriteResultPlacedBudget.tailWriteResult_placed_ok
      x st_init st R s0 s answers res w0 w1 w2 w3 bs Hp hm hres hs
  · intro x st_init st R s0 s answers e w0 w1 w2 w3 w4 w5 Hp hm hst hs
    rw [segExitPlaced_eq_tempTwins]
    rw [encTailVPlaced_eq_tempTwins] at hs
    exact LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFreePrevSessionsPlacedBudget.tailWriteErr_placed_ok
      x st_init st R s0 s answers e w0 w1 w2 w3 w4 w5 Hp hm hst hs
  · intro x st_init st R s0 s answers e w0 w1 w2 w3 w4 w5 Hp prevCap prevPtr hm hst hs
    rw [segExitPlaced_eq_tempTwins]
    rw [encTailVPlaced_eq_tempTwins] at hs
    exact w1t_tailFreePrevSessions hdealloc x st_init st R s0 s answers e w0 w1 w2 w3 w4 w5 Hp
      prevCap prevPtr hm hst hs
  · intro x st_init st R s0 s answers e w0 w1 w2 w3 w4 w5 Hp g rec hm hst hs
    refine LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFromSessionStateErrPlacedBudget.tailFromSessionStateErrPlaced_step
      x st_init st R s0 s answers e w0 w1 w2 w3 w4 w5 Hp g rec hm hs
      fun s1 b469 hm1 hs1 => ?_
    rw [segExitPlaced_eq_tempTwins]
    rw [encTailVPlaced_eq_tempTwins] at hs1
    exact w1t_tailDropRecordCur hdealloc hC.toTempTwinsFull.dropSs x st_init st R s0 s1 answers e
      w0 w1 w2 w3 w4 w5 Hp curScratch (Or.inl rfl) g rec b469 hm1 hst hs1
  · intro x st_init st R s0 s answers e w0 w1 w2 w3 w4 w5 Hp scratch hscr g rec ot ok hsom hm hst hs
    exact LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrPreKeyEncryptPlacedBudget.tailPreKeyEncryptErr_placed_ok
      hhooks.dealloc hDropRec x st_init st R s0 s answers e w0 w1 w2 w3 w4 w5 Hp scratch hscr g rec
      ot ok hsom hm hst hs

end W1T_EncTailsAssemble

/-! ## Parametric `encrypt` Slot and `PeerSpqrStateTight640` Guard Lift -/

section W1T_Slot

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open VerifiedLibraries (mallocngLib)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.HMAC (ShaState hmacWith keyToBytes32 sha256IV)
open CryptoGames.LibsignalSession (
  ChainKey Crypto Mut OutgoingTripleRatchet SessionState ShaCompress
)
open CryptoGames.LibsignalSessionApi (
  CiphertextMessage PreKeySignalMessage Session SessionRecord execOk
)
open CryptoGames.Ratchet (chainHmac chainKeySeed)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalFullPlacement LibsignalHooks LibsignalPlacement
  LibsignalRoLoaded blkLib_eq_39 blkLib_eq_114 blkPC_38 blkPC_39 blkPC_60 blkPC_61 blkPC_69
  blkPC_114 blkPC_252 blkPl_38 blkPl_39 blkPl_60 blkPl_61 blkPl_69 blkPl_114 blkPl_252
  libsignalMutatedBlocks libsignalSessionExterns libsignalSessionLib lsProg_114
  lsRustNoAllocShimSym ls_externAt?_of_mem ls_hook_ok_ultra_of_mem ls_subroutine_ok_of_block
  lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.Cli.LibsignalTripleRatchet (otrEncryptName)
open CryptoVerification.CliRatchet.EncPlaced (instIsLsBlockProg_464 lsProg_464)
open CryptoVerification.CliRatchet.Placed (blkPC_428 blkPl_428 instIsLsBlockProg_428)
open CryptoVerification.CliRatchet.SendPlaced (blkPC_427 blkPl_427 instIsLsBlockProg_427)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives aesEncHookMallocng pqxdhSpqrModel)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles NoFsEv ls_subroutine_ok_rocl_of_block subroutine_ok_withLsCodeRoLoaded_of_plain
  subroutine_ok_withLsCodeRoLoaded_of_rocl withLsRoCl
)
open CryptoVerification.LibsignalSession (hmacSpec)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (
  CallingConventionPreserved_of_calleeSaved Frame disjointRegions_of_ro_rw
  hookMemcpy_eq_memcpyHook hookMemset_eq_memsetHook lsCompress256Sym lsMemcpySym lsMemsetSym
  lsSha256IVAddr new_from_slice_placed_run rodata_placed_sha256IV
)
open CryptoVerification.LibsignalSessionRepr (chainKeyBytes)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrDecodeState spqrV1 spqrV1_emptyOk)
open CryptoVerification.LibsignalTripleRatchet (
  HkdfPlacedHooks LibsignalCodeRoLoaded SendCall SpqrModel blkPC_63 blkPl_63
  extract_withLsCodeRoLoaded keys_ls_hook_ok_of_mem lsPanicConstAddOverflowSym
  newFromSliceSpec newFromSliceStack noAllocShimSpec
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer (isBlock_nfsResult)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsAesEncSym lsReadFileSym
)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.KitInst (
  cliGhostExterns_blackBox cliIdentityVtRoSym
)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit (
  savePollNeed saveShimNeed trustPollNeed trustShimNeed
)
open CryptoVerification.SignalSession.Cli.MainHops (
  cliIo cliRunBudgets cliRunNeeds cliWrOk
)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_569 lsProg_589)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (EncGhost mkSlot)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks CliGhostHooksFs cliExternsPlaced_row cliGhostExterns
)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1EncGhost)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  aesEnc_row_placed cliEncRecOk_opened
  cliGhostExterns_panic_handle_alloc_error cliGhostExterns_panic_handle_error
  cliGhostExterns_panic_option_expect_failed cliGhostExterns_sat_of_cliExternsPlaced
  encodeInjOn_deserializeScopeP_Q scopeIn scopeKit
  scopeKit_pqrState_lt scopeKit_recordInScopeEnc
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.DecodeState (canonicalV1InnerHeap)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv VmPreserved
)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (FormatInnerEnv aesEncBudgetSpec formatInnerBudgetEnvSpec withVmPreserved)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux (
  PublicApiEncHooksPlaced otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudget (
  withStores_placed_okVT_fs_cli
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.RootPlacedBudget (
  otrEncryptEmpty_coins_placed_ok otrEncryptV1_coins_placed_ok
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux (
  hmacExcHooks hmacExcHooks_compress hmacExcHooks_memcpy runsTo_block_lift_vm
  stripExecOutside_readBytes stripExecOutside_readable stripExecOutside_rw unstrip_frame
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat (
  expand_multi_info_placed_vm_ok_of_other_block_sat
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat (
  extract_placed_vm_ok_of_other_block_sat
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (fineAesEnc_budget_hookSat)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (
  w1BinaryIdKitPlacedBudgetFixed w1BinarySessKitPlacedBudgetFixed w1BinarySessKitPlacedFixed_okSE
)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges (
  tlb_DecodeStateGuardedEnv tlb_EpochDirectionMergeBlk325TightOkOf
  tlb_V1StateMergeBlk325TightOkOf tlb_V1StateMergePlacedTightOkOf
)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (
  PeerSpqrStateTight640 SpqrStateTight640 peerSpqrStateTight640_of_cliSessionStoreSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudgetAux (
  FromKeyEnv FromOtrEnv WithStoresEncEnv
)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins (
  OtrEncryptCoreEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget (
  cliIdKitOkIE_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCallees (
  OtrRoCalleesPlacedOk nextChainKey_39_vm_cro_ok transfer_tr_cro_of_block uuidTryParse_252_vm_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams (
  w2IdVt_placed_ok w2SessVt_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget (
  CliRunHooksBundle
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (encSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget (
  cliExternsPlaced_rustAllocShimVm_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudget (
  W1InnerPlacedOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget (
  CliEncryptSlotEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudget (
  cliEncrypt_slot_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks CliGhostSpqrAllocHooks
  cliExternsPlaced_alloc_budget_sat cliExternsPlaced_compress256Multi_budget_sat
  cliExternsPlaced_dealloc_budget_sat cliExternsPlaced_durationSinceBounded_budget_sat
  cliExternsPlaced_exactMemcpy_sat
  cliExternsPlaced_framelessMemcpy_budget_sat cliExternsPlaced_noAllocShim_budget_sat
  cliExternsPlaced_realloc_budget_sat cliExternsPlaced_sessionMemcpyRegion_budget_sat
  cliExternsPlaced_sessionMemsetRegion_budget_sat cliExternsPlaced_shim_budget_sat
  cliExternsPlaced_timeAdd_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (spqrSendCoinsPlacedSpecTOfEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (
  sessDeserialize_cli_dcan_byBytes_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget (
  serializeCanonSeqFree_cli_placed
)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStatePlacedOkOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget (
  DecodeStateCalleeContractsClPlacedX
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget (
  public_key_serialize_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeysBudget (
  messageKeysPlacedSpec message_keys_placed_cro_ok
)
open LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat (
  hmac_placed_cro_ok_at_block_sat new_from_slice_placed_cro_budget_ok_at_block_sat
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (
  HkdfPlacedHooksExactBudgetSat
)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.CoreStepEnvBudget (nextChainKeyPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceIdBudget (
  parseSid_placed_ok_of_code
)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (generateKeysSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget (
  generateKeys_placed_ok_of_contracts
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.AddressesBudget (
  serialize_addresses_placed_ok_of_rustAllocShimVm
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudget (computeMac_placed_cro_ok)
open LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux (newFromSliceBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget (encode_varint_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLenBudget (encoded_len_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewBudget (signalMessageNew_placed_cro_ok)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget (signalMessageNewSpec)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem w1t_cal_subroutine_ok_storeKitCro_of_trCro [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hc, hpre⟩ :=
        CryptoVerification.LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hp
      dsimp only [withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨⟨hc.1, hc.2⟩, hpre⟩)
    (fun _ _ _ _ hq => hq)

private theorem w1t_cal_subroutine_ok_trCro_of_storeKitCro [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hc, hpre⟩ := extract_withLsCodeRoLoaded hp
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨⟨hc.1, hc.2⟩, hpre⟩)
    (fun _ _ _ _ hq => hq)

private theorem w1t_cal_hookSat_noAllocShimBudget_of_withVmPreserved {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)) :
    HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, noAllocShimSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

private theorem w1t_cal_stripS_read64 (p : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS p s).mem.read64 a = s.mem.read64 a := by
  cases s
  simp [ProofLib.stripS, Memory.read64, ProofLib.strip_read8]

private theorem w1t_cal_stripExecOutside_hmacSt {F : ShaState → List (BitVec 8) → ShaState}
    {p : BitVec 64 → Bool} {m : Memory} {a : BitVec 64} {key msg : List (BitVec 8)} :
    CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt
      (ProofLib.stripExecOutside p m) a F key msg ↔
    CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt m a F key msg := by
  unfold CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt
  simp only [stripExecOutside_readBytes, Memory.read64, ProofLib.strip_read8]

private theorem w1t_cal_new_from_slice_114_vm_cro_ok [LibsignalPlacement] (F : ShaCompress)
    {H : LibsignalHooks}
    (h_mc : H lsMemcpySym = some memcpyHook)
    (h_ms : H lsMemsetSym = some memsetHook)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok ((blkPC_114).rebase (blkPl_114).base H) (blkPl_114).base
      (withLsCodeRoLoaded lsmpl (newFromSliceBudgetSpec F)) := by
  refine subroutine_ok_intro fun ⟨ret, keyA, key⟩ R s0 hpc hrun hpre_cro hsp => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre_cro
  dsimp only [newFromSliceBudgetSpec, withVmPreserved, newFromSliceSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_nat, hkey_len⟩, hsep⟩
  have hb_out := IsBlock.memRegion ret 0x98
  have hb_key := IsBlock.pointsToBytes (a := keyA) key
  have hb_stk := IsBlock.memRegion (s0.sp - 544#64) 544
  have hsep_out : s0.mem ⊨ memRegion ret 0x98 ∗ (memRegion (s0.sp - 544#64) 544 ∗
      ((keyA ↦ₛ key) ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_key : s0.mem ⊨ (keyA ↦ₛ key) ∗ (memRegion (s0.sp - 544#64) 544 ∗
      (memRegion ret 0x98 ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 544#64) 544 ∗
      (memRegion ret 0x98 ∗ (keyA ↦ₛ key) ∗ R) := by
    simp only [newFromSliceStack, stackAt] at hsep
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hkey_eq : s0.mem.readBytes keyA key.length = key := (hb_key.read hsep_key).2
  have hrw_out : s0.mem.RW ret 0x98 := fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_stk : s0.mem.RW (s0.sp - 544#64) 544 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_placed_sha256IV hro
  have hread_iv : s0.mem.Readable lsSha256IVAddr 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hdisj_iv : DisjointRegions lsSha256IVAddr 32 (s0.sp - 544#64) 544 :=
    disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk
  have hdisj_out : DisjointRegions (s0.readReg64 .x0) 0x98 (s0.sp - 544#64) 544 := by
    rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out
  have hdisj_key : (s0.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s0.readReg64 .x1) (s0.readReg64 .x2).toNat (s0.sp - 544#64) 544 := by
    rcases key with _ | ⟨k0, ks⟩
    · exact Or.inl hx2_nat
    · exact Or.inr (by
        rw [hx1, hx2_nat]
        exact hb_key.disjoint hb_stk (by simp) (by decide) hsep_key)
  have hal_sp : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  intro _hL114_in
  have heq114 : ∀ X, lsProg_114 X = libsignalSessionLib.blockProgram lsmpl 114 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := lsProg_114 X)
  have hL114_bp : (libsignalSessionLib.blockProgram lsmpl 114 H).CodeLoaded s0.mem :=
    hcl 114 (by decide) (by decide) H (fun _ => none) Syscall.standard
  let Q114 := libsignalSessionLib.blockProgram lsmpl 114 (hmacExcHooks F H)
  let kp114 := ProofLib.progKeep Q114
  have hm_s0 : (ProofLib.stripS kp114 s0).mem = ProofLib.stripExecOutside kp114 s0.mem := by
    cases s0; rfl
  have hrunsP := new_from_slice_placed_run (F := F) (s₀ := s0) h_mc h_c256
    hpc hrun (by rw [hx2_nat]; exact hkey_len) hiv_eq hread_iv hdisj_iv
    (by rw [hx0]; exact hrw_out) hrw_stk hdisj_out hdisj_key hal_sp
  have hrunsQ := new_from_slice_placed_run (F := F) (s₀ := ProofLib.stripS kp114 s0)
    (hmacExcHooks_memcpy F H) (hmacExcHooks_compress F H)
    (by cases s0; exact hpc)
    (by cases s0; exact hrun)
    (by have hr : (ProofLib.stripS kp114 s0).readReg64 .x2 = s0.readReg64 .x2 := by cases s0; rfl
        rw [hr, hx2_nat]; exact hkey_len)
    (by rw [hm_s0, stripExecOutside_readBytes]; exact hiv_eq)
    (by rw [hm_s0]; exact stripExecOutside_readable kp114 s0.mem _ _ hread_iv)
    (by have hs : (ProofLib.stripS kp114 s0).sp = s0.sp := by cases s0; rfl
        rwa [hs])
    (by have hr : (ProofLib.stripS kp114 s0).readReg64 .x0 = s0.readReg64 .x0 := by cases s0; rfl
        rw [hm_s0, hr, hx0]; exact stripExecOutside_rw kp114 s0.mem _ _ hrw_out)
    (by have hs : (ProofLib.stripS kp114 s0).sp = s0.sp := by cases s0; rfl
        rw [hm_s0, hs]; exact stripExecOutside_rw kp114 s0.mem _ _ hrw_stk)
    (by have hr : (ProofLib.stripS kp114 s0).readReg64 .x0 = s0.readReg64 .x0 := by cases s0; rfl
        have hs : (ProofLib.stripS kp114 s0).sp = s0.sp := by cases s0; rfl
        rwa [hr, hs])
    (by have hr1 : (ProofLib.stripS kp114 s0).readReg64 .x1 = s0.readReg64 .x1 := by cases s0; rfl
        have hr2 : (ProofLib.stripS kp114 s0).readReg64 .x2 = s0.readReg64 .x2 := by cases s0; rfl
        have hs : (ProofLib.stripS kp114 s0).sp = s0.sp := by cases s0; rfl
        rwa [hr1, hr2, hs])
    (by have hs : (ProofLib.stripS kp114 s0).sp = s0.sp := by cases s0; rfl
        rwa [hs])
  obtain ⟨sf, hsteps_bp, hvm, htr, hvregs, hsf_or⟩ :=
    runsTo_block_lift_vm h_mc h_ms h_c256 blkLib_eq_114 rfl rfl hL114_bp
      (heq114 H ▸ hrunsP) (heq114 _ ▸ hrunsQ)
      (fun _ hs => hs.2.1) (fun _ hs => hs.2.1)
  have hsteps : Steps ((blkPC_114).rebase (blkPl_114).base H) s0 sf := by
    change Steps (lsProg_114 H) s0 sf
    rwa [heq114 H]
  have hsf_raw : sf.pc = s0.readReg64 .lr ∧ sf.status = .Running ∧
      CryptoVerification.LibsignalSession.CryptoHmacSha256.CalleeSaved s0 sf ∧
      sf.mem.read64 (s0.readReg64 .x0) = 0#64 ∧
      CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt sf.mem (s0.readReg64 .x0 + 8#64)
        F (s0.mem.readBytes (s0.readReg64 .x1) (s0.readReg64 .x2).toNat) [] ∧
      Frame s0.mem sf.mem [(s0.readReg64 .x0, 0x98), (s0.sp - 544#64, 544)] := by
    rcases hsf_or with hsf_strip | hsf_real
    · rcases hsf_strip with ⟨hpc1, hstat1, hcs1, htag1, hhmac1, hframe1⟩
      have hm_sf : (ProofLib.stripS kp114 sf).mem = ProofLib.stripExecOutside kp114 sf.mem := by
        cases sf; rfl
      have hr_s00 : (ProofLib.stripS kp114 s0).readReg64 .x0 = s0.readReg64 .x0 := by cases s0; rfl
      have hr_s01 : (ProofLib.stripS kp114 s0).readReg64 .x1 = s0.readReg64 .x1 := by cases s0; rfl
      have hr_s02 : (ProofLib.stripS kp114 s0).readReg64 .x2 = s0.readReg64 .x2 := by cases s0; rfl
      have hr_s0lr : (ProofLib.stripS kp114 s0).readReg64 .lr = s0.readReg64 .lr := by cases s0; rfl
      have hsp_s0 : (ProofLib.stripS kp114 s0).sp = s0.sp := by cases s0; rfl
      rw [hm_s0, hm_sf, hr_s00, hsp_s0] at hframe1
      rw [hm_s0, hm_sf, hr_s00, hr_s01, hr_s02, stripExecOutside_readBytes] at hhmac1
      exact ⟨(by rw [hr_s0lr] at hpc1; cases sf; exact hpc1),
        (by cases sf; exact hstat1),
        ⟨by cases s0; cases sf; exact hcs1.1,
         fun r hr => by have := hcs1.2 r hr; cases s0; cases sf; exact this⟩,
        (by rw [hr_s00, w1t_cal_stripS_read64] at htag1; exact htag1),
        w1t_cal_stripExecOutside_hmacSt.mp hhmac1,
        unstrip_frame hframe1 hvm.perm_eq⟩
    · exact hsf_real
  rcases hsf_raw with ⟨hpc_sf, hstat_sf, hcallee, hret_sf, hst_sf, hframe_sf⟩
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hstat_sf, ?_,
    CallingConventionPreserved_of_calleeSaved hcallee hvregs⟩⟩
  dsimp only [withLsCodeRoLoaded, newFromSliceBudgetSpec, withVmPreserved, newFromSliceSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr, ?_⟩
  rw [hx0] at hret_sf hst_sf hframe_sf
  rw [hx1, hx2_nat, hkey_eq] at hst_sf
  have hpost_sep := Frame.update_two_blocks hb_out
    (isBlock_nfsResult F ret key) hb_stk hb_stk hsep_out hframe_sf ⟨hret_sf, hst_sf⟩ trivial
  simp only [newFromSliceStack, stackAt]
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost_sep

private theorem w1t_cal_compress256 (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W) lsCompress256Sym =
      some (compress256Hook W.C.F) :=
  (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_other g
    (cliExternsPlaced mmpl W) (sym := lsCompress256Sym)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (CryptoVerification.SignalSession.Cli.Slots.cliExternsPlaced_compress256 mmpl W)

private theorem w1t_cal_new_from_slice_cro_budget_ok_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 114)
      (withLsCodeRoLoaded lsmpl (newFromSliceBudgetSpec W.C.F)) :=
  new_from_slice_placed_cro_budget_ok_at_block_sat (callerProg := callerProg) (i := i) W.C.F
    (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)
    (w1t_cal_compress256 mmpl g W) hi

private theorem w1t_cal_hmac_vm_cro_ok_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 73)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hmacSpec W.C.F))) :=
  hmac_placed_cro_ok_at_block_sat (callerProg := callerProg) (i := i) W.C.F
    (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)
    (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
    (w1t_cal_compress256 mmpl g W) hi

private theorem w1t_publicApiEncHooks [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hG : CliGhostAllocHooks M A lim g)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    PublicApiEncHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  shim := cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq
  alloc := cliExternsPlaced_alloc_budget_sat mmpl g W hG
  dealloc := cliExternsPlaced_dealloc_budget_sat mmpl g W hG
  realloc := cliExternsPlaced_realloc_budget_sat mmpl g W hG
  memcpy := cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG
  stringClone := hh.stringClone
  timeAdd := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
    (cliExternsPlaced_timeAdd_budget_sat mmpl W)
  durationSince := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
    (cliExternsPlaced_durationSinceBounded_budget_sat mmpl W)
  handleError := cliGhostExterns_panic_handle_error mmpl g W
  handleAllocError := cliGhostExterns_panic_handle_alloc_error mmpl g W
  expectFailed := cliGhostExterns_panic_option_expect_failed mmpl g W

private theorem w1t_generateKeys_428_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_428).rebase (blkPl_428).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim W.C.F)) := by
  haveI : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    ⟨cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG,
     cliExternsPlaced_exactMemcpy_sat mmpl g W hG,
     w1t_cal_compress256 mmpl g W⟩
  have hext69 := extract_placed_vm_ok_of_other_block_sat W.C
    (callerProg := (blkPC_69).rebase (blkPl_69).base
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (cliGhostExterns g (cliExternsPlaced mmpl W))
  have hexp69 := expand_multi_info_placed_vm_ok_of_other_block_sat W.C
    (callerProg := (blkPC_69).rebase (blkPl_69).base
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (cliGhostExterns g (cliExternsPlaced mmpl W))
  have hdealloc69 := keys_ls_hook_ok_of_mem
    (prog := (blkPC_69).rebase (blkPl_69).base
      (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 69)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
  have hgk69 := generateKeys_placed_ok_of_contracts (C := W.C) hext69 hexp69 hdealloc69
  have _ := instIsLsBlockProg_428 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact transfer_tr_cro_of_block
    (callerProg := (blkPC_428).rebase (blkPl_428).base
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (calleeProg := (blkPC_69).rebase (blkPl_69).base
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    hgk69

private theorem w1t_signalMessageNew_428_placed_cro_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_428).rebase (blkPl_428).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 63)
      (withLsCodeRoLoaded lsmpl (signalMessageNewSpec M A lim W.C.F uuidTryParse)) := by
  have hNoAlloc := cliExternsPlaced_noAllocShim_budget_sat mmpl g W hG.shim_eq
  have hshim_b := w1t_cal_hookSat_noAllocShimBudget_of_withVmPreserved hNoAlloc
  have hAlloc := cliExternsPlaced_alloc_budget_sat mmpl g W hG
  have hDealloc := cliExternsPlaced_dealloc_budget_sat mmpl g W hG
  have hRealloc := cliExternsPlaced_realloc_budget_sat mmpl g W hG
  have hpks205 := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (public_key_serialize_placed_ok hshim_b hAlloc)
  have hparse206 := parseSid_placed_ok_of_code (cliGhostExterns g (cliExternsPlaced mmpl W))
    (uuidTryParse_252_vm_placed_ok (cliGhostExterns g (cliExternsPlaced mmpl W)))
  have hparse61 := ls_subroutine_ok_of_block
    (callerProg := (blkPC_61).rebase (blkPl_61).base
      (cliGhostExterns g (cliExternsPlaced mmpl W))) hparse206
  have hser61 := serialize_addresses_placed_ok_of_rustAllocShimVm hparse61
    (cliExternsPlaced_rustAllocShimVm_sat mmpl g W hG.shim_eq)
    hAlloc
  have hmac60 := computeMac_placed_cro_ok W.C M A lim
    (cliGhostExterns g (cliExternsPlaced mmpl W))
    (w1t_cal_new_from_slice_cro_budget_ok_at_block mmpl g W hG
      (callerProg := (blkPC_60).rebase (blkPl_60).base
        (cliGhostExterns g (cliExternsPlaced mmpl W))))
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block
        (callerProg := (blkPC_60).rebase (blkPl_60).base
          (cliGhostExterns g (cliExternsPlaced mmpl W))) hpks205))
    (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_compress256Multi_budget_sat mmpl W))
    hDealloc
    (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
  have hnew63 := signalMessageNew_placed_cro_ok (C := W.C)
    hNoAlloc
    hAlloc
    hDealloc
    (cliExternsPlaced_framelessMemcpy_budget_sat mmpl g W hG)
    (ls_subroutine_ok_of_block
      (callerProg := (blkPC_63).rebase (blkPl_63).base
        (cliGhostExterns g (cliExternsPlaced mmpl W))) hpks205)
    (ls_subroutine_ok_of_block
      (callerProg := (blkPC_63).rebase (blkPl_63).base
        (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
        (encoded_len_placed_ok A.repAlloc (cliGhostExterns g (cliExternsPlaced mmpl W)))))
    (ls_subroutine_ok_of_block
      (callerProg := (blkPC_63).rebase (blkPl_63).base
        (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (encode_varint_placed_ok hshim_b hAlloc hRealloc))
    (ls_subroutine_ok_of_block
      (callerProg := (blkPC_63).rebase (blkPl_63).base
        (cliGhostExterns g (cliExternsPlaced mmpl W))) hser61)
    (transfer_tr_cro_of_block
      (callerProg := (blkPC_63).rebase (blkPl_63).base
        (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (calleeProg := (blkPC_60).rebase (blkPl_60).base
        (cliGhostExterns g (cliExternsPlaced mmpl W))) hmac60)
  have _ := instIsLsBlockProg_428 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact transfer_tr_cro_of_block
    (callerProg := (blkPC_428).rebase (blkPl_428).base
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (calleeProg := (blkPC_63).rebase (blkPl_63).base
      (cliGhostExterns g (cliExternsPlaced mmpl W))) hnew63

private theorem w1t_otrRoCalleesPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hG : CliGhostAllocHooks M A lim g)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    OtrRoCalleesPlacedOk mmpl g W A lim := by
  have _ := instIsLsBlockProg_428 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact
    { messageKeys := transfer_tr_cro_of_block
        (callerProg := (blkPC_428).rebase (blkPl_428).base
          (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (calleeProg := (blkPC_38).rebase (blkPl_38).base
          (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (message_keys_placed_cro_ok
          (w1t_cal_hmac_vm_cro_ok_at_block mmpl g W hG
            (callerProg := (blkPC_38).rebase (blkPl_38).base
              (cliGhostExterns g (cliExternsPlaced mmpl W))))
          (cliExternsPlaced_noAllocShim_budget_sat mmpl g W hG.shim_eq)
          (cliExternsPlaced_alloc_budget_sat mmpl g W hG))
      signalMessageNew := w1t_signalMessageNew_428_placed_cro_ok mmpl g W A lim hG
      nextChainKey := transfer_tr_cro_of_block
        (callerProg := (blkPC_428).rebase (blkPl_428).base
          (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (calleeProg := (blkPC_39).rebase (blkPl_39).base
          (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (nextChainKey_39_vm_cro_ok
          (w1t_cal_hmac_vm_cro_ok_at_block mmpl g W hG
            (callerProg := (blkPC_39).rebase (blkPl_39).base
              (cliGhostExterns g (cliExternsPlaced mmpl W))))
          (hh.panics lsPanicConstAddOverflowSym (by decide))) }

/-- Byte-slice projection of a `SendCall`-indexed block-427 envelope. -/
def w1t_sendBytesEnvOf (SendEnv : SendCall → List AllocEvent → Prop) : SpqrSendBudgetEnv :=
  fun stBs rest evs =>
    SendEnv { ret := 0#64, st := ⟨0#64, 0#64, 0#64, stBs⟩, cur := 0#64, rest := rest } evs

/-- Block-464 `W1InnerPlacedOk` at `w1t_sendBytesEnvOf SendEnv` from a parametric `.spqrSendCoins` seam. -/
theorem w1t_w1Inner_of_sendCoins [LibsignalFullPlacement]
    {mmpl : MultiPlacement}
    (brkStart : BitVec 64)
    (ghFixed : CliGhostHooks) (hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (SendEnv : SendCall → List AllocEvent → Prop)
    (hSend427 : subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv)))
    (hSendEmpty : ∀ rest, w1t_sendBytesEnvOf SendEnv [] rest [])
    (hSend_ptr_congr : ∀ (sc : SendCall) (evs : List AllocEvent),
      SendEnv sc evs ↔ w1t_sendBytesEnvOf SendEnv sc.st.bytes sc.rest evs)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ghFixed)
    (_hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : CliRunHooksBundle mmpl ghFixed W
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : lsmpl.base 547 ≠ 0#64) :
    W1InnerPlacedOk mmpl ghFixed W
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      cliRunBudgets scopeIn (w1t_sendBytesEnvOf SendEnv)
      (w1BinarySessKitPlacedBudgetFixed
        (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc cliRunBudgets)
      (w1BinaryIdKitPlacedBudgetFixed
        (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc cliRunBudgets) := by
  let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
  let H := cliGhostExterns ghFixed (cliExternsPlaced mmpl W)
  have hG := hGSpqr.toCliGhostAllocHooks
  have hh := hHooks.runHooks
  have hhooks := w1t_publicApiEncHooks mmpl ghFixed W A cliBudgetLimits hG hh
  have hAesEnc : HookSat H lsAesEncSym (aesEncBudgetSpec W.C.E fineCostModel A cliBudgetLimits) :=
    cliGhostExterns_sat_of_cliExternsPlaced mmpl ghFixed W
      (fineAesEnc_budget_hookSat γ tp brkStart cliBudgetLimits hPl_mng W.C.E
        (cliExternsPlaced_row mmpl W (aesEnc_row_placed mmpl W)))
  have hFmtEnv : HookSat H CryptoVerification.LibsignalTripleRatchet.Encrypt.lsFormatInnerSym
      (formatInnerBudgetEnvSpec fineCostModel A cliBudgetLimits FormatInnerEnv) :=
    hh.formatInner
  have hOtrRo := w1t_otrRoCalleesPlacedOk mmpl ghFixed W A cliBudgetLimits hG hh
  have _ := instIsLsBlockProg_427 H
  have _ := instIsLsBlockProg_464 H
  have _ := instIsLsBlockProg_428 H
  have hSend_eq : SendEnv = fun sc evs => w1t_sendBytesEnvOf SendEnv sc.st.bytes sc.rest evs := by
    funext sc evs; exact propext (hSend_ptr_congr sc evs)
  have hSend427_bytes :
      subroutine_ok ((blkPC_427).rebase (blkPl_427).base H) (lsmpl.base 427)
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
          (spqrSendCoinsPlacedSpecTOfEnv fineCostModel A cliBudgetLimits 0#64
            (pqxdhSpqrModel ⟨W.C, W.Q⟩)
            (fun sc evs => w1t_sendBytesEnvOf SendEnv sc.st.bytes sc.rest evs))) :=
    hSend_eq ▸ hSend427
  have hSend428 := w1t_cal_subroutine_ok_trCro_of_storeKitCro
    (subroutine_ok_withLsCodeRoLoaded_of_rocl (ls_subroutine_ok_rocl_of_block
      (callerProg := (blkPC_428).rebase (blkPl_428).base H)
      hSend427_bytes (by decide) (by decide) (by decide)))
  have hOtrT :
      subroutine_ok (lsProg_464 H) (libsignalSessionLib.fnAddr lsmpl otrEncryptName)
        (withLsRoCl lsmpl
          (otrEncryptPlacedSpecQF (fun st rest => st.length < 2 ^ 32 ∧ 64 ≤ rest.length)
            tokenInitPlacedAt W.C A cliBudgetLimits 0#64 uuidTryParse
            (pqxdhSpqrModel ⟨W.C, W.Q⟩) (w1t_sendBytesEnvOf SendEnv))) := by
    have h428 := otrEncryptV1_coins_placed_ok tokenInitPlacedAt W.C A cliBudgetLimits 0#64
      (pqxdhSpqrModel ⟨W.C, W.Q⟩) (w1t_sendBytesEnvOf SendEnv) H
      hAesEnc hFmtEnv (cliExternsPlaced_dealloc_budget_sat mmpl ghFixed W hG)
      hSend428 hOtrRo.messageKeys
      (w1t_generateKeys_428_placed_ok mmpl ghFixed W A cliBudgetLimits hG)
      hOtrRo.signalMessageNew hOtrRo.nextChainKey
    have h428' := w1t_cal_subroutine_ok_storeKitCro_of_trCro h428
    change subroutine_ok _ (lsmpl.base 428 + 0#64) _
    rw [BitVec.add_zero]
    exact ls_subroutine_ok_rocl_of_block
      (callerProg := lsProg_464 H) (j := 428) h428' (by decide) (by decide) (by decide)
  have hOtrEmpty :
      subroutine_ok (lsProg_464 H) (libsignalSessionLib.fnAddr lsmpl otrEncryptName)
        (withLsRoCl lsmpl
          (otrEncryptPlacedSpecQ (· = []) W.C A cliBudgetLimits 0#64 uuidTryParse
            (pqxdhSpqrModel ⟨W.C, W.Q⟩) (w1t_sendBytesEnvOf SendEnv))) := by
    have h428 := otrEncryptEmpty_coins_placed_ok W.C A cliBudgetLimits 0#64
      (pqxdhSpqrModel ⟨W.C, W.Q⟩) (w1t_sendBytesEnvOf SendEnv) H
      (spqrV1_emptyOk W.C.F W.Q.K) hSendEmpty
      (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl ghFixed W hG)
      hAesEnc hFmtEnv (cliExternsPlaced_dealloc_budget_sat mmpl ghFixed W hG)
      hOtrRo.messageKeys
      (w1t_generateKeys_428_placed_ok mmpl ghFixed W A cliBudgetLimits hG)
      hOtrRo.signalMessageNew hOtrRo.nextChainKey
    have h428' := w1t_cal_subroutine_ok_storeKitCro_of_trCro h428
    change subroutine_ok _ (lsmpl.base 428 + 0#64) _
    rw [BitVec.add_zero]
    exact ls_subroutine_ok_rocl_of_block
      (callerProg := lsProg_464 H) (j := 428) h428' (by decide) (by decide) (by decide)
  have hRead589 :
      subroutine_ok (lsProg_589 H) (lsρ lsReadFileSym)
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
          (readFileSpecPlaced cliIo.rd cliWrOk A cliBudgetLimits cliRunBudgets.readFile
            (ReadFileRuleEnvFixed cliIo.rd))) :=
    subroutine_ok_withLsCodeRoLoaded_of_plain
      (ls_hook_ok_ultra_of_mem (prog := lsProg_589 H) (i := 589) hsat
        (by decide) (by decide) (by decide))
  have hDeser46 := sessDeserialize_cli_dcan_byBytes_placed_ok mmpl ghFixed W
    (Scope := scopeKit) (A := A) (lim := cliBudgetLimits) hG (fun _ h => h)
  have hDeser569 := subroutine_ok_withLsCodeRoLoaded_of_rocl
    (ls_subroutine_ok_rocl_of_block (callerProg := lsProg_569 H) (j := 46)
      hDeser46 (by decide) (by decide) (by decide))
  have hSer52 := serializeCanonSeqFree_cli_placed mmpl ghFixed W hG
  have hTails := @w1t_encTailsVTPlaced _ fineCostModel A cliBudgetLimits
  intro F peer hok
  exact withStores_placed_okVT_fs_cli hhooks
    (w1BinarySessKitPlacedFixed_okSE cliRunBudgets F peer h547 hh hRead589 hDeser569 hSer52)
    (cliIdKitOkIE_placed
      (rd := cliIo.rd) (F0 := F) (pathOk := cliWrOk) (peer := peer)
      (readStk := cliRunBudgets.readFile)
      (s1 := trustShimNeed) (s2 := trustPollNeed cliRunBudgets.readFile)
      (s3 := saveShimNeed) (s4 := savePollNeed cliRunBudgets.readFile)
      (vtSym := cliIdentityVtRoSym)
      (readProg := lsProg_589 H) (jRead := 589)
      h547 (fun _ hp => hp.2) hh hRead589
      (cliGhostExterns_blackBox mmpl ghFixed W)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (by decide) (by decide))
    hOtrT hOtrEmpty
    (w2SessVt_placed_ok A.repAlloc cliRunBudgets h547 F peer)
    (w2IdVt_placed_ok A.repAlloc cliRunBudgets h547 F peer)
    (Or.inr ⟨⟨⟨fun _ _ _ => NoFsEv.nil, fun _ _ _ _ => NoFsEv.nil⟩,
      ⟨fun _ _ _ _ => NoFsEv.nil, fun _ _ _ => NoFsEv.nil⟩⟩,
      hh.fs (lsProg_464 H) 464⟩)
    (fun r ⟨hsc, _⟩ => scopeKit_recordInScopeEnc hsc)
    (fun r s ⟨hsc, _⟩ hsess => scopeKit_pqrState_lt hsc s hsess)
    (fun {x r sess otr taken k m otr'} haddr h15 =>
      cliEncRecOk_opened (A := A.repAlloc) (b := 0#64) (pathOk := cliWrOk)
        (Scope₀ := scopeIn) (F0 := F) (peer := peer) (s1 := 0) (s2 := 0) (s3 := 0) (s4 := 0)
        (C := W.C) (K := W.Q.K) (parse := uuidTryParse)
        (fun _ h => h) hok haddr h15)
    (hTails hhooks)

/-- Outer block-579 `encrypt` slot contract parametric in `SendEnv`. -/
theorem w1t_hole3_w1_inner_of_sendCoins [LibsignalFullPlacement]
    {mmpl : MultiPlacement}
    (brkStart : BitVec 64)
    (ghFixed : CliGhostHooks) (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (SendEnv : SendCall → List AllocEvent → Prop)
    (hSend427 : subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv)))
    (hSendEmpty : ∀ rest, w1t_sendBytesEnvOf SendEnv [] rest [])
    (hSend_ptr_congr : ∀ (sc : SendCall) (evs : List AllocEvent),
      SendEnv sc evs ↔ w1t_sendBytesEnvOf SendEnv sc.st.bytes sc.rest evs)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : CliRunHooksBundle mmpl ghFixed W
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : lsmpl.base 547 ≠ 0#64) :
    (mkSlot
      (encSlotSpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (CliEncryptSlotEnv ⟨W.C, W.Q⟩
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
          (w1t_sendBytesEnvOf SendEnv)
          (w1BinarySessKitPlacedBudgetFixed
            (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc cliRunBudgets)
          (w1BinaryIdKitPlacedBudgetFixed
            (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc cliRunBudgets))
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (lsmpl.base 464) := by
  intro stk h1 h2
  exact cliEncrypt_slot_placed (i := 579) mmpl ghFixed W
    (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
    cliRunBudgets (cliRunSemD2c_placed X W) scopeIn (w1t_sendBytesEnvOf SendEnv)
    (w1BinarySessKitPlacedBudgetFixed
      (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc cliRunBudgets)
    (w1BinaryIdKitPlacedBudgetFixed
      (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc cliRunBudgets)
    hHooks.runHooks
    (w1t_w1Inner_of_sendCoins brkStart ghFixed hPl_mng W γ tp SendEnv hSend427 hSendEmpty
      hSend_ptr_congr hGSpqr hFs hsat hHooks h547)
    encodeInjOn_deserializeScopeP_Q (fun _ h => h) rfl
    (fun _ _ _ _ hf he => ⟨hf.1, he⟩) stk h1 h2

/-- Constructs `LibsignalFullPlacement` from `libsignalSessionLib.LinkedAt elfBytes mpl`. -/
@[instance_reducible]
def w1t_libsignalFullPlacementOf {elfBytes : List (BitVec 8)} (mpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt elfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup) : LibsignalFullPlacement where
  toLibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  placeable := hLs.choose_spec.2.1

/-- Guarded-tight binary-kit `W1` (`encrypt`) slot envelope (`maxOps = 109`). -/
noncomputable def w1t_cliEncryptBinaryKitSlotEnvExact [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets) :
    EncGhost → List AllocEvent → Prop :=
  let sendEnv : SpqrSendBudgetEnv := w1t_SendTightBytesEnv W.C.F W.Q.K
  fun x evs =>
    PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
      CliEncryptSlotEnv ⟨W.C, W.Q⟩ A B sendEnv
        (w1BinarySessKitPlacedBudgetFixed A.repAlloc B)
        (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B)
        x evs

private theorem w1t_seqEnv_congr {P₁ P₂ Q₁ Q₂ : List AllocEvent → Prop}
    (hP : P₁ = P₂) (hQ : Q₁ = Q₂) : SeqEnv P₁ Q₁ = SeqEnv P₂ Q₂ :=
  hP ▸ hQ ▸ rfl

private theorem w1t_slotEnv_eq_of_peer [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (x : EncGhost)
    (hPeer : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val) :
    CliEncryptSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets
        (w1t_SendGuardedBytesEnv W.C.F W.Q.K)
        (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets) x =
      w1t_cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets x := by
  funext evs
  have hsend_eq_on (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (hSt : SpqrStateTight640 W.C.F W.Q.K otr.pqrState) :
      w1t_SendGuardedBytesEnv W.C.F W.Q.K otr.pqrState =
        w1t_SendTightBytesEnv W.C.F W.Q.K otr.pqrState := by
    funext rest evs0
    exact propext ⟨fun h => h hSt, fun h _ => h⟩
  have hotr_core (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (hSt : SpqrStateTight640 W.C.F W.Q.K otr.pqrState)
      (ptext : List (BitVec 8)) (loc : Option AddrGhost) (rem : AddrGhost)
      (rest : List (BitVec 8)) :
      OtrEncryptCoreEnv W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (w1t_SendGuardedBytesEnv W.C.F W.Q.K) uuidTryParse otr ptext loc rem rest =
        OtrEncryptCoreEnv W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (w1t_SendTightBytesEnv W.C.F W.Q.K) uuidTryParse otr ptext loc rem rest := by
    unfold OtrEncryptCoreEnv
    exact w1t_seqEnv_congr (congrFun (hsend_eq_on otr hSt) rest) rfl
  have hfrom_otr (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8)))
      (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8)))
      (hScAt : (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget.w1SessKitPlaced
        A.repAlloc cliRunBudgets x.F x.peer).ScopeAt
        scopeKit StoresGhost.opened.sessions (w1EncGhost x).rem.val r)
      (hcur : r.currentSession = some sess)
      (hotr : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken)) :
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromOtrEnv
          W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) (w1t_SendGuardedBytesEnv W.C.F W.Q.K)
          uuidTryParse
          (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget.w1SessKitPlaced
            A.repAlloc cliRunBudgets x.F x.peer)
          (LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsKitEnv
            (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets x.F x.peer))
          StoresGhost.opened.sessions
          (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget.w1IdKitPlaced
            A.repAlloc cliRunBudgets x.F x.peer)
          (LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsIkitEnv
            (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets x.F x.peer))
          StoresGhost.opened.identity (w1EncGhost x) sess otr taken =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromOtrEnv
          W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) (w1t_SendTightBytesEnv W.C.F W.Q.K)
          uuidTryParse
          (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget.w1SessKitPlaced
            A.repAlloc cliRunBudgets x.F x.peer)
          (LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsKitEnv
            (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets x.F x.peer))
          StoresGhost.opened.sessions
          (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget.w1IdKitPlaced
            A.repAlloc cliRunBudgets x.F x.peer)
          (LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsIkitEnv
            (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets x.F x.peer))
          StoresGhost.opened.identity (w1EncGhost x) sess otr taken := by
    have hrem : (w1EncGhost x).rem.val = x.peer.val := rfl
    have hTop :=
      LibsignalBinary.Proofs.PeakBudget.SpqrSendTieLemmas.topStateTight_of_cliSessionStoreSpecPlaced_fromSessionState
        (A := A.repAlloc) (F := W.C.F) (K := W.Q.K) (files := x.F)
        (pathOk := cliWrOk) (peer := x.peer)
        (s1 := CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadShimNeed)
        (s2 := CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadPollNeed cliRunBudgets.readFile)
        (s3 := CryptoVerification.SignalSession.Cli.KitInst.SessKit.storeShimNeed)
        (s4 := CryptoVerification.SignalSession.Cli.KitInst.SessKit.storePollNeedX)
        hScAt hcur hotr (hrem.symm ▸ hPeer)
    have hSt : SpqrStateTight640 W.C.F W.Q.K otr.pqrState := Or.inr hTop
    funext evs1
    unfold
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromOtrEnv
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromKeyEnv
    rw [hotr_core otr hSt, hotr_core otr hSt]
  unfold w1t_cliEncryptBinaryKitSlotEnvExact CliEncryptSlotEnv
    LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.WithStoresEncEnv
  dsimp only
  refine propext ⟨fun h _ => ?_, fun h => ?_⟩
  · rcases h with h0 | ⟨e1, e2, rfl, h1, h2⟩
    · exact Or.inl h0
    · refine SeqEnv.append h1 ?_
      rcases h2 with hf | hstr | hseq
      · exact Or.inl hf
      · exact Or.inr (Or.inl hstr)
      · refine Or.inr (Or.inr ?_)
        rcases hseq with hf | ⟨ea, eb, rfl, ha, hb⟩
        · exact Or.inl hf
        · refine SeqEnv.append ha ?_
          rcases hb with hf | ⟨r, sess, otr, taken, hScAt, hcur, hotr, hfo⟩
          · exact Or.inl hf
          · refine Or.inr ⟨r, sess, otr, taken, hScAt, hcur, hotr, ?_⟩
            rwa [← hfrom_otr r sess otr taken hScAt hcur hotr]
  · have h' := h hPeer
    rcases h' with h0 | ⟨e1, e2, rfl, h1, h2⟩
    · exact Or.inl h0
    · refine SeqEnv.append h1 ?_
      rcases h2 with hf | hstr | hseq
      · exact Or.inl hf
      · exact Or.inr (Or.inl hstr)
      · refine Or.inr (Or.inr ?_)
        rcases hseq with hf | ⟨ea, eb, rfl, ha, hb⟩
        · exact Or.inl hf
        · refine SeqEnv.append ha ?_
          rcases hb with hf | ⟨r, sess, otr, taken, hScAt, hcur, hotr, hfo⟩
          · exact Or.inl hf
          · refine Or.inr ⟨r, sess, otr, taken, hScAt, hcur, hotr, ?_⟩
            rwa [hfrom_otr r sess otr taken hScAt hcur hotr]

/-- Block-464 `encrypt` (`W1`) slot witness parameterized by block 325's `DecodeStatePlacedOkOfEnv`. -/
theorem w1t_hole3_w1_inner_of_decodeState
    {elfBytes : List (BitVec 8)} {brkStart : BitVec 64}
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt elfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64)
    (h325 : @DecodeStatePlacedOkOfEnv (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
      canonicalV1InnerHeap (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
      (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) :
    letI : LibsignalFullPlacement := w1t_libsignalFullPlacementOf mpl hLs hblk hext_nodup
    (mkSlot
      (encSlotSpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (w1t_cliEncryptBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464) := by
  letI : LibsignalFullPlacement := w1t_libsignalFullPlacementOf mpl hLs hblk hext_nodup
  let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
  have hSend427 := w1t_cliSpqrSendCoins_placed_ok_guarded_of_decodeState
    γ mmpl tp brkStart cliBudgetLimits ghFixed W hPl_mng hGSpqr h325
  have hSlot := w1t_hole3_w1_inner_of_sendCoins brkStart ghFixed hPl_mng X W γ tp
    (w1t_SendGuardedEnv W.C.F W.Q.K) hSend427
    (w1t_sendGuardedBytes_empty W.C.F W.Q.K)
    (fun _ _ => Iff.rfl)
    hGSpqr hFs hsat hHooks h547
  intro stk h1 h2
  have hok := hSlot stk h1 h2
  exact subroutine_ok_mono hok
    (fun (x, st) _ _ hpre => by
      dsimp only [mkSlot, CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        encSlotSpecPlaced] at hpre ⊢
      refine Satisfies.mono ?_ hpre
      refine sepConj_mono_left ?_
      refine sepConj_mono_left ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, hfit⟩ => by
        by_cases hPeer : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val
        · have heq : w1t_sendBytesEnvOf (w1t_SendGuardedEnv W.C.F W.Q.K) =
              w1t_SendGuardedBytesEnv W.C.F W.Q.K := rfl
          rw [heq, w1t_slotEnv_eq_of_peer W A x hPeer]
          exact ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, hfit⟩
        · exact False.elim
            (w1t_s427_not_fitsEnv_of_univ (fun _ hp => False.elim (hPeer hp)) hfit))
    (fun (x, st) _ _ _ hpost => by
      dsimp only [mkSlot, CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        encSlotSpecPlaced] at hpost ⊢
      refine Satisfies.mono ?_ hpost
      refine sepConj_mono_left ?_
      refine Entails.sepExists_mono fun evs => ?_
      refine Entails.sepExists_mono fun g' => ?_
      refine Entails.sepExists_mono fun e => ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨hevs, htr, hout, hser⟩ => by
        by_cases hPeer : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val
        · have heq : w1t_sendBytesEnvOf (w1t_SendGuardedEnv W.C.F W.Q.K) =
              w1t_SendGuardedBytesEnv W.C.F W.Q.K := rfl
          rw [heq, w1t_slotEnv_eq_of_peer W A x hPeer] at hevs
          exact ⟨hevs, htr, hout, hser⟩
        · exact ⟨fun hp => False.elim (hPeer hp), htr, hout, hser⟩)
    (fun _ _ _ _ hp => hp)

/-- Specializes `w1t_hole3_w1_inner_of_decodeState` using `e2a_decodeState_cl_placed_ok_of_v1Merge_109` and block 298/299 merge contracts. -/
theorem w1t_hole3_w1_inner_of_e2a325
    {elfBytes : List (BitVec 8)} {brkStart : BitVec 64}
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt elfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64)
    (hE2a325 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      DecodeStateCalleeContractsClPlacedX canonicalV1InnerHeap
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) →
      tlb_EpochDirectionMergeBlk325TightOkOf
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits 2 4
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) →
      tlb_V1StateMergeBlk325TightOkOf
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits 80
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) →
      DecodeStatePlacedOkOfEnv canonicalV1InnerHeap
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
        (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hEpochDir :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      DecodeStateCalleeContractsClPlacedX canonicalV1InnerHeap
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) →
      tlb_EpochDirectionMergeBlk325TightOkOf
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits 2 4
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hV1Merge :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      tlb_V1StateMergeBlk325TightOkOf
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits 80
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) :
    letI : LibsignalFullPlacement := w1t_libsignalFullPlacementOf mpl hLs hblk hext_nodup
    (mkSlot
      (encSlotSpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (w1t_cliEncryptBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  have hc := w1t_decodeStateCalleeContractsClPlacedX_cli mmpl ghFixed W hGSpqr.toCliGhostAllocHooks
  exact w1t_hole3_w1_inner_of_decodeState
    hLs hblk hext_nodup ghFixed hPl_mng X W γ tp hGSpqr hFs hsat hHooks h547
    (hE2a325 hc (hEpochDir hc) hV1Merge)

end W1T_Slot

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W1InnerTight
